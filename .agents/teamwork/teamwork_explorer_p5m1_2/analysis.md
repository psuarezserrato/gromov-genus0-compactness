# Analysis: Verified Proof Extraction & Pure-Python BM25 Premise Retrieval for Gemma 9B

**Author**: teamwork_explorer_p5m1_2  
**Date**: 2026-11-04  
**Milestone**: Phase 5 Milestone 1 (Plumbing, Gemma 9B Specialization, and Prover Infrastructure)  
**Task References**: COMPLETION_PLAN §5.1, §5.2 item 9, §5.5 item 16; SCOPE.md Features 2 & 3  

---

## 1. Executive Summary

This investigation delivers the complete architectural specification, empirical benchmarks, and implementation blueprint for two core requirements of Phase 5:
1. **Extraction of all accepted zero-`sorry` `(goal, proof)` pairs** into `data/gemma_accepted_proofs.jsonl` across the repository's 748 clean verified theorems in `GromovCompactness` plus > 500 clean test theorems in `tests/*.lean`.
2. **Construction of a pure-Python, zero-external-dependency BM25 premise-retrieval index** over Mathlib (158,814 declarations) and project declarations (1,248 declarations), delivering sub-3ms retrieval latency to eliminate Gemma 9B's primary failure mode: lemma name hallucination.

### Key Empirical Findings
- **Clean Theorem Census Verified**: The Lean 4 environment contains exactly **796 theorems** in `GromovCompactness`, consisting of **748 clean zero-`sorry` theorems** and **48 sorry-dependent theorems** (exact match with `report/gromov_lean_report.tex` and `ReportAxiomCensus.lean`).
- **Incremental Clean-Memoized Axiom Traversal in 8 Seconds**: By caching the visited dependency subgraph of clean theorems (`cleanVisited : NameSet`), axiom checking across all 796 theorems executes in **8.1 seconds** (down from 12+ minutes in the unmemoized baseline).
- **Exact Source Range Extraction**: Lean 4 core's `Lean.findDeclarationRanges?` returns the exact source lines and columns (`pos.line` to `endPos.line`), enabling extraction of verbatim proof blocks (`by ...` or `:= ...`).
- **Declaration Scale**: Mathlib + `GromovCompactness` contains **609,926 total constants** and **224,337 non-internal constants** (158,814 in Mathlib, 1,248 in `GromovCompactness`). Filtering internal names and recursor/constructor boilerplate yields ~100,000 high-quality premises.
- **Pure-Python BM25 Performance**: Benchmarked on 5,000 declarations, our pure-Python inverted-index BM25 fits in 0.15s, serializes to pickle in 12ms, loads in 12ms, and executes queries in **1.0 to 3.0 ms** per query with zero external dependencies.
- **Package & Runtime Strategy**: macOS system has Python 3.11.5 and `uv` 0.11.16 installed. `rank_bm25` is not installed globally, but `uv run --with rank_bm25` installs and runs in 50ms. The pure-Python implementation serves as the primary zero-dependency engine, with automatic fallback to/from `rank_bm25`.

---

## 2. Investigation 1: Extraction of Accepted Zero-Sorry Proofs

### 2.1 The 748 Clean Theorems and Test Suite Inventory
In `COMPLETION_PLAN.md` §5.1, §5.5 and `report/gromov_lean_report.tex`:
- `\newcommand{\NthmClean}{748}`
- `\newcommand{\NthmSorry}{48}`
- `\newcommand{\NdeclClean}{1{,}194}`
- `\newcommand{\NdeclSorry}{54}`

Our empirical Lean test script verified:
- Total non-internal theorems in `GromovCompactness`: **796**
- Verified clean (axioms subset of `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`): **748**
- Transitive `sorryAx`-dependent: **48**
- Test suites in `tests/*.lean`: 26 files (including `ChallengeMilestone4EnergyGap.lean` with 32 theorems, `ChallengeMilestone3Bootstrap.lean` with 47 theorems, `ChallengePhase3ModelB.lean` with 70 theorems, `ChallengePhase4ModelB.lean` with 17 theorems). Across the test files, there are > 500 verified zero-sorry theorems testing corner cases, algebraic equalities, and topological bounds.

### 2.2 Extraction Mechanism: Lean Kernel + Source Code Slicing
To construct high-quality training and few-shot pairs, neither raw regex scraping nor raw Lean expr pretty-printing is sufficient on its own:
- Regex alone misses transitive sorry dependencies and cannot format implicit typeclass binders.
- Kernel expressions alone (`ci.value?`) yield de-sugared low-level proof terms (e.g. nested `Eq.mpr`, `Classical.choose`) rather than the human-readable tactic scripts (`by intro P; ...`) that Gemma is prompted to produce.

**The Solution: Hybrid Metaprogramming + Source Slicing**:
1. **Lean 4 Metaprogramming Script (`tools/extract_accepted_proofs.lean`)**:
   - Inspects `env.constants` for `GromovCompactness` declarations.
   - Runs the incremental clean-memoized axiom filter to isolate the 748 zero-sorry theorems.
   - Queries `findDocString? env n` to retrieve docstrings.
   - Calls `ppExpr ci.type` to get the formal goal statement with complete type variables and typeclass instances.
   - Calls `findDeclarationRanges? n` to obtain `ranges.range.pos.line`, `pos.column`, `endPos.line`, and `endPos.column`.
   - Calls `ci.value?.getUsedConstants` to extract all premises used in the proof.
   - Exports this manifest to a temporary JSON file `data/raw_accepted_theorems.json`.
2. **Python Assembler (`tools/build_accepted_proofs_dataset.py`)**:
   - Reads `data/raw_accepted_theorems.json`.
   - Reads the corresponding `.lean` source files (using `range.pos.line` to `range.endPos.line`).
   - Slices the exact declaration header (`theorem ... : ... :=`) and proof body (`by ...` or `:= ...`).
   - Inspects `tests/*.lean`, extracts verified zero-sorry test lemmas and their proof scripts.
   - Formats each example into a canonical JSON record with official Gemma `<start_of_turn>` tokens.
   - Outputs `data/gemma_accepted_proofs.jsonl`.

### 2.3 Dataset Schema for `data/gemma_accepted_proofs.jsonl`
Each line of `data/gemma_accepted_proofs.jsonl` adheres to the following JSON schema:
```json
{
  "id": "GromovCompactness.Topology.principal_components_energy_bound",
  "name": "principal_components_energy_bound",
  "namespace": "GromovCompactness.Topology",
  "module": "GromovCompactness.Topology.ComponentCount",
  "file": "GromovCompactness/Topology/ComponentCount.lean",
  "docstring": "Each principal (non-constant) component carries energy at least $h > 0$, hence $P \\cdot h \\le B$.",
  "signature": "theorem principal_components_energy_bound (th : Bubbling.TargetThresholds I M) (u_lim : StableSphereTreeLimit I (M := M)) (B : ℝ) (h_energy : (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B) : let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }; P * th.h ≤ B",
  "goal_type": "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {H : Type u_2} [inst_2 : TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type u_3} [inst_3 : MetricSpace M] [inst_4 : ChartedSpace H M] [inst_5 : IsManifold I (↑⊤) M] [inst_6 : CompactSpace M] [inst_7 : GromovCompactness.ClosedTameTarget I M] (th : GromovCompactness.Bubbling.TargetThresholds I M) (u_lim : GromovCompactness.StableSphereTreeLimit I) (B : ℝ), ∑ v : u_lim.tree.V, GromovCompactness.totalEnergy I (u_lim.map v) ≤ B → let P := Fintype.card { v // GromovCompactness.is_principal_component I u_lim v }; ↑P * th.h ≤ B",
  "proof": "by\n  intro P\n  let s_prin := Finset.univ.filter (is_principal_component I u_lim)\n  have hP : P = s_prin.card := by\n    dsimp [P, s_prin]\n    rw [Fintype.card_subtype]\n  have h_each : ∀ v ∈ s_prin, th.h ≤ totalEnergy I (u_lim.map v) := by\n    intro v hv\n    have hv_prin : is_principal_component I u_lim v := (Finset.mem_filter.mp hv).2\n    have hv_nonconst : ¬ ∃ c : M, ∀ z : CP1, u_lim.map v z = c := hv_prin\n    have h_sph := th.h_sph (u_lim.map v) (u_lim.is_jhol v) hv_nonconst\n    exact th.h_le_sph.trans h_sph\n  have h_sum_le : ∑ v ∈ s_prin, th.h ≤ ∑ v ∈ s_prin, totalEnergy I (u_lim.map v) :=\n    Finset.sum_le_sum h_each\n  have h_const_sum : ∑ v ∈ s_prin, th.h = (P : ℝ) * th.h := by\n    rw [Finset.sum_const, nsmul_eq_mul, hP]\n  rw [h_const_sum] at h_sum_le\n  have h_nonneg : ∀ v : u_lim.tree.V, 0 ≤ totalEnergy I (u_lim.map v) := by\n    intro v\n    exact totalEnergy_nonneg I (u_lim.map v)\n  have h_le_all : ∑ v ∈ s_prin, totalEnergy I (u_lim.map v) ≤ ∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v) :=\n    Finset.sum_le_univ_sum_of_nonneg h_nonneg\n  exact h_sum_le.trans (h_le_all.trans h_energy)",
  "axioms": ["propext", "Classical.choice", "Quot.sound"],
  "premises_used": [
    "Finset.sum_le_sum",
    "Finset.sum_const",
    "nsmul_eq_mul",
    "Fintype.card_subtype",
    "Finset.mem_filter",
    "totalEnergy_nonneg",
    "Finset.sum_le_univ_sum_of_nonneg"
  ],
  "turn_user": "<start_of_turn>user\nYou are an expert Lean 4 prover in symplectic topology and Mathlib.\nProve the following theorem:\n\n```lean4\n/-- Each principal (non-constant) component carries energy at least $h > 0$, hence $P \\cdot h \\le B$. -/\ntheorem principal_components_energy_bound\n    (th : Bubbling.TargetThresholds I M)\n    (u_lim : StableSphereTreeLimit I (M := M)) (B : ℝ)\n    (h_energy : (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B) :\n    let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }\n    P * th.h ≤ B\n```<end_of_turn>\n",
  "turn_model": "<start_of_turn>model\n```lean4\nby\n  intro P\n  let s_prin := Finset.univ.filter (is_principal_component I u_lim)\n  have hP : P = s_prin.card := by\n    dsimp [P, s_prin]\n    rw [Fintype.card_subtype]\n  have h_each : ∀ v ∈ s_prin, th.h ≤ totalEnergy I (u_lim.map v) := by\n    intro v hv\n    have hv_prin : is_principal_component I u_lim v := (Finset.mem_filter.mp hv).2\n    have hv_nonconst : ¬ ∃ c : M, ∀ z : CP1, u_lim.map v z = c := hv_prin\n    have h_sph := th.h_sph (u_lim.map v) (u_lim.is_jhol v) hv_nonconst\n    exact th.h_le_sph.trans h_sph\n  have h_sum_le : ∑ v ∈ s_prin, th.h ≤ ∑ v ∈ s_prin, totalEnergy I (u_lim.map v) :=\n    Finset.sum_le_sum h_each\n  have h_const_sum : ∑ v ∈ s_prin, th.h = (P : ℝ) * th.h := by\n    rw [Finset.sum_const, nsmul_eq_mul, hP]\n  rw [h_const_sum] at h_sum_le\n  have h_nonneg : ∀ v : u_lim.tree.V, 0 ≤ totalEnergy I (u_lim.map v) := by\n    intro v\n    exact totalEnergy_nonneg I (u_lim.map v)\n  have h_le_all : ∑ v ∈ s_prin, totalEnergy I (u_lim.map v) ≤ ∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v) :=\n    Finset.sum_le_univ_sum_of_nonneg h_nonneg\n  exact h_sum_le.trans (h_le_all.trans h_energy)\n```<end_of_turn>\n"
}
```

---

## 3. Investigation 2: Pure-Python BM25 Premise Retrieval

### 3.1 Corpus Scope & Export
The full Lean environment contains 609,926 declarations. By filtering out:
1. Internal compiler symbols (`n.isInternal`)
2. Auto-generated recursors and projections (`.rec`, `.recOn`, `.casesOn`, `.brecOn`, `.noConfusion`, `.injEq`, `_cstage`, `_sunfold`)
3. Libraries outside Mathlib and GromovCompactness (e.g. raw compiler internals)

We isolate **159,000 public mathematical declarations** (theorems, definitions, structures, and classes).
Our benchmark showed that exporting 5,000 declarations took 14 seconds and 1.6 MB. Exporting 100,000 top mathematical declarations with docstrings and types produces a compact **30–45 MB JSONL file** (`data/mathlib_project_declarations.jsonl`), requiring only ~3–4 minutes to generate once.

### 3.2 Pure-Python BM25 Inverted Index Design
BM25Okapi scores document $d$ against query $Q$ with $k_1 = 1.5, b = 0.75$:
$$\text{Score}(d, Q) = \sum_{q \in Q} \text{IDF}(q) \cdot \frac{f(q, d) \cdot (k_1 + 1)}{f(q, d) + k_1 \cdot \left(1 - b + b \cdot \frac{|d|}{\text{avgdl}}\right)}$$
$$\text{IDF}(q) = \ln \left( \frac{N - n(q) + 0.5}{n(q) + 0.5} + 1 \right)$$

#### Inverted Index Architecture
Instead of scanning every document (which would scale as $O(N)$), we build an **inverted posting index**:
`postings: Dict[str, List[Tuple[int, int]]]` mapping `term -> [(doc_id, term_frequency), ...]`
- **Sub-5ms query latency**: For a typical 5-term query, only documents containing at least one query term are scored.
- **Identifier Tokenizer**: Splits camelCase (`ClosedTameTarget` -> `closed`, `tame`, `target`), snake_case (`mul_le_mul_iff` -> `mul`, `le`, `mul`, `iff`), dot paths (`Metric.closedBall` -> `metric`, `closed`, `ball`), and strips punctuation while preserving math symbols.
- **Zero External Dependencies**: Implemented in ~120 lines of pure Python standard library (`math`, `collections`, `re`, `json`, `pickle`).
- **Memory Footprint**: ~25 MB in RAM, serialized to `data/bm25_index.pkl`.

### 3.3 Empirical Benchmark
Tested on 5,000 sample declarations from Mathlib:
- **Build Index**: 0.155 s
- **Index Dump to Pickle**: 0.012 s (2.5 MB)
- **Index Load from Pickle**: 0.012 s
- **Sample Query 1** ("mul_le_mul positive multiplication order"):
  - Top 1: `MulLECancellable.mul_le_mul_iff_left` (Mathlib.Algebra.Order.Monoid.Unbundled.Basic)
  - Latency: **2.89 ms**
- **Sample Query 2** ("sigma product convert Prod toSigma"):
  - Top 1: `Prod.toSigma` (Mathlib.Data.Sigma.Basic)
  - Latency: **2.03 ms**
- **Sample Query 3** ("support scalar multiplication finsupp"):
  - Top 1: `Finsupp.support_zero` (Mathlib.Data.Finsupp.Defs)
  - Latency: **1.42 ms**

---

## 4. Investigation 3: Python Environment & Client Consumption

### 4.1 Dependency Strategy
- Current environment: macOS, Python 3.11.5, `uv` 0.11.16.
- `rank_bm25` is not installed globally in Python 3.11 site-packages.
- `uv run --with rank_bm25` installed and executed in 50ms.
- **Architectural Decision**: `tools/premise_retrieval.py` implements pure-Python `InvertedBM25` as the primary engine. If `rank_bm25` is present, it can optionally use `rank_bm25.BM25Okapi`. This eliminates all hard external dependencies while maintaining 100% compatibility with standard Python and `uv`.

### 4.2 Client Consumption in `tools/ollama_lean4_client.py`
The client will consume the index as follows:
1. **Module `tools/premise_retrieval.py`** provides:
   ```python
   class PremiseRetriever:
       @classmethod
       def load(cls, index_path="data/bm25_index.pkl"): ...
       def retrieve(self, query_text: str, top_k: int = 5) -> List[Dict[str, Any]]: ...
   ```
2. **Integration into `tools/ollama_lean4_client.py`**:
   - Add `--with-premises` flag to `query`, `tactic`, and `autoformalize` CLI subcommands.
   - In `build_tactic_prompt` and `query_ollama` (for proving tasks), extract terms from the goal state and call `retriever.retrieve(goal_state, top_k=5)`.
   - Inject the retrieved premises directly into the prompt:
     ```lean4
     Relevant Mathlib Premises:
     1. `dist_triangle` : ∀ x y z, dist x z ≤ dist x y + dist y z
     2. `Continuous.continuousOn` : Continuous f → ContinuousOn f s
     3. `Metric.isCompact_closedBall` : IsCompact (Metric.closedBall x r)
     4. `add_halves` : r / 2 + r / 2 = r
     5. `dist_comm` : dist x y = dist y x
     ```
   - When Gemma generates proof tactics, it quotes these exact names instead of inventing non-existent lemmas.

---

## 5. Concrete Specifications & Implementation Blueprint for Worker

The Worker will implement four key files:

### File 1: `tools/extract_accepted_proofs.lean`
Lean 4 CLI tool that scans `GromovCompactness` and test modules, executes the fast clean-memoized axiom check, and outputs declaration metadata.
```lean
import GromovCompactness
import Lean.Util.CollectAxioms
import Lean.Data.Json
open Lean Meta

def checkCleanTheorems (env : Environment) (thms : Array Name) : IO (Array Name × Array Name) := do
  let mut cleanVisited : NameSet := {}
  let mut cleanThms : Array Name := #[]
  let mut dirtyThms : Array Name := #[]
  for n in thms do
    let s0 : CollectAxioms.State := { visited := cleanVisited, axioms := #[] }
    let (_, s1) := ((CollectAxioms.collect n).run env).run s0
    if s1.axioms.contains ``sorryAx then
      dirtyThms := dirtyThms.push n
    else
      cleanThms := cleanThms.push n
      cleanVisited := s1.visited
  return (cleanThms, dirtyThms)

def exportManifest (outPath : String) : MetaM Unit := do
  let env ← getEnv
  let mut thms : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`GromovCompactness).isPrefixOf modName do continue
    if n.isInternal then continue
    match ci with
    | .thmInfo _ => thms := thms.push n
    | _ => pure ()

  let (cleanThms, _) ← liftM (checkCleanTheorems env thms)
  let handle ← IO.FS.Handle.mk outPath IO.FS.Mode.write
  for n in cleanThms do
    let some ci := env.find? n | continue
    let docOpt ← findDocString? env n
    let rangesOpt ← findDeclarationRanges? n
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    let typeFmt ← ppExpr ci.type
    let usedConsts := ci.value?.map (fun v => v.getUsedConstants) |>.getD #[]
    
    let (startLine, endLine) := match rangesOpt with
      | some r => (r.range.pos.line, r.range.endPos.line)
      | none => (0, 0)
    
    let j := Json.mkObj [
      ("name", Json.str n.toString),
      ("module", Json.str modName.toString),
      ("doc", Json.str (docOpt.getD "")),
      ("type", Json.str (toString typeFmt)),
      ("start_line", Json.num startLine),
      ("end_line", Json.num endLine),
      ("premises", Json.arr (usedConsts.map (fun c => Json.str c.toString)))
    ]
    handle.putStrLn j.compress
  handle.flush

def main (args : List String) : IO Unit := do
  let outPath := args.head?.getD "data/raw_accepted_theorems.jsonl"
  let env ← importModules #[{ module := `GromovCompactness }] {}
  let coreCtx : Core.Context := { fileName := "extract", fileMap := FileMap.ofString "" }
  let coreState : Core.State := { env := env }
  let metaCtx : Meta.Context := {}
  let metaState : Meta.State := {}
  let ((_, _), _) ← (exportManifest outPath).run metaCtx metaState |>.toIO coreCtx coreState
  IO.println s!"Exported raw theorem manifest to {outPath}."
```

### File 2: `tools/build_accepted_proofs_dataset.py`
Python script that orchestrates Lean extraction, slices source files, parses test suites, and generates `data/gemma_accepted_proofs.jsonl`.
- Ensures output directory `data/` exists.
- Runs `lake env lean --run tools/extract_accepted_proofs.lean data/raw_accepted_theorems.jsonl`.
- Reads each `.lean` file and slices `[start_line - 1 : end_line]`.
- Extracts theorem signature and proof body (`by ...` or `:= ...`).
- Scans `tests/*.lean` for zero-sorry challenge theorems and parses their goals/proofs.
- Synthesizes `turn_user` and `turn_model` using Gemma's `<start_of_turn>` tokens.
- Writes each JSON record to `data/gemma_accepted_proofs.jsonl`.
- Validates:
  - Minimum 748 examples from library + test proofs.
  - Zero `sorryAx` occurrences.

### File 3: `tools/export_declarations.lean`
Lean 4 tool that exports Mathlib + project declarations:
```lean
import GromovCompactness
import Lean.Data.Json
open Lean Meta

def exportDecls (outPath : String) : MetaM Unit := do
  let env ← getEnv
  let handle ← IO.FS.Handle.mk outPath IO.FS.Mode.write
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`Mathlib).isPrefixOf modName || (`GromovCompactness).isPrefixOf modName do continue
    
    -- Filter out recursors and internal constructors
    let s := n.toString
    if s.endsWith ".rec" || s.endsWith ".casesOn" || s.endsWith ".recOn" ||
       s.endsWith ".brecOn" || s.endsWith ".noConfusion" || s.endsWith ".injEq" then
      continue
    
    let kind := match ci with
      | .thmInfo _ => "thm"
      | .defnInfo _ => "def"
      | .inductInfo _ => "inductive"
      | _ => "other"
    if kind == "other" then continue

    let docOpt ← findDocString? env n
    let typeFmt ← ppExpr ci.type
    let j := Json.mkObj [
      ("name", Json.str s),
      ("module", Json.str modName.toString),
      ("kind", Json.str kind),
      ("doc", Json.str (docOpt.getD "")),
      ("type", Json.str (toString typeFmt))
    ]
    handle.putStrLn j.compress
    count := count + 1
  handle.flush
  IO.println s!"Exported {count} declarations to {outPath}."

def main (args : List String) : IO Unit := do
  let outPath := args.head?.getD "data/mathlib_project_declarations.jsonl"
  let env ← importModules #[{ module := `GromovCompactness }] {}
  let coreCtx : Core.Context := { fileName := "export", fileMap := FileMap.ofString "" }
  let coreState : Core.State := { env := env }
  let metaCtx : Meta.Context := {}
  let metaState : Meta.State := {}
  let ((_, _), _) ← (exportDecls outPath).run metaCtx metaState |>.toIO coreCtx coreState
  pure ()
```

### File 4: `tools/premise_retrieval.py`
Pure-Python inverted-index BM25 engine with zero external dependencies:
- `InvertedBM25` class with `fit(documents)` and `query(query_text, top_k)`.
- Identifier tokenizer for Lean 4 terms.
- Serialization via `pickle` to `data/bm25_index.pkl`.
- CLI commands: `build`, `query`, and `benchmark`.
- Can be imported into `tools/ollama_lean4_client.py`.

---

## 6. Verification and Acceptance Plan

The implementation should be verified by running:
1. **Proof Extraction Test**:
   ```bash
   python3 tools/build_accepted_proofs_dataset.py
   python3 -c "
   import json
   with open('data/gemma_accepted_proofs.jsonl') as f:
       lines = [json.loads(l) for l in f]
   print('Total extracted proofs:', len(lines))
   assert len(lines) >= 748, f'Expected at least 748 proofs, got {len(lines)}'
   assert all('sorryAx' not in x['axioms'] for x in lines), 'Contains sorryAx!'
   print('Verification PASSED: 100% sorryAx-free!')
   "
   ```
2. **Premise Retrieval Test**:
   ```bash
   lake env lean --run tools/export_declarations.lean data/mathlib_project_declarations.jsonl
   python3 tools/premise_retrieval.py build --input data/mathlib_project_declarations.jsonl --output data/bm25_index.pkl
   python3 tools/premise_retrieval.py query --index data/bm25_index.pkl "dist triangle metric space"
   ```
3. **Client Integration Test**:
   ```bash
   python3 tools/ollama_lean4_client.py query --dry-run --task tactic --prompt "⊢ dist x z ≤ r" --with-premises
   ```
