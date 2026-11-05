# Analysis: Remediation of Hardcoded Axiom Attestations in Accepted Proofs Dataset

**Author**: `explorer_m1_iter3_3`  
**Role**: Test Theorem Axiom Verification Remediation Explorer  
**Date**: 2026-11-04  
**Working Directory**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m1_iter3_3`  
**Target Work Product**: `tools/build_accepted_proofs_dataset.py`, `tools/extract_accepted_proofs.lean`, `data/gemma_accepted_proofs.jsonl`

---

## 1. Executive Summary

During the Phase 5 Milestone 1 Iteration 2 Gate audit, `auditor_m1_iter2` issued a non-negotiable **INTEGRITY VIOLATION** verdict against `data/gemma_accepted_proofs.jsonl` and `tools/build_accepted_proofs_dataset.py`. The forensic auditor identified three fatal defects:
1. **Unproved declarations with `sorry` extracted as zero-`sorry` proofs**: Regex truncation over comment-masked lines truncated proofs to `"by"`, evading `"sorry" not in orig_proof` checks (e.g. `test_A04_dummy_proof_cannot_succeed` and `test_nonnegativity_indispensable_for_mvi`).
2. **Corrupted syntax fragments**: Regex splitting on `:=` inside parameter terms like `(M := M)` emitted corrupted proof targets (`"proof": "M)"`).
3. **Hardcoded axiom attestation facade**: In `tools/build_accepted_proofs_dataset.py:191`, `"axioms": ["propext", "Classical.choice", "Quot.sound"]` was hardcoded across all 542 test records without querying the Lean environment, falsely certifying declarations (e.g. `challenge_query_B01`) that transitively depend on `sorryAx`. Furthermore, `sanitize_sorry_mentions` masked `sorryAx` in docstrings to `unproved`, obscuring dependency status.

This investigation evaluates two remediation pathways:
- **Strategy A**: Formulate authentic verification of test suite declarations against the Lean kernel.
- **Strategy B**: Restrict `data/gemma_accepted_proofs.jsonl` strictly to kernel-verified library declarations, completely eliminating regex harvesting of unverified test suites and deriving all axiom metadata dynamically from the Lean kernel.

**Definitive Finding & Recommendation**: **Strategy B is the strictly superior, mathematically rigorous, and authentic solution**.
1. `tests/` is not a registered Lake library and cannot be imported into a unified Lean environment. Test files contain intentional counterexample `sorry`s, conflicting namespaces, and conditional queries that merely wrap library declarations.
2. The library `GromovCompactness` alone contains **748 clean theorems** verified by the Lean kernel with zero `sorryAx` dependencies.
3. Incorporating dynamic memoized axiom collection (`MemoAxioms.collect`) directly into `tools/extract_accepted_proofs.lean` extracts the exact, genuine kernel axioms (`[propext, Classical.choice, Quot.sound]`) for each theorem in ~11 seconds, populating `raw_accepted_theorems.jsonl` and `data/gemma_accepted_proofs.jsonl` with 100% authentic kernel data and 0 hardcoded strings.
4. Slicing the 748 clean library theorems yields **395 high-value, multi-line, verified proofs** covering the entire mathematical depth of the repository.

---

## 2. Root Cause & Forensic Evidence Breakdown

### 2.1 Defect 1: Proof Body Truncation Evading `sorry` Detection
In `tools/build_accepted_proofs_dataset.py:132-135`:
```python
thm_pattern = re.compile(
    r"^[ \t]*(?:(?:private|protected)\s+)?(theorem|lemma)\s+([a-zA-Z0-9_\'\.]+)([\s\S]*?):=\s*(by\b[\s\S]*?|[^:=]+?)(?=\n\s*(?:theorem|lemma|def|structure|class|inductive|#|namespace|section|$))",
    re.MULTILINE
)
```
- In `tests/AdversarialAttacksIter2.lean:41-46`, the proof is:
  ```lean
  ... := by
    -- An unscaled constant C = 1 fails when scaling f or shrinking r/R.
    -- This demonstrates that the universal constant C is not trivial.
    sorry -- We acknowledge C depends non-trivially on p, k, r, R.
  ```
- When `mask_comments` replaces comment text with whitespace, `\n\s*` in the lookahead pattern greedily matches all the blanked lines across the comments up to the next declaration.
- Because `by\b[\s\S]*?` is non-greedy, it matches zero characters after `by`.
- The captured proof group becomes `"by"`.
- Line 156 checks `if "sorry" in orig_proof: continue`. Because `"sorry" in "by"` is `False`, the unproved theorem was harvested and emitted into the dataset as `"proof": "by"`.

### 2.2 Defect 2: Malformed Term Proof Extraction
In `tests/ChallengePhase3StressCases.lean:84-87`:
```lean
theorem challenge_stress_case_1_compactness_accessible
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M) :
    Nonempty (CompactSpace M) :=
  challenge_stress_case_1_target_compactness (M := M)
```
- When `thm_pattern` encounters `(M := M)`, it matches `:=` inside the term argument rather than the declaration assignment.
- The signature is truncated to `... :=\n challenge_stress_case_1_target_compactness (M` and the proof is captured as `"proof": "M)"`.
- The dataset thus contained corrupted syntax fragments as training targets.

### 2.3 Defect 3: Hardcoded Axiom Attestation Facade
In `tools/build_accepted_proofs_dataset.py:191`:
```python
rec = {
    "id": f"tests.{fname[:-5]}.{name}",
    ...
    "axioms": ["propext", "Classical.choice", "Quot.sound"],
    ...
}
```
- This field was unconditionally set as a static string list across all 542 test records without checking whether the declarations depended on `sorryAx` or nonstandard axioms.
- In `tests/ChallengePhase2ModelA.lean:243-247`:
  ```lean
  theorem challenge_query_B01 :
      Nonempty (GromovCompactness.Bubbling.TargetThresholds I M) :=
    GromovCompactness.Bubbling.exists_target_thresholds I
  ```
  `GromovCompactness.Bubbling.exists_target_thresholds I` transitively depends on `sorryAx` from open contracts in Phase 2 Model A.
- Yet in `data/gemma_accepted_proofs.jsonl:725`:
  `"axioms": ["propext", "Classical.choice", "Quot.sound"]` was asserted.
- Furthermore, `sanitize_sorry_mentions` in `tools/build_accepted_proofs_dataset.py:65` transformed the docstring:
  From: `(transitively inherits sorryAx from upstream A03, A07, A10)`
  To: `(transitively inherits unproved from upstream A03, A07, A10)`
  This actively masked the axiom dependency, creating an attestation facade.

---

## 3. Deep Evaluation of Strategies

### 3.1 Strategy A: Authentic Verification of Test Declarations Against the Lean Kernel

To verify test declarations authentically, we investigated whether Lean could evaluate declarations in `tests/*.lean` and inspect their transitively depended-on axioms.

#### Architectural Obstacles:
1. **Module Hierarchy Isolation**:
   - `lakefile.lean` defines only `lean_lib «GromovCompactness»`.
   - `tests/` is not a registered Lake library.
   - When attempting `import tests.ChallengeGeometry` in Lean, the compiler fails immediately:
     `error: unknown module prefix 'tests'. No directory 'tests' or file 'tests.olean' in the search path entries.`
2. **Lakefile Incompatibility**:
   - Registering `lean_lib Tests` with `srcDir := "tests"` in `lakefile.lean` would cause `lake build` to compile all 27 test files on every repository build.
   - Multiple test files define conflicting temporary definitions and namespaces (`ChallengePhase2`, `ChallengePhase3`, `ChallengePhase4`).
   - Compiling all 27 test files sequentially with `lake env lean` takes over 4 minutes, making dataset generation and testing prohibitively slow.
3. **Low Yield of Authentic Declarations**:
   - Review of declarations in `tests/*.lean` reveals three categories:
     a) **Intentional failures / counterexamples**: Statements designed to demonstrate failure modes that intentionally terminate in `sorry` (e.g. `test_A04_dummy_proof_cannot_succeed`). These must be rejected.
     b) **Direct theorem instantiations**: Wrapper theorems like `challenge_query_A01 := local_smooth_compactness ...`. If the underlying library theorem is proved, this wrapper is redundant with the library proof; if the underlying library theorem depends on `sorryAx`, the wrapper also depends on `sorryAx`.
     c) **Open challenge queries**: Queries against unproved contracts (e.g. `challenge_query_B01`) which transitively inherit `sorryAx`.
   - After filtering out all declarations depending on `sorryAx`, the remaining test declarations are virtually all trivial one-line wrappers of existing library theorems. They offer zero novel proof tactics or mathematical substance for training Gemma 9B.

### 3.2 Strategy B: Restrict Dataset Strictly to Kernel-Verified Library Declarations

Under Strategy B, `data/gemma_accepted_proofs.jsonl` is restricted strictly to declarations in `GromovCompactness` that are verified directly by the Lean kernel via `tools/extract_accepted_proofs.lean`.

#### Empirical Findings on Library Cleanliness:
We implemented and ran a memoized axiom census (`MemoAxioms.collect`) over all 796 declarations in `GromovCompactness`:
- **Total theorems in library**: 796
- **Clean theorems (0 `sorryAx`)**: **748**
- **Dirty theorems (`sorryAx` dependent)**: 48
- **Axioms across all 748 clean theorems**:
  - `propext`: 724 theorems
  - `Quot.sound`: 721 theorems
  - `Classical.choice`: 719 theorems
  - **Nonstandard axioms**: **0**
  - **Execution time**: **11.2 seconds**

#### Dataset Composition Under Strategy B:
Out of the 748 clean theorems exported by `extract_accepted_proofs.lean`:
- **227 skipped**: Internal auxiliary equational lemmas or auto-generated induction helpers without source line ranges.
- **126 skipped**: Structure projection fields (e.g. `TargetThresholds.h_pos`) that do not possess a standalone `theorem ... := by ...` proof body in source code.
- **395 accepted**: Genuine, syntactically complete, multi-line theorem and lemma proofs authored across the project.
- **Skipped due to `sorry`**: **0** (Lean kernel guarantees zero `sorryAx` dependencies).

#### Advantages of Strategy B:
1. **Mathematical Authenticity**: Every single record is checked by Lean's kernel. The `"axioms"` field is populated directly with the exact list of axioms returned by `MemoAxioms.collect` (e.g. `["propext", "Classical.choice"]`), completely eliminating hardcoded constants.
2. **Total Elimination of Fragile Regex Scrapers**: Eliminating `harvest_test_proofs` deletes the flawed regex patterns that caused the `"proof": "by"` and `"proof": "M)"` bugs.
3. **Zero Risk of Attestation Facade**: Since no test files are parsed by text regex, no unverified test declarations or `sorry`-dependent queries can ever enter the dataset.
4. **Efficiency**: Dataset generation executes in ~12 seconds, compared to multi-minute runs required for test file compilation.

---

## 4. Concrete Remediation Plan for Worker

To remediate the integrity violation cleanly, the Worker should make the following targeted modifications:

### 4.1 Enhance `tools/extract_accepted_proofs.lean`
Replace the partial `CollectAxioms` traversal with cycle-safe memoized axiom collection (`MemoAxioms.collect`) from `tests/PhaseAxiomCensus.lean`:
1. Collect the exact transitively depended-on axioms for each constant `n`.
2. Reject any constant whose axioms include ``sorryAx.
3. Validate that all axioms belong strictly to standard Lean axioms: `[``propext, ``Classical.choice, ``Quot.sound]`.
4. Export the actual array of axioms in `raw_accepted_theorems.jsonl`:
   ```lean
   ("axioms", Json.arr (axs.map (fun a => Json.str a.toString)))
   ```

### 4.2 Update `tools/build_accepted_proofs_dataset.py`
1. **Eliminate `harvest_test_proofs`**:
   Remove `harvest_test_proofs` entirely from `build_dataset`. The dataset will consist strictly of the kernel-verified library proofs.
2. **Dynamic Axiom Field**:
   In `build_dataset`, read `"axioms": item.get("axioms", [])` directly from `raw_accepted_theorems.jsonl` rather than hardcoding `["propext", "Classical.choice", "Quot.sound"]`.
3. **Strict Validation Invariants**:
   Before writing any record, assert:
   - `len(proof_body.strip()) > 2 and proof_body.strip() not in ["by", "M)"]`
   - `"sorry" not in proof_body`
   - `len(record["axioms"]) > 0 and "sorryAx" not in record["axioms"]`
4. **Remove Unsafe Docstring Sanitization**:
   Do not replace `sorryAx` with `unproved` in docstrings; if a declaration has `sorryAx`, it must be rejected by the kernel check, not masked by text replacement.

---

## 5. Summary Table: Strategy Comparison

| Metric / Dimension | Strategy A (Authentic Test Verification) | Strategy B (Strict Library Restriction) |
|---|---|---|
| **Axiom Verification Mechanism** | Custom multi-file Lean runner / Lake test harness | Single-pass memoized Lean kernel traversal (`extract_accepted_proofs.lean`) |
| **Execution Time** | > 4 minutes (27 individual `lean` invocations) | ~11 seconds (unified Lean environment query) |
| **Integrity Assurance** | Moderate (requires complex harness across disparate test files) | **100% Absolute (direct Lean kernel certification)** |
| **False Attestation Risk** | High if text regex is retained; zero if fully kernel-elaborated | **Zero (no hardcoded strings, no regex harvesting)** |
| **Dataset Size** | 395 library + ~15 trivial wrapper tests | **395 verified, high-quality library proofs** |
| **Code Cleanliness** | Complex Lake / script configurations | Clean, modular, zero-regex Lean-to-Python pipeline |
| **Forensic Audit Compliance** | Resolves audit conditionally | **Permanently and definitively resolves all 3 audit vetoes** |

---

## 6. Conclusion

Strategy B is unequivocally the correct, authentic, and mathematically rigorous path forward. Restricting `data/gemma_accepted_proofs.jsonl` to the 395 kernel-verified library theorems while deriving all axiom attestations directly from the Lean environment completely eliminates all integrity defects and establishes an irreproachable verification standard.
