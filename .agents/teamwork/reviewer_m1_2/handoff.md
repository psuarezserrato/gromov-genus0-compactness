# Phase 5 Milestone 1 Reviewer Handoff Report

**Reviewer**: `reviewer_m1_2`
**Working Directory**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/reviewer_m1_2`
**Verdict**: **REQUEST_CHANGES**

---

## 1. Observation

### Observation 1: Strict 9B Model Policy CLI Bypass
- In `tools/ollama_lean4_client.py`, lines 936–947 (`cmd_query`), 990–1001 (`cmd_autoformalize`), and 1042–1053 (`cmd_suggest_tactic`):
  ```python
  model = args.model
  if not model and not args.dry_run:
      model, reason, _ = detect_best_model(args.host, preferred_tag=args.model)
      if not model:
          if is_json:
              print(json.dumps({"status": "error", "error": f"No suitable model found: {reason}"}, indent=2))
          else:
              print(f"[ERROR] No suitable model found: {reason}")
          return 1
  else:
      model = model or "gemma2:9b"
  ```
- Command execution:
  ```bash
  python3 tools/ollama_lean4_client.py query --prompt "State Hofer's lemma" --model gemma2:27b --dry-run
  ```
  Output:
  ```
  Dispatching query to 'gemma2:27b' (Task: autoformalize, Host: http://localhost:11434)...
  ```
  No warning or redirection occurred.
- Host inspection via `ollama list`:
  ```
  NAME                         ID              SIZE      MODIFIED       
  gemma-lean4:latest           031f913365cd    6.6 GB    25 minutes ago    
  gemma2:9b-instruct-q5_K_M    272e1f3a41a6    6.6 GB    9 days ago        
  gemma4:12B                   4eb23ef187e2    7.6 GB    4 months ago      
  gemma4:e4b                   c6eb396dbd59    9.6 GB    5 months ago      
  gemma2:9b                    ff02c3702f32    5.4 GB    5 months ago      
  ```
  `gemma4:12B` is actively installed locally. Requesting `--model gemma4:12B` will execute the forbidden 12B model.
- Ledger inspection in `.agents/gemma_usage.jsonl` lines 12 and 16:
  ```json
  {"timestamp": "2026-11-04T22:25:35Z", "call_type": "proving", "model": "gemma2:27b", "goal_hash": "fca81cc4a64cbb95", "declaration": "", "task_type": "autoformalize", "latency_ms": 1.19, "eval_count": null, "eval_duration_ms": null, "status": "error", "accepted": null, "axioms": [], "error": "HTTP Error 404: Not Found"}
  {"timestamp": "2026-11-04T22:25:57Z", "call_type": "proving", "model": "gemma2:27b", "goal_hash": "cf07194ee232eb53", "declaration": "", "task_type": "autoformalize", "latency_ms": 1.25, "eval_count": null, "eval_duration_ms": null, "status": "error", "accepted": null, "axioms": [], "error": "HTTP Error 404: Not Found"}
  ```
  Direct HTTP requests for forbidden models were dispatched to Ollama and generated 404s.

### Observation 2: Facade Dummy Proofs in Accepted Proofs Dataset
- In `tools/build_accepted_proofs_dataset.py`, lines 165–168:
  ```python
  # Fallback if slice couldn't split :=
  if not proof_body:
      proof_body = f"by\n  -- Proved declaration in {mod_name}\n  exact {item['name']}"
  ```
- Inspection of `data/gemma_accepted_proofs.jsonl` using Python:
  ```python
  Total records: 1289
  From library: 748, From tests: 541
  Sorry anywhere: 97, Sorry in proof: 0
  Fallback dummy proof: 344 (26.7% of all records, 46.0% of library records)
  ```
- Examples of synthesized dummy proofs in `data/gemma_accepted_proofs.jsonl`:
  - Line 4: `GromovCompactness.Audit.LibraryAuditRecord.manifold_with_corners_available` -> `proof`: `"by\n  -- Proved declaration in GromovCompactness.LibraryAudit\n  exact GromovCompactness.Audit.LibraryAuditRecord.manifold_with_corners_available"`
  - Line 5: `GromovCompactness.Extensions.MarkedStableTreeLimit.mark_ne_node` -> `proof`: `"by\n  -- Proved declaration in GromovCompactness.Extensions.MarkedCurves\n  exact GromovCompactness.Extensions.MarkedStableTreeLimit.mark_ne_node"`
  - Line 10: `GromovCompactness.inv_lin.proof_3` -> `proof`: `"by\n  -- Proved declaration in GromovCompactness.Geometry.Sphere\n  exact GromovCompactness.inv_lin.proof_3"`
  - Line 25: `GromovCompactness.Extensions.VaryingAlmostComplexStructures.J_seq_sq` -> `proof`: `"by\n  -- Proved declaration in GromovCompactness.Extensions.VaryingJ\n  exact GromovCompactness.Extensions.VaryingAlmostComplexStructures.J_seq_sq"`

### Observation 3: Docstring Regex Contamination in Test Proof Extraction
- In `tools/build_accepted_proofs_dataset.py`, lines 75–78:
  ```python
  thm_pattern = re.compile(
      r"(?:/--(.*?)--/\s*)?(theorem|lemma)\s+([a-zA-Z0-9_'.]+)([\s\S]*?):=\s*(by\b[\s\S]*?|[^:=]+?)(?=\n\s*(?:theorem|lemma|def|structure|class|inductive|#|namespace|section|$))",
      re.MULTILINE
  )
  ```
- Matches prose containing the word "theorem" inside docstrings and comments:
  - `tests.ChallengeMilestone3Bootstrap.with` (from comment `theorem with ZERO sorry...`)
  - `tests.ChallengePhase3ModelB.in` (from comment `theorem in GhostBranching.lean...`)
  - `tests.ChallengePhase3StressCases.in` (from comment `theorem in the bubbling or compactness pipeline...`)

### Observation 4: Verified High-Performance Kernel Axiom Census Tool (P0-6)
- Command: `lake env lean tests/PhaseAxiomCensus.lean`
  Output:
  ```
  ==================================================
  Phase Axiom Census: scope=GromovCompactness
  Elapsed time: 4566 ms
  Total declarations in scope: 1248 (theorems: 796)
  Clean declarations: 1194 (theorems: 748)
  Sorry-dependent: 54 (theorems: 48)
  STATUS: FAILED (54 sorryAx dependencies)
  ==================================================
  ```
  Exited with code 1 in 4.56 seconds (< 15 second target, down from ~12 minutes). Baseline match: 1,194 clean / 54 sorryAx.
- Command: `./tools/phase_axiom_census.sh GromovCompactness.Extensions.Homology`
  Output:
  ```
  Elapsed time: 3031 ms
  Total declarations in scope: 40 (theorems: 18)
  Clean declarations: 40 (theorems: 18)
  Sorry-dependent: 0 (theorems: 0)
  STATUS: CLEAN (0 sorryAx dependencies)
  ```
  Exited with code 0.
- Command: `./tools/phase_axiom_census.sh GromovCompactness.Extensions.Automorphisms`
  Output:
  ```
  Elapsed time: 2950 ms
  Total declarations in scope: 41 (theorems: 21)
  Clean declarations: 35 (theorems: 15)
  Sorry-dependent: 6 (theorems: 6)
  STATUS: FAILED (6 sorryAx dependencies)
  ```
  Exited with code 1, isolating the exact 6 sorry-dependent contract declarations (#30–#35).
- Empty scope behavior: `./tools/phase_axiom_census.sh GromovCompactness.NonExistent` reports 0 declarations and exits with code 0.

### Observation 5: Zero Modelfile Contamination & Fast BM25 Retrieval
- Command: `ollama show gemma-lean4:latest --modelfile | grep -E "3DSymFlux|SymFluxLean"` exited with code 1 and produced 0 matches.
- Command: `python3 tools/premise_retrieval.py benchmark`:
  Average Query Latency: **2.18 ms** (target: < 5.0 ms).
- Command: `lake build`: Exited with code 0.

---

## 2. Logic Chain

1. **Strict 9B Local Model Guarantee**:
   - `COMPLETION_PLAN.md` §5.1 mandates a strict 9B-only local memory model policy: no 12B or 27B models, querying `/api/tags` first so uninstalled tags never trigger 404s.
   - Observation 1 demonstrates that `detect_best_model` is bypassed whenever `--model` is supplied on the CLI due to the `if not model and not args.dry_run:` guard.
   - Furthermore, Observation 1 shows that `gemma4:12B` is installed locally on the system. Passing `--model gemma4:12B` dispatches directly to the 12B model without interception.
   - Observation 1 also shows that queries to `gemma2:27b` actually reached Ollama and logged HTTP 404 errors in `.agents/gemma_usage.jsonl`.
   - Conclusion: The strict 9B local policy is not enforced at the CLI execution level and requires remediation.

2. **Accepted Proofs Training Integrity**:
   - `COMPLETION_PLAN.md` §5.1 & §5.5 mandate extracting all verified zero-sorry `(goal, proof)` pairs from the repository's verified theorems into a structured JSONL training/few-shot dataset (`data/gemma_accepted_proofs.jsonl`).
   - Observation 2 demonstrates that 344 records (46.0% of all library declarations, 26.7% of the entire dataset) contain tautological fallback dummy proofs (`by exact <self_name>`), caused by exporting compiler-generated structure fields, equational lemmas, and inductive theorems from the Lean environment that have no standalone proof body in the source code.
   - Fine-tuning or few-shot prompting Gemma on `exact <self_name>` teaches the model self-referential tautologies (`exact my_goal`) rather than constructive proofs.
   - Observation 3 shows that regex parsing errors extracted prose from test docstrings as spurious theorem declarations named `with` and `in`.
   - Conclusion: The accepted proofs dataset is contaminated with dummy proofs and parsing artifacts and must be filtered and regenerated.

3. **Census Tool & Modelfile Soundness**:
   - Observation 4 confirms that `tests/PhaseAxiomCensus.lean` and `tools/phase_axiom_census.sh` fulfill all requirements of P0-6: runtime under 5 seconds (150x faster than previous census), exact match to project baseline, and proper non-zero exit codes on dirty modules.
   - Observation 5 confirms that `Modelfile.gromov-lean4` has 0 legacy contamination and `premise_retrieval.py` provides 2.18 ms query latency.

---

## 3. Caveats

- **Ollama Local Service**: While offline mock responses and dry-run queries function correctly, live execution requires `ollama serve` running on port 11434.
- **Empty Prefix in Census**: Running the census with an invalid or misspelled module prefix currently returns exit code 0 because `dirty` is empty. A safeguard should be added.

---

## 4. Conclusion

Verdict: **REQUEST_CHANGES**.

While the Census Tool (P0-6), Modelfile specialization, and BM25 premise retriever are well-engineered and performant, the milestone cannot be certified due to:
1. Strict 9B model policy bypass in CLI entrypoints allowing 12B/27B execution and generating 404s.
2. Contamination of `data/gemma_accepted_proofs.jsonl` with 344 circular dummy proofs (`exact <self>`) and spurious test docstring extractions (`with`, `in`).

Both defects are directly actionable and must be remediated by `teamwork_worker_p5m1`.

---

## 5. Verification Method

To verify the findings and confirm subsequent remediation:

```bash
# 1. Test 9B CLI policy bypass (should redirect to 9B or reject with warning, not dispatch to 27b/12b)
python3 tools/ollama_lean4_client.py query --prompt "State Hofer's lemma" --model gemma2:27b --dry-run
python3 tools/ollama_lean4_client.py query --prompt "State Hofer's lemma" --model gemma4:12B --dry-run

# 2. Check for circular dummy proofs in accepted proofs dataset (must be 0)
python3 -c "
import json
lines = [json.loads(l) for l in open('data/gemma_accepted_proofs.jsonl')]
dummy = sum(1 for l in lines if '-- Proved declaration in' in l.get('proof', ''))
print(f'Dummy fallback proofs: {dummy}')
assert dummy == 0, f'Found {dummy} dummy fallback proofs!'
"

# 3. Check for spurious declaration names from test docstrings (must be 0)
python3 -c "
import json
lines = [json.loads(l) for l in open('data/gemma_accepted_proofs.jsonl')]
spurious = [l['id'] for l in lines if l.get('name') in ('with', 'in')]
print(f'Spurious docstring declarations: {len(spurious)}')
assert len(spurious) == 0, f'Found spurious declarations: {spurious}'
"

# 4. Verify fast axiom census tool (< 15 seconds)
lake env lean tests/PhaseAxiomCensus.lean
./tools/phase_axiom_census.sh GromovCompactness.Extensions.Homology
./tools/phase_axiom_census.sh GromovCompactness.Extensions.Automorphisms

# 5. Verify Modelfile zero contamination
ollama show gemma-lean4:latest --modelfile | grep -E "3DSymFlux|SymFluxLean"

# 6. Verify BM25 retrieval latency (< 5 ms)
python3 tools/premise_retrieval.py benchmark
```
