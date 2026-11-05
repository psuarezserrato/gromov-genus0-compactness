# Forensic Audit Report: Phase 5 Milestone 1 Iteration 2 Gate

**Work Product**: Iteration 2 Remediations (`tools/ollama_lean4_client.py`, `data/gemma_accepted_proofs.jsonl`, `tools/build_accepted_proofs_dataset.py`, `tests/PhaseAxiomCensus.lean`, `tools/phase_axiom_census.sh`)  
**Profile**: General Project (Demo Mode per `ORIGINAL_REQUEST.md`)  
**Verdict**: **INTEGRITY VIOLATION** (Work Product Rejected)

---

## Executive Summary

While Remediations 1, 3, and 4 (`tools/ollama_lean4_client.py` 9B policy enforcement, `tests/PhaseAxiomCensus.lean` prefix/total handling, and `lake build` compilation) were implemented genuinely and pass empirical forensic checks, **Remediation 2 fails critical integrity standards**:

`tools/build_accepted_proofs_dataset.py` contains severe extraction flaws in `harvest_test_proofs`:
1. **Unproved declarations with `sorry` extracted and certified as accepted zero-`sorry` proofs**:
   `tests.AdversarialAttacksIter2.test_A04_dummy_proof_cannot_succeed` (`tests/AdversarialAttacksIter2.lean:45`) and `tests.ChallengeMilestone2Challenger2.test_nonnegativity_indispensable_for_mvi` (`tests/ChallengeMilestone2Challenger2.lean:214`) both terminate in `sorry` in source code. Due to non-greedy regex matching over comment-masked lines (`by\b[\s\S]*?`), their proofs were truncated to `"by"`, evading the `"sorry" not in orig_proof` filter and populating `data/gemma_accepted_proofs.jsonl` with incomplete `"proof": "by"` pairs for unproved theorems.
2. **Corrupted non-proof syntax fragments emitted as model training targets**:
   In `tests.ChallengePhase3StressCases.challenge_stress_case_1_compactness_accessible`, regex splitting on `:=` inside a type argument `(M := M)` corrupted the record: the theorem signature swallowed the proof body, and the proof was extracted as `"proof": "M)"`.
3. **Hardcoded axiom attestation facade**:
   In `tools/build_accepted_proofs_dataset.py:191`, `"axioms": ["propext", "Classical.choice", "Quot.sound"]` is hardcoded across all 542 test records without inspecting the Lean environment, falsely certifying test declarations (including `tests.ChallengePhase2ModelA.challenge_query_B01` which transitively depends on `sorryAx` via `GromovCompactness.Bubbling.exists_target_thresholds`).

Under the strict integrity rules of the forensic auditor ("Trust nothing, verify empirically, block on ANY failure"), this work product cannot be certified. Verdict: **INTEGRITY VIOLATION**.

---

## Phase Results

| # | Check Name | Target | Result | Details |
|---|------------|--------|--------|---------|
| 1 | Strict 9B Model Policy Enforcement | `tools/ollama_lean4_client.py` | **PASS** | `resolve_model_for_task` and `query_ollama` strictly validate 9B models, intercepting and redirecting 12B/27B/70B models with warnings and zero HTTP 404s. |
| 2 | Genuine Zero-Sorry Dataset Extraction | `data/gemma_accepted_proofs.jsonl` & `tools/build_accepted_proofs_dataset.py` | **FAIL** | Contains 2 truncated unproved `sorry` theorems with `"proof": "by"`, corrupted record with `"proof": "M)"`, and hardcoded axiom attestations on 542 test records. |
| 3 | Dynamic Axiom Census Verification | `tests/PhaseAxiomCensus.lean` & `tools/phase_axiom_census.sh` | **PASS** | Dynamic module traversal, correct `total == 0` error throwing on typo scopes, fast abort on empty prefixes, clean scope certification, dirty scope detection. |
| 4 | Full Project Compilation | Workspace | **PASS** | `lake build` exits 0 cleanly. All 42 unit tests in `test_ollama_pipeline.py` pass cleanly. |

---

## Detailed Evidence

### Check 1: `tools/ollama_lean4_client.py` (PASS)
- Tested dry-run redirection for forbidden models:
  ```bash
  python3 tools/ollama_lean4_client.py query --model gemma4:12B --prompt "State Hofer's lemma" --dry-run
  # Output: [WARNING] Model 'gemma4:12B' is disallowed by the strict 9B policy (12B/27B forbidden). Redirecting to optimal 9B model.
  # Dispatching query to 'gemma-lean4:latest' (Exit code: 0)

  python3 tools/ollama_lean4_client.py query --model gemma2:27b --prompt "State Hofer's lemma" --dry-run
  # Output: [WARNING] Model 'gemma2:27b' is disallowed by the strict 9B policy (12B/27B forbidden). Redirecting to optimal 9B model.
  # Dispatching query to 'gemma-lean4:latest' (Exit code: 0)
  ```
- Tested live redirection for forbidden models:
  ```bash
  python3 tools/ollama_lean4_client.py query --model gemma2:27b --prompt "State Hofer's lemma" --timeout 15.0
  # Output: [WARNING] Model 'gemma2:27b' is disallowed by the strict 9B policy (12B/27B forbidden). Redirecting to optimal 9B model.
  # Dispatching query to 'gemma-lean4:latest' ...
  ```
- Checked `~/.ollama/logs/server.log`:
  ```text
  [GIN] 2026/11/04 - 15:05:30 | 200 |   1.93ms |       127.0.0.1 | GET      "/api/tags"
  slot print_timing: id  0 | task 2895 | n_gen =    100, tg =  10.48 t/s, tg_3s =  10.59 t/s
  slot print_timing: id  0 | task 2895 | n_gen =    132, tg =  10.50 t/s, tg_3s =  10.55 t/s
  ```
  Zero HTTP 404 status codes occurred.
- Verified test suite: `python3 tools/test_ollama_pipeline.py` ran 42 tests in 36.595s with exit code 0.

### Check 2: `data/gemma_accepted_proofs.jsonl` (FAIL — INTEGRITY VIOLATION)

#### Evidence 2.1: Unproved `sorry` declarations disguised as zero-sorry proofs with `"proof": "by"`
In `tests/AdversarialAttacksIter2.lean:41-46`:
```lean
            1 * (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
                 sobolevNorm p 0 f (Metric.closedBall 0 R))) := by
  -- An unscaled constant C = 1 fails when scaling f or shrinking r/R.
  -- This demonstrates that the universal constant C is not trivial.
  sorry -- We acknowledge C depends non-trivially on p, k, r, R.
```
Verbatim record in `data/gemma_accepted_proofs.jsonl`:
```json
{
  "id": "tests.AdversarialAttacksIter2.test_A04_dummy_proof_cannot_succeed",
  "name": "test_A04_dummy_proof_cannot_succeed",
  "proof": "by",
  "axioms": ["propext", "Classical.choice", "Quot.sound"],
  "turn_model": "<start_of_turn>model\n```lean4\nby\n```<end_of_turn>\n"
}
```

In `tests/ChallengeMilestone2Challenger2.lean:208-214`:
```lean
theorem test_nonnegativity_indispensable_for_mvi :
    ∃ (e : ℂ → ℝ) (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) (r / 2)),
      ContinuousOn e (Metric.closedBall 0 r) ∧
      (∫ w in Metric.ball (0 : ℂ) r, e w = 0) ∧
      e z ≠ 0 := by
  -- The odd function x ↦ x integrates to 0 on symmetric balls, but does not vanish point-wise.
  sorry
```
Verbatim record in `data/gemma_accepted_proofs.jsonl`:
```json
{
  "id": "tests.ChallengeMilestone2Challenger2.test_nonnegativity_indispensable_for_mvi",
  "name": "test_nonnegativity_indispensable_for_mvi",
  "proof": "by",
  "axioms": ["propext", "Classical.choice", "Quot.sound"],
  "turn_model": "<start_of_turn>model\n```lean4\nby\n```<end_of_turn>\n"
}
```

#### Evidence 2.2: Corrupted non-proof string emitted as proof target
In `tests/ChallengePhase3StressCases.lean:84-87`:
```lean
theorem challenge_stress_case_1_compactness_accessible
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M) :
    Nonempty (CompactSpace M) :=
  challenge_stress_case_1_target_compactness (M := M)
```
Verbatim record in `data/gemma_accepted_proofs.jsonl`:
```json
{
  "id": "tests.ChallengePhase3StressCases.challenge_stress_case_1_compactness_accessible",
  "name": "challenge_stress_case_1_compactness_accessible",
  "signature": "theorem challenge_stress_case_1_compactness_accessible\n    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M) :\n    Nonempty (CompactSpace M) :=\n  challenge_stress_case_1_target_compactness (M",
  "proof": "M)",
  "turn_model": "<start_of_turn>model\n```lean4\nM)\n```<end_of_turn>\n"
}
```

#### Evidence 2.3: Root Cause in `tools/build_accepted_proofs_dataset.py`
In `tools/build_accepted_proofs_dataset.py:132-135`:
```python
thm_pattern = re.compile(
    r"^[ \t]*(?:(?:private|protected)\s+)?(theorem|lemma)\s+([a-zA-Z0-9_\'\.]+)([\s\S]*?):=\s*(by\b[\s\S]*?|[^:=]+?)(?=\n\s*(?:theorem|lemma|def|structure|class|inductive|#|namespace|section|$))",
    re.MULTILINE
)
```
1. Because `by\b[\s\S]*?` is non-greedy, when comments follow `:= by`, `mask_comments` turns comments into spaces. `\n\s*` in the lookahead greedily spans all whitespace across the masked comments up to the next declaration keyword, leaving `[\s\S]*?` to match 0 characters. Thus `orig_proof` becomes `"by"`.
2. `"sorry" in "by"` evaluates to `False`, bypassing the `if "sorry" in orig_proof:` filter.
3. In `harvest_test_proofs:191`:
```python
"axioms": ["propext", "Classical.choice", "Quot.sound"]
```
This field is hardcoded unconditionally without checking whether declarations (e.g. `challenge_query_B01`) transitively depend on `sorryAx`.

### Check 3: `tests/PhaseAxiomCensus.lean` (PASS)
- Typo scope error:
  `./tools/phase_axiom_census.sh GromovCompactness.Extensions.Automorphism` -> exits with code 1:
  `STATUS: ERROR (0 declarations found for prefix GromovCompactness.Extensions.Automorphism)`
- Empty prefix fast abort:
  `MODULE_PREFIX="" lake env lean tests/PhaseAxiomCensus.lean` -> exits with code 1 in 3.5s:
  `STATUS: ERROR (empty module prefix)`
- Clean scope certification:
  `./tools/phase_axiom_census.sh GromovCompactness.Extensions.Homology` -> exits with code 0:
  `STATUS: CLEAN (0 sorryAx dependencies)`
- Dirty scope detection:
  `./tools/phase_axiom_census.sh GromovCompactness` -> exits with code 1:
  `STATUS: FAILED (54 sorryAx dependencies)`

### Check 4: Full project compilation (PASS)
- `lake build` compiled with exit code 0.

---

## Verdict: INTEGRITY VIOLATION

The dataset `data/gemma_accepted_proofs.jsonl` contains unproved `sorry` declarations disguised as zero-sorry proofs with truncated `"proof": "by"` bodies, corrupted records (`"proof": "M)"`), and hardcoded axiom attestations on 542 test records. The work product is **REJECTED**.
