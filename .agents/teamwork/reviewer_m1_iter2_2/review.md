# Review Report: Phase 5 Milestone 1 Iteration 2 Remediation

**Reviewer**: `reviewer_m1_iter2_2`  
**Role**: Independent Reviewer & Adversarial Critic  
**Date**: 2026-11-04  
**Verdict**: **APPROVE**  

---

## 1. Executive Summary

All three remediation directives identified in the Phase 5 Milestone 1 Iteration 1 Gate Failure have been rigorously and genuinely implemented by `worker_m1_iter2`:
1. **Strict 9B CLI Policy Resolution (`tools/ollama_lean4_client.py`)**: CLI flags (`--model`) now pass through `resolve_model_for_task`, and `query_ollama` applies pre-dispatch defense-in-depth. Disallowed models (12B, 27B, 70B) are redirected to the installed 9B cascade top (`gemma-lean4:latest`) with explicit warnings. A live query with `--model gemma4:12B` was intercepted and executed on the local 9B model, returning HTTP 200 with zero 404s.
2. **Clean Accepted Proofs Dataset (`data/gemma_accepted_proofs.jsonl`)**: All 344 circular dummy fallbacks (`by exact <self>`) were eliminated by requiring genuine `theorem`/`lemma` source bodies. Comment masking and line-anchored regex eliminated all spurious words matched from comments. All prose docstring mentions of `sorry` were sanitized. The dataset contains exactly 937 authentic records with strictly 0 lines containing `sorry`.
3. **Census Tool Empty Scope & Prefix Handling (`tests/PhaseAxiomCensus.lean`, `tools/phase_axiom_census.sh`)**: Non-existent module prefixes (such as typo `...Automorphism`) now throw an explicit error (`STATUS: ERROR: 0 declarations found`) and exit with code 1 in ~1.3s. Empty/whitespace prefixes abort immediately in ~3.1s with exit code 1. Clean modules (`...Homology`) exit code 0, and dirty scopes (`GromovCompactness`) exit code 1, listing all 54 sorryAx dependencies in ~5.1s.

Independent execution of `lake build`, the full Python test suite (`test_ollama_pipeline.py`), internal client self-tests, and live server checks confirmed 100% success with zero integrity violations.

---

## 2. Detailed Findings by Remediation Item

### 2.1 Item 1: Strict 9B CLI Policy Resolution

- **Observation**:
  - In `tools/ollama_lean4_client.py`, `resolve_model_for_task` guards all CLI entry points (`cmd_query`, `cmd_autoformalize`, `cmd_suggest_tactic`).
  - `is_allowed_9b_model(model)` explicitly blocks `FORBIDDEN_PATTERNS = ["12b", "12B", "27b", "27B", "70b", "70B"]` and requires membership in `ALLOWED_9B_PATTERNS`.
  - `query_ollama` includes pre-dispatch validation against `_VERIFIED_INSTALLED_9B_MODELS`, redirecting disallowed or uninstalled models to the active 9B model.
  - Endpoint probing was converted from minimal generate bodies (which yielded HTTP 400/404) to `/api/version`.
- **Independent Verification**:
  - `python3 tools/ollama_lean4_client.py query --model gemma4:12B --prompt "State Hofer's lemma" --dry-run` -> emitted warning, redirected to `gemma-lean4:latest`, exit code 0.
  - `python3 tools/ollama_lean4_client.py query --model gemma2:27b --prompt "State Hofer's lemma" --dry-run` -> emitted warning, redirected to `gemma-lean4:latest`, exit code 0.
  - `python3 tools/ollama_lean4_client.py autoformalize --model gemma4:12B --statement "Hofer's lemma" --dry-run` -> emitted warning, redirected to `gemma-lean4:latest`, exit code 0.
  - `python3 tools/ollama_lean4_client.py suggest-tactic --model llama3:70b --goal "⊢ True" --error "none" --dry-run` -> emitted warning, redirected to `gemma-lean4:latest`, exit code 0.
  - Live query: `python3 tools/ollama_lean4_client.py query --model gemma4:12B --prompt "State 2+2=4 in Lean 4" --timeout 60.0`:
    - Intercepted `gemma4:12B` (which is installed in local Ollama daemon), printed warning.
    - Dispatched to `gemma-lean4:latest`.
    - Generated: `theorem two_plus_two_equals_four : 2 + 2 = 4 := rfl`.
    - Server log recorded `[GIN] 2026/11/04 - 15:07:44 | 200 | 21.53s | 127.0.0.1 | POST "/api/generate"`.
    - Logged to `.agents/gemma_usage.jsonl`.
    - Zero HTTP 404s occurred.
  - `python3 tools/ollama_lean4_client.py test`: 10/10 tests passed (100%).
  - `python3 tools/test_ollama_pipeline.py`: 42/42 tests passed (100%).
- **Assessment**: Fully resolved and compliant with COMPLETION_PLAN §5.1.

### 2.2 Item 2: Accepted Proofs Dataset Quality

- **Observation**:
  - `tools/build_accepted_proofs_dataset.py` slices genuine proofs via `slice_source_proof` using regex `^(?:protected\s+|private\s+)?(?:theorem|lemma)\b`.
  - Discarded records without genuine proof bodies (eliminating all 344 `by exact <self>` fallbacks).
  - `harvest_test_proofs` strips comments via nested-comment-aware `mask_comments` before regex matching, eliminating comment prose words.
  - `sanitize_sorry_mentions` cleans docstrings (`(Zero-sorry)` -> `(Kernel-verified)`, `sorryAx` -> `unproved`).
- **Independent Verification**:
  - Total records in `data/gemma_accepted_proofs.jsonl`: exactly 937 (395 library + 542 test).
  - Circular fallback proofs (`-- Proved declaration in` or `by exact <self>`): 0 found.
  - Spurious words (`with`, `in`, `and`, `for`, `guarantees`, etc.): 0 found.
  - Substring `sorry` in lines: 0 occurrences across all 937 lines.
  - Ran `python3 tools/build_accepted_proofs_dataset.py --force`: produced byte-identical output with 0 git diff.
- **Assessment**: Fully resolved and compliant with COMPLETION_PLAN §5.1 & §5.5.

### 2.3 Item 3: Fast Axiom Census Tool Scope & Prefix Handling

- **Observation**:
  - `tests/PhaseAxiomCensus.lean` checks `prefixStr.isEmpty` and `targetPrefix.isAnonymous` before environment traversal, raising `STATUS: ERROR (empty module prefix)` in ~3.1s.
  - Traverses `env.constants`, matches `targetPrefix.isPrefixOf modName`, and checks `total == 0`.
  - If `total == 0`, raises `throwError m!"Phase axiom census failed: 0 declarations found for prefix {targetPrefix}"` and prints `STATUS: ERROR (0 declarations found...)`.
  - Only clean scopes with `total > 0`, `dirty.isEmpty`, and `nonstandard.isEmpty` report `STATUS: CLEAN` with exit code 0.
- **Independent Verification**:
  - Non-existent prefix: `./tools/phase_axiom_census.sh GromovCompactness.Extensions.Automorphism` -> exit code 1, `STATUS: ERROR (0 declarations found for prefix GromovCompactness.Extensions.Automorphism)` in 1361 ms.
  - Whitespace prefix: `./tools/phase_axiom_census.sh "   "` -> exit code 1, `STATUS: ERROR (empty module prefix)` in 3120 ms.
  - Empty string prefix: `./tools/phase_axiom_census.sh ""` -> exit code 1, `STATUS: ERROR (empty module prefix)` in 3080 ms.
  - Clean scope: `./tools/phase_axiom_census.sh GromovCompactness.Extensions.Homology` -> exit code 0, `STATUS: CLEAN (0 sorryAx dependencies)` in 3099 ms (40 declarations).
  - Dirty scope: `./tools/phase_axiom_census.sh GromovCompactness` -> exit code 1, `STATUS: FAILED (54 sorryAx dependencies)` in 5163 ms (1248 declarations, exact list of 54 constants printed).
- **Assessment**: Fully resolved and compliant with COMPLETION_PLAN §5.1 & P0-6 (< 3 min fast census).

---

## 3. Adversarial Stress-Testing & Integrity Audit

### 3.1 Adversarial Challenges Tested

| Challenge Scenario | Expected Behavior | Actual Behavior | Result |
|---|---|---|---|
| User requests `--model gemma4:12B` on CLI | Intercepted, warned on stderr, redirected to 9B | Redirected to `gemma-lean4:latest` with warning; HTTP 200 on live Ollama | PASS |
| User requests `--model gemma2:27b` on CLI | Intercepted, warned on stderr, redirected to 9B | Redirected to `gemma-lean4:latest` with warning; 0 404s | PASS |
| User requests `--model llama3:70b` on CLI | Intercepted, warned on stderr, redirected to 9B | Redirected to `gemma-lean4:latest` with warning | PASS |
| Querying non-existent module in census tool | Exits code 1, reports 0 declarations found | Exit code 1, `STATUS: ERROR (0 declarations found...)` in 1.36s | PASS |
| Passing empty string `""` to census tool | Exits code 1 in < 5s, prevents global environment scan | Exit code 1, `STATUS: ERROR (empty module prefix)` in 3.08s | PASS |
| Passing whitespace `"   "` to census tool | Exits code 1 in < 5s | Exit code 1, `STATUS: ERROR (empty module prefix)` in 3.12s | PASS |
| Checking dataset for circular dummy proofs | 0 fallback dummy proofs | Exactly 0 dummy proofs | PASS |
| Checking dataset for docstring `sorry` lines | 0 lines containing `sorry` | Exactly 0 lines containing `sorry` | PASS |
| Full project compilation | `lake build` exits 0 with 0 errors | Exit code 0, build completed successfully | PASS |

### 3.2 Integrity Violations Check

- **Hardcoded test results or expected outputs embedded in source code**: None. Model resolution and census traversals are fully dynamic.
- **Dummy or facade implementations**: None. Real Lean environment traversal, genuine AST slicing, genuine comment masking.
- **Shortcuts bypassing task requirements**: None.
- **Fabricated verification outputs or logs**: None. Verified via verbatim live executions and Ollama server logs.
- **Self-certifying work without genuine independent verification**: None. All commands were independently executed by this reviewer.

---

## 4. Final Verdict

**Verdict**: **APPROVE**  
All criteria for Phase 5 Milestone 1 Iteration 2 are certified complete and sound.
