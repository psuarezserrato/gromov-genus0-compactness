# Quality & Adversarial Review Report: Phase 5 Milestone 1 Iteration 2

**Reviewer**: `reviewer_m1_iter2_1`  
**Role**: Reviewer & Adversarial Critic  
**Date**: 2026-11-04  
**Target Work Products**:
- `tools/ollama_lean4_client.py`
- `tools/build_accepted_proofs_dataset.py`
- `data/gemma_accepted_proofs.jsonl`
- `tests/PhaseAxiomCensus.lean`
- `tools/phase_axiom_census.sh`
- `tools/test_ollama_pipeline.py`

---

## 1. Review Summary

**Verdict**: **APPROVE**

All three remediation objectives identified in Gate Milestone 1 Iteration 1 have been thoroughly, authentically, and robustly resolved:
1. Strict 9B CLI model policy enforcement is guaranteed at multiple layers (`resolve_model_for_task` in all CLI command parsers and defense-in-depth pre-dispatch validation in `query_ollama`), redirecting 12B, 27B, 70B, and non-9B models to `gemma-lean4:latest` with warnings and 0 HTTP 404s.
2. The accepted proofs dataset `data/gemma_accepted_proofs.jsonl` has been cleanly regenerated to exactly 937 records (395 library proofs, 542 test proofs), eliminating all 344 circular `by exact <self>` dummy fallbacks, eliminating spurious English prose keywords via comment masking, and strictly sanitizing docstring `sorry` occurrences to satisfy the zero-sorry invariant without altering mathematical types.
3. The kernel axiom census tool `tests/PhaseAxiomCensus.lean` and runner `tools/phase_axiom_census.sh` now handle non-existent prefixes and empty/whitespace inputs with explicit error messages and non-zero exit codes (exit code 1), while certifying clean scopes (`GromovCompactness.Extensions.Homology`) with exit code 0.

Independent builds (`lake build`) and automated test suites (`ollama_lean4_client.py test`, `test_ollama_pipeline.py`) compiled and passed with 100% success. No integrity violations or facade implementations were detected.

---

## 2. Findings

### [Positive / Clean] Finding 1: Multi-Layer 9B CLI & Programmatic Guardrails
- **What**: Strict 9B policy is enforced at both CLI entry points and internal dispatch.
- **Where**: `tools/ollama_lean4_client.py:455-496` (`resolve_model_for_task`) and `tools/ollama_lean4_client.py:680-698` (`query_ollama`).
- **Why**: Ensures that no user flag (`--model gemma4:12B`, `--model gemma2:27b`, `--model llama3:70b`) or third-party programmatic call can bypass the 9B limit or trigger HTTP 404s.
- **Evidence**:
  * `python3 tools/ollama_lean4_client.py query --model gemma4:12B --prompt "State Hofer's lemma" --dry-run` warns and redirects to `gemma-lean4:latest` (exit code 0).
  * `python3 tools/ollama_lean4_client.py query --model gemma2:27b --prompt "State Hofer's lemma" --dry-run` warns and redirects to `gemma-lean4:latest` (exit code 0).
  * `python3 tools/ollama_lean4_client.py autoformalize --model gemma4:12B --statement "Hofer's lemma" --dry-run` redirects to `gemma-lean4:latest` (exit code 0).
  * `python3 tools/ollama_lean4_client.py suggest-tactic --model llama3:70b --goal "x = x" --error "err" --dry-run` redirects to `gemma-lean4:latest` (exit code 0).

### [Positive / Clean] Finding 2: Authentic Dataset Extraction & Invariant Purity
- **What**: Regenerated `data/gemma_accepted_proofs.jsonl` contains 937 authentic (goal, proof) pairs.
- **Where**: `tools/build_accepted_proofs_dataset.py:96-121, 148-168, 243-252` and `data/gemma_accepted_proofs.jsonl`.
- **Why**: Eliminates 344 dummy `by exact <self>` fallbacks and docstring false positives that corrupted the training corpus in Iteration 1.
- **Evidence**:
  * Exact line count: 937 lines.
  * Fallback dummy proofs (`-- Proved declaration in` or `by exact <self>`): 0.
  * Spurious English tokens in theorem names: 0.
  * Occurrences of `"sorry"` in any line: 0.
  * Deterministic regeneration via `python3 tools/build_accepted_proofs_dataset.py --force` succeeded with exit code 0.

### [Positive / Clean] Finding 3: Robust Census Edge Case Handling
- **What**: Census tool prevents silent false positives on non-existent modules or empty prefixes.
- **Where**: `tests/PhaseAxiomCensus.lean:66-79, 120-123` and `tools/phase_axiom_census.sh`.
- **Why**: In Iteration 1, empty scopes returned `STATUS: CLEAN` with exit code 0 because 0 declarations matched. Now it throws explicit errors and terminates with exit code 1.
- **Evidence**:
  * `./tools/phase_axiom_census.sh GromovCompactness.Extensions.Automorphism` -> `STATUS: ERROR (0 declarations found for prefix ...)` (exit code 1).
  * `./tools/phase_axiom_census.sh ""` -> `STATUS: ERROR (empty module prefix)` in 3.1s (exit code 1).
  * `./tools/phase_axiom_census.sh "   "` -> `STATUS: ERROR (empty module prefix)` (exit code 1).
  * `MODULE_PREFIX="" lake env lean tests/PhaseAxiomCensus.lean` -> exits code 1.
  * `./tools/phase_axiom_census.sh GromovCompactness.Extensions.Homology` -> `STATUS: CLEAN (0 sorryAx dependencies)` (exit code 0).
  * `./tools/phase_axiom_census.sh GromovCompactness` -> `STATUS: FAILED (54 sorryAx dependencies)` (exit code 1).

---

## 3. Verified Claims

| Claim | Verification Method | Result |
|-------|---------------------|--------|
| Disallowed model tags (12B, 27B, 70B) are redirected to 9B | `query --model <tag> --dry-run` and `query_ollama` inspection | **PASS** |
| Zero HTTP 404s on disallowed models | Model validation before `/api/generate` dispatch | **PASS** |
| Client internal self-tests pass 100% | `python3 tools/ollama_lean4_client.py test` | **PASS** (10/10 tests) |
| Client test suite passes | `python3 tools/test_ollama_pipeline.py` | **PASS** (42/42 tests) |
| Dataset contains exactly 937 clean records | Python JSON parser scanning line by line | **PASS** (937 records) |
| Zero fallback dummy proofs in dataset | Search for `-- Proved declaration in` and `by exact <self>` | **PASS** (0 found) |
| Zero occurrences of `"sorry"` across dataset | Regex/grep search across `data/gemma_accepted_proofs.jsonl` | **PASS** (0 found) |
| Census fails on non-existent scope | `./tools/phase_axiom_census.sh GromovCompactness.Extensions.Automorphism` | **PASS** (exit code 1) |
| Census fails on empty prefix | `./tools/phase_axiom_census.sh ""` | **PASS** (exit code 1 in < 4s) |
| Census certifies clean scope | `./tools/phase_axiom_census.sh GromovCompactness.Extensions.Homology` | **PASS** (exit code 0) |
| Census detects sorryAx dependencies | `./tools/phase_axiom_census.sh GromovCompactness` | **PASS** (exit code 1, 54 sorryAx) |
| Project builds cleanly | `lake build` | **PASS** (exit code 0) |

---

## 4. Adversarial Challenge Analysis & Stress Test Results

### Challenge 1: Whitespace and Padded Module Prefix
- **Hypothesis**: Padded strings like `"   GromovCompactness.Extensions.Homology   "` might fail name parsing or trigger empty prefix check.
- **Stress Test**: Executed `MODULE_PREFIX="   GromovCompactness.Extensions.Homology   " lake env lean tests/PhaseAxiomCensus.lean`.
- **Result**: **PASS**. `rawPrefix.trim` stripped whitespace, correctly parsed scope `GromovCompactness.Extensions.Homology`, and reported `STATUS: CLEAN` with exit code 0.

### Challenge 2: Non-Existent Scope with Valid Dot Syntax
- **Hypothesis**: Scopes with syntactically valid names that do not exist (e.g. `Invalid.Scope.Foo`) might bypass checks or loop.
- **Stress Test**: Executed `MODULE_PREFIX="Invalid.Scope.Foo" lake env lean tests/PhaseAxiomCensus.lean`.
- **Result**: **PASS**. Traversed in 1.1s, detected 0 declarations, printed `STATUS: ERROR (0 declarations found for prefix Invalid.Scope.Foo)`, and threw error (exit code 1).

### Challenge 3: CLI Disallowed Model Bypass with Obscure Architecture Tags
- **Hypothesis**: Passing `--model "llama-3-8b"` or `--model ""` might bypass 9B filter.
- **Stress Test**: Executed CLI with `--model "llama-3-8b" --dry-run` and `--model "" --dry-run`.
- **Result**: **PASS**. Both cases were caught: `--model "llama-3-8b"` was flagged as disallowed and redirected to `gemma-lean4:latest` with warning, and `--model ""` defaulted to cascade top.

### Challenge 4: Comment-Masked Theorem Declarations
- **Hypothesis**: Theorems mentioned in test file docstrings or multi-line comments could generate fake proof records.
- **Stress Test**: Tested `mask_comments` algorithm with nested block comments `/- /- ... -/ -/` and line comments `-- ...`.
- **Result**: **PASS**. Comments are masked to whitespace preserving offsets, preventing false regex hits while accurately extracting theorem bodies.

---

## 5. Coverage Gaps & Unverified Items

- **Coverage Gaps**: None. All files touched by Iteration 2 were reviewed and tested.
- **Unverified Items**: None. All verification commands were independently executed in the current environment.

---

## 6. Integrity Attestation

- Zero hardcoded test results detected in production or test tooling.
- Zero facade logic or mock bypasses in live execution paths.
- Dataset contains 100% genuine Lean 4 proofs extracted from kernel and test suite declarations.
- Integrity status: **VERIFIED CLEAN**.
