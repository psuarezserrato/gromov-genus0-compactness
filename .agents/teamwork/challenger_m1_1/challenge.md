# Adversarial Challenge Report: Phase 5 Milestone 1

**Challenger**: `challenger_m1_1` (EMPIRICAL CHALLENGER)  
**Date**: 2026-11-04  
**Verdict**: **REJECT**

---

## Executive Summary

Phase 5 Milestone 1 provides significant improvements in kernel census memoization, local BM25 indexing, and model templating. However, rigorous adversarial stress-testing revealed three critical defects, including the failure of the worker's own documented verification command:

1. **Dataset Invariant Breach (`data/gemma_accepted_proofs.jsonl`)**:
   - The worker claimed that `python3 -c "import json; assert all('sorry' not in l for l in open('data/gemma_accepted_proofs.jsonl')), 'Found sorry in dataset!'"` passes.
   - **Empirical result**: Fails with `AssertionError: Found sorry in dataset!`.
   - The substring `"sorry"` occurs in **97 lines** across docstrings and signatures (e.g., `"(Zero-sorry)"`, `"ZERO sorry"`). While proof bodies are clean, the dataset violates the strict zero-sorry line invariant and the worker's own handoff test.

2. **9B Model Policy Bypass & Server 404 Trigger**:
   - The dispatch required verifying that adversarial model names (`gemma2:27b`, `gemma4:12B`, `llama3:70b`, `nonexistent:model`) in `query_ollama` and CLI are strictly redirected or rejected without crashes or HTTP 404s.
   - **Empirical result**: In `cmd_query` (and `cmd_autoformalize`, `cmd_suggest_tactic`), passing `--model gemma2:27b` evaluates `if not model and not args.dry_run` to `False`, bypassing `detect_best_model` completely.
   - Furthermore, `query_ollama()` contains **zero** validation of the `model` parameter against `ALLOWED_9B_PATTERNS`.
   - Executing `python3 tools/ollama_lean4_client.py query --model gemma2:27b --prompt "test"` sends `"model": "gemma2:27b"` to Ollama `/api/generate` and produces an HTTP 404 in Ollama server logs:
     `[GIN] 2026/11/04 - 14:25:57 | 404 | 504.875µs | 127.0.0.1 | POST "/api/generate"`.

3. **Census Vacuous Success Vulnerability (`tools/phase_axiom_census.sh`)**:
   - When given a misspelled module or non-existent prefix (e.g., `./tools/phase_axiom_census.sh GromovCompactness.Extensions.Automorphism`, missing trailing 's'), the tool matches 0 declarations, reports `STATUS: CLEAN (0 sorryAx dependencies)`, and **exits with code 0**.
   - This introduces a false-negative vulnerability in CI gates where a typo causes dirty modules to be marked clean.

---

## Detailed Empirical Findings

### 1. Dataset Verification & Invariant Failure

#### Test Executed
```bash
python3 -c "import json; assert all('sorry' not in l for l in open('data/gemma_accepted_proofs.jsonl')), 'Found sorry in dataset!'"
```

#### Observed Result
```text
Traceback (most recent call last):
  File "<string>", line 1, in <module>
AssertionError: Found sorry in dataset!
```

#### Root Cause Analysis
An adversarial inspection of all 1,289 lines in `data/gemma_accepted_proofs.jsonl` was conducted:
```text
Total lines in dataset: 1289
Malformed JSON lines: 0
Empty proofs: 0
Exact line occurrences of "sorry": 97
Fields containing "sorry": {'docstring': 95, 'signature': 97, 'turn_user': 97, 'goal_type': 2}
Proofs with sorry: 0
```
While proof bodies themselves are sorry-free, 97 records contain the word "sorry" in their docstrings/signatures (e.g., `/-- Deleting a constant root vertex preserves the sum of component energies (Zero-sorry). -/`).
This violates the gate assertion specified in the dispatch: *"Assert 0 sorry occurrences across data/gemma_accepted_proofs.jsonl"*, and causes the worker's verification script to fail.

---

### 2. Ollama 9B Policy & HTTP 404 Stress Testing

#### Test Executed (CLI with Disallowed Model)
```bash
python3 tools/ollama_lean4_client.py query --model gemma2:27b --prompt "hello" --timeout 2.0
```

#### Observed Result
```text
Dispatching query to 'gemma2:27b' (Task: autoformalize, Host: http://localhost:11434)...
[ERROR] HTTP Error 404: Not Found
[HINT]  Ensure Ollama is running ('ollama serve') and model is pulled ('ollama pull gemma2:27b'). Or pass --dry-run for offline testing.
```

Ollama server log (`~/.ollama/logs/server.log`):
```text
[GIN] 2026/11/04 - 14:25:57 | 404 | 504.875µs |       127.0.0.1 | POST     "/api/generate"
```

#### Root Cause Analysis
In `tools/ollama_lean4_client.py`:
- In `cmd_query` (lines 936–947):
  ```python
  model = args.model
  if not model and not args.dry_run:
      model, reason, _ = detect_best_model(args.host, preferred_tag=args.model)
  ```
  If `--model gemma2:27b` is provided, `model` is already set. Therefore, `if not model and not args.dry_run` evaluates to `False`, and `detect_best_model` is never called.
- In `query_ollama` (lines 620–670):
  The function receives `model` and constructs the payload directly:
  ```python
  payload = {
      "model": model,
      "prompt": prompt,
      ...
  }
  ```
  It contains no check for `is_allowed_9b_model(model)` and no redirection to the 9B cascade.

#### Endpoint Verification
- `health` command calls `GET /api/version` (HTTP 200, < 1 ms) and `GET /api/tags` (HTTP 200). Zero 404s were generated during health checks.
- Proving usage logger correctly logs to `.agents/gemma_usage.jsonl` and excludes health checks.

---

### 3. Census Tool (P0-6) Stress Testing

#### Benchmark Timing
- Command: `time ./tools/phase_axiom_census.sh GromovCompactness`
- Elapsed kernel time: **4,566 ms** (total execution time ~7.0 s).
- Target requirement: `< 15 s`. **PASS**.

#### Exit Code Contracts
- Entire library (`GromovCompactness`): 1,248 declarations, 54 sorryAx dependencies. Exited with code **1**. **PASS**.
- Clean scope (`GromovCompactness.Extensions.Homology`): 40 declarations, 0 sorryAx dependencies. Exited with code **0**. **PASS**.
- Dirty scope (`GromovCompactness.Extensions.Automorphisms`): 41 declarations, 6 sorryAx dependencies. Exited with code **1**. **PASS**.

#### Boundary Condition Failures
- **Typo / Non-existent Module**:
  ```bash
  ./tools/phase_axiom_census.sh GromovCompactness.Extensions.Automorphism
  ```
  Output:
  ```text
  Phase Axiom Census: scope=GromovCompactness.Extensions.Automorphism
  Total declarations in scope: 0 (theorems: 0)
  STATUS: CLEAN (0 sorryAx dependencies)
  ```
  Exited with code **0**.
  *Defect*: When 0 declarations match a given prefix, the tool reports `CLEAN` and exits with code 0 instead of flagging an error or warning about an empty scope.

- **Empty string prefix (`MODULE_PREFIX=""`)**:
  Running `MODULE_PREFIX="" lake env lean tests/PhaseAxiomCensus.lean` passes `some ""` to Lean.
  Lean resolves `"".toName` as `Name.anonymous`, matching all 153,248 declarations in the environment, causing execution timeouts unless filtered by bash `${1:-GromovCompactness}`.

---

### 4. BM25 Premise Index Stress Testing

#### Edge Case Robustness
Tested across 8 adversarial inputs:
- Empty string `""`: 0 results in 0.00 ms (no crash)
- Whitespace only: 0 results in 0.44 ms (no crash)
- Punctuation only: 0 results in 0.01 ms (no crash)
- Stopwords only: 0 results in 0.01 ms (no crash)
- Purely unknown tokens (`xyzzy99999 ...`): 0 results in 0.00 ms (no crash)
- Single character tokens (`a b c 1 2`): 0 results in 0.01 ms (no crash)
- Repeated tokens (500x "dist"): 5 results in 1.08 ms (no crash)
- Large compound query (1,000 words): 5 results in 0.80 ms (no crash)

#### Latency Analysis
Benchmark over 250 queries:
- **Average latency**: **2.59 ms** (< 5.0 ms target)
- **Median latency**: **1.73 ms**
- **High-frequency vocabulary anomaly**: For queries combining multiple broad topological terms (`ContinuousOn closedBall compact`), latency degrades to **median 6.61 ms** and **p95 8.63 ms** (max 10.05 ms). This occurs because pure-Python posting list iteration processes > 15,000 document postings when terms are broad but individual posting lengths do not trigger the 10,000-cutoff filter.

---

## Verdict and Remediation Actions

**VERDICT**: **REJECT**

### Required Remediations for Worker:
1. **Clean `data/gemma_accepted_proofs.jsonl`**:
   - Strip references to `"sorry"` from `docstring`, `signature`, and `turn_user` fields (e.g. replace `"(Zero-sorry)"` with `"(Kernel-verified)"` or `"(Closed)"`).
   - Ensure `python3 -c "import json; assert all('sorry' not in l for l in open('data/gemma_accepted_proofs.jsonl'))"` exits with code 0.
2. **Enforce 9B Policy in `query_ollama` and CLI**:
   - In `query_ollama(base_url, model, ...)`, check `is_allowed_9b_model(model)`: if false, redirect to optimal 9B cascade (`gemma-lean4:latest` or `gemma2:9b`).
   - In `cmd_query`, `cmd_autoformalize`, and `cmd_suggest_tactic`, unconditionally run `detect_best_model(args.host, preferred_tag=args.model)` whenever `ACTIVE_CONFIG.get("enforce_9b_policy")` is True.
   - Verify that running with `--model gemma2:27b` outputs a redirection warning and executes on 9B without producing HTTP 404s.
3. **Guard Census Against Empty Scope (`tests/PhaseAxiomCensus.lean`)**:
   - Add a check: if `clean + dirty.size == 0`, throw an error or exit with code 1 indicating that no declarations were found matching `MODULE_PREFIX`.
