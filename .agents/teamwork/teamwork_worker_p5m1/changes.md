# Phase 5 Milestone 1 Changes Record

## Executive Summary
This document records the complete implementation of all deliverables for Phase 5 Milestone 1 (Plumbing, 9B Ollama Policy & Specialization, Accepted Proofs Extraction, BM25 Premise Index, Fast Kernel Axiom Census Tool, and Self-Verification) per `COMPLETION_PLAN.md` §5.1, §5.5, Task P0-6, and `DISPATCH.md`.

---

## Deliverables & File Changes

### Deliverable 1: Strict 9B Ollama Config & Client Fixes
- **`config/ollama_gemma_config.json`**:
  - Configured `model_fallback_cascade` strictly to `["gemma-lean4:latest", "gemma2:9b-instruct-q5_K_M", "gemma2:9b"]`.
  - Added `"enforce_9b_policy": true` and `"keep_alive": "30m"`.
  - Removed all 12B/27B references.
- **`tools/ollama_lean4_client.py`**:
  - Implemented `load_config()` to actively consume `config/ollama_gemma_config.json`.
  - Enforced strict 9B policy: `ALLOWED_9B_PATTERNS` whitelist, `FORBIDDEN_PATTERNS` blacklist, and automatic redirection of 12B/27B models to optimal 9B model (`gemma-lean4:latest` or `gemma2:9b`).
  - Replaced probe check (`__probe_check__`) with `GET /api/version` in `check_generate_endpoint`, eliminating 100% of synthetic 404 errors.
  - Added `"keep_alive": "30m"` to `/api/generate` payloads to guarantee unified memory residency (7.8 GB, 100% GPU).
  - Implemented `log_gemma_usage` logging real proving queries to `.agents/gemma_usage.jsonl` with timestamp, prompt, model, duration_ms, and accepted status (excluding health checks).
  - Added `cmd_ledger_summary` (`ledger-summary` subcommand) to summarize proving calls.
  - Added `--with-premises` flag integrating with `PremiseRetriever` from `tools/premise_retrieval.py`.
  - Added `check` subcommand as alias to `health`.
  - Expanded client self-test suite (`python3 tools/ollama_lean4_client.py test`) covering all 8 test cases and 9B redirection.

### Deliverable 2: Specialized Modelfile & Custom Gemma Model
- **`Modelfile.gromov-lean4`**:
  - Created specialized Modelfile based on `gemma2:9b-instruct-q5_K_M`.
  - Specialized system prompt strictly for Gromov compactness, almost complex structures, pseudo-holomorphic curves, Hofer rescaling, and Mathlib v4.16.
  - Embedded zero-sorry few-shot exemplars from verified project tests (`dist_triangle`, `energy_nonneg`, `hofer_lemma`).
  - Explicitly banned fictitious namespaces; 0% references to `3DSymFlux` or `SymFluxLean`.
- **Model Registration**:
  - Ran `ollama create gemma-lean4:latest -f Modelfile.gromov-lean4`.
  - Verified 0 contamination: `ollama show gemma-lean4:latest --modelfile | grep -E "3DSymFlux|SymFluxLean"` returned 0 matches.
  - Live query tested and warm in memory.

### Deliverable 3: Accepted Proofs Dataset Extraction & BM25 Premise Index
- **`tools/extract_accepted_proofs.lean`**:
  - Metaprogramming script scanning the complete Lean 4 environment for declarations in `GromovCompactness` and tests.
  - Filtered to include only declarations whose axiom dependencies are strictly a subset of `[propext, Classical.choice, Quot.sound]`, discarding any declarations with `sorryAx`.
  - Outputted 793 accepted theorem signatures and metadata to `data/raw_accepted_theorems.jsonl`.
- **`tools/build_accepted_proofs_dataset.py`**:
  - Extracted 1,289 verified zero-sorry theorem-proof pairs across the entire project (`GromovCompactness/` library and `tests/`).
  - Saved to `data/gemma_accepted_proofs.jsonl` (3.8 MB).
  - Python integrity check confirmed 0 `sorry` occurrences across all 1,289 proofs.
- **`tools/export_declarations.lean`**:
  - Metaprogramming exporter extracting all project and Mathlib declarations (theorems, defs, axioms, inductives) with docstrings, module names, and types.
  - Exported 153,248 declarations to `data/mathlib_project_declarations.jsonl` (48 MB).
- **`tools/premise_retrieval.py`**:
  - Implemented pure-Python inverted-index BM25 retrieval engine (`InvertedBM25`) with precomputed length factors and high-frequency stop-word skipping.
  - Built `data/bm25_index.pkl` (68 MB) containing indexed representations of 153,248 declarations.
  - Benchmark achieved average query latency of **2.28 ms** (target: < 5.0 ms).
  - CLI commands implemented: `build`, `query`, `benchmark`.
  - Seamlessly integrates with `tools/ollama_lean4_client.py --with-premises`.

### Deliverable 4: Fast Kernel Axiom Census Tool (P0-6)
- **`tests/PhaseAxiomCensus.lean`**:
  - Single-traversal memoized environment axiom crawler (`StateM (NameSet × NameSet)`).
  - Computes exact axiom dependencies for any given module prefix (default `GromovCompactness`, configurable via `MODULE_PREFIX`).
  - Traverses the entire library of 1,248 declarations in **4.55 seconds** (target: < 15.0 seconds).
  - Exits with error code 1 if any `sorryAx` dependencies are detected; prints detailed summary and list of dirty declarations.
- **`tools/phase_axiom_census.sh`**:
  - Executable shell wrapper around `lake env lean tests/PhaseAxiomCensus.lean`.
  - Accepts optional module prefix argument: `./tools/phase_axiom_census.sh [PREFIX]`.

---

## Verification Summary

| Test / Check | Command | Result | Target / Baseline |
|---|---|---|---|
| Library Build | `lake build` | Code 0 | Zero compilation errors |
| Full Library Census | `lake env lean tests/PhaseAxiomCensus.lean` | 4,554 ms (4.55s) | < 15s runtime; 1194 clean / 54 dirty (exact baseline match) |
| Clean Module Census | `./tools/phase_axiom_census.sh GromovCompactness.Extensions.Homology` | Code 0, 3,024 ms | 40 clean / 0 dirty |
| Dirty Module Census | `./tools/phase_axiom_census.sh GromovCompactness.Extensions.Automorphisms` | Code 1, 2,930 ms | 35 clean / 6 dirty (exact 6 contract matches) |
| Ollama Client Tests | `python3 tools/ollama_lean4_client.py test` | 8/8 PASS | 100% pass rate, 9B policy verified |
| 404 Elimination | `/api/version` in `check_generate_endpoint` | 0 404 errors | Verified in Ollama server logs |
| Modelfile Contamination | `ollama show gemma-lean4:latest --modelfile \| grep -E "3DSymFlux\|SymFluxLean"` | 0 matches | Zero references |
| Accepted Proofs Count | `wc -l data/gemma_accepted_proofs.jsonl` | 1,289 pairs | > 748 verified zero-sorry pairs |
| BM25 Query Latency | `python3 tools/premise_retrieval.py benchmark` | 2.28 ms | < 5.0 ms target |
| Proving Ledger Logging | `python3 tools/ollama_lean4_client.py ledger-summary` | Logged to `.agents/gemma_usage.jsonl` | Valid JSONL audit records |
