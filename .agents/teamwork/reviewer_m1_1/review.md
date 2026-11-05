# Phase 5 Milestone 1 Quality & Adversarial Review Report

**Reviewer**: `reviewer_m1_1` (Roles: reviewer, critic)  
**Target Milestone**: Phase 5 Milestone 1 (Plumbing, 9B Ollama Policy & Specialization, Premise Retrieval, Dataset Extraction, and Fast Axiom Census Tool P0-6)  
**Worker Under Review**: `teamwork_worker_p5m1`  
**Date**: 2026-11-04  

---

## 1. Executive Summary & Verdict

**Verdict**: **APPROVE**

Phase 5 Milestone 1 delivers an exceptionally high-quality foundation for Phase 5. All required deliverables—strict 9B Ollama configuration, `/api/version` probing, zero-contamination specialized `gemma-lean4:latest` model, accepted proofs extraction, sub-3ms BM25 premise retrieval, and sub-5s kernel axiom census—have been independently built, executed, benchmarked, and stress-tested. No integrity violations or hardcoded facades were found.

---

## 2. Independent Verification & Benchmark Results

| Test Target | Command Executed | Expected | Actual Result | Status |
|-------------|------------------|----------|---------------|--------|
| **Project Build** | `lake build` | Exit code 0 | Exit code 0, 0 build errors | **PASS** |
| **Ollama Client Self-Tests** | `python3 tools/ollama_lean4_client.py test` | 8/8 tests pass | 8/8 tests pass (100% pass rate) | **PASS** |
| **Ollama Health & Endpoint** | `python3 tools/ollama_lean4_client.py check` | Connects, no 404s, 9B detected | HTTP 200 via `/api/version`, detected `gemma-lean4:latest` | **PASS** |
| **Legacy Namespace Contamination** | `ollama show gemma-lean4:latest --modelfile \| grep -E "3DSymFlux\|SymFluxLean"` | Exit code 1 (no matches) | Exit code 1, 0 matches found | **PASS** |
| **BM25 Benchmark Latency** | `python3 tools/premise_retrieval.py benchmark` | Average latency < 5.0 ms | **2.26 ms** average latency | **PASS** |
| **Fast Axiom Census (Whole Project)** | `lake env lean tests/PhaseAxiomCensus.lean` | < 180s, exact baseline 1194/54 | **4.62s** elapsed; 1194 clean / 54 sorryAx; Exit code 1 | **PASS** |
| **Census on Clean Scope** | `./tools/phase_axiom_census.sh GromovCompactness.Extensions.Homology` | Exit code 0, 0 sorryAx | **3.04s** elapsed; 40 clean / 0 sorryAx; Exit code 0 | **PASS** |
| **Census on Dirty Scope** | `./tools/phase_axiom_census.sh GromovCompactness.Extensions.Automorphisms` | Exit code 1, 6 sorryAx | **2.94s** elapsed; 35 clean / 6 sorryAx (#30-#35); Exit code 1 | **PASS** |
| **Accepted Proofs Extraction** | Dataset validation script | 1,289 records, 0 sorry in proofs | 1,289 records; 0 occurrences of sorry in `proof` key | **PASS** |
| **Live 9B Prover Query & Usage Ledger** | `python3 tools/ollama_lean4_client.py query --prompt "..." --json` | Dispatches to 9B, logs to ledger | Succeeded in 7.76s; logged to `.agents/gemma_usage.jsonl` | **PASS** |

---

## 3. Detailed Quality Assessment

### 3.1 Strict 9B Ollama Policy & Client Implementation (`config/ollama_gemma_config.json`, `tools/ollama_lean4_client.py`)
- **Strict 9B Enforcement**: `enforce_9b_policy: true` is properly implemented. Any attempt to request `12b`, `27b`, or `70b` models is blocked by `is_allowed_9b_model` and cleanly redirected to the optimal 9B cascade model (`gemma-lean4:latest` -> `gemma2:9b-instruct-q5_K_M` -> `gemma2:9b`).
- **404 Elimination**: Replaced the non-existent `__probe_check__` generate call with `GET /api/version`, which executes in < 1 ms without generating 404 errors in Ollama server logs.
- **Keep-Alive**: Configured `"keep_alive": "30m"` in config and payload, preventing constant model evictions during proof search sessions.
- **Usage Ledger**: Proving calls are recorded to `.agents/gemma_usage.jsonl` with sha256 goal hash, timestamp, model, task type, token counts, and latency, while health check calls are excluded.
- **Premise Injection**: `--with-premises` flag hooks into `tools/premise_retrieval.py` to seamlessly prepend top retrieved Mathlib premises to the prompt.

### 3.2 Modelfile & Gemma Specialization (`Modelfile.gromov-lean4`)
- **Domain Specialization**: The system prompt is specifically crafted for Lean 4 v4.16, Mathlib naming conventions, symplectic geometry, Cauchy-Riemann equations, Hofer rescaling, and Gromov compactness.
- **Zero Legacy Contamination**: Audited via `ollama show gemma-lean4:latest --modelfile` and grep; confirmed zero references to legacy project namespaces (`3DSymFlux`, `SymFluxLean`).
- **Exemplars**: Three curated zero-sorry exemplars from project tests are embedded as few-shot turn messages.

### 3.3 Accepted Proofs Dataset (`tools/extract_accepted_proofs.lean`, `tools/build_accepted_proofs_dataset.py`, `data/gemma_accepted_proofs.jsonl`)
- **Dataset Scale**: 1,289 verified theorem-proof pairs (748 library proofs, 541 test suite proofs).
- **Format**: Conforms to official Gemma `<start_of_turn>user` / `<start_of_turn>model` chat formatting.
- **Purity**: Verified that zero proofs in `data/gemma_accepted_proofs.jsonl` contain `sorry`.

### 3.4 Inverted BM25 Premise Retriever (`tools/premise_retrieval.py`, `data/bm25_index.pkl`)
- **Corpus Coverage**: Indexes 153,248 declarations from Mathlib and `GromovCompactness`.
- **Performance**: High-performance inverted index with precomputed document length normalization factors achieves **2.26 ms** latency per query, more than 2x faster than the 5.0 ms ceiling.
- **Index Serialization**: Clean `to_dict` / `from_dict` serialization into a 68 MB pickle file that loads reliably in ~0.8s on startup.

### 3.5 Fast Kernel Axiom Census Tool (`tests/PhaseAxiomCensus.lean`, `tools/phase_axiom_census.sh`, P0-6)
- **Traversals & Memoization**: The memoized traversal algorithm (`MemoAxioms.collect`) eliminates redundant AST traversals across shared transitive dependencies.
- **Dramatic Performance Leap**: The previous census (`tests/ReportAxiomCensus.lean`) ran for > 7 minutes (hung without memoization); the new tool completes the full 1,248 declaration library in **4.62 seconds** (well within the < 3 minute target and < 15 second stretch goal).
- **Axiom Purity**: Strictly checks for standard axioms (`[propext, Classical.choice, Quot.sound]`) and logs `NONSTANDARD AXIOM` on any deviation.
- **Precision**: Accurately identified the exact 54 sorryAx-dependent declarations across the library and exactly 6 in `Extensions.Automorphisms`.

---

## 4. Adversarial Findings & Critic Observations

### Finding 1: Verification Command False Positive on JSON Lines [Minor]
- **What**: In the worker handoff report (§5, command 8), the suggested verification command was:
  `python3 -c "import json; assert all('sorry' not in l for l in open('data/gemma_accepted_proofs.jsonl')), 'Found sorry in dataset!'"`
- **Where**: `teamwork_worker_p5m1/handoff.md` line 176.
- **Why**: This command checks if the substring `'sorry'` appears anywhere in the serialized JSON string line `l`. 97 declarations in our repository include phrases like `"(Zero-sorry)"` or `"with 0 sorry."` in their docstrings and signatures. Consequently, that command failed with an `AssertionError` even though the proofs themselves were 100% sorry-free.
- **Verification**: Running `assert all('sorry' not in json.loads(l)['proof'] for l in open('data/gemma_accepted_proofs.jsonl'))` confirmed that exactly 0 proofs contain `sorry`.
- **Recommendation**: Upstream documentation and tests should inspect `json.loads(l)['proof']` rather than matching against the entire line `l`.

### Finding 2: Axiom Census Returns Clean on Empty / Misspelled Scope [Minor]
- **What**: If an invalid or misspelled module prefix is passed to `./tools/phase_axiom_census.sh` (e.g. `./tools/phase_axiom_census.sh GromovCompactness.NonExistent`), the census finds 0 declarations and reports `STATUS: CLEAN (0 sorryAx dependencies)` with exit code 0.
- **Where**: `tests/PhaseAxiomCensus.lean` lines 76-80, 107-110.
- **Why**: A typo in CI scripts or milestone automation could cause a test to erroneously pass even if no declarations were matched.
- **Suggestion**: In a future iteration, if `clean + dirty.size == 0`, emit a warning or require a flag `--allow-empty` to prevent silent passes on typos.

### Finding 3: Truncated Markdown Code Blocks in Client Response Extraction [Minor]
- **What**: `extract_lean_code` in `tools/ollama_lean4_client.py` uses `re.findall(r"```(?:lean4|lean)?\s*(.*?)\s*```", raw_text, re.DOTALL)`.
- **Where**: `tools/ollama_lean4_client.py` lines 546-551.
- **Why**: If a live LLM generation hits `num_predict` or max tokens and truncates before emitting the closing triple backticks, `extract_lean_code` falls back to returning the raw unstripped string including the opening ```` ```lean4 ````.
- **Suggestion**: Add a fallback regex `r"```(?:lean4|lean)?\s*(.*)"` when no closing backticks are found.

---

## 5. Integrity Verification Checklist

- [x] **No hardcoded test scores or results**: Dynamic environment and index queries confirmed.
- [x] **No dummy/facade implementations**: Real BM25 postings, real Lean 4 AST traversal, real Ollama HTTP communication.
- [x] **No task shortcuts or bypasses**: Full pipeline from Lean extraction to BM25 index built natively.
- [x] **No fabricated logs or artifacts**: Artifacts verified directly on disk.
- [x] **Independent verification**: Built and tested in clean environment.

---

## 6. Conclusion

Phase 5 Milestone 1 meets all technical specifications and acceptance criteria. The codebase is clean, well-tested, fast, and ready for Phase 5 Milestone 2.
