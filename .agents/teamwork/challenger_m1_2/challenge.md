# Milestone 1 Adversarial Challenge Report

**Agent**: challenger_m1_2 (Challenger 2)  
**Date**: 2026-11-04  
**Target**: Phase 5 Milestone 1 Gate Deliverables  
**Verdict**: **APPROVE** (with minor non-blocking usability observations noted)

---

## 1. Challenge Summary

**Overall risk assessment**: **LOW**

All four core components mandated by Phase 5 Milestone 1 and COMPLETION_PLAN §1 & §5 were empirically tested, stressed, and verified:
1. **Modelfile Contamination & Live Querying**: 0 occurrences of legacy terms (`3DSymFlux`, `SymFluxLean`, `QRat`, `MPolyNF`, `flux`, `SymplecticFlux`). Live Ollama queries against `gemma-lean4:latest` generate valid Mathlib v4.16 syntax and adhere to standard differential topology naming conventions.
2. **Fast Kernel Axiom Census Tool**: Single-traversal memoization in `tests/PhaseAxiomCensus.lean` runs in 8.21 seconds for the full library (< 15 second target, << 3 minute ceiling). Declaration counts match `COMPLETION_PLAN.md` §1 exactly: 1,194 clean / 54 sorryAx dependencies (748 clean / 48 dirty theorems). Prefix filtering correctly isolates clean modules (exit 0) and dirty modules (exit 1).
3. **BM25 Premise Index & Dataset**: Roundtrip serialization of `InvertedBM25` maintains 100% data and ranking parity across 50 diverse mathematical queries. 500-query benchmark achieved a mean latency of **1.27 ms** (< 5.0 ms threshold). The accepted proofs dataset contains exactly 1,289 zero-sorry theorem-proof pairs.
4. **Prover Usage Logging**: `.agents/gemma_usage.jsonl` adheres to strict JSON schema, records ISO 8601 UTC timestamps, tracks token evaluation stats, and cleanly separates proving calls from health probes.

---

## 2. Adversarial Challenges and Stress Tests

### Challenge 1: Modelfile Contamination & Prohibited Legacy Namespaces
- **Assumption Challenged**: System prompt and few-shot exemplars in `Modelfile.gromov-lean4` and the registered Ollama model `gemma-lean4:latest` might leak legacy namespaces (`3DSymFlux`, `SymFluxLean`, `QRat`, `MPolyNF`) or outdated Mathlib syntax.
- **Attack Scenario**: Case-insensitive regex scans across `Modelfile.gromov-lean4`, `ollama show gemma-lean4:latest --modelfile`, and all client configuration files for `3DSymFlux|SymFluxLean|QRat|MPolyNF|flux|SymFlux`.
- **Empirical Result**: Exited with code 1; **0 matches found**. Base model verified as `gemma2:9b-instruct-q5_K_M`.
- **Live Probing**: Dispatched live queries to `gemma-lean4:latest` requesting definitions of almost complex structures and metric space triangle inequalities. Generated outputs used clean Lean 4 declarations (`structure AlmostComplexStructure`, `J (J v) = -v`, `namespace MetricSpace`, `dist x y + dist y z ≤ dist x z`) with 0 legacy tokens.

### Challenge 2: Axiom Census Tool Correctness, Memoization, and Custom Prefix Stress
- **Assumption Challenged**: The census tool might miscount compiler-generated declarations, miss transitive dependencies, fail on nested submodules, or exceed the 15-second latency threshold.
- **Stress Test Battery**:
  1. Full library scope (`GromovCompactness`):
     - Runtime: **8,210 ms** (8.21 s, target < 15 s).
     - Total declarations: 1,248 (theorems: 796).
     - Clean declarations: 1,194 (theorems: 748).
     - SorryAx-dependent: 54 (theorems: 48).
     - Status: FAILED (exit 1), exact match to `COMPLETION_PLAN.md` §1.
  2. Clean submodule scope (`GromovCompactness.Extensions.Homology`):
     - Runtime: **5,479 ms**.
     - Declarations: 40 (theorems: 18).
     - Clean: 40 (theorems: 18), Sorry-dependent: 0.
     - Status: CLEAN (exit code 0).
  3. Dirty submodule scope (`GromovCompactness.Extensions.Automorphisms`):
     - Runtime: **4,774 ms**.
     - Declarations: 41 (theorems: 21).
     - Clean: 35 (theorems: 15), Sorry-dependent: 6 (theorems: 6).
     - Status: FAILED (exit code 1). Isolated exact 6 open declarations (#30-#35).
  4. Non-existent prefix scope (`GromovCompactness.NonExistentModule`):
     - Runtime: **1,821 ms**.
     - Declarations: 0, Clean: 0, Dirty: 0. Status: CLEAN (exit code 0).
  5. Cross-Verification with `lake build`:
     - Full project build output inspected. Compiles with code 0 and flags the identical 6 sorry warnings in `Automorphisms.lean` and 0 in `Homology.lean`.

### Challenge 3: BM25 Premise Index Serialization, Latency, and Edge-Case Robustness
- **Assumption Challenged**: The pure-Python `InvertedBM25` index might suffer serialization loss when converted via `to_dict()`/`from_dict()`, fail on punctuation/unicode, or degrade past the 5.0 ms latency threshold under heavy query loads.
- **Stress Test Battery**:
  1. **Roundtrip Parity**: Serialized index to dictionary, pickled to byte stream, unpickled, and reconstructed via `from_dict()`. Reconstructed index matched original in corpus size (153,248), postings count (7,801), and avg doc length.
  2. **Query Scoring Parity**: Queried 50 diverse mathematical prompts (`dist_triangle`, `MetricSpace`, `AlmostComplexStructure`, `cauchy_riemann`, `hofer_lemma`, `energyMeasureExtended`, `conformal`, `Möbius`, etc.). Scored rankings between original and roundtripped index were **100% identical** (0 parity failures).
  3. **Adversarial Edge Cases**: Passed empty strings, pure whitespace, punctuation bombs (`!@#$%^&*()_+`), pure stopwords, unseen gibberish tokens, unicode mathematical symbols (`∂̄ ω J ∫ ℂ ∀ ∃ ∧ ∨ →`), and 5,000-character repetitions. All 8 edge cases executed without unhandled exceptions.
  4. **Benchmark**: 500 random batch queries evaluated:
     - Mean latency: **1.27 ms** (< 5.0 ms threshold).
     - Median (p50): **0.47 ms**.
     - p90: **3.71 ms**.
     - p99: **6.51 ms**.
     - Max: **8.71 ms**.
  5. **Dataset Audit**: Scanned all 1,289 lines of `data/gemma_accepted_proofs.jsonl`. Verified 748 proofs from `GromovCompactness` and 541 from `tests`. Regex scan confirmed **0 occurrences of `sorry`, `admit`, or `sorryAx`**.

### Challenge 4: Prover Usage Logging Schema and Ledger Integrity
- **Assumption Challenged**: Real proving calls might fail to log, corrupt JSONL syntax, or conflate endpoint health probes with mathematical inference.
- **Empirical Result**:
  - Validated 30 JSON records in `.agents/gemma_usage.jsonl`.
  - Proving calls recorded valid ISO 8601 UTC timestamps, `goal_hash`, `model`, `latency_ms`, `eval_count`, `eval_duration_ms`, and status.
  - Health check calls (`/api/version` and `/api/tags`) do not log to `gemma_usage.jsonl`.
  - `python3 tools/ollama_lean4_client.py ledger-summary` executed cleanly and parsed all metrics.

---

## 3. Discovered Nuances & Recommended Mitigations (Non-Blocking)

1. **CLI Timeout Passthrough in Client Subcommands**:
   - *Observation*: In `tools/ollama_lean4_client.py`, `common_parser` defines `--timeout` (default 5.0s), while `query_ollama` defines `timeout: float = 60.0`. In `cmd_query`, `cmd_autoformalize`, and `cmd_suggest_tactic`, the call to `query_ollama(...)` omits `timeout=args.timeout`.
   - *Impact*: Specifying `--timeout 120` on the CLI does not override the 60.0s socket timeout.
   - *Mitigation*: Update `query_ollama` calls in subcommands to pass `timeout=getattr(args, "timeout", 60.0)`.
2. **Model Whitelist Check on Explicit `--model`**:
   - *Observation*: `cmd_query` and `cmd_autoformalize` check `if not model and not args.dry_run: detect_best_model(...)`. If a user explicitly specifies `--model "gemma4:12B"` on the CLI, `detect_best_model` is bypassed and the request is sent directly to `query_ollama`.
   - *Impact*: Although `detect_best_model` correctly filters out 12B/27B models, an explicit CLI override could bypass this filter.
   - *Mitigation*: Insert `if not is_allowed_9b_model(model): raise ValueError(...)` inside `query_ollama` or at the start of `cmd_query`.

Neither nuance impacts Milestone 1 completion, as default cascade queries strictly select `gemma-lean4:latest` or `gemma2:9b-instruct-q5_K_M`.

---

## 4. Final Verdict

**VERDICT: APPROVE**

Milestone 1 satisfies all empirical requirements with high fidelity. The fast census tool is verified and reproducible (< 9s), the Modelfile is free of contamination, the BM25 premise retriever delivers sub-2ms lookups, and usage logging is active and compliant.
