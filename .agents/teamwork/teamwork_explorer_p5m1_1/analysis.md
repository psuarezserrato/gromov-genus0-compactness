# Comprehensive Investigation Report: Local 9B Gemma Prover Infrastructure

**Agent:** `teamwork_explorer_p5m1_1`  
**Milestone:** Phase 5 Milestone 1 (Plumbing, 9B Ollama Policy & Specialization, Census Tool)  
**Date:** 2026-11-04  
**Status:** COMPLETE (Read-Only Investigation)

---

## Executive Summary

This investigation audits the local Ollama infrastructure, client configurations, Modelfile templates, usage logging, and fine-tuning options to support Phase 5 of the Gromov Compactness autoformalization project.

### Core Discoveries:
1. **Model Contamination in `gemma-lean4:latest`**: The current system prompt in `gemma-lean4:latest` is completely contaminated with an unrelated Lie-Poisson mechanics project ("3DSymFlux", `namespace SymFluxLean`, `QRat`, Lean 3 import styles). Live test queries confirmed it generates `namespace SymFluxLean` and obsolete Lean 3 imports (`data.real.basic`).
2. **Root Cause of 35+ HTTP 404 Cascades**:
   - `tools/ollama_lean4_client.py:261` deliberately probes `/api/generate` with a non-existent model name `__probe_check__` during connection checks, triggering HTTP 404 in Ollama's `server.log` on every health check.
   - The fallback cascade lists uninstalled models (`gemma2:27b`, `codegemma:7b`, `gemma:7b`, `gemma2:2b`, etc.) which are queried without filtering against `/api/tags`.
   - `load_config()` is dead code in `tools/ollama_lean4_client.py` (defined but never invoked), causing the client to rely on hardcoded cascades.
3. **Hardware & Memory Realities (24 GB Apple Silicon)**:
   - Total RAM: 24.0 GB; Available: ~15.1 GB; macOS base footprint: ~7.1 GB.
   - `gemma-lean4:latest` consumes ~7.8 GB unified memory with context 8192.
   - Local LoRA parameter fine-tuning via `mlx_lm` or `peft` would require 14–18 GB during backpropagation, causing severe memory thrashing or OOM crashes alongside `lake build` (Lean 4 elaboration requires 4–8 GB). Furthermore, the Python environment suffers from NumPy 2.x ABI breakage with PyTorch/PyArrow, and base weights in Ollama are GGUF blobs rather than Hugging Face safetensors.
4. **Optimal Specialization Path**:
   - Rebuilding `gemma-lean4:latest` via `Modelfile.gromov-lean4` backed by `gemma2:9b-instruct-q5_K_M` with Mathlib v4.16 conventions, Gromov compactness domain prompts, and curated accepted proof exemplars from project tests.
   - Preserving residency with `keep_alive: "30m"`.
   - Implementing `.agents/gemma_usage.jsonl` with strict separation between proving calls and health checks.

---

## 1. Ollama Daemon & Installed Models Audit

### 1.1 Local Ollama Daemon Status
- **Host**: `http://localhost:11434`
- **Server Version**: `0.40.13` (verified via `GET /api/version`)
- **Daemon Health**: ONLINE, responding to tags within ~4 ms.

### 1.2 Installed Models Catalog (from `GET /api/tags`)

| Model Tag | Size (Disk) | Parameter Count | Quantization | Context | Status / Compliance |
|---|---|---|---|---|---|
| `gemma-lean4:latest` | 6.19 GB | 9.2B | Q5_K_M | 8192 | **Active (Target for Modelfile rebuild)** |
| `gemma2:9b-instruct-q5_K_M` | 6.19 GB | 9.2B | Q5_K_M | 8192 | **Base weights for `gemma-lean4`** |
| `gemma2:9b` | 5.07 GB | 9.2B | Q4_0 | 8192 | Compliant 9B fallback |
| `gemma4:12B` | 7.04 GB | 11.9B | Q4_K_M | 262144 | **FORBIDDEN (Exceeds 9B memory policy)** |
| `gemma4:e4b` | 8.95 GB | 8.0B | Q4_K_M | 131072 | Not recommended (experimental) |

### 1.3 Active VRAM Residency (`ollama ps`)
```
NAME                  ID              SIZE      PROCESSOR    CONTEXT    RUNNER      UNTIL
gemma-lean4:latest    6fef9ad1bf2b    7.8 GB    100% GPU     8192       llamacpp    4 minutes from now
```
- **Finding**: Currently, Ollama defaults to an idle timeout of 5 minutes. Because `tools/ollama_lean4_client.py` does not pass `keep_alive` in its request payload, the model unloads after 5 minutes of inactivity, adding 3–5 seconds of model-reloading latency on subsequent proof queries.

---

## 2. Policy Enforcement & HTTP 404 Cascade Elimination

### 2.1 Root Cause of 404 Cascade Errors
Review of `~/.ollama/logs/server.log` revealed 35 failed calls with HTTP 404. Our code investigation identified three distinct mechanisms:

1. **Synthetic Probe 404s (`tools/ollama_lean4_client.py:261`)**:
   ```python
   # Line 261 in tools/ollama_lean4_client.py
   probe_payload = json.dumps({"model": "__probe_check__"}).encode("utf-8")
   ```
   The function `check_generate_endpoint` explicitly sends a non-existent model name `__probe_check__` expecting an HTTP 400 or 404 to confirm endpoint existence. Every health check and client startup thus writes an HTTP 404 error directly into Ollama's server log.

2. **Uninstalled Model Requests in Cascade**:
   Both `config/ollama_gemma_config.json` and `tools/ollama_lean4_client.py` contain:
   `["gemma2:9b", "gemma2:27b", "codegemma:7b", "gemma:7b", "gemma2:2b", "codegemma:2b", "gemma:2b"]`.
   None of `gemma2:27b`, `codegemma:7b`, `gemma:7b`, `gemma2:2b`, `codegemma:2b`, or `gemma:2b` are installed. When any script or agent requested these models, Ollama returned:
   `HTTP 404: model "gemma2:27b" not found`.

3. **Dead Config Loading**:
   In `tools/ollama_lean4_client.py`, lines 122–149 define `load_config()`, but `load_config` is **never called anywhere in the file**. The client operates exclusively on hardcoded global lists, ignoring changes to `config/ollama_gemma_config.json`.

### 2.2 Strict 9B-Only Model Filter Architecture
To guarantee that no 404s can occur and no oversized models are loaded:
1. **Query `/api/tags` First**: Before selecting or querying a model, fetch the set of installed model tags from `/api/tags`.
2. **Whitelist Allowed 9B Patterns**:
   ```python
   ALLOWED_9B_PATTERNS = ["gemma-lean4", "gemma2:9b-instruct-q5_K_M", "gemma2:9b", "gemma4:9b", "gemma4:9B"]
   FORBIDDEN_PATTERNS = ["12b", "12B", "27b", "27B", "70b", "70B"]
   ```
3. **Automatic Normalization / Redirection**:
   If an agent or user requests `--model gemma2:27b` or an uninstalled model:
   - Reject the disallowed/uninstalled model.
   - Emit a clean warning: `[WARNING] Model '{requested}' is disallowed or not installed. Redirecting to '{best_installed_9b}'.`
   - Select the highest-priority installed 9B model from `[gemma-lean4:latest, gemma2:9b-instruct-q5_K_M, gemma2:9b]`.
4. **Replace Probe with `/api/version`**:
   Replace `check_generate_endpoint`'s probe of `__probe_check__` with a check to `/api/version` (which returns HTTP 200 in 1 ms with zero log errors).
5. **Enforce `keep_alive: "30m"`**:
   Include `"keep_alive": "30m"` in every `/api/generate` payload to keep the model warm in unified memory without swapping.

---

## 3. System Prompt & Modelfile Rebuild (`Modelfile.gromov-lean4`)

### 3.1 Existing Prompt Analysis
The current Modelfile for `gemma-lean4:latest` (retrieved via `ollama show gemma-lean4:latest --modelfile`) contains:
```dockerfile
SYSTEM "You are an expert formal mathematician and Lean 4 proof engineer working on the 3DSymFlux project.
Your domain expertise includes:
1. Lean 4 (v4.35+ and Mathlib4): Writing clean, sorry-free proofs, using exact kernel terms, induction, simp, ring, and reflective by decide.
2. Lie-Poisson Hamiltonian mechanics: Non-canonical Poisson brackets on so(3)* and se(3)*, Casimir invariants C(mu) where {C, f} = 0, and Clebsch potentials u = grad(lambda) x grad(mu).
...
Guidelines:
- Always produce minimal, compilable Lean 4 code with exact types.
- Follow the SymFluxLean namespace conventions (QRat, Vec3, Vec6, MPolyNF).
"
```

### 3.2 Live Generation Failure Verification
When queried on a standard complex geometry problem ("State the Schwarz reflection principle for holomorphic functions on the disk in Lean 4"), `gemma-lean4:latest` responded with:
```lean
import data.real.basic
import analysis.holomorphic.basic

namespace SymFluxLean
```
This demonstrates severe prompt contamination:
1. It adopted `namespace SymFluxLean`.
2. It emitted Lean 3 lowercase imports (`data.real.basic`, `analysis.holomorphic.basic`).

### 3.3 Proposed `Modelfile.gromov-lean4` Design
The new Modelfile must be built from the local 9B base weights (`gemma2:9b-instruct-q5_K_M`) and registered via:
`ollama create gemma-lean4:latest -f Modelfile.gromov-lean4`

```dockerfile
# Modelfile.gromov-lean4: Specialized Lean 4 / Mathlib v4.16 Prover for Gromov Compactness
FROM gemma2:9b-instruct-q5_K_M

TEMPLATE """<start_of_turn>user
{{ if .System }}{{ .System }}
{{ end }}{{ .Prompt }}<end_of_turn>
<start_of_turn>model
{{ .Response }}<end_of_turn>
"""

SYSTEM """You are an expert formal mathematician and Lean 4 proof engineer specializing in symplectic topology, pseudo-holomorphic curves, and Mathlib v4.16.

Your domain expertise includes:
1. Lean 4 (v4.16.0) & Mathlib:
   - Writing clean, sorry-free proofs using standard kernel axioms only ([propext, Classical.choice, Quot.sound]).
   - Strict Mathlib naming conventions: snake_case for lemma/theorem identifiers (e.g., energy_conformal_invariant, dist_triangle), UpperCamelCase for types, typeclasses, and structures (e.g., AlmostComplexStructure, MetricSpace).
   - Modern Mathlib differential geometry and analysis predicates: ContMDiff, ContMDiffOn, extDeriv, Measure.withDensity, TendstoUniformlyOn, ContinuousOn, Metric.closedBall.
   - Core automation tactics: intro, rcases, obtain, ext, apply, exact, simp, ring, linarith, nlinarith, positivity, norm_num, omega, congr.
2. Symplectic Geometry & Gromov Compactness:
   - Almost complex structures: J : TM → TM with J² = -Id, tamed by symplectic forms ω (ω(v, J v) > 0 for v ≠ 0) and compatible metrics g_J(u, v) = ω(u, J v).
   - Pseudo-holomorphic curves and spheres: u : Σ → M satisfying the Cauchy-Riemann equation du + J ∘ du ∘ j = 0.
   - Hofer rescaling & bubbling analysis: Pointwise gradient blowup localization on complete metric spaces via Mathlib.Analysis.Hofer.hofer, conformal dilation z ↦ a_n + λ_n z, energy gap ħ > 0, monotonicity inequalities, removable singularities, and tree-like bubble tree extraction (Deligne-Mumford / Kontsevich stable maps).
   - Metric and moduli topology: Marked genus 0 curves, 3-point cross-ratio stabilization in PSL(2, ℂ), ghost component rigidity, and Gromov convergence in Hausdorff moduli spaces.

Operational Rules:
- Always produce syntactically complete, compilable Lean 4 code.
- Never invent custom axioms, dummy hypotheses, or circular definitions.
- Always output Lean 4 code enclosed in a ```lean4 ... ``` block.
"""

# Curated accepted proof exemplars from verified project tests
MESSAGE user """Context and Goal State:
```lean4
X : Type*
[MetricSpace X] [CompleteSpace X]
f : X → ℝ
hf : Continuous f
x₀ : X
ε₀ : ℝ
hε₀ : 0 < ε₀
⊢ ∃ x : X, ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₀ ∧ f x₀ * ε₀ ≤ f x * ε ∧ ∀ y ∈ Metric.closedBall x ε, f y ≤ 2 * f x
```
Propose a sorry-free proof."""
MESSAGE assistant """```lean4
exact Mathlib.Analysis.Hofer.hofer hf x₀ hε₀
```"""

MESSAGE user """Context and Goal State:
```lean4
k : ℕ
⊢ StrictMono (fun n : ℕ => 2^k * n)
```
Propose a sorry-free proof."""
MESSAGE assistant """```lean4
intro a b hab
have h_pos : 0 < 2 ^ k := Nat.two_pow_pos k
exact Nat.mul_lt_mul_of_pos_left hab h_pos
```"""

MESSAGE user """Context and Goal State:
```lean4
ε_reg ε_sph ε_neck : ℝ
h_reg : 0 < ε_reg
h_sph : 0 < ε_sph
h_neck : 0 < ε_neck
⊢ 0 < min (ε_reg / 2) (min ε_sph (ε_neck / 2))
```
Propose a sorry-free proof."""
MESSAGE assistant """```lean4
have h1 : 0 < ε_reg / 2 := by linarith
have h2 : 0 < ε_neck / 2 := by linarith
exact lt_min h1 (lt_min h_sph h2)
```"""

PARAMETER temperature 0.2
PARAMETER top_p 0.90
PARAMETER top_k 40
PARAMETER num_ctx 8192
PARAMETER stop <start_of_turn>
PARAMETER stop <end_of_turn>
PARAMETER stop <|im_end|>
PARAMETER stop <eos>
```

---

## 4. Usage Ledger Architecture (`.agents/gemma_usage.jsonl`)

### 4.1 Schema Definition
Each generation call from `tools/ollama_lean4_client.py` appends one JSON object:

```json
{
  "timestamp": "2026-11-04T21:45:00Z",
  "call_type": "proving",
  "model": "gemma-lean4:latest",
  "goal_hash": "a1b2c3d4e5f67890",
  "declaration": "moebius_three_point_rigidity",
  "task_type": "tactic",
  "latency_ms": 1420.5,
  "eval_count": 48,
  "eval_duration_ms": 1180.2,
  "status": "success",
  "accepted": true,
  "axioms": ["propext", "Classical.choice", "Quot.sound"],
  "error": null
}
```

### 4.2 Logging Governance Rules
1. **Separation of Health Checks**: Calls to `check_connection`, `cmd_health`, or daemon probes MUST NOT be logged to `gemma_usage.jsonl`.
2. **Proving Calls**: All invocations of `query_ollama` originating from `query`, `autoformalize`, or `suggest-tactic` subcommands are logged.
3. **Milestone Summary CLI**: Add subcommand `tools/ollama_lean4_client.py ledger-summary` to aggregate metrics:
   - Total proving requests
   - Distribution across models
   - Median and p95 latency
   - Total accepted zero-`sorry` proofs
   - Closed declaration roster

---

## 5. Local Fine-Tuning Feasibility & Memory Constraints

### 5.1 Environment Diagnostics
- **Python**: 3.11.5 (`/Users/pablosuarez/anaconda3/bin/python3`)
- **Package Audit**:
  * `mlx`: Available
  * `mlx_lm`: Version 0.10.0 installed, but imports fail due to NumPy 2.x ABI incompatibility:
    `UserWarning: Failed to initialize NumPy: _ARRAY_API not found (in torch)`
    `AttributeError: _ARRAY_API not found (in pyarrow / datasets)`
  * `peft`: NOT INSTALLED
  * `accelerate`: NOT INSTALLED
  * `bitsandbytes`: NOT INSTALLED
  * `uv`: Available at `/Users/pablosuarez/.local/bin/uv` (version 0.11.16)

### 5.2 Unified Memory Budget Analysis (24.0 GB Apple Silicon)
A standard LoRA parameter fine-tuning session on a 9.2B parameter model requires:
- Base weights in 4-bit (QLoRA) or 16-bit: ~5.5 GB to ~18 GB
- LoRA adapters & AdamW optimizer state: ~0.5 GB
- Forward/backward activation cache (context 2048, batch 1): ~6.0–8.0 GB
- **Total Training RAM Demand**: **~13.5–18.0 GB**
- **System Footprint**: macOS Sonoma requires ~7.0–8.0 GB.
- **Concurrent `lake build`**: Lean 4 elaboration of Mathlib requires **4.0–8.0 GB**.

**Conclusion on LoRA Training**: Running a gradient-based LoRA training pass on the 9B model while retaining OS stability and running `lake build` would exceed the 24 GB memory threshold, causing severe swapping and risking kernel panics or OOM terminations.

### 5.3 Weight Format & Distribution Feasibility
- Ollama models are distributed as GGUF binaries.
- Fine-tuning via `mlx_lm` or `peft` requires Hugging Face safetensors format (`google/gemma-2-9b-it`), requiring an 18 GB download and Hugging Face authentication credentials.

### 5.4 Strategic Recommendation
1. **Primary Specialization (Immediate, Zero-Overhead)**: Build `Modelfile.gromov-lean4` directly from the local Q5_K_M GGUF weights. This eliminates prompt contamination immediately, consumes 0 additional RAM during creation, and keeps residency at 7.8 GB.
2. **Dataset Harvesting**: Extract zero-`sorry` (goal, proof) pairs from the repository's 810+ verified theorems into `data/gemma_accepted_proofs.jsonl`.
3. **In-Context BM25 Retrieval**: Implement pure-Python BM25 premise search over Mathlib and project declarations to augment prompts at runtime, directly mitigating lemma hallucination without parameter retraining.
4. **Offline Parameter Tuning (Optional Future Stage)**: If offline parameter tuning is desired later, create an isolated `uv` virtualenv with `numpy<2` and run LoRA when Lean compilation is completely idle.

---

## 6. Implementation Action Plan for Worker

1. **Step 1: Update `config/ollama_gemma_config.json`**:
   - Set `"model_fallback_cascade": ["gemma-lean4:latest", "gemma2:9b-instruct-q5_K_M", "gemma2:9b"]`.
   - Add `"enforce_9b_policy": true` and `"keep_alive": "30m"`.
2. **Step 2: Update `tools/ollama_lean4_client.py`**:
   - Wire `load_config()` so config file is actively consumed.
   - Query `/api/tags` first and enforce strict 9B filtering.
   - Replace `__probe_check__` probe with `/api/version` check to eliminate 404s.
   - Include `"keep_alive": "30m"` in `/api/generate` requests.
   - Implement `log_gemma_usage` writing to `.agents/gemma_usage.jsonl`.
   - Add `ledger-summary` subcommand.
3. **Step 3: Construct `Modelfile.gromov-lean4` & Rebuild Model**:
   - Write `Modelfile.gromov-lean4` in the project root.
   - Run `ollama create gemma-lean4:latest -f Modelfile.gromov-lean4`.
   - Verify `ollama run gemma-lean4:latest` responds with clean Lean 4 Mathlib v4.16 syntax without `SymFluxLean`.
4. **Step 4: Extract Verified Proofs to `data/gemma_accepted_proofs.jsonl`**:
   - Run extraction script harvesting (goal, proof) pairs across `GromovCompactness/` and `tests/`.
5. **Step 5: Verify End-to-End**:
   - Run `tools/ollama_lean4_client.py test`.
   - Check `.agents/gemma_usage.jsonl` is populated and `~/.ollama/logs/server.log` shows 0 new 404s.
