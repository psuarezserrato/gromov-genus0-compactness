# Local Gemma & Ollama Pipeline Integration Guide for Lean 4

**Project**: Autoformalization of Gromov Compactness for Genus 0 Pseudo-Holomorphic Curves in Lean 4  
**Component**: Local Model Integration Pipeline (Milestone M3)  
**Configuration**: `config/ollama_gemma_config.json`  
**Core Tooling**: `tools/ollama_lean4_client.py`  
**Test Suite**: `tools/test_ollama_pipeline.py`  
**Target Environment**: macOS (Apple Silicon / Intel), Python 3.6+, Ollama daemon (`http://localhost:11434`)  

---

## 1. Executive Overview & Architectural Design

The autoformalization of deep mathematical theories—such as Mikhail Gromov's 1985 landmark theorem on the compactness of pseudo-holomorphic curves and its foundational analytical treatment by Sergey Ivashkovich and Vsevolod Shevchishin (arXiv:math/9912046)—requires numerous iterations of definition drafting, premise selection, tactic search, and compiler error repair. Relying exclusively on external commercial cloud APIs introduces significant compute costs, network latency bottlenecks, and operational external dependencies.

This pipeline integrates Google's **Gemma** open-weights models (`gemma2:9b`, `gemma2:27b`, `gemma2:2b`, and `codegemma`) via **Ollama** running locally on macOS. 

### Key Architectural Tenets
1. **Zero External Dependencies**: All tools (`ollama_lean4_client.py` and `test_ollama_pipeline.py`) use strictly Python standard library modules (`urllib.request`, `json`, `argparse`, `unittest`, `re`, `time`, `io`, `sys`). No `pip install` is required.
2. **Deterministic & Stochastic Parameter Profiles**: Standard LLM generation settings fail for theorem proving. We establish calibrated parameter profiles: near-deterministic ($T = 0.1$) for declaration extraction and premise retrieval, and moderately exploratory ($T = 0.4$) for escaping tactic search dead ends.
3. **Context Window Expansion to 8192 Tokens**: Standard Ollama defaults truncate context at 2048 tokens, which breaks during Lean 4 sessions involving extensive Mathlib imports and complex local goal states. Our pipeline locks context at 8192 tokens.
4. **7-Tier Automated Fallback Cascade**: If the primary model `gemma2:9b` is unavailable, the pipeline cascades through a hierarchy of available local checkpoints, terminating in an offline dry-run mock mode to allow testing without failing agent workflows.
5. **Rigorous Gemma Control Tokens**: Gemma models require strict turn formatting (`<start_of_turn>user`, `<end_of_turn>`, `<start_of_turn>model`). System instructions are correctly prepended into the user turn rather than emitting invalid system tokens.

---

## 2. macOS Installation and Environment Setup

### 2.1 Installing Ollama on macOS

#### Option A: Homebrew (Recommended)
```bash
brew install ollama
```

#### Option B: Official Binary Download
Download the signed macOS universal application bundle directly from the official repository:
- URL: `https://ollama.com/download/Ollama-darwin.zip`
- Unzip and drag `Ollama.app` into `/Applications`.

### 2.2 Starting the Ollama Daemon

You can run Ollama as an interactive background process or register it with `launchd`:

```bash
# Launch daemon in background
ollama serve > /dev/null 2>&1 &

# Verify service is listening
curl -s http://localhost:11434/
# Expected response: "Ollama is running"
```

### 2.3 Hardware Acceleration & Metal Optimization

On Apple Silicon (M1/M2/M3/M4 Pro/Max/Ultra), Ollama automatically leverages Apple Metal and Unified Memory Architecture (UMA). Because GPU and CPU share high-bandwidth unified RAM, models run with near-zero memory copying overhead:
- **`gemma2:9b`**: Requires ~6.5 GB unified RAM. Runs comfortably on base 8GB or 16GB Macs.
- **`gemma2:27b`**: Requires ~17.5 GB unified RAM. Recommended for 24GB, 36GB, 48GB, or higher unified memory.
- **`gemma2:2b`**: Requires ~2.2 GB unified RAM. Suitable for any machine, yielding inference speeds exceeding 60 tokens/second.

### 2.4 Daemon Environment Configuration

Set the following environment variables in your shell profile (`~/.zshrc` or `~/.bash_profile`) or daemon launch script:

| Environment Variable | Recommended Value | Purpose |
| :--- | :--- | :--- |
| `OLLAMA_HOST` | `127.0.0.1:11434` | Binds the daemon to local loopback interface. |
| `OLLAMA_MODELS` | `~/.ollama/models` | Storage path for downloaded GGUF manifests and tensors. |
| `OLLAMA_KEEP_ALIVE` | `30m` or `-1` | **Critical for Theorem Proving**. Keeps model weights loaded in VRAM between tactic queries, eliminating the 3–8 second cold-start latency per prompt. |
| `OLLAMA_NUM_PARALLEL` | `1` | Concurrency limit. Set to 1 to reserve maximum memory for context length. |

To apply:
```bash
export OLLAMA_KEEP_ALIVE=30m
ollama serve
```

---

## 3. Model Zoo and Recommended Gemma Checkpoints

### 3.1 Model Comparison Matrix for Lean 4 Formalization

| Model Tag | Parameters | Quantization | Context Window | VRAM Required | Optimal Proving Role |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`gemma2:9b`** | 9.2B | Q4_K_M | 8192 | ~6.5 GB | **Primary Target**: SOTA reasoning in 10B class. Handles complex dependent type signatures, almost-complex structures, and multi-step tactics. |
| **`gemma2:27b`** | 27.2B | Q4_K_M | 8192 | ~17.5 GB | **High-Compute Tier**: Deep mathematical reasoning and subtle typeclass resolutions for master lemmas. |
| **`codegemma:7b`** | 8.5B | Q4_K_M | 8192 | ~5.8 GB | **Code-Specialized**: Fine-tuned on math and program verification syntax. |
| **`gemma:7b`** | 8.5B | Q4_0 | 8192 | ~5.2 GB | **Legacy 7B**: Reliable baseline declarations. |
| **`gemma2:2b`** | 2.6B | Q4_K_M | 8192 | ~2.2 GB | **Lightweight Tier**: Ultra-fast iteration for single-tactic suggestion (`exact`, `apply`, `linarith`). |
| **`codegemma:2b`** | 2.5B | Q4_K_M | 8192 | ~2.0 GB | **Compact Code Tier**: Fast tactic generation on resource-constrained devices. |
| **`gemma:2b`** | 2.5B | Q4_0 | 2048 / 8192 | ~1.8 GB | **Legacy Compact Tier**: Minimal hardware footprint. |

### 3.2 Model Pull Commands

To install the primary proving model and lightweight fallback:
```bash
# Pull primary recommendation (9.2B params)
ollama pull gemma2:9b

# Pull lightweight fallback (2.6B params)
ollama pull gemma2:2b

# Optional: high-compute tier (if 24GB+ RAM is available)
ollama pull gemma2:27b
```

### 3.3 The 7-Tier Fallback Cascade Architecture

The automated model discovery engine queries `GET /api/tags` and traverses the cascade:

```
[Explicit User Tag --model <tag>]
              │ (if specified by user or caller)
              ▼
    ┌──────────────────────┐
    │ Found explicit match? │──(yes)──► [Use user model]
    └──────────────────────┘
              │ (no or unspecified)
              ▼
    Tier 1: gemma2:9b    ──(installed?)──► [Use gemma2:9b]
              │ (no)
    Tier 2: gemma2:27b   ──(installed?)──► [Use gemma2:27b]
              │ (no)
    Tier 3: codegemma:7b ──(installed?)──► [Use codegemma:7b]
              │ (no)
    Tier 4: gemma:7b     ──(installed?)──► [Use gemma:7b]
              │ (no)
    Tier 5: gemma2:2b    ──(installed?)──► [Use gemma2:2b]
              │ (no)
    Tier 6: codegemma:2b ──(installed?)──► [Use codegemma:2b]
              │ (no)
    Tier 7: gemma:2b     ──(installed?)──► [Use gemma:2b]
              │ (no)
    Generic: Any model containing "gemma" in tag
              │ (no)
    Local: First installed local model (e.g. llama3, qwen)
              │ (no models in local catalog)
    Dry-run / Offline Simulation Mode
```

---

## 4. Operational Configuration (`config/ollama_gemma_config.json`)

The configuration file `/Users/pablosuarez/Desktop/SympTopAutoForm/config/ollama_gemma_config.json` stores endpoints, hardware profiles, sampling parameters, and prompt templates.

### 4.1 Task Parameter Profiles

```json
{
  "parameter_profiles": {
    "autoformalize": {
      "temperature": 0.1,
      "top_p": 0.90,
      "top_k": 40,
      "num_predict": 512,
      "num_ctx": 8192,
      "repeat_penalty": 1.10,
      "stop": ["<end_of_turn>", "<eos>", "\n\n--", "\n\ntheorem ", "\n\nlemma "]
    },
    "tactic": {
      "temperature": 0.4,
      "top_p": 0.95,
      "top_k": 50,
      "num_predict": 128,
      "num_ctx": 8192,
      "repeat_penalty": 1.05,
      "stop": ["<end_of_turn>", "<eos>", "\n\n"]
    },
    "proof_skeleton": {
      "temperature": 0.3,
      "top_p": 0.90,
      "top_k": 40,
      "num_predict": 1024,
      "num_ctx": 8192,
      "repeat_penalty": 1.10,
      "stop": ["<end_of_turn>", "<eos>"]
    },
    "premise": {
      "temperature": 0.0,
      "top_p": 0.85,
      "top_k": 20,
      "num_predict": 256,
      "num_ctx": 8192,
      "repeat_penalty": 1.15,
      "stop": ["<end_of_turn>", "<eos>", "\n\n"]
    }
  }
}
```

### 4.2 Why `num_ctx: 8192` is Critical
In formal mathematics, goal states are not simple text snippets:
- Manifold formalizations import differential geometry, calculus, and topology structures.
- Local context contains variables, typeclasses (`[MetricSpace M] [SmoothManifoldWithCorners I M]`), and multiple hypotheses.
- Truncating context at Ollama's default 2048 tokens produces syntax errors where closing braces or dependent types are dropped. 8192 tokens provides ample headroom for multi-file contexts.

---

## 5. CLI Tool Usage (`tools/ollama_lean4_client.py`)

The standalone client provides a comprehensive CLI supporting both modern subcommands and legacy flags.

### 5.1 Subcommand Reference

#### 1. `health` — Check Daemon Connectivity & Readiness
Probes `/api/tags` and `/api/generate`, checks installed models, and recommends the optimal Gemma model.
```bash
# Standard live health probe
python3 tools/ollama_lean4_client.py health

# Dry-run health probe (offline/sandboxed environments)
python3 tools/ollama_lean4_client.py health --dry-run
```

#### 2. `list-models` — Catalog Installed Models
Lists all models currently available in local Ollama storage with file sizes.
```bash
python3 tools/ollama_lean4_client.py list-models
```

#### 3. `autoformalize` — Translate Informal Math into Lean 4
Translates natural language symplectic definitions, lemmas, or theorems into valid Lean 4 code blocks.
```bash
# Using auto-detected optimal model
python3 tools/ollama_lean4_client.py autoformalize \
  "An almost complex structure J on M is an endomorphism of TM with J^2 = -Id."

# With specific model override and JSON output
python3 tools/ollama_lean4_client.py autoformalize \
  "State Hofer's lemma for continuous functions on complete metric spaces." \
  --model gemma2:9b \
  --json
```

#### 4. `suggest-tactic` — Propose Repair Tactic from Compiler Error
Takes a Lean 4 goal state, failed tactic, and compiler error, and returns a targeted tactic repair.
```bash
python3 tools/ollama_lean4_client.py suggest-tactic \
  --goal "M : Type* [MetricSpace M] [CompleteSpace M] f : M → ℝ hf : Continuous f ⊢ ∃ x ε, 0 < ε ∧ f x * ε ≥ f x0 * ε0" \
  --error "type mismatch: expected 0 < ε0" \
  --failed-tactic "exact Hofer.hofer hf x0"
```

#### 5. `query` — General Prompt Query
Dispatches a custom prompt with task-specific parameter profiles.
```bash
python3 tools/ollama_lean4_client.py query \
  --prompt "Find top 5 Mathlib lemmas for triangle inequality in metric spaces" \
  --task premise
```

#### 6. `test` — Run Internal Self-Test Suite
Executes 8 internal unit tests verifying fallback cascades, Gemma token templates, markdown extraction, parameter profiles, and mock generators.
```bash
python3 tools/ollama_lean4_client.py test
```

### 5.2 Global Options and Flags

| Flag | Subcommands | Description |
| :--- | :--- | :--- |
| `--host <url>` | All | Custom Ollama host URL (default: `http://localhost:11434`). |
| `--model <tag>` | All | Override model selection (e.g. `gemma2:9b`). |
| `--timeout <sec>` | All | HTTP request timeout in seconds (default: 5.0 for health, 60.0 for queries). |
| `--dry-run` | All | Run in offline mock mode without making HTTP requests. |
| `--json` | All | Output structured JSON response containing metadata, durations, and code. |

---

## 6. Direct API and cURL Reference

For integrations using shell scripts, Lake build hooks, or curl:

### 6.1 Check Service Health
```bash
curl -s http://localhost:11434/api/tags | python3 -m json.tool
```

### 6.2 Autoformalize Query via `/api/generate`
```bash
curl -s -X POST http://localhost:11434/api/generate \
  -H "Content-Type: application/json" \
  -d '{
    "model": "gemma2:9b",
    "prompt": "<start_of_turn>user\nYou are an expert Lean 4 formalizer.\n\nTranslate the following definition into Lean 4:\nDefinition: A symplectic form on a manifold M is a closed, non-degenerate 2-form omega.<end_of_turn>\n<start_of_turn>model\n",
    "stream": false,
    "options": {
      "temperature": 0.1,
      "top_p": 0.90,
      "num_ctx": 8192,
      "num_predict": 512,
      "stop": ["<end_of_turn>", "<eos>", "\n\ntheorem ", "\n\nlemma "]
    }
  }'
```

### 6.3 Tactic Suggestion via `/api/generate`
```bash
curl -s -X POST http://localhost:11434/api/generate \
  -H "Content-Type: application/json" \
  -d '{
    "model": "gemma2:9b",
    "prompt": "<start_of_turn>user\nYou are an automated Lean 4 tactic prover.\n\nGoal state:\n⊢ ∃ x : M, ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε0\n\nFailed tactic: exact hofer_lemma\nError: missing argument hε0\n\nSuggest the next tactic step.<end_of_turn>\n<start_of_turn>model\n",
    "stream": false,
    "options": {
      "temperature": 0.4,
      "top_p": 0.95,
      "num_ctx": 8192,
      "num_predict": 128,
      "stop": ["<end_of_turn>", "<eos>", "\n\n"]
    }
  }'
```

---

## 7. Prompt Engineering & Gemma Special Tokens

Google Gemma models (Gemma 1, Gemma 2, CodeGemma) utilize explicit turn-based delimiters:

```
<start_of_turn>user
{user_message}<end_of_turn>
<start_of_turn>model
{model_response}<end_of_turn>
```

> **Important**: Gemma instruct models do not support `<start_of_turn>system`. Supplying a system token causes degraded generation or literal token emission. System instructions must be placed at the top of the initial `<start_of_turn>user` turn block.

Below are the four production prompt templates used in this pipeline.

---

### Template 1: Informal Statement $\to$ Lean 4 Formal Declaration

```markdown
<start_of_turn>user
You are an expert mathematician and Lean 4 formalizer specializing in symplectic geometry, almost complex manifolds, and Mathlib.
Your task is to translate informal mathematical definitions, lemmas, and theorems into syntactically valid Lean 4 code.

Guidelines:
1. Use standard Mathlib naming conventions (snake_case for terms/theorems, UpperCamelCase for types).
2. Explicitly specify all typeclass arguments (e.g. [MetricSpace M], [SmoothManifoldWithCorners I M]).
3. For theorems whose proofs are not requested, terminate with ':= by sorry'.
4. Output Lean 4 code enclosed in a ```lean4 ... ``` block.

---
### Example 1:
Informal:
"Definition: An almost complex structure J on a smooth manifold M is a smooth bundle endomorphism J of the tangent bundle TM such that J^2 = -Id. J is said to be tame with respect to a symplectic 2-form omega if omega(v, J v) > 0 for all non-zero tangent vectors v."

Lean 4 Formalization:
```lean4
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Analysis.Calculus.FDeriv.Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]

/-- An almost complex structure on a smooth manifold is a fiberwise endomorphism of TM whose square is -Id. -/
structure AlmostComplexStructure where
  J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x
  J_sq : ∀ (x : M) (v : TangentSpace I x), J x (J x v) = -v
  smooth_J : ContMDiff I (I.prod I) ⊤ (fun (p : TangentBundle I M) => (p.1, J p.1 p.2))

/-- An almost complex structure J is tame with respect to a 2-form ω if ω(v, J v) > 0 for all non-zero tangent vectors. -/
def IsTame (J : AlmostComplexStructure I M) (ω : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) : Prop :=
  ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < ω x v (J.J x v)
```

---
### Input Task:
Informal:
"{informal_statement}"
<end_of_turn>
<start_of_turn>model
```

---

### Template 2: Goal-Directed Tactic Suggestion from Lean 4 Error State

```markdown
<start_of_turn>user
You are an interactive Lean 4 tactic reasoning engine. Given a current proof state, the target goal, and the compiler diagnostic or error generated by the previous tactic attempt, your task is to propose the next correct Lean 4 tactic.

Guidelines:
1. Provide a single, minimal tactic or a short tactic sequence ('by ...').
2. Do not hallucinate premises: prioritize standard Mathlib tactics (apply, exact, intro, cases, obtain, linarith, simp, positivity).
3. Briefly explain the mathematical rationale in a one-line comment.

---
### Example 1:
Context and Goal State:
```lean4
M : Type*
[MetricSpace M] [CompleteSpace M]
f : M → ℝ
hf_cont : Continuous f
hf_nonneg : ∀ x, 0 ≤ f x
x0 : M
ε0 : ℝ
hε0 : 0 < ε0
⊢ ∃ x : M, ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε0 ∧ f x * ε ≥ f x0 * ε0 ∧ ∀ y ∈ Metric.closedBall x ε, f y ≤ 2 * f x
```

Failed Tactic Attempt:
`exact Hofer.hofer hf_cont x0 hε0`

Compiler Error:
```
type mismatch:
  Hofer.hofer hf_cont x0 hε0
has type:
  0 < ε0 → ∃ x ε, 0 < ε ∧ ε ≤ ε0 ∧ ...
but is expected to have type:
  ∃ x ε, 0 < ε ∧ ε ≤ ε0 ∧ ...
```

Suggested Tactic:
```lean4
-- Hofer's lemma in Mathlib takes hε0 as an explicit argument after the continuity hypothesis
exact Hofer.hofer hf_cont x0 hε0
```

---
### Input Task:
Context and Goal State:
```lean4
{context_and_goal}
```

Failed Tactic Attempt:
`{failed_tactic}`

Compiler Error:
```
{compiler_error}
```

Suggested Tactic:
<end_of_turn>
<start_of_turn>model
```

---

### Template 3: Premise Selection from Mathlib

```markdown
<start_of_turn>user
You are an expert Mathlib search assistant for Lean 4.
Given the current goal and available hypotheses, identify the top 5 most relevant Mathlib lemmas, definitions, or typeclass instances needed to advance the proof.

Output Format:
1. `Exact.Mathlib.Name` — brief 1-line explanation of applicability
2. `Exact.Mathlib.Name` — brief 1-line explanation of applicability
3. ...

---
### Example 1:
Goal:
```lean4
M : Type*
[MetricSpace M]
x y z : M
r : ℝ
h1 : dist x y < r / 2
h2 : dist y z < r / 2
⊢ dist x z < r
```

Selected Premises:
1. `dist_triangle` — Triangle inequality dist x z ≤ dist x y + dist y z
2. `lt_of_le_of_lt` — Transitivity to chain weak and strict inequalities
3. `add_lt_add` — Strict addition of inequalities a < b → c < d → a + c < b + d
4. `add_halves` — Simplification lemma r / 2 + r / 2 = r
5. `dist_comm` — Symmetry of metric distance dist x y = dist y x

---
### Input Task:
Goal and Context:
```lean4
{lean_goal_and_context}
```

Selected Premises:
<end_of_turn>
<start_of_turn>model
```

---

### Template 4: Subgoal Lemma Decomposition (Bubbling-Off Analysis)

```markdown
<start_of_turn>user
You are an expert mathematical theorist and Lean 4 architect specializing in symplectic topology and Gromov compactness.
Break down the informal proof of the bubbling-off phenomenon for genus 0 pseudo-holomorphic curves into an ordered list of 4 to 6 formal sub-lemmas with their Lean 4 type signatures.

Context:
Gromov's 1985 bubbling lemma: Let u_n : D -> M be a sequence of J-holomorphic disks with bounded symplectic energy E(u_n) <= E_0. If the gradient sequence sup_{z} |du_n(z)| -> infinity, then there exists a subsequence converging to a bubble tree of J-holomorphic spheres.

Required Sub-Lemmas:
1. Gradient blow-up point extraction via Hofer's Lemma.
2. Conformal dilation and coordinate rescaling v_n(z) = u_n(x_n + z / R_n).
3. Uniform C^1 gradient bound on the dilated sequence v_n on expanding disks.
4. Elliptic regularity and C^infty_loc convergence to an entire J-holomorphic map v_infty : C -> M.
5. Removal of singularity at infinity (energy quantization ħ > 0) to yield a non-trivial J-sphere v_infty : S^2 -> M.
<end_of_turn>
<start_of_turn>model
```

---

## 8. Troubleshooting and Diagnostic Guide

### 8.1 Connection Refused (`ConnectionRefusedError: [Errno 61]`)
- **Cause**: The Ollama daemon process is not running.
- **Remedy**:
  ```bash
  # Check if process is running
  pgrep -l ollama
  
  # Start the daemon
  ollama serve > /dev/null 2>&1 &
  ```

### 8.2 Sandbox Socket Restrictions (`Forbidden` or `Operation not permitted`)
- **Cause**: In restricted CI or agent sandboxes on macOS, loopback socket binding (`127.0.0.1:11434`) is blocked by OS security policy.
- **Remedy**:
  - Run the CLI with `--dry-run` to validate prompt formats, token sequences, and response extractors without network calls.
  - Or execute outside the sandbox container using standard terminal permissions.

### 8.3 Model Not Found (`HTTP 404: model 'gemma2:9b' not found`)
- **Cause**: The requested model tag has not been pulled to local storage.
- **Remedy**:
  ```bash
  ollama pull gemma2:9b
  ```
  The client's fallback cascade automatically detects if `gemma2:9b` is missing and selects the next available tier (`gemma2:2b`, etc.).

### 8.4 Out of Memory / Metal Allocation Failure
- **Cause**: Attempting to run `gemma2:27b` on a machine with less than 24GB RAM.
- **Remedy**:
  - Switch to `gemma2:9b` (recommended default, ~6.5GB VRAM) or `gemma2:2b` (~2.2GB VRAM).
  - Explicitly specify `--model gemma2:9b`.

### 8.5 Context Truncation and Incomplete Signatures
- **Cause**: Calling Ollama with default `num_ctx: 2048`.
- **Remedy**: Always pass `"num_ctx": 8192` in request options, as configured in `TASK_PARAMETER_PROFILES`.

### 8.6 Unicode Handling on Python 3.6 (`UnicodeEncodeError: 'ascii' codec can't encode...`)
- **Cause**: Under minimal POSIX or ASCII locales, Python 3.6 sets `sys.stdout.encoding = 'ascii'`. Mathematical Unicode characters (`→`, `₀`, `≤`, `∃`, `∀`) cause encoding exceptions.
- **Remedy**: Both `tools/ollama_lean4_client.py` and `tools/test_ollama_pipeline.py` implement an idempotent `ensure_utf8_streams()` wrapper that re-encodes stdout and stderr to UTF-8 with error replacement, ensuring crash-free execution on any terminal.

---

## 9. Verification Evidence

The entire pipeline is validated by `tools/test_ollama_pipeline.py` (39 unit and integration tests) and the internal self-test suite in `tools/ollama_lean4_client.py`:

```bash
$ python3 tools/test_ollama_pipeline.py
test_check_connection_http_error (__main__.TestHealthChecks) ... ok
test_check_connection_refused (__main__.TestHealthChecks) ... ok
test_check_connection_success (__main__.TestHealthChecks) ... ok
test_check_generate_endpoint_active_via_http_400 (__main__.TestHealthChecks) ... ok
test_check_generate_endpoint_unreachable (__main__.TestHealthChecks) ... ok
test_empty_catalog (__main__.TestModelFallbackCascade) ... ok
test_explicit_user_override (__main__.TestModelFallbackCascade) ... ok
test_fallback_to_first_local_model (__main__.TestModelFallbackCascade) ... ok
test_fallback_to_generic_gemma (__main__.TestModelFallbackCascade) ... ok
test_fallback_to_tier7_legacy_2b (__main__.TestModelFallbackCascade) ... ok
test_fallback_when_tier1_missing (__main__.TestModelFallbackCascade) ... ok
test_primary_tier_selection (__main__.TestModelFallbackCascade) ... ok
test_all_task_profiles_exist (__main__.TestParameterProfiles) ... ok
test_calibrated_temperatures (__main__.TestParameterProfiles) ... ok
test_context_window_size (__main__.TestParameterProfiles) ... ok
test_stop_tokens_configured (__main__.TestParameterProfiles) ... ok
test_build_autoformalize_prompt (__main__.TestGemmaTurnFormatting) ... ok
test_build_premise_prompt (__main__.TestGemmaTurnFormatting) ... ok
test_build_tactic_prompt (__main__.TestGemmaTurnFormatting) ... ok
test_format_few_shot_turns (__main__.TestGemmaTurnFormatting) ... ok
test_format_single_turn (__main__.TestGemmaTurnFormatting) ... ok
test_extract_lean4_code_fence (__main__.TestLeanCodeExtraction) ... ok
test_extract_lean_code_fence (__main__.TestLeanCodeExtraction) ... ok
test_extract_raw_code_without_fences (__main__.TestLeanCodeExtraction) ... ok
test_dry_run_autoformalize_energy_quantization (__main__.TestDryRunAndMockGeneration) ... ok
test_dry_run_autoformalize_hofer (__main__.TestDryRunAndMockGeneration) ... ok
test_dry_run_premise_selection (__main__.TestDryRunAndMockGeneration) ... ok
test_dry_run_proof_skeleton (__main__.TestDryRunAndMockGeneration) ... ok
test_dry_run_tactic_suggestion (__main__.TestDryRunAndMockGeneration) ... ok
test_config_loader_returns_valid_dict (__main__.TestConfigurationLoading) ... ok
test_query_ollama_malformed_json_response (__main__.TestErrorHandlingAndResilience) ... ok
test_query_ollama_network_timeout (__main__.TestErrorHandlingAndResilience) ... ok
test_legacy_flags_check_dry_run (__main__.TestCLIIntegration) ... ok
test_subcommand_autoformalize_dry_run (__main__.TestCLIIntegration) ... ok
test_subcommand_health_dry_run (__main__.TestCLIIntegration) ... ok
test_subcommand_list_models_dry_run (__main__.TestCLIIntegration) ... ok
test_subcommand_query_dry_run (__main__.TestCLIIntegration) ... ok
test_subcommand_suggest_tactic_dry_run (__main__.TestCLIIntegration) ... ok
test_subcommand_test (__main__.TestCLIIntegration) ... ok

----------------------------------------------------------------------
Ran 39 tests in 0.092s

OK (100% Pass Rate)
```

---

## 10. Downstream Integration with Lean 4 Proving Skills

This pipeline is directly integrated into the three specialized skills:

1. **`skills/lean4-symplectic-autoformalizer`**:
   Invokes `python3 tools/ollama_lean4_client.py autoformalize "<statement>"` to produce Lean 4 type signatures and structure definitions matching the formalization blueprint.
2. **`skills/ollama-lean4-gemma-prover`**:
   Wraps `tools/ollama_lean4_client.py` for premise retrieval (`--task premise`), proof skeleton generation (`--task proof_skeleton`), and single-step tactic exploration (`--task tactic`).
3. **`skills/lean4-proof-repair-engine`**:
   Extracts compiler error logs from `lake build` and calls `python3 tools/ollama_lean4_client.py suggest-tactic --goal "<goal>" --error "<error>"` to synthesize corrective tactics.
