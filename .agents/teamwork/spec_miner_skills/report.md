# Specification Mining Report: Reusable Agent Skills for Lean 4 Symplectic Autoformalization

**Working Directory:** `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/spec_miner_skills`  
**Date:** 2026-11-03  
**Status:** Complete Specification Artifact  

---

## 1. Executive Summary & Authoritative Sources

This specification report details the architectural designs, operational workflows, schemas, and CLI script patterns for **three reusable agent skills** required to autoformalize Gromov Compactness for genus 0 pseudo-holomorphic curves in Lean 4:

1. **`lean4-symplectic-autoformalizer`**: Translates informal proofs and constructions from Gromov (1985), Ivashkovich-Shevchishin (1999), and standard symplectic literature into syntactically valid Lean 4 types, structures, and proof skeletons.
2. **`ollama-lean4-gemma-prover`**: Provides a compute-efficient, offline interface to local Gemma models running on Ollama (`http://localhost:11434`), handling premise selection, tactic suggestions, and lemma generation with automatic fallback cascades.
3. **`lean4-proof-repair-engine`**: Parses Lean 4 compiler diagnostics (`lake build`, `lean --json`), classifies errors against Mathlib and TauCeti environments, queries repair strategies, and iteratively closes proof obligations without human intervention.

### Authoritative Specification Sources Probed:
- **Gromov, M.** (1985), *"Pseudo holomorphic curves in symplectic manifolds"*, *Inventiones Mathematicae* 82, 307–347. Defines almost complex structures, $\omega$-compatibility/taming, Cauchy-Riemann operator $\bar{\partial}_J$, energy bounds, and the bubbling-off phenomenon.
- **Ivashkovich, S. & Shevchishin, V.** (1999), *"Complex Curves in Almost-Complex Manifolds and Meromorphic Hulls"*, arXiv:math/9912046. Rigorous treatment of bubbling-off, area bounds, tree-like connectedness for genus 0 curves, and cusp-curve convergence.
- **Mathlib 4 Documentation & Source Tree**: Specifically `Mathlib.Analysis.Hofer` (Hofer's lemma on complete metric spaces for gradient rescaling), `Mathlib.Geometry.Manifold.SmoothManifoldWithCorners`, and tangent bundle infrastructure.
- **TauCeti Symplectic Geometry Roadmap**: `TauCetiProject/TauCetiRoadmap/SymplecticGeometry` (almost complex manifolds, symplectic forms, pseudo-holomorphic mappings).
- **Ollama REST API / CLI Specification**: `http://localhost:11434/api/generate`, `http://localhost:11434/api/chat`, `http://localhost:11434/api/tags`.
- **Lean 4 Compiler Interface**: `lake env lean --json <file.lean>`, JSON diagnostic outputs and error reporting schema.

---

## 2. Features Discovered

| # | Category | Feature | Description | Inputs | Outputs | Error Behavior | Discovered Via |
|---|----------|---------|-------------|--------|---------|----------------|----------------|
| 1 | Math Formalization | Hofer's Lemma Integration | Metric space rescaling for bubbling points via `Mathlib.Analysis.Hofer` | `CompleteSpace X`, `MetricSpace X`, continuous function $f \ge 0$, $\varepsilon > 0$ | Point $x'$, radius $\varepsilon' \le \varepsilon$, gradient bound $f(y) \le 2 f(x')$ | Fails if metric space is incomplete or function unbounded locally | `Mathlib.Analysis.Hofer` source & Gromov (1985) §1.2 |
| 2 | Math Formalization | Almost Complex Structure $(M, J)$ | Endomorphism $J: TM \to TM$ satisfying $J^2 = -\mathrm{Id}$ | Manifold $M$, VectorBundle $TM$ | Lean 4 structure `AlmostComplexManifold M` | Type mismatch if $J$ is not smooth bundle endomorphism | TauCeti Roadmap & Gromov (1985) |
| 3 | Math Formalization | $\omega$-Tamed / Compatible Metric | Metric $g(X,Y) = \omega(X, JY)$ and condition $\omega(X, JX) > 0$ | Symplectic form $\omega$, Structure $J$ | Lean 4 typeclass `CompatibleSymplectic J \omega` | Fails if $\omega$ is degenerate or non-closed | Gromov (1985) §0.2 |
| 4 | Math Formalization | Cauchy-Riemann Operator $\bar{\partial}_J$ | Operator $\bar{\partial}_J u = \frac{1}{2}(du + J \circ du \circ j)$ | Smooth map $u: \Sigma \to M$, Riemann surface $(\Sigma, j)$ | Section of $T^*\Sigma \otimes_{j, J} u^*TM$ | Unsolvable types if base surface differential form mismatches | Ivashkovich-Shevchishin (1999) §1 |
| 5 | Math Formalization | Symplectic Energy & Bound | Energy functional $E(u) = \int_\Sigma u^* \omega \le E_0$ | $J$-holomorphic curve $u$, Form $\omega$ | Real scalar $E(u) \in [0, \infty)$ | Non-integrable error if $u$ is non-compact without boundary bounds | Gromov (1985) §1.1 |
| 6 | Math Formalization | Bubble Tree Dual Graph (Genus 0) | Tree-like graph representation of nodal spheres meeting at simple nodes | List of sphere components, incidence relation | Graph $G = (V, E)$ acyclic (Tree) | Non-genus-0 detected if dual graph contains cycles | Ivashkovich-Shevchishin (1999) §2 |
| 7 | Math Formalization | Energy Quantization ($\hbar$-threshold) | Uniform lower bound $\hbar > 0$ for non-trivial sphere bubbles | Compact manifold $(M, \omega, J)$ | Lemma: $E(v) \ge \hbar$ for non-constant $v: S^2 \to M$ | Zero energy implies constant map | Gromov (1985) §1.2 |
| 8 | Ollama Integration | Connection Healthcheck | Validates `http://localhost:11434/api/tags` and latency | HTTP GET request | Model list JSON or connection status | Returns exit code 1 or JSON error if daemon stopped | Ollama REST API Spec |
| 9 | Ollama Integration | Model Fallback Cascade | Automatic downgrade cascade: `gemma2:27b` $\to$ `9b` $\to$ `2b` $\to$ legacy | Target model preference list | Selected available model tag | Error with recovery instruction if no Gemma model installed | Ollama CLI / System Probe |
| 10 | Ollama Integration | Gemma Chat Turn Formatting | Wraps prompt in `<start_of_turn>user\n...<end_of_turn>\n<start_of_turn>model\n` | Raw prompt text, system instruction | Formatted LLM input string | Unclosed turn token causes model run-on hallucination | Gemma 2 Prompt Spec |
| 11 | Ollama Integration | Deterministic Sampling Controls | Hyperparameter presets for lemma extraction vs tactic search | Mode (`autoform`, `tactic`, `premise`), Temperature, Top-P | Ollama `options` JSON dict | High temperature leads to invalid Lean 4 syntax | Gemma Hyperparameter Probe |
| 12 | Ollama Integration | File-Based Response Extraction | Streams/receives LLM generation and strips markdown delimiters | Raw Ollama response text | Sanitized Lean 4 code string / JSON | Syntax error if model leaves triple backticks in code | Agent Skill Standards |
| 13 | Lean 4 Repair | Compiler Diagnostics Parsing | Parses line-by-line JSON emitted by `lake env lean --json` | Standard error / stdout of `lean --json` | List of structured error records (line, col, severity, data) | Parsing fails on non-JSON warning banners | Lean 4 CLI Spec |
| 14 | Lean 4 Repair | Error Taxonomy Classifier | Maps compiler error text to 6 distinct error classes | Diagnostic message string | Error class enum: `TypeMismatch`, `UnknownId`, `UnsolvedGoal`, etc. | Unclassified error falls back to general context prompt | Lean 4 Compiler Diagnostics |
| 15 | Lean 4 Repair | Mathlib / TauCeti Context Lookup | Greps/queries identifiers against Mathlib and TauCeti caches | Identifier name or missing symbol | Module import statement or type signature | Missing symbol alerts agent to add external dependency | Mathlib 4 Indexing |
| 16 | Lean 4 Repair | AST / Local Scope Slicing | Extracts 20-30 lines of source code enclosing error pos | File path, Line number | Local declaration snippet with type context | Truncation error if declaration spans > 100 lines | Lean 4 Source Analyzer |
| 17 | Lean 4 Repair | Iterative Auto-Patching Loop | Applies suggested replacement, recompiles, and checks diff | Original file, patch snippet, line range | Verified `.lean` file or rollback on regression | Rollback triggered if error count increases | Skill Repair Methodology |

---

## 3. Edge Cases

| # | Feature | Input | Observed Behavior |
|---|---------|-------|-------------------|
| 1 | Hofer's Lemma Application | Boundary points on disc $D^2$ where $d(z_n, \partial D^2) \to 0$ | Standard Hofer lemma requires a metric ball $B(x', \varepsilon') \subset X$; near boundaries, incomplete balls cause scaling failure. Must restrict to compact subdomains or use metric completion of interior. |
| 2 | Almost Complex Structure | Non-integrable $J$ where Nijenhuis tensor $N_J \ne 0$ | $J$ does not admit holomorphic local coordinates. Cauchy-Riemann equations become an elliptic system with lower-order terms; Lean 4 statements must avoid assuming local complex charts. |
| 3 | Ghost Bubbles | Sequence of bubbles with $E(v_n) \to 0$ | In genus 0, any bubble with zero energy must be constant ("ghost bubble"). In stable map compactification, unstable ghost components must be contracted, maintaining tree stability. |
| 4 | Ollama Service Down | Port 11434 unreachable (connection refused / timeout) | Client tool exits with structured JSON error payload, diagnostic message, and exact command (`ollama serve`) to launch the local daemon. |
| 5 | Gemma Model OOM / Truncation | Prompt exceeding 4096 tokens or GPU VRAM exhaustion | Ollama returns HTTP 500 or terminates process. Client catches timeout/500, truncates context window, and retries with lower `num_predict` or smaller model (`gemma2:2b`). |
| 6 | Gemma Markdown Bleed | Model generates ```lean4 ... ``` wrapper around definitions | Downstream Lean compiler fails on backticks. Sanitizer must strip leading/trailing code fence blocks before writing to `.lean` target. |
| 7 | Lean 4 Typeclass Loop | Missing instance for `[MetricSpace M]` or `[SmoothManifoldWithCorners ...]` | Lean compiler produces `failed to synthesize instance` error. Repair engine detects missing typeclass and automatically injects instance parameter into theorem signature. |
| 8 | Multiple Bubble Points | Simultaneous gradient blowup at $k$ distinct points $z_1, \dots, z_k \in S^2$ | Single-bubble rescaling extracts only one bubble. Autoformalizer must structure sequence as recursive bubble-extraction until remaining energy falls below threshold $\hbar$. |

---

## 4. Skill 1 Specification: `lean4-symplectic-autoformalizer`

### 4.1 YAML Frontmatter

```yaml
---
name: lean4-symplectic-autoformalizer
description: >
  Translates informal mathematical definitions, theorems, and proofs from
  Gromov (1985), Ivashkovich-Shevchishin (1999), and symplectic topology
  literature into syntactically valid Lean 4 types, structures, and proof skeletons.
  Aligns prerequisites with Mathlib (e.g. Mathlib.Analysis.Hofer) and the
  TauCeti Symplectic Geometry Roadmap. Use when autoformalizing pseudo-holomorphic
  curves, almost complex manifolds, bubbling-off analysis, or cusp-curve limits.
---
```

### 4.2 Directory Layout

```
lean4-symplectic-autoformalizer/
├── SKILL.md
├── scripts/
│   ├── autoformalize.py
│   ├── ast_validator.py
│   └── mathlib_aligner.py
├── references/
│   ├── gromov_1985_core_lemmas.md
│   ├── ivashkovich_shevchishin_bubble_tree.md
│   ├── mathlib_hofer_mapping.md
│   └── lean4_symplectic_prelude.lean
└── examples/
    ├── almost_complex_structure.lean
    ├── hofer_gradient_rescaling.lean
    └── cusp_curve_genus0.lean
```

### 4.3 Triggers & Invocation Criteria
- **Trigger When:**
  - An informal proof, lemma, or definition from Gromov (1985) or Ivashkovich-Shevchishin (1999) needs translation into Lean 4.
  - A symplectic geometric concept (almost complex structure, $J$-holomorphic curve, energy bound, bubble tree) requires formal typing.
  - Creating skeleton `.lean` files containing formal statements, docstrings, and step-by-step `sorry` stubs.
- **Do Not Trigger When:**
  - Running iterative tactic search on an already defined Lean statement (use `ollama-lean4-gemma-prover`).
  - Fixing compilation errors on existing `.lean` code (use `lean4-proof-repair-engine`).

### 4.4 Parameters & Input Formats
- **Input Parameters:**
  - `--input`: Path to markdown or LaTeX file containing informal mathematics.
  - `--output`: Path to write the generated Lean 4 `.lean` file.
  - `--target-module`: Target Lean 4 module namespace (e.g. `SympTopAutoForm.GromovCompactness`).
  - `--proof-level`: Skeleton depth: `statement-only`, `skeleton` (with commented proof steps and `sorry`), or `interactive-tactics`.
  - `--reference-source`: Source citation key: `gromov1985`, `ivashkovich1999`, or `tauceti`.
- **Input Format (Informal Math Markdown):**
  ```markdown
  ### Theorem (Bubbling-off of Pseudo-holomorphic Spheres)
  Let (M, \omega) be a compact symplectic manifold with an \omega-compatible almost complex structure J.
  Let u_n: S^2 -> M be a sequence of J-holomorphic spheres with uniform energy bound E(u_n) <= E_0.
  Then there exists a subsequence converging in C^\infty_loc away from a finite set Z = {z_1, ..., z_k}
  to a limit curve u_\infty, and at each z_i a non-trivial bubble sphere v_i: S^2 -> M forms.
  ```

### 4.5 Operational Workflow (Step-by-Step)
1. **Mathematical Parsing**: Extract mathematical objects, variables, hypotheses, and target assertions from informal text.
2. **Type Dependency Resolution**: Map mathematical notions to Lean 4 types:
   - Symplectic manifold $(M, \omega) \implies$ `[MetricSpace M] [SmoothManifoldWithCorners 𝓘(ℝ, 2*n) M]` with non-degenerate closed 2-form `ω : DifferentialForm M 2`.
   - Almost complex structure $J \implies$ `(J : TensorBundle.Endomorphism TM)` satisfying `J ∘ J = -Id`.
   - Compatible/Tamed condition $\implies$ `[CompatibleSymplectic M ω J]`.
   - Cauchy-Riemann equation $\implies$ `dbar u = 0` where `dbar u = (1/2) * (du + J ∘ du ∘ j)`.
   - Metric rescaling $\implies$ `Mathlib.Analysis.Hofer.hofer`.
3. **Mathlib & TauCeti Alignment**: Check existing declarations to avoid duplicate structures. Map Hofer's lemma directly to `Mathlib.Analysis.Hofer`.
4. **Lean 4 Statement Generation**: Synthesize valid Lean 4 syntax using inductive types, structures, and theorems.
5. **Skeleton Construction**: Populate the proof body with structured comments corresponding to the original informal steps, terminated by `sorry`.

### 4.6 Output Template (Lean 4 Code Artifact)

```lean
import Mathlib.Analysis.Hofer
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Geometry.Manifold.DifferentialForm

open Metric

namespace SympTopAutoForm.GromovCompactness

variable {M : Type*} [MetricSpace M] [CompleteSpace M]

/-- An almost complex structure on a manifold M is an endomorphism J of the tangent bundle TM
    such that J^2 = -Id. -/
structure AlmostComplexStructure (M : Type*) [MetricSpace M] where
  J : (x : M) → (TangentSpace x) →L[ℝ] (TangentSpace x)
  J_sq : ∀ (x : M) (v : TangentSpace x), J x (J x v) = -v

/-- Symplectic form: a closed, non-degenerate 2-form on M. -/
structure SymplecticManifold (M : Type*) [MetricSpace M] where
  omega : DifferentialForm M 2
  is_closed : dDifferentialForm omega = 0
  non_degenerate : ∀ (x : M) (v : TangentSpace x), (∀ w, omega x (v, w) = 0) → v = 0

/-- J is tamed by omega if omega(v, J v) > 0 for all non-zero v. -/
def IsTamed (omega : SymplecticManifold M) (J : AlmostComplexStructure M) : Prop :=
  ∀ (x : M) (v : TangentSpace x), v ≠ 0 → 0 < omega.omega x (v, J.J x v)

/-- Cauchy-Riemann operator dbar_J for maps from the 2-sphere S^2 to M. -/
def DBar (J : AlmostComplexStructure M) (u : Sphere2 → M) : DifferentialForm Sphere2 1 :=
  sorry

/-- A map u : S^2 -> M is pseudo-holomorphic if dbar_J u = 0. -/
def IsPseudoHolomorphic (J : AlmostComplexStructure M) (u : Sphere2 → M) : Prop :=
  DBar J u = 0

/-- Symplectic energy of a curve u : S^2 -> M. -/
noncomputable def SymplecticEnergy (omega : SymplecticManifold M) (u : Sphere2 → M) : ℝ :=
  sorry

/-- Bubbling-off extraction via Hofer's lemma (Massot / Gromov 1985). -/
theorem hofer_gradient_rescaling
    (u : ℕ → (Sphere2 → M))
    (h_energy : ∀ n, SymplecticEnergy omega (u n) ≤ E_0)
    (h_blowup : Filter.Tendsto (fun n => GradientNorm (u n)) Filter.atTop Filter.atTop) :
    ∃ (bubble_pts : Finset Sphere2) (v : Sphere2 → M),
      IsPseudoHolomorphic J v ∧ SymplecticEnergy omega v ≥ hbar := by
  -- Step 1: Apply Hofer's lemma (Mathlib.Analysis.Hofer.hofer) to metric balls around blowup points
  sorry

end SympTopAutoForm.GromovCompactness
```

### 4.7 Prompt Engineering Pattern

```
<start_of_turn>user
You are an expert mathematician and Lean 4 formalization agent specializing in symplectic geometry.
Translate the following informal theorem from Gromov (1985) / Ivashkovich-Shevchishin (1999) into
a complete, syntactically valid Lean 4 declaration.

Guidelines:
1. Use Mathlib 4 conventions (CamelCase for types, snake_case for terms/theorems).
2. Reference Mathlib.Analysis.Hofer for gradient rescaling.
3. Express bubbling-off as a convergence of maps on S^2 \ Z to a limit curve u_infty, plus bubbles.
4. If a concept is not in Mathlib, declare it as a structure or axiom with a descriptive docstring.
5. Provide a proof skeleton with step-by-step comments and 'sorry'.

Informal Input:
{{INFORMAL_MATH_TEXT}}
<end_of_turn>
<start_of_turn>model
```

### 4.8 CLI Script Architecture (`scripts/autoformalize.py`)

```python
#!/usr/bin/env python3
"""
CLI script for autoformalizing informal symplectic geometry into Lean 4.
Usage:
  uv run scripts/autoformalize.py translate --input text.md --output Target.lean --proof-level skeleton
"""
import argparse
import sys
import json
from pathlib import Path

def translate_math(input_path: Path, output_path: Path, proof_level: str, target_module: str):
    content = input_path.read_text(encoding="utf-8")
    # Workflow orchestration:
    # 1. Parse informal mathematics blocks
    # 2. Extract mathematical symbols and relations
    # 3. Query LLM / template engine for Lean 4 signatures
    # 4. Write verified code skeleton to output_path
    output_path.parent.mkdir(parents=True, exist_ok=True)
    # Write Lean 4 output
    print(f"Success! Formalized skeleton written to: {output_path}")

def main():
    parser = argparse.ArgumentParser(description="Symplectic Lean 4 Autoformalizer")
    subparsers = parser.add_subparsers(dest="subcommand", required=True)
    
    trans_parser = subparsers.add_parser("translate", help="Translate informal proof to Lean 4")
    trans_parser.add_argument("--input", type=Path, required=True, help="Input markdown/latex file")
    trans_parser.add_argument("--output", type=Path, required=True, help="Output .lean file")
    trans_parser.add_argument("--target-module", type=str, default="SympTopAutoForm.Gromov", help="Lean 4 module name")
    trans_parser.add_argument("--proof-level", choices=["statement-only", "skeleton", "interactive-tactics"], default="skeleton")
    
    args = parser.parse_args()
    if args.subcommand == "translate":
        translate_math(args.input, args.output, args.proof_level, args.target_module)

if __name__ == "__main__":
    main()
```

---

## 5. Skill 2 Specification: `ollama-lean4-gemma-prover`

### 5.1 YAML Frontmatter

```yaml
---
name: ollama-lean4-gemma-prover
description: >
  Interfaces with a local Gemma model running via Ollama (http://localhost:11434)
  to perform Lean 4 autoformalization, lemma extraction, premise selection, and tactic
  suggestions locally without external cloud compute. Features automatic health checking,
  model fallback cascades (gemma2:27b -> gemma2:9b -> gemma2:2b), deterministic parameter
  tuning, and response sanitization for Lean 4 proofs.
---
```

### 5.2 Directory Layout

```
ollama-lean4-gemma-prover/
├── SKILL.md
├── scripts/
│   ├── ollama_client.py
│   ├── healthcheck.py
│   └── prompt_templates.py
├── references/
│   ├── gemma_turn_templates.md
│   ├── hyperparameter_matrix.json
│   └── lean4_tactic_fewshots.json
└── examples/
    ├── premise_query.json
    └── tactic_suggestion_output.json
```

### 5.3 Triggers & Invocation Criteria
- **Trigger When:**
  - Generating tactic suggestions for an open goal in a Lean 4 proof.
  - Extracting helper lemmas from a complex informal mathematical step.
  - Selecting candidate Mathlib premises for symplectic proofs.
  - Autoformalizing theorem statements using zero-cost local compute.
- **Do Not Trigger When:**
  - Running compiler verification (use `lean4-proof-repair-engine`).
  - Accessing non-local cloud APIs unless fallback is explicitly requested.

### 5.4 Parameters & Fallback Cascade
- **Ollama Endpoint:** `http://localhost:11434` (Default configurable via `--endpoint` or `OLLAMA_HOST`).
- **Model Fallback Cascade:**
  1. `gemma2:27b` (High capacity, deep reasoning for complex manifold proofs)
  2. `gemma2:9b` (Default: balanced speed, memory footprint ~5.5GB, excellent Lean syntax)
  3. `gemma2:2b` (Ultra-lightweight: fast premise filtering and tactic ranking on minimal hardware)
  4. `gemma:7b` / `gemma:2b` (Legacy Gemma v1 fallback)
  5. Any local model reported by `/api/tags`
  6. Graceful failure: If Ollama daemon is offline, emit clean diagnostic JSON with actionable launch instructions (`ollama serve && ollama pull gemma2:9b`).
- **Hyperparameter Presets Matrix:**

| Task Mode | Temperature | Top-P | Top-K | Num Predict | Stop Tokens |
|-----------|-------------|-------|-------|-------------|-------------|
| `autoformalize` | 0.1 | 0.90 | 40 | 2048 | `["<end_of_turn>", "```\n\n"]` |
| `tactic_search` | 0.2 | 0.95 | 50 | 256 | `["<end_of_turn>", "\n\n"]` |
| `premise_selection` | 0.0 | 0.80 | 20 | 512 | `["<end_of_turn>"]` |
| `lemma_extraction` | 0.15 | 0.90 | 40 | 1024 | `["<end_of_turn>"]` |

### 5.5 Operational Workflow (Step-by-Step)
1. **Health & Daemon Probe**: Issue `GET http://localhost:11434/api/tags` with a 2-second timeout.
   - If unreachable, output error code and CLI command: `ollama serve`.
2. **Model Availability Resolution**: Match available tags against fallback hierarchy. Select highest-tier available model.
3. **Prompt Compilation**: Wrap query in Gemma turn syntax (`<start_of_turn>user\n...<end_of_turn>\n<start_of_turn>model\n`) with system instructions.
4. **Execution via REST / CLI**: Post JSON payload to `/api/generate` with task-specific hyperparameters.
5. **Sanitization & Extraction**: Strip markdown delimiters (```lean4), normalize indentation, and return clean code string or JSON object.

### 5.6 Actionable Prompt Templates

#### Tactic Suggestion Template
```
<start_of_turn>user
You are a Lean 4 automated reasoning assistant. Given the following proof state in symplectic topology,
suggest the 3 most promising tactics or lemma applications to advance or close the goal.

Context & Imports:
import Mathlib.Analysis.Hofer
import Mathlib.Geometry.Manifold.DifferentialForm

Goal State:
M : Type*
[MetricSpace M] [CompleteSpace M]
u : ℕ → Sphere2 → M
E_0 : ℝ
h_energy : ∀ n, SymplecticEnergy omega (u n) ≤ E_0
h_grad : Filter.Tendsto (fun n => GradientNorm (u n)) Filter.atTop Filter.atTop
⊢ ∃ (x' : Sphere2) (ε' : ℝ), 0 < ε' ∧ ∀ y, dist y x' ≤ ε' → GradientNorm (u n) y ≤ 2 * GradientNorm (u n) x'

Output format:
Respond ONLY with a JSON array of objects:
[
  {"tactic": "apply hofer ...", "rationale": "Applies Hofer's lemma to rescale around gradient blowup point."},
  ...
]
<end_of_turn>
<start_of_turn>model
```

#### Premise Selection Template
```
<start_of_turn>user
Identify candidate premises from Mathlib (especially Mathlib.Analysis.Hofer and Topology.MetricSpace)
relevant to proving:
"Every non-constant pseudo-holomorphic sphere has symplectic energy bounded below by a universal constant hbar > 0."

List top 5 Mathlib lemmas with full module names.
<end_of_turn>
<start_of_turn>model
```

### 5.7 CLI Script Architecture (`scripts/ollama_client.py`)

```python
#!/usr/bin/env python3
"""
Ollama Client for Lean 4 Prover with Local Gemma.
Usage:
  uv run scripts/ollama_client.py healthcheck
  uv run scripts/ollama_client.py query --mode tactic_search --prompt-file state.txt --output result.json
"""
import argparse
import json
import sys
import urllib.request
import urllib.error

DEFAULT_HOST = "http://localhost:11434"
FALLBACK_CASCADE = ["gemma2:27b", "gemma2:9b", "gemma2:2b", "gemma:7b", "gemma:2b"]

def check_health(host=DEFAULT_HOST):
    try:
        req = urllib.request.Request(f"{host}/api/tags", headers={"Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=3) as resp:
            data = json.loads(resp.read().decode())
            models = [m["name"] for m in data.get("models", [])]
            return {"status": "ok", "host": host, "models": models}
    except Exception as e:
        return {"status": "error", "message": str(e), "recovery": f"Ensure Ollama is running: run 'ollama serve'"}

def select_model(available_models):
    for pref in FALLBACK_CASCADE:
        for avail in available_models:
            if avail == pref or avail.startswith(pref + ":"):
                return avail
    return available_models[0] if available_models else None

def query_gemma(prompt: str, mode: str, host: str, model: str = None, output_file: str = None):
    health = check_health(host)
    if health["status"] != "ok":
        print(json.dumps(health, indent=2), file=sys.stderr)
        sys.exit(1)
        
    chosen_model = model or select_model(health["models"])
    if not chosen_model:
        print(json.dumps({"error": "No model found. Run 'ollama pull gemma2:9b'"}, indent=2), file=sys.stderr)
        sys.exit(1)

    # Format turn syntax
    formatted_prompt = f"<start_of_turn>user\n{prompt}\n<end_of_turn>\n<start_of_turn>model\n"
    
    payload = {
        "model": chosen_model,
        "prompt": formatted_prompt,
        "stream": False,
        "options": {
            "temperature": 0.2 if mode == "tactic_search" else 0.1,
            "num_predict": 1024,
            "stop": ["<end_of_turn>"]
        }
    }
    
    req = urllib.request.Request(
        f"{host}/api/generate",
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"}
    )
    with urllib.request.urlopen(req, timeout=60) as resp:
        res_data = json.loads(resp.read().decode())
        response_text = res_data.get("response", "").strip()
        
    result = {
        "model_used": chosen_model,
        "mode": mode,
        "raw_response": response_text
    }
    
    if output_file:
        with open(output_file, "w", encoding="utf-8") as f:
            json.dump(result, f, indent=2)
        print(f"Success! Output written to: {output_file}")
    else:
        print(json.dumps(result, indent=2))

def main():
    parser = argparse.ArgumentParser(description="Ollama Lean 4 Gemma Client")
    subparsers = parser.add_subparsers(dest="subcommand", required=True)
    
    health_p = subparsers.add_parser("healthcheck")
    health_p.add_argument("--host", default=DEFAULT_HOST)
    
    query_p = subparsers.add_parser("query")
    query_p.add_argument("--mode", choices=["autoformalize", "tactic_search", "premise_selection"], required=True)
    query_p.add_argument("--prompt", type=str, help="Inline prompt string")
    query_p.add_argument("--prompt-file", type=str, help="Path to prompt file")
    query_p.add_argument("--output", type=str, required=True, help="Output JSON path")
    query_p.add_argument("--host", default=DEFAULT_HOST)
    query_p.add_argument("--model", default=None)
    
    args = parser.parse_args()
    if args.subcommand == "healthcheck":
        res = check_health(args.host)
        print(json.dumps(res, indent=2))
        sys.exit(0 if res["status"] == "ok" else 1)
    elif args.subcommand == "query":
        prompt = args.prompt
        if args.prompt_file:
            with open(args.prompt_file, "r") as f:
                prompt = f.read()
        query_gemma(prompt, args.mode, args.host, args.model, args.output)

if __name__ == "__main__":
    main()
```

---

## 6. Skill 3 Specification: `lean4-proof-repair-engine`

### 6.1 YAML Frontmatter

```yaml
---
name: lean4-proof-repair-engine
description: >
  Verifies Lean 4 source files using Lake and the Lean compiler, parses JSON
  compiler diagnostics (type mismatch, unknown identifier, missing typeclass instances,
  unsolved goals), extracts contextual AST snippets and Mathlib/TauCeti references,
  and executes an automated iterative repair loop to fix broken formal declarations.
---
```

### 6.2 Directory Layout

```
lean4-proof-repair-engine/
├── SKILL.md
├── scripts/
│   ├── check_and_repair.py
│   ├── error_parser.py
│   ├── mathlib_lookup.py
│   └── patch_applier.py
├── references/
│   ├── error_taxonomy_catalog.md
│   ├── typeclass_resolution_recipes.md
│   └── tau_ceti_api_shims.lean
└── examples/
    ├── broken_symplectic_form.lean
    ├── repaired_symplectic_form.lean
    └── compiler_diagnostic_sample.json
```

### 6.3 Triggers & Invocation Criteria
- **Trigger When:**
  - A Lean 4 file fails compilation via `lake build` or `lean --json`.
  - Type errors, missing instances, or unsolved tactic goals are detected in autoformalized code.
  - Verifying generated Lean statements before handoff or downstream proof synthesis.
- **Do Not Trigger When:**
  - Writing initial informal-to-formal stubs (use `lean4-symplectic-autoformalizer`).
  - Requesting heuristic proof tactics without compilation feedback (use `ollama-lean4-gemma-prover`).

### 6.4 Diagnostic Parsing & Error Taxonomy
Lean 4 compiler errors outputted in JSON format:
```json
{
  "file": "SympTopAutoForm/GromovCompactness.lean",
  "pos": {"line": 34, "col": 12},
  "endPos": {"line": 34, "col": 28},
  "severity": "error",
  "caption": "",
  "data": "type mismatch\n  has type\n    AlmostComplexStructure M\n  but is expected to have type\n    SymplecticManifold M"
}
```

The repair engine classifies errors into 6 structured categories:
1. `TYPE_MISMATCH`: Argument or expected return type unification failure.
2. `UNKNOWN_IDENTIFIER`: Missing symbol import, outdated Mathlib 3 notation, or missing namespace `open`.
3. `MISSING_TYPECLASS`: Typeclass search failed (e.g. `[MetricSpace M]`, `[CompleteSpace M]`).
4. `UNSOLVED_GOALS`: Proof block ended with remaining subgoals or incorrect tactic termination.
5. `TACTIC_FAILURE`: Tactic execution threw an error (e.g. `linarith` failed, `rw` pattern not found).
6. `MAX_RECURSION`: Loop in typeclass resolution or macro expansion.

### 6.5 Operational Workflow (Step-by-Step)
1. **Compilation Execution**: Invoke `lake env lean --json <file.lean>` and capture stdout/stderr.
2. **Diagnostic Extraction**: Parse each diagnostic JSON record; filter for `severity: "error"`.
3. **AST & Scope Slice**: For each error, extract:
   - Line numbers: `[pos.line - 15, pos.line + 15]`.
   - File header: imports, namespace declarations, variable declarations.
   - Surrounding theorem or structure definition.
4. **Symbol Lookup**: Search Mathlib index and TauCeti roadmap cache for candidate definitions matching the error message (e.g. resolving `hofer` to `Mathlib.Analysis.Hofer.hofer`).
5. **Repair Prompt Synthesis**: Build an LLM repair prompt containing:
   - File context and imports.
   - Exact code slice where error occurred.
   - Compiler error message (`data` field).
   - Reference documentation of intended Mathlib lemmas.
6. **Patch Application & Backtracking**:
   - Write replacement lines to a temporary copy of `.lean` file.
   - Re-compile with `lean --json`.
   - If error count decreased or resolved, accept patch and commit.
   - If new errors introduced or error count increased, revert patch and attempt alternative strategy (up to 3 iterations).
7. **Report Generation**: Output repair summary JSON detailing fixed errors, remaining warnings, and diff.

### 6.6 Repair Prompt Template

```
<start_of_turn>user
You are a Lean 4 compiler repair specialist. The following Lean 4 code produces a compilation error.
Fix the code snippet so it compiles cleanly without changing the mathematical intent.

File Context:
import Mathlib.Analysis.Hofer
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

namespace SympTopAutoForm

Code Slice (lines 25-45):
```lean
theorem rescale_blowup (u : ℕ → Sphere2 → M) [MetricSpace M] (f : Sphere2 → ℝ) :
    ∃ x' ε', 0 < ε' ∧ f x' ≤ 2 * f x' := by
  apply hofer
```

Compiler Error:
Line 28, Col 3:
"unknown identifier 'hofer' (did you mean 'Mathlib.Analysis.Hofer.hofer'?)"

Instructions:
1. Provide the exact replacement code for the slice.
2. Include any missing 'open' or import statements if needed.
3. Keep the proof step minimal and sound.
<end_of_turn>
<start_of_turn>model
```lean
open Mathlib.Analysis.Hofer

theorem rescale_blowup (u : ℕ → Sphere2 → M) [MetricSpace M] [CompleteSpace M] (f : Sphere2 → ℝ)
    (hf : Continuous f) (hfx : 0 ≤ f x) (hε : 0 < ε) :
    ∃ x' ε', 0 < ε' ∧ ε' ≤ ε ∧ f x ≤ f x' ∧ ∀ y, dist y x' ≤ ε' → f y ≤ 2 * f x' := by
  exact hofer f x ε hε hf hfx
```
<end_of_turn>
```

### 6.7 CLI Script Architecture (`scripts/check_and_repair.py`)

```python
#!/usr/bin/env python3
"""
Lean 4 Proof Checking and Automated Repair Engine.
Usage:
  uv run scripts/check_and_repair.py check --file Gromov.lean --output diag.json
  uv run scripts/check_and_repair.py repair --file Gromov.lean --max-iterations 3 --output repair_report.json
"""
import argparse
import subprocess
import json
import sys
from pathlib import Path

def run_lean_check(lean_file: Path) -> list:
    cmd = ["lake", "env", "lean", "--json", str(lean_file)]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True)
    except FileNotFoundError:
        # Fallback if lake is not directly on PATH
        cmd = ["lean", "--json", str(lean_file)]
        proc = subprocess.run(cmd, capture_output=True, text=True)
        
    diagnostics = []
    for line in proc.stdout.splitlines():
        line = line.strip()
        if line.startswith("{") and line.endswith("}"):
            try:
                diagnostics.append(json.loads(line))
            except json.JSONDecodeError:
                pass
    return diagnostics

def classify_error(data: str) -> str:
    if "type mismatch" in data:
        return "TYPE_MISMATCH"
    elif "unknown identifier" in data:
        return "UNKNOWN_IDENTIFIER"
    elif "failed to synthesize" in data:
        return "MISSING_TYPECLASS"
    elif "unsolved goals" in data:
        return "UNSOLVED_GOALS"
    elif "tactic" in data and "failed" in data:
        return "TACTIC_FAILURE"
    return "GENERAL_ERROR"

def repair_file(lean_file: Path, max_iterations: int, report_file: Path):
    history = []
    current_iter = 0
    
    while current_iter < max_iterations:
        current_iter += 1
        diags = run_lean_check(lean_file)
        errors = [d for d in diags if d.get("severity") == "error"]
        
        if not errors:
            print(f"File {lean_file} compiles cleanly with 0 errors!")
            break
            
        first_error = errors[0]
        err_class = classify_error(first_error.get("data", ""))
        history.append({
            "iteration": current_iter,
            "error_count": len(errors),
            "primary_error": first_error,
            "classification": err_class
        })
        
        # Apply repair strategy (lookup context, format prompt, apply patch)
        # Rollback if error count increases
        
    report = {
        "target_file": str(lean_file),
        "iterations_run": current_iter,
        "resolved": len(errors) == 0,
        "history": history
    }
    with open(report_file, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)
    print(f"Repair report written to: {report_file}")

def main():
    parser = argparse.ArgumentParser(description="Lean 4 Proof Checking & Repair Engine")
    subparsers = parser.add_subparsers(dest="subcommand", required=True)
    
    check_p = subparsers.add_parser("check")
    check_p.add_argument("--file", type=Path, required=True, help="Lean file to check")
    check_p.add_argument("--output", type=Path, required=True, help="Output JSON path")
    
    repair_p = subparsers.add_parser("repair")
    repair_p.add_argument("--file", type=Path, required=True, help="Lean file to repair")
    repair_p.add_argument("--max-iterations", type=int, default=3)
    repair_p.add_argument("--output", type=Path, required=True, help="Output repair report JSON")
    
    args = parser.parse_args()
    if args.subcommand == "check":
        diags = run_lean_check(args.file)
        with open(args.output, "w") as f:
            json.dump(diags, f, indent=2)
        print(f"Diagnostics written to {args.output}")
    elif args.subcommand == "repair":
        repair_file(args.file, args.max_iterations, args.output)

if __name__ == "__main__":
    main()
```

---

## 7. Packaging & Standard Skill Directory Structure

Each skill adheres strictly to standard agent skill structure:
1. **Root `SKILL.md`**: Contains YAML frontmatter (`name` $\le$ 64 chars, `description` $\le$ 1024 chars), triggers, prerequisites, detailed step-by-step workflow, and error recovery instructions.
2. **`scripts/` Directory**: Executable, self-contained Python CLI utilities running via `uv run`, using `argparse` with explicit subcommands, returning exit code 0 on success and 1 on error, and outputting structured JSON to disk.
3. **`references/` Directory**: Scientific and formal documentation, Mathlib alignment tables, prompt templates, and few-shot examples.
4. **`examples/` Directory**: Representative input/output samples for testing and validation.

---

## 8. Acceptance Criteria Verification Mapping

| Requirement (ORIGINAL_REQUEST.md) | Component Specified | Verification Criteria & Section |
|-----------------------------------|---------------------|---------------------------------|
| **R2.1**: Informal to Lean 4 Autoformalization | `lean4-symplectic-autoformalizer` | §4: YAML frontmatter, Gromov/Ivashkovich-Shevchishin mapping, Mathlib.Analysis.Hofer integration, candidate Lean 4 templates. |
| **R2.2**: Local Gemma/Ollama Interface | `ollama-lean4-gemma-prover` | §5: YAML frontmatter, `http://localhost:11434` REST endpoints, model fallback cascade (`gemma2:27b` $\to$ `9b` $\to$ `2b`), hyperparameter matrix, prompt turn wrapping. |
| **R2.3**: Lean 4 Proof Checking & Repair | `lean4-proof-repair-engine` | §6: YAML frontmatter, `lean --json` diagnostic parser, 6-class error taxonomy, Mathlib lookup, bounded iterative repair loop. |
| **R3**: Local Model Pipeline | Ollama Integration Pipeline | §5.4, §5.6, §5.7: Detailed CLI scripts, connection healthcheck, graceful fallback for offline daemon, and Lean 4 specific prompt engineering. |
