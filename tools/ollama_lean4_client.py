#!/usr/bin/env python3
"""
ollama_lean4_client.py — Zero-External-Dependency Ollama/Gemma Client for Lean 4

Production-grade client for local Gemma inference via Ollama (http://localhost:11434).
Designed specifically for Lean 4 autoformalization, tactic suggestion, premise selection,
and proof skeleton synthesis for Gromov compactness in symplectic geometry.

Features:
- Zero external dependencies (uses standard library: urllib, json, argparse, re, time).
- Dual endpoint connection checks: /api/tags and /api/generate.
- 7-tier model fallback cascade:
  gemma2:9b -> gemma2:27b -> codegemma:7b -> gemma:7b -> gemma2:2b -> codegemma:2b -> gemma:2b -> local fallback -> dry-run mock.
- Official Gemma chat turn formatting (<start_of_turn>, <end_of_turn>).
- Domain-specific prompt templates with few-shot Lean 4 symplectic geometry pairs.
- CLI subcommands: health, list-models, query, autoformalize, suggest-tactic, test.
- Fully compatible with Python 3.6+.
"""

import sys
import os
import io

def ensure_utf8_streams():
    """Ensure stdout and stderr use UTF-8 encoding idempotently on Python 3.6."""
    if getattr(sys, "_utf8_configured", False):
        return
    sys._utf8_configured = True
    if hasattr(sys.stdout, "buffer") and (not sys.stdout.encoding or sys.stdout.encoding.lower() != "utf-8"):
        try:
            sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8", errors="replace")
        except Exception:
            pass
    if hasattr(sys.stderr, "buffer") and (not sys.stderr.encoding or sys.stderr.encoding.lower() != "utf-8"):
        try:
            sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding="utf-8", errors="replace")
        except Exception:
            pass

ensure_utf8_streams()

import json
import argparse
import time
import urllib.request
import urllib.error
import re
import subprocess
import shutil
from typing import Dict, List, Optional, Tuple, Any

DEFAULT_OLLAMA_HOST = "http://localhost:11434"

# Model fallback cascade for mathematical formalization (local fine-tuned/quantized first)
MODEL_PRIORITY_CASCADE = [
    "gemma-lean4:latest",        # Tier 0: Domain-customized Lean 4 Gemma model (~6.6GB VRAM)
    "gemma-lean4",               # Tier 0 alias
    "gemma2:9b-instruct-q5_K_M", # Tier 0.5: Local quantized instruct Gemma 2 (~6.6GB VRAM)
    "gemma2:9b",                 # Tier 1: Primary target, SOTA 10B math/dependent type reasoning (~6.5GB VRAM)
    "gemma2:27b",                # Tier 2: High-compute tier, deep mathematical reasoning (~17.5GB VRAM)
    "codegemma:7b",              # Tier 3: Code-specialized Gemma 1 checkpoint (~5.8GB VRAM)
    "gemma:7b",                  # Tier 4: Base Gemma 1 7B (~5.2GB VRAM)
    "gemma2:2b",                 # Tier 5: Lightweight Gemma 2 for resource-constrained hardware (~2.2GB VRAM)
    "codegemma:2b",              # Tier 6: Lightweight CodeGemma 2B (~2.0GB VRAM)
    "gemma:2b",                  # Tier 7: Base Gemma 1 2B (~1.8GB VRAM)
]

# Tuned task-specific generation parameters for Lean 4 proving
TASK_PARAMETER_PROFILES = {
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


def find_config_file() -> Optional[str]:
    """Locate configuration file from standard locations."""
    candidates = [
        os.path.join(os.path.dirname(__file__), "..", "config", "ollama_gemma_config.json"),
        os.path.join(os.getcwd(), "config", "ollama_gemma_config.json"),
        os.path.expanduser("~/.config/ollama_gemma_config.json")
    ]
    for c in candidates:
        if os.path.isfile(c):
            return os.path.abspath(c)
    return None


def load_config(config_path: Optional[str] = None) -> Dict[str, Any]:
    """
    Loads JSON configuration if available, falling back to internal defaults.
    """
    path = config_path or find_config_file()
    if path and os.path.isfile(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            pass
    return {
        "service": {
            "default_host": DEFAULT_OLLAMA_HOST,
            "endpoints": {
                "tags": "/api/tags",
                "generate": "/api/generate",
                "chat": "/api/chat",
                "show": "/api/show",
                "version": "/api/version"
            },
            "connect_timeout_seconds": 3.0,
            "request_timeout_seconds": 60.0
        },
        "model_fallback_cascade": MODEL_PRIORITY_CASCADE,
        "parameter_profiles": TASK_PARAMETER_PROFILES
    }


def find_ollama_binary() -> Optional[str]:
    """Locate the ollama binary executable across system, App bundle, and user paths."""
    candidates = [
        shutil.which("ollama"),
        "/usr/local/bin/ollama",
        "/opt/homebrew/bin/ollama",
        "/Applications/Ollama.app/Contents/Resources/ollama",
        os.path.expanduser("~/bin/ollama"),
        os.path.expanduser("~/.local/bin/ollama"),
    ]
    for c in candidates:
        if c and os.path.isfile(c) and os.access(c, os.X_OK):
            return os.path.abspath(c)
    return None


def is_ollama_running(base_url: str = DEFAULT_OLLAMA_HOST, timeout: float = 2.0) -> bool:
    """Fast check whether Ollama server is active and responding at base_url."""
    tags_url = f"{base_url.rstrip('/')}/api/tags"
    req = urllib.request.Request(tags_url, headers={"User-Agent": "Lean4AutoForm-GemmaClient/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as response:
            return response.status == 200
    except Exception:
        return False


def ensure_ollama_daemon(base_url: str = DEFAULT_OLLAMA_HOST,
                         autostart: bool = True,
                         timeout: float = 12.0) -> Tuple[bool, str, Optional[int]]:
    """
    Ensures that an Ollama daemon is running and responding at base_url.
    If not running and autostart=True, launches a headless `ollama serve` background daemon.
    Returns: (is_healthy, status_message, pid_or_none)
    """
    if is_ollama_running(base_url, timeout=2.0):
        return True, f"Ollama daemon is active and responding at {base_url}", None

    if not autostart:
        return False, f"Ollama daemon is not responding at {base_url} (autostart disabled)", None

    ollama_bin = find_ollama_binary()
    if not ollama_bin:
        return False, "Ollama executable not found in PATH or standard installation locations", None

    try:
        proc = subprocess.Popen(
            [ollama_bin, "serve"],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            start_new_session=True,
            close_fds=True,
        )
        pid = proc.pid
    except Exception as e:
        return False, f"Failed to spawn headless ollama serve process: {e}", None

    start_time = time.time()
    while time.time() - start_time < timeout:
        time.sleep(0.5)
        if is_ollama_running(base_url, timeout=1.0):
            return True, f"Successfully started headless Ollama daemon (PID {pid}) at {base_url}", pid

    return False, f"Spawned Ollama daemon (PID {pid}), but failed to respond at {base_url} within {timeout}s", pid


def check_connection(base_url: str = DEFAULT_OLLAMA_HOST,
                     timeout: float = 3.0,
                     autostart: bool = True) -> Tuple[bool, str, Dict[str, Any]]:
    """
    Validates connectivity to Ollama /api/tags endpoint.
    If unreachable and autostart is True, attempts to start headless daemon automatically.
    Returns: (is_connected, message, metadata)
    """
    tags_url = f"{base_url.rstrip('/')}/api/tags"
    req = urllib.request.Request(tags_url, headers={"User-Agent": "Lean4AutoForm-GemmaClient/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as response:
            if response.status == 200:
                body = response.read().decode("utf-8")
                data = json.loads(body)
                return True, "Successfully connected to Ollama /api/tags", data
            else:
                return False, f"HTTP error {response.status} from Ollama tags endpoint", {}
    except (urllib.error.URLError, ConnectionError, OSError) as e:
        if autostart:
            started, start_msg, _ = ensure_ollama_daemon(base_url, autostart=True, timeout=8.0)
            if started:
                try:
                    with urllib.request.urlopen(req, timeout=timeout) as response:
                        if response.status == 200:
                            body = response.read().decode("utf-8")
                            data = json.loads(body)
                            return True, f"Connected to Ollama /api/tags ({start_msg})", data
                except Exception:
                    pass
        reason_str = getattr(e, "reason", str(e))
        hint = "\nHint: Ensure the Ollama daemon is running with 'ollama serve'."
        return False, f"Connection failed to {base_url}: {reason_str}.{hint}", {}
    except Exception as e:
        return False, f"Unexpected error connecting to {base_url}: {str(e)}", {}


def check_generate_endpoint(base_url: str = DEFAULT_OLLAMA_HOST, timeout: float = 3.0) -> Tuple[bool, str]:
    """
    Validates availability of Ollama /api/generate endpoint using an empty or minimal probe.
    Returns: (is_available, message)
    """
    gen_url = f"{base_url.rstrip('/')}/api/generate"
    # Sending empty body or invalid model to check HTTP response (Ollama returns 400 or 404 for missing fields, not 502/refused)
    probe_payload = json.dumps({"model": "__probe_check__"}).encode("utf-8")
    req = urllib.request.Request(
        gen_url,
        data=probe_payload,
        headers={"Content-Type": "application/json", "User-Agent": "Lean4AutoForm-GemmaClient/1.0"}
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as response:
            return True, f"Generate endpoint responded with HTTP {response.status}"
    except urllib.error.HTTPError as e:
        # 400 or 404 means the endpoint exists and is processing JSON requests
        if e.code in (400, 404):
            return True, f"Generate endpoint active (HTTP {e.code} received for probe request)"
        return False, f"Generate endpoint returned HTTP error {e.code}"
    except urllib.error.URLError as e:
        return False, f"Generate endpoint unreachable: {e.reason}"
    except Exception as e:
        return False, f"Generate endpoint error: {str(e)}"


def detect_best_model(base_url: str = DEFAULT_OLLAMA_HOST,
                      preferred_tag: Optional[str] = None,
                      tags_data: Optional[Dict[str, Any]] = None,
                      timeout: float = 3.0) -> Tuple[Optional[str], str, List[str]]:
    """
    Discovers available models and selects the optimal Gemma model via the 7-tier fallback cascade.
    Returns: (selected_model, reason, available_models)
    """
    if tags_data is None:
        ok, msg, data = check_connection(base_url, timeout=timeout)
        if not ok:
            return None, f"Cannot detect models: {msg}", []
        tags_data = data

    models = [m.get("name", "") for m in tags_data.get("models", [])]
    if not models:
        return None, "No models found in local Ollama repository. Run 'ollama pull gemma2:9b'.", []

    # 1. User specified preferred tag takes highest precedence
    if preferred_tag:
        matched = [m for m in models if m == preferred_tag or m.startswith(f"{preferred_tag}:") or preferred_tag.startswith(m)]
        if matched:
            return matched[0], f"Matched explicitly requested model: {matched[0]}", models

    # 2. Check 7-tier fallback priority cascade
    for candidate in MODEL_PRIORITY_CASCADE:
        matched = [m for m in models if m == candidate or m.startswith(f"{candidate}:") or candidate.startswith(m)]
        if matched:
            return matched[0], f"Selected optimal cascade model: {matched[0]}", models

    # 3. Check for any model containing 'gemma'
    gemma_models = [m for m in models if "gemma" in m.lower()]
    if gemma_models:
        return gemma_models[0], f"Selected available Gemma model: {gemma_models[0]}", models

    # 4. Fallback to any local model
    return models[0], f"No Gemma model found; falling back to first available model: {models[0]}", models


def format_gemma_prompt(system_instructions: str,
                        user_prompt: str,
                        few_shot_turns: Optional[List[Tuple[str, str]]] = None) -> str:
    """
    Formats the conversation prompt using Google Gemma's official control tokens:
    <start_of_turn>user
    {system_and_user_text}<end_of_turn>
    <start_of_turn>model
    {response}<end_of_turn>
    """
    formatted = ""

    # Initial turn: embed system instructions inside the first user turn (standard for Gemma instruct)
    if few_shot_turns:
        first_user_content = f"{system_instructions.strip()}\n\n{few_shot_turns[0][0].strip()}"
        formatted += f"<start_of_turn>user\n{first_user_content}<end_of_turn>\n"
        formatted += f"<start_of_turn>model\n{few_shot_turns[0][1].strip()}<end_of_turn>\n"

        for u, m in few_shot_turns[1:]:
            formatted += f"<start_of_turn>user\n{u.strip()}<end_of_turn>\n"
            formatted += f"<start_of_turn>model\n{m.strip()}<end_of_turn>\n"

        formatted += f"<start_of_turn>user\n{user_prompt.strip()}<end_of_turn>\n"
    else:
        full_content = f"{system_instructions.strip()}\n\n{user_prompt.strip()}"
        formatted += f"<start_of_turn>user\n{full_content}<end_of_turn>\n"

    formatted += "<start_of_turn>model\n"
    return formatted


def build_autoformalize_prompt(informal_text: str, custom_system: Optional[str] = None) -> str:
    """Constructs prompt for translating informal symplectic math into Lean 4."""
    system_inst = custom_system or (
        "You are an expert mathematician and Lean 4 formalizer specializing in symplectic geometry, "
        "almost complex manifolds, and Mathlib.\n"
        "Your task is to translate informal mathematical definitions, lemmas, and theorems into syntactically valid Lean 4 code.\n\n"
        "Guidelines:\n"
        "1. Use standard Mathlib naming conventions (snake_case for terms/theorems, UpperCamelCase for types).\n"
        "2. Explicitly specify all typeclass arguments (e.g. [MetricSpace M], [SmoothManifoldWithCorners I M]).\n"
        "3. For theorems whose proofs are not requested, terminate with ':= by sorry'.\n"
        "4. Output Lean 4 code enclosed in a ```lean4 ... ``` block."
    )
    few_shot = [
        (
            "Informal:\n\"Definition: An almost complex structure J on a smooth manifold M is a smooth bundle endomorphism J of the tangent bundle TM such that J^2 = -Id. J is said to be tame with respect to a symplectic 2-form omega if omega(v, J v) > 0 for all non-zero tangent vectors v.\"",
            "```lean4\nimport Mathlib.Geometry.Manifold.SmoothManifoldWithCorners\nimport Mathlib.Analysis.Calculus.FDeriv.Basic\n\nvariable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]\nvariable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)\nvariable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]\n\n/-- An almost complex structure on a smooth manifold is a fiberwise endomorphism of TM whose square is -Id. -/\nstructure AlmostComplexStructure where\n  J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x\n  J_sq : ∀ (x : M) (v : TangentSpace I x), J x (J x v) = -v\n  smooth_J : ContMDiff I (I.prod I) ⊤ (fun (p : TangentBundle I M) => (p.1, J p.1 p.2))\n\n/-- An almost complex structure J is tame with respect to a 2-form ω if ω(v, J v) > 0 for all non-zero tangent vectors. -/\ndef IsTame (J : AlmostComplexStructure I M) (ω : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) : Prop :=\n  ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < ω x v (J.J x v)\n```"
        )
    ]
    query = f"Informal:\n\"{informal_text.strip()}\""
    return format_gemma_prompt(system_inst, query, few_shot)


def build_tactic_prompt(goal_state: str, compiler_error: str, failed_tactic: Optional[str] = None) -> str:
    """Constructs prompt for suggesting a repair tactic given compiler error."""
    system_inst = (
        "You are an interactive Lean 4 tactic reasoning engine. Given a current proof state, the target goal, "
        "and the compiler diagnostic or error generated by the previous tactic attempt, your task is to propose the next correct Lean 4 tactic.\n\n"
        "Guidelines:\n"
        "1. Provide a single, minimal tactic or a short tactic sequence ('by ...').\n"
        "2. Do not hallucinate premises: prioritize standard Mathlib tactics (apply, exact, intro, cases, obtain, linarith, simp, positivity).\n"
        "3. Briefly explain the mathematical rationale in a one-line comment."
    )
    few_shot = [
        (
            "Context and Goal State:\n```lean4\nM : Type*\n[MetricSpace M] [CompleteSpace M]\nf : M → ℝ\nhf_cont : Continuous f\nhf_nonneg : ∀ x, 0 ≤ f x\nx0 : M\nε0 : ℝ\nhε0 : 0 < ε0\n⊢ ∃ x : M, ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε0 ∧ f x * ε ≥ f x0 * ε0 ∧ ∀ y ∈ Metric.closedBall x ε, f y ≤ 2 * f x\n```\n\nFailed Tactic Attempt:\n`exact Hofer.hofer hf_cont x0 hε0`\n\nCompiler Error:\n```\ntype mismatch:\n  Hofer.hofer hf_cont x0 hε0\nhas type:\n  0 < ε0 → ∃ x ε, 0 < ε ∧ ε ≤ ε0 ∧ ...\nbut is expected to have type:\n  ∃ x ε, 0 < ε ∧ ε ≤ ε0 ∧ ...\n```",
            "```lean4\n-- Hofer's lemma in Mathlib takes hε0 as an explicit argument after the continuity hypothesis\nexact Hofer.hofer hf_cont x0 hε0\n```"
        )
    ]
    failed_part = f"\n\nFailed Tactic Attempt:\n`{failed_tactic}`" if failed_tactic else ""
    query = f"Context and Goal State:\n```lean4\n{goal_state.strip()}\n```{failed_part}\n\nCompiler Error:\n```\n{compiler_error.strip()}\n```"
    return format_gemma_prompt(system_inst, query, few_shot)


def build_premise_prompt(goal_and_context: str) -> str:
    """Constructs prompt for retrieving relevant Mathlib premises."""
    system_inst = (
        "You are an expert Mathlib search assistant for Lean 4.\n"
        "Given the current goal and available hypotheses, identify the top 5 most relevant Mathlib lemmas, definitions, or typeclass instances needed to advance the proof.\n\n"
        "Output Format:\n"
        "1. `Exact.Mathlib.Name` — brief 1-line explanation of applicability\n"
        "2. `Exact.Mathlib.Name` — brief 1-line explanation of applicability\n"
        "3. ..."
    )
    few_shot = [
        (
            "Goal:\n```lean4\nM : Type*\n[MetricSpace M]\nx y z : M\nr : ℝ\nh1 : dist x y < r / 2\nh2 : dist y z < r / 2\n⊢ dist x z < r\n```",
            "Selected Premises:\n1. `dist_triangle` — Triangle inequality dist x z ≤ dist x y + dist y z\n2. `lt_of_le_of_lt` — Transitivity to chain weak and strict inequalities\n3. `add_lt_add` — Strict addition of inequalities a < b → c < d → a + c < b + d\n4. `add_halves` — Simplification lemma r / 2 + r / 2 = r\n5. `dist_comm` — Symmetry of metric distance dist x y = dist y x"
        )
    ]
    query = f"Goal and Context:\n```lean4\n{goal_and_context.strip()}\n```"
    return format_gemma_prompt(system_inst, query, few_shot)


def extract_lean_code(raw_text: str) -> str:
    """Extracts Lean 4 code from markdown blocks or cleans raw generated response."""
    code_blocks = re.findall(r"```(?:lean4|lean)?\s*(.*?)\s*```", raw_text, re.DOTALL | re.IGNORECASE)
    if code_blocks:
        return code_blocks[0].strip()
    return raw_text.strip()


def generate_mock_response(task_type: str, prompt: str, model: str) -> str:
    """
    Generates realistic, syntactically correct mock responses for offline/dry-run execution.
    Maintains real mathematical state corresponding to Gromov compactness formalization.
    """
    if task_type == "autoformalize":
        if "hofer" in prompt.lower():
            return (
                "```lean4\n"
                "/-- Hofer's lemma on complete metric spaces (Massot 2020 / Mathlib.Analysis.Hofer). -/\n"
                "theorem hofer_lemma {X : Type*} [MetricSpace X] [CompleteSpace X]\n"
                "    (f : X → ℝ) (hf : Continuous f) (x₀ : X) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :\n"
                "    ∃ (x : X) (ε : ℝ), 0 < ε ∧ ε ≤ ε₀ ∧ f x₀ * ε₀ ≤ f x * ε ∧\n"
                "      ∀ y ∈ Metric.closedBall x ε, f y ≤ 2 * f x := by\n"
                "  exact Mathlib.Analysis.Hofer.hofer hf x₀ hε₀\n"
                "```"
            )
        elif "energy" in prompt.lower() or "quantization" in prompt.lower():
            return (
                "```lean4\n"
                "/-- Minimal energy gap (ħ > 0) for non-constant pseudo-holomorphic spheres (Gromov 1985). -/\n"
                "theorem energy_quantization_sphere (M : Type*) [MetricSpace M] (J : AlmostComplexStructure M)\n"
                "    (ω : SymplecticForm M) (h_tame : IsTame J ω) :\n"
                "    ∃ (ħ : ℝ), 0 < ħ ∧ ∀ (u : PseudoHolomorphicCurve J Sphere M),\n"
                "      ¬ IsConstant u → ħ ≤ Energy ω u := by\n"
                "  sorry\n"
                "```"
            )
        else:
            return (
                "```lean4\n"
                "/-- Smooth pseudo-holomorphic curve map into an almost complex manifold (M, J). -/\n"
                "structure PseudoHolomorphicMap (Σ : Type*) (M : Type*) [TopologicalSpace Σ] [TopologicalSpace M]\n"
                "    (j : AlmostComplexStructure Σ) (J : AlmostComplexStructure M) where\n"
                "  toFun : Σ → M\n"
                "  d_cauchy_riemann : ∀ (z : Σ) (v : TangentSpace z), d toFun (j z v) = J (toFun z) (d toFun v)\n"
                "```"
            )
    elif task_type == "tactic":
        if "hofer" in prompt.lower():
            return "```lean4\n-- Apply Massot's Hofer lemma formulation with explicit positivity witness\nexact Mathlib.Analysis.Hofer.hofer hf_cont x0 hε0\n```"
        else:
            return "```lean4\n-- Apply continuity and compact exhaustion\nobtain ⟨x, hx⟩ := Metric.isCompact_closedBall.exists_isMaxOn h_nonempty\nexact hx\n```"
    elif task_type == "premise":
        return (
            "Selected Premises:\n"
            "1. `Mathlib.Analysis.Hofer.hofer` — Massot's Hofer lemma for continuous functions on complete metric spaces\n"
            "2. `Metric.closedBall` — Definition and properties of closed metric balls in Lean 4\n"
            "3. `Continuous.continuousOn` — Restriction of continuity to closed subsets\n"
            "4. `isCompact_closedBall` — Compactness of closed balls in proper metric spaces\n"
            "5. `dist_le_of_mem_closedBall` — Pointwise distance bounds in closed balls"
        )
    elif task_type == "proof_skeleton":
        return (
            "```lean4\n"
            "-- Bubbling-off decomposition for genus 0 pseudo-holomorphic curves\n"
            "lemma gradient_blowup_point (u_seq : ℕ → D → M) (h_energy : ∀ n, Energy (u_seq n) ≤ E₀) :\n"
            "    ∃ (x_seq : ℕ → D) (R_seq : ℕ → ℝ), GradientBlowup x_seq R_seq := sorry\n\n"
            "lemma dilated_sequence_c1_bound (v_seq : ℕ → ℂ → M) : UniformC1Bound v_seq := sorry\n\n"
            "lemma elliptic_bootstrap_convergence (v_seq : ℕ → ℂ → M) : ∃ v_lim, ClocConvergence v_seq v_lim := sorry\n\n"
            "lemma removable_singularity_at_infinity (v_lim : ℂ → M) : ExtendsToSphere v_lim := sorry\n"
            "```"
        )
    return "-- Default Lean 4 mock response\ntheorem mock_goal_proven : True := trivial\n"


def query_ollama(base_url: str,
                 model: str,
                 prompt: str,
                 task_type: str = "autoformalize",
                 options_override: Optional[Dict[str, Any]] = None,
                 timeout: float = 60.0,
                 dry_run: bool = False) -> Dict[str, Any]:
    """
    Dispatches generation request to Ollama /api/generate endpoint.
    Handles network timeouts, parsing, and offline dry-run simulation.
    """
    options = TASK_PARAMETER_PROFILES.get(task_type, TASK_PARAMETER_PROFILES["autoformalize"]).copy()
    if options_override:
        options.update(options_override)

    payload = {
        "model": model,
        "prompt": prompt,
        "stream": False,
        "options": options
    }

    if dry_run:
        mock_text = generate_mock_response(task_type, prompt, model)
        return {
            "status": "mock",
            "model": model,
            "task_type": task_type,
            "elapsed_sec": 0.001,
            "payload_preview": payload,
            "raw_response": mock_text,
            "lean_code": extract_lean_code(mock_text)
        }

    if not is_ollama_running(base_url, timeout=1.5):
        ensure_ollama_daemon(base_url, autostart=True, timeout=10.0)

    generate_url = f"{base_url.rstrip('/')}/api/generate"
    data_bytes = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(
        generate_url,
        data=data_bytes,
        headers={"Content-Type": "application/json", "User-Agent": "Lean4AutoForm-GemmaClient/1.0"}
    )

    t0 = time.time()
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            resp_body = resp.read().decode("utf-8")
            resp_json = json.loads(resp_body)
            elapsed = time.time() - t0
            raw_text = resp_json.get("response", "")
            return {
                "status": "success",
                "model": model,
                "task_type": task_type,
                "elapsed_sec": round(elapsed, 3),
                "raw_response": raw_text,
                "lean_code": extract_lean_code(raw_text),
                "total_duration": resp_json.get("total_duration"),
                "eval_count": resp_json.get("eval_count"),
                "eval_duration": resp_json.get("eval_duration")
            }
    except Exception as e:
        return {
            "status": "error",
            "model": model,
            "task_type": task_type,
            "error": str(e),
            "hint": "Ensure Ollama is running ('ollama serve') and model is pulled ('ollama pull " + model + "'). Or pass --dry-run for offline testing."
        }


def run_self_test() -> int:
    """
    Executes an internal validation test suite for offline verification.
    Tests fallback logic, Gemma turn tokens, Lean code extractor, dry-run responses,
    and parameter profiles.
    """
    print("============================================================")
    print("RUNNING OLLAMA / GEMMA LEAN 4 CLIENT SELF-TEST SUITE")
    print("============================================================")
    failures = 0

    # Test 1: Priority cascade selection
    print("\n[Test 1] Testing fallback priority cascade algorithm...")
    mock_tags = {
        "models": [
            {"name": "mistral:7b"},
            {"name": "llama3.1:8b"},
            {"name": "gemma2:2b"},
            {"name": "gemma2:9b"},
        ]
    }
    best, reason, _ = detect_best_model(tags_data=mock_tags)
    if best == "gemma2:9b":
        print(f"  PASS: Correctly selected primary tier '{best}' ({reason})")
    else:
        print(f"  FAIL: Expected 'gemma2:9b', got '{best}'")
        failures += 1

    # Test 1a: Fine-tuned gemma-lean4 top priority
    print("\n[Test 1a] Testing fine-tuned gemma-lean4 top priority...")
    mock_tags_lean4 = {
        "models": [
            {"name": "gemma2:9b"},
            {"name": "gemma-lean4:latest"},
        ]
    }
    best_lean4, reason_lean4, _ = detect_best_model(tags_data=mock_tags_lean4)
    if best_lean4 == "gemma-lean4:latest":
        print(f"  PASS: Correctly selected domain model '{best_lean4}' ({reason_lean4})")
    else:
        print(f"  FAIL: Expected 'gemma-lean4:latest', got '{best_lean4}'")
        failures += 1

    # Test 2: Cascade fallback when primary is missing
    print("\n[Test 2] Testing fallback cascade when gemma2:9b is absent...")
    mock_tags_fallback = {
        "models": [
            {"name": "qwen2.5-coder:7b"},
            {"name": "gemma:2b"},
        ]
    }
    best_fb, reason_fb, _ = detect_best_model(tags_data=mock_tags_fallback)
    if best_fb == "gemma:2b":
        print(f"  PASS: Correctly fell back to '{best_fb}' ({reason_fb})")
    else:
        print(f"  FAIL: Expected 'gemma:2b', got '{best_fb}'")
        failures += 1

    # Test 3: Explicit preferred tag matching
    print("\n[Test 3] Testing explicit user model override...")
    best_exp, _, _ = detect_best_model(preferred_tag="gemma2:2b", tags_data=mock_tags)
    if best_exp == "gemma2:2b":
        print(f"  PASS: Correctly respected explicit user tag '{best_exp}'")
    else:
        print(f"  FAIL: Expected 'gemma2:2b', got '{best_exp}'")
        failures += 1

    # Test 4: Gemma prompt formatting structure (<start_of_turn>, <end_of_turn>)
    print("\n[Test 4] Testing Gemma turn tokens formatting compliance...")
    p = build_autoformalize_prompt("Let (M, J) be an almost complex manifold.")
    if "<start_of_turn>user" in p and "<end_of_turn>" in p and "<start_of_turn>model\n" in p:
        print("  PASS: Control tokens (<start_of_turn>, <end_of_turn>) properly formatted")
    else:
        print("  FAIL: Turn control tokens missing or malformed")
        failures += 1

    # Test 5: Lean code block extraction
    print("\n[Test 5] Testing Lean code block extraction from markdown...")
    raw_markdown = "Here is the code:\n```lean4\ntheorem hofer_test : True := trivial\n```\nDone."
    code = extract_lean_code(raw_markdown)
    if code == "theorem hofer_test : True := trivial":
        print(f"  PASS: Extracted pure Lean declaration: '{code}'")
    else:
        print(f"  FAIL: Extracted code mismatch: '{code}'")
        failures += 1

    # Test 6: Parameter profiles verification
    print("\n[Test 6] Verifying parameter profiles for formal math tasks...")
    for task in ["autoformalize", "tactic", "proof_skeleton", "premise"]:
        prof = TASK_PARAMETER_PROFILES[task]
        assert prof["num_ctx"] == 8192, f"{task} num_ctx must be 8192"
        assert "stop" in prof and len(prof["stop"]) > 0, f"{task} must define stop tokens"
    assert TASK_PARAMETER_PROFILES["autoformalize"]["temperature"] == 0.1
    assert TASK_PARAMETER_PROFILES["tactic"]["temperature"] == 0.4
    assert TASK_PARAMETER_PROFILES["premise"]["temperature"] == 0.0
    print("  PASS: All 4 parameter profiles match formal specification (8192 context, calibrated temperatures)")

    # Test 7: Dry-run query execution (autoformalize Hofer's lemma)
    print("\n[Test 7] Testing dry-run query execution for Hofer's lemma autoformalization...")
    res = query_ollama("http://localhost:11434", "gemma2:9b", "Hofer's lemma", task_type="autoformalize", dry_run=True)
    if res["status"] == "mock" and "hofer" in res["lean_code"].lower():
        print(f"  PASS: Dry-run generated mock Lean 4 declaration:\n{res['lean_code']}")
    else:
        print(f"  FAIL: Dry-run query failed: {res}")
        failures += 1

    # Test 8: Dry-run tactic suggestion
    print("\n[Test 8] Testing dry-run tactic suggestion...")
    tactic_res = query_ollama("http://localhost:11434", "gemma2:9b", "Hofer's lemma goal", task_type="tactic", dry_run=True)
    if tactic_res["status"] == "mock" and "hofer" in tactic_res["lean_code"].lower():
        print(f"  PASS: Dry-run generated mock tactic:\n{tactic_res['lean_code']}")
    else:
        print(f"  FAIL: Dry-run tactic query failed: {tactic_res}")
        failures += 1

    print("\n============================================================")
    if failures == 0:
        print("ALL 8 SELF-TESTS PASSED SUCCESSFULLY (100% PASS RATE)")
        print("============================================================")
        return 0
    else:
        print(f"SELF-TEST SUITE FAILED WITH {failures} ERRORS")
        print("============================================================")
        return 1


# ==============================================================================
# CLI Subcommand Implementations
# ==============================================================================

def cmd_health(args) -> int:
    """Subcommand: Check Ollama service connectivity and endpoint readiness."""
    print(f"Checking connection to Ollama service at {args.host}...")
    ok_daemon, msg_daemon, _ = ensure_ollama_daemon(args.host, autostart=True, timeout=args.timeout)
    if ok_daemon:
        print(f"[OK]   daemon: {msg_daemon}")
    else:
        print(f"[WARN] daemon: {msg_daemon}")

    ok_tags, msg_tags, tags_data = check_connection(args.host, timeout=args.timeout, autostart=True)
    if not ok_tags:
        print(f"[FAIL] /api/tags: {msg_tags}")
        if args.dry_run:
            print("[INFO] --dry-run active: Mocking healthy offline status")
            return 0
        return 1
    print(f"[OK]   /api/tags: {msg_tags}")

    ok_gen, msg_gen = check_generate_endpoint(args.host, timeout=args.timeout)
    if not ok_gen:
        print(f"[WARN] /api/generate: {msg_gen}")
    else:
        print(f"[OK]   /api/generate: {msg_gen}")

    models = [m.get("name", "") for m in tags_data.get("models", [])]
    print(f"[INFO] Discovered {len(models)} model(s) installed locally.")
    best, reason, _ = detect_best_model(args.host, preferred_tag=args.model, tags_data=tags_data)
    print(f"[INFO] Optimal Gemma Model: {best} ({reason})")
    return 0


def cmd_list_models(args) -> int:
    """Subcommand: List all models currently available in local Ollama daemon."""
    print(f"Querying installed models from {args.host}...")
    ok, msg, data = check_connection(args.host, timeout=args.timeout)
    if not ok:
        print(f"[ERROR] {msg}")
        if args.dry_run:
            print("[INFO] Showing simulated model catalog (--dry-run):")
            for m in MODEL_PRIORITY_CASCADE:
                print(f"  - {m} (simulated)")
            return 0
        return 1

    models = data.get("models", [])
    if not models:
        print("[INFO] No models found in local repository.")
        print("Run 'ollama pull gemma2:9b' to download the recommended model.")
        return 0

    print(f"\nDiscovered {len(models)} installed model(s):")
    for idx, m in enumerate(models, 1):
        name = m.get("name", "unknown")
        size = m.get("size", 0) / (1024 * 1024)
        print(f"  {idx}. {name:<20} ({size:.1f} MB)")

    best, reason, _ = detect_best_model(args.host, preferred_tag=args.model, tags_data=data)
    print(f"\nRecommended Proving Model: {best} ({reason})")
    return 0


def cmd_query(args) -> int:
    """Subcommand: General prompt query with task-specific parameters."""
    is_json = getattr(args, "json", False)
    model = args.model
    if not model and not args.dry_run:
        model, reason, _ = detect_best_model(args.host, preferred_tag=args.model)
        if not model:
            if is_json:
                print(json.dumps({"status": "error", "error": f"No suitable model found: {reason}"}, indent=2))
            else:
                print(f"[ERROR] No suitable model found: {reason}")
            return 1
    else:
        model = model or "gemma2:9b"

    prompt = args.prompt
    if not prompt:
        if is_json:
            print(json.dumps({"status": "error", "error": "Argument --prompt is required for query subcommand."}, indent=2))
        else:
            print("[ERROR] Argument --prompt is required for query subcommand.")
        return 1

    formatted_prompt = format_gemma_prompt("You are an expert Lean 4 mathematician.", prompt)
    if not is_json:
        print(f"Dispatching query to '{model}' (Task: {args.task}, Host: {args.host})...")
    res = query_ollama(args.host, model, formatted_prompt, task_type=args.task, dry_run=args.dry_run)

    if is_json:
        print(json.dumps(res, indent=2))
    else:
        if res.get("status") in ("success", "mock"):
            print("\n" + "=" * 60)
            print("LEAN 4 OUTPUT:")
            print("=" * 60)
            print(res.get("lean_code", ""))
            print("=" * 60)
        else:
            print(f"[ERROR] {res.get('error')}")
            if "hint" in res:
                print(f"[HINT]  {res['hint']}")
            return 1
    return 0


def cmd_autoformalize(args) -> int:
    """Subcommand: Autoformalize informal mathematical statement into Lean 4."""
    is_json = getattr(args, "json", False)
    model = args.model
    if not model and not args.dry_run:
        model, reason, _ = detect_best_model(args.host, preferred_tag=args.model)
        if not model:
            if is_json:
                print(json.dumps({"status": "error", "error": f"No suitable model detected: {reason}"}, indent=2))
            else:
                print(f"[ERROR] No suitable model detected: {reason}")
            return 1
    else:
        model = model or "gemma2:9b"

    statement = args.statement
    if not statement:
        if is_json:
            print(json.dumps({"status": "error", "error": "Informal mathematical statement is required."}, indent=2))
        else:
            print("[ERROR] Informal mathematical statement is required.")
        return 1

    prompt = build_autoformalize_prompt(statement)
    if not is_json:
        print(f"Autoformalizing statement using model '{model}'...")
    res = query_ollama(args.host, model, prompt, task_type="autoformalize", dry_run=args.dry_run)

    if is_json:
        print(json.dumps(res, indent=2))
    else:
        if res.get("status") in ("success", "mock"):
            print("\n" + "=" * 60)
            print("FORMALIZED LEAN 4 DECLARATION:")
            print("=" * 60)
            print(res.get("lean_code", ""))
            print("=" * 60)
        else:
            print(f"[ERROR] {res.get('error')}")
            return 1
    return 0


def cmd_suggest_tactic(args) -> int:
    """Subcommand: Suggest Lean 4 tactic given goal state and compiler error."""
    is_json = getattr(args, "json", False)
    model = args.model
    if not model and not args.dry_run:
        model, reason, _ = detect_best_model(args.host, preferred_tag=args.model)
        if not model:
            if is_json:
                print(json.dumps({"status": "error", "error": f"No suitable model detected: {reason}"}, indent=2))
            else:
                print(f"[ERROR] No suitable model detected: {reason}")
            return 1
    else:
        model = model or "gemma2:9b"

    if not args.goal or not args.error:
        if is_json:
            print(json.dumps({"status": "error", "error": "Both --goal and --error are required for suggest-tactic."}, indent=2))
        else:
            print("[ERROR] Both --goal and --error are required for suggest-tactic.")
        return 1

    prompt = build_tactic_prompt(args.goal, args.error, failed_tactic=args.failed_tactic)
    if not is_json:
        print(f"Generating tactic suggestion using model '{model}'...")
    res = query_ollama(args.host, model, prompt, task_type="tactic", dry_run=args.dry_run)

    if is_json:
        print(json.dumps(res, indent=2))
    else:
        if res.get("status") in ("success", "mock"):
            print("\n" + "=" * 60)
            print("SUGGESTED TACTIC:")
            print("=" * 60)
            print(res.get("lean_code", ""))
            print("=" * 60)
        else:
            print(f"[ERROR] {res.get('error')}")
            return 1
    return 0


def cmd_test(args) -> int:
    """Subcommand: Run internal self-test suite."""
    return run_self_test()


# ==============================================================================
# Main Entry Point with Dual Subcommand / Legacy Flag Dispatch
# ==============================================================================

def main():
    common_parser = argparse.ArgumentParser(add_help=False)
    common_parser.add_argument("--host", default=DEFAULT_OLLAMA_HOST, help="Ollama host URL (default: http://localhost:11434)")
    common_parser.add_argument("--timeout", type=float, default=5.0, help="HTTP request timeout in seconds")
    common_parser.add_argument("--model", default=None, help="Specific model tag (e.g. gemma2:9b)")
    common_parser.add_argument("--dry-run", action="store_true", help="Execute offline dry-run with mock Lean 4 responses")
    common_parser.add_argument("--json", action="store_true", help="Format CLI output as JSON")

    parser = argparse.ArgumentParser(
        parents=[common_parser],
        description="Ollama / Gemma Client for Lean 4 Autoformalization (Gromov Compactness)"
    )

    # Legacy flags for compatibility with scripts and skills
    parser.add_argument("--check", action="store_true", help="Legacy flag: check connection and model discovery")
    parser.add_argument("--test", action="store_true", help="Legacy flag: run internal self-test suite")
    parser.add_argument("--task", choices=["autoformalize", "tactic", "proof_skeleton", "premise"], default="autoformalize")
    parser.add_argument("--prompt", help="Legacy flag: query prompt text")

    # Subparsers for modern CLI subcommands
    subparsers = parser.add_subparsers(dest="subcommand", help="Available subcommands")

    # Subcommand: health
    sub_health = subparsers.add_parser("health", parents=[common_parser], help="Check Ollama service connection and endpoint health")
    sub_health.set_defaults(func=cmd_health)

    # Subcommand: list-models
    sub_list = subparsers.add_parser("list-models", parents=[common_parser], help="List installed Ollama models and optimal Gemma recommendation")
    sub_list.set_defaults(func=cmd_list_models)

    # Subcommand: query
    sub_query = subparsers.add_parser("query", parents=[common_parser], help="Dispatch prompt query to model")
    sub_query.add_argument("--prompt", required=True, help="Prompt text to dispatch")
    sub_query.add_argument("--task", choices=["autoformalize", "tactic", "proof_skeleton", "premise"], default="autoformalize")
    sub_query.set_defaults(func=cmd_query)

    # Subcommand: autoformalize
    sub_auto = subparsers.add_parser("autoformalize", parents=[common_parser], help="Translate informal mathematical statement into Lean 4")
    sub_auto.add_argument("statement", nargs="?", default=None, help="Informal statement string")
    sub_auto.add_argument("--statement", dest="statement_opt", default=None, help="Informal statement string via flag")
    sub_auto.set_defaults(func=lambda args: cmd_autoformalize(setattr(args, "statement", args.statement or args.statement_opt) or args))

    # Subcommand: suggest-tactic
    sub_tactic = subparsers.add_parser("suggest-tactic", parents=[common_parser], help="Propose Lean 4 tactic given goal state and error")
    sub_tactic.add_argument("--goal", required=True, help="Current Lean 4 goal state")
    sub_tactic.add_argument("--error", required=True, help="Lean 4 compiler error message")
    sub_tactic.add_argument("--failed-tactic", default=None, help="Previous failed tactic attempt")
    sub_tactic.set_defaults(func=cmd_suggest_tactic)

    # Subcommand: test
    sub_test = subparsers.add_parser("test", parents=[common_parser], help="Run comprehensive offline self-test suite")
    sub_test.set_defaults(func=cmd_test)

    args = parser.parse_args()

    # Route legacy flags first
    if args.test:
        sys.exit(run_self_test())
    if args.check:
        sys.exit(cmd_health(args))
    if args.prompt and not args.subcommand:
        sys.exit(cmd_query(args))

    # Route subcommands
    if hasattr(args, "func"):
        sys.exit(args.func(args))
    elif args.subcommand is None:
        if args.dry_run:
            args.prompt = "State Hofer's lemma in Lean 4"
            sys.exit(cmd_query(args))
        parser.print_help()
        sys.exit(0)


if __name__ == "__main__":
    main()
