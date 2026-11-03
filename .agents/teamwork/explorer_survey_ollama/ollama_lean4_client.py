#!/usr/bin/env python3
"""
ollama_lean4_client.py — Standalone Zero-Dependency Ollama/Gemma Client for Lean 4
Designed for autoformalization, tactic suggestion, and premise selection workflows.
Compatible with Python 3.6+ without external pip dependencies.
"""

import sys
import json
import argparse
import time
import urllib.request
import urllib.error
import re
from typing import Dict, List, Optional, Tuple, Any

DEFAULT_OLLAMA_HOST = "http://localhost:11434"

# Fallback cascade priority for mathematical theorem proving in Lean 4
MODEL_PRIORITY_CASCADE = [
    "gemma2:9b",       # Primary: high reasoning, manageable 8k context, ~6GB VRAM
    "gemma2:27b",      # High tier: deep mathematical reasoning, ~18GB VRAM
    "codegemma:7b",    # Code-specialized Gemma 1 variant
    "gemma:7b",        # Base Gemma 1 7B
    "gemma2:2b",       # Lightweight Gemma 2 for resource-constrained laptops
    "codegemma:2b",    # Lightweight CodeGemma
    "gemma:2b",        # Base Gemma 1 2B
]

# Task-specific parameter profiles for Ollama generation
TASK_PARAMETER_PROFILES = {
    "autoformalize": {
        "temperature": 0.1,
        "top_p": 0.90,
        "top_k": 40,
        "num_predict": 512,
        "num_ctx": 8192,
        "repeat_penalty": 1.1,
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
        "repeat_penalty": 1.1,
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


def check_connection(base_url: str = DEFAULT_OLLAMA_HOST, timeout: float = 3.0) -> Tuple[bool, str, Dict[str, Any]]:
    """
    Validates connectivity to Ollama service.
    Returns: (is_connected, message, metadata)
    """
    tags_url = f"{base_url.rstrip('/')}/api/tags"
    req = urllib.request.Request(tags_url, headers={"User-Agent": "Lean4AutoForm-GemmaClient/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as response:
            if response.status == 200:
                body = response.read().decode("utf-8")
                data = json.loads(body)
                return True, "Connected successfully to Ollama", data
            else:
                return False, f"HTTP error {response.status} from Ollama tags endpoint", {}
    except urllib.error.URLError as e:
        return False, f"Connection failed to {base_url}: {e.reason}", {}
    except Exception as e:
        return False, f"Unexpected error connecting to {base_url}: {str(e)}", {}


def detect_best_model(base_url: str = DEFAULT_OLLAMA_HOST,
                      preferred_tag: Optional[str] = None,
                      tags_data: Optional[Dict[str, Any]] = None,
                      timeout: float = 3.0) -> Tuple[Optional[str], str, List[str]]:
    """
    Discovers available models and selects the optimal Gemma model via fallback cascade.
    Returns: (selected_model, reason, available_models)
    """
    if tags_data is None:
        ok, msg, data = check_connection(base_url, timeout=timeout)
        if not ok:
            return None, f"Cannot detect models: {msg}", []
        tags_data = data

    models = [m.get("name", "") for m in tags_data.get("models", [])]
    if not models:
        return None, "No models found in local Ollama instance", []

    # 1. Check preferred tag if explicitly supplied
    if preferred_tag:
        matched = [m for m in models if m == preferred_tag or m.startswith(f"{preferred_tag}:") or preferred_tag.startswith(m)]
        if matched:
            return matched[0], f"Matched explicitly requested model: {matched[0]}", models

    # 2. Check fallback priority cascade
    for candidate in MODEL_PRIORITY_CASCADE:
        matched = [m for m in models if m == candidate or m.startswith(f"{candidate}:") or candidate.startswith(m)]
        if matched:
            return matched[0], f"Selected optimal priority model: {matched[0]}", models

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

    # Initial turn: embed system instructions inside the first user turn (standard for Gemma)
    first_user_content = f"{system_instructions.strip()}\n\n{few_shot_turns[0][0]}" if few_shot_turns else f"{system_instructions.strip()}\n\n{user_prompt.strip()}"

    formatted += f"<start_of_turn>user\n{first_user_content}<end_of_turn>\n"

    if few_shot_turns:
        # Add model response for first few-shot
        formatted += f"<start_of_turn>model\n{few_shot_turns[0][1]}<end_of_turn>\n"

        # Subsequent few-shot turns
        for u, m in few_shot_turns[1:]:
            formatted += f"<start_of_turn>user\n{u.strip()}<end_of_turn>\n"
            formatted += f"<start_of_turn>model\n{m.strip()}<end_of_turn>\n"

        # Final query user turn
        formatted += f"<start_of_turn>user\n{user_prompt.strip()}<end_of_turn>\n"

    # Prompt ending for model completion
    formatted += "<start_of_turn>model\n"
    return formatted


def extract_lean_code(raw_text: str) -> str:
    """
    Extracts Lean 4 code from markdown blocks or cleans raw generated response.
    """
    code_blocks = re.findall(r"```(?:lean4|lean)?\s*(.*?)\s*```", raw_text, re.DOTALL | re.IGNORECASE)
    if code_blocks:
        return code_blocks[0].strip()
    return raw_text.strip()


def query_ollama(base_url: str,
                 model: str,
                 prompt: str,
                 task_type: str = "autoformalize",
                 options_override: Optional[Dict[str, Any]] = None,
                 timeout: float = 60.0,
                 dry_run: bool = False) -> Dict[str, Any]:
    """
    Dispatches generation request to Ollama /api/generate endpoint.
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
        return {
            "status": "mock",
            "model": model,
            "task_type": task_type,
            "payload_preview": payload,
            "response": "-- [MOCK DRY RUN RESPONSE]\n-- Lean 4 code generation placeholder\ntheorem mock_theorem : True := by\n  trivial\n"
        }

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
            "error": str(e)
        }


def run_self_test() -> int:
    """
    Executes an internal validation test suite for offline verification.
    """
    print("============================================================")
    print("RUNNING OLLAMA / GEMMA LEAN 4 CLIENT SELF-TEST SUITE")
    print("============================================================")
    failures = 0

    # Test 1: Fallback cascade ranking with simulated model list
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
        print(f"  PASS: Correctly selected high-priority '{best}' ({reason})")
    else:
        print(f"  FAIL: Expected 'gemma2:9b', got '{best}'")
        failures += 1

    # Test 2: Fallback when primary model is missing
    print("\n[Test 2] Testing fallback when gemma2:9b is absent...")
    mock_tags_small = {
        "models": [
            {"name": "qwen2.5-coder:7b"},
            {"name": "gemma:2b"},
        ]
    }
    best_small, reason_small, _ = detect_best_model(tags_data=mock_tags_small)
    if best_small == "gemma:2b":
        print(f"  PASS: Correctly fell back to '{best_small}' ({reason_small})")
    else:
        print(f"  FAIL: Expected 'gemma:2b', got '{best_small}'")
        failures += 1

    # Test 3: Gemma prompt formatting structure
    print("\n[Test 3] Testing Gemma chat template compliance...")
    system_inst = "You are a Lean 4 formalizer."
    user_p = "Formalize Hofer's lemma."
    few_shot = [
        ("Informal: If x > 0 and y > 0 then x + y > 0.",
         "```lean4\ntheorem add_pos (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 < x + y := add_pos hx hy\n```")
    ]
    prompt = format_gemma_prompt(system_inst, user_p, few_shot)
    if "<start_of_turn>user" in prompt and "<end_of_turn>" in prompt and "<start_of_turn>model\n" in prompt:
        print("  PASS: Control tokens (<start_of_turn>, <end_of_turn>) formatted properly")
    else:
        print("  FAIL: Control tokens missing or malformed")
        failures += 1

    # Test 4: Lean code extraction from markdown blocks
    print("\n[Test 4] Testing Lean code block extraction...")
    markdown_sample = "Here is the formalization:\n```lean4\ntheorem test_thm : 1 + 1 = 2 := rfl\n```\nHope this helps!"
    code = extract_lean_code(markdown_sample)
    if code == "theorem test_thm : 1 + 1 = 2 := rfl":
        print(f"  PASS: Successfully extracted code block: '{code}'")
    else:
        print(f"  FAIL: Extracted code mismatch: '{code}'")
        failures += 1

    # Test 5: Dry-run query execution
    print("\n[Test 5] Testing dry-run query execution...")
    res = query_ollama("http://localhost:11434", "gemma2:9b", prompt, task_type="autoformalize", dry_run=True)
    if res["status"] == "mock" and "mock_theorem" in res["response"]:
        print("  PASS: Dry-run payload and mock response verified")
    else:
        print(f"  FAIL: Dry run failed: {res}")
        failures += 1

    # Test 6: Parameter profiles verification
    print("\n[Test 6] Verifying parameter profiles for formal math tasks...")
    auto_params = TASK_PARAMETER_PROFILES["autoformalize"]
    tactic_params = TASK_PARAMETER_PROFILES["tactic"]
    premise_params = TASK_PARAMETER_PROFILES["premise"]
    assert auto_params["temperature"] == 0.1, "Autoformalize temperature should be near-deterministic"
    assert auto_params["num_ctx"] == 8192, "Autoformalize context window should be 8192"
    assert tactic_params["temperature"] == 0.4, "Tactic search temperature should be moderately explorative"
    assert premise_params["temperature"] == 0.0, "Premise selection temperature should be greedy"
    print("  PASS: All task parameter profiles verified")

    print("\n============================================================")
    if failures == 0:
        print("ALL 6 TESTS PASSED SUCCESSFULLY (100% PASS RATE)")
        print("============================================================")
        return 0
    else:
        print(f"TESTS COMPLETED WITH {failures} FAILURES")
        print("============================================================")
        return 1


def main():
    parser = argparse.ArgumentParser(description="Ollama / Gemma Client for Lean 4 Autoformalization")
    parser.add_argument("--host", default=DEFAULT_OLLAMA_HOST, help="Ollama host URL (default: http://localhost:11434)")
    parser.add_argument("--model", default=None, help="Specific model tag to use (default: auto-detect via fallback)")
    parser.add_argument("--task", choices=["autoformalize", "tactic", "proof_skeleton", "premise"], default="autoformalize")
    parser.add_argument("--prompt", help="User prompt to submit")
    parser.add_argument("--dry-run", action="store_true", help="Perform offline dry-run test without network call")
    parser.add_argument("--check", action="store_true", help="Check connection and list discovered models")
    parser.add_argument("--test", action="store_true", help="Run comprehensive internal unit test suite")

    args = parser.parse_args()

    if args.test:
        sys.exit(run_self_test())

    if args.check:
        print(f"Checking connection to Ollama at {args.host}...")
        ok, msg, data = check_connection(args.host)
        if not ok:
            print(f"[ERROR] {msg}")
            sys.exit(1)
        print(f"[SUCCESS] {msg}")
        best, reason, models = detect_best_model(args.host, preferred_tag=args.model, tags_data=data)
        print(f"Discovered {len(models)} model(s): {', '.join(models)}")
        print(f"Recommended Model: {best} ({reason})")
        sys.exit(0)

    if not args.prompt and not args.dry_run:
        print("Error: --prompt is required unless running with --check, --test, or --dry-run")
        sys.exit(1)

    prompt = args.prompt or "Formalize: If X is a compact metric space, then every sequence has a convergent subsequence."
    model = args.model
    if not model and not args.dry_run:
        model, reason, _ = detect_best_model(args.host, preferred_tag=args.model)
        if not model:
            print(f"[ERROR] Could not detect any suitable model: {reason}")
            sys.exit(1)
    else:
        model = model or "gemma2:9b"

    print(f"Dispatching query using model '{model}' (Task: {args.task})...")
    gemma_prompt = format_gemma_prompt("You are an expert Lean 4 mathematician.", prompt)
    res = query_ollama(args.host, model, gemma_prompt, task_type=args.task, dry_run=args.dry_run)
    print(json.dumps(res, indent=2))


if __name__ == "__main__":
    main()
