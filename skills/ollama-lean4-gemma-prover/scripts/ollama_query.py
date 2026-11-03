#!/usr/bin/env python3
"""
ollama_query.py - Local Gemma Query and Reasoning Engine for Lean 4.

Interacts with local Gemma models hosted on Ollama (http://localhost:11434).
Supports:
- Connection health checking and model inventory
- Prioritized model fallback cascade
- Gemma 2 canonical turn formatting (<start_of_turn>, <end_of_turn>)
- Task-specific hyperparameter presets (autoformalize, tactic, premise, proof_skeleton)
- Response sanitization (stripping markdown fences)
- Offline mock mode for deterministic CI/CD and tests
"""

import argparse
import json
import os
import re
import sys
import time
import io
import urllib.error
import urllib.request
from pathlib import Path


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

DEFAULT_HOST = os.environ.get("OLLAMA_HOST", "http://localhost:11434")

DEFAULT_FALLBACK_CASCADE = [
    "gemma2:9b",
    "gemma2:27b",
    "codegemma:7b",
    "gemma:7b",
    "gemma2:2b",
    "codegemma:2b",
    "gemma:2b"
]

HYPERPARAMETER_PROFILES = {
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


def load_config_if_available():
    candidates = [
        Path("config/ollama_gemma_config.json"),
        Path("/Users/pablosuarez/Desktop/SympTopAutoForm/config/ollama_gemma_config.json")
    ]
    for p in candidates:
        if p.exists():
            try:
                with open(p, "r", encoding="utf-8") as f:
                    return json.load(f)
            except Exception:
                pass
    return None


def check_health(host=DEFAULT_HOST, timeout=3.0) -> dict:
    url = f"{host.rstrip('/')}/api/tags"
    start_t = time.time()
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "Lean4GemmaProver/1.0"})
        with urllib.request.urlopen(req, timeout=timeout) as response:
            latency_ms = round((time.time() - start_t) * 1000, 2)
            data = json.loads(response.read().decode("utf-8"))
            models = [m["name"] for m in data.get("models", [])]
            return {
                "status": "online",
                "host": host,
                "latency_ms": latency_ms,
                "model_count": len(models),
                "available_models": models
            }
    except Exception as e:
        return {
            "status": "offline",
            "host": host,
            "error": str(e),
            "recommendation": "Ollama daemon is unreachable. Start it with 'ollama serve' in your terminal."
        }


def resolve_model(available_models: list, requested_model: str = None) -> str:
    if requested_model:
        matched = [m for m in available_models if m == requested_model or m.startswith(f"{requested_model}:") or requested_model.startswith(m)]
        if matched:
            return matched[0]
        if not available_models:
            return requested_model

    for pref in DEFAULT_FALLBACK_CASCADE:
        for m in available_models:
            if m == pref or m.startswith(pref + ":"):
                return m

    if requested_model:
        return requested_model
    return available_models[0] if available_models else "gemma2:9b"


def format_gemma_prompt(prompt: str, system_instruction: str = None) -> str:
    formatted = "<start_of_turn>user\n"
    if system_instruction:
        formatted += f"{system_instruction.strip()}\n\n"
    formatted += f"{prompt.strip()}\n<end_of_turn>\n<start_of_turn>model\n"
    return formatted


def sanitize_response(text: str) -> str:
    cleaned = text.strip()
    # Strip opening ```lean4 or ```lean or ```
    cleaned = re.sub(r"^```(?:lean4|lean|json)?\n", "", cleaned)
    # Strip closing ```
    cleaned = re.sub(r"\n```$", "", cleaned)
    return cleaned.strip()


def mock_gemma_response(prompt: str, mode: str) -> str:
    """Deterministic offline mock responses for unit tests and CI."""
    if mode == "tactic":
        return "-- Applying Patrick Massot's Hofer lemma to rescale around blowup point\nexact Mathlib.Analysis.Hofer.hofer hf_cont x0 hε0"
    elif mode == "premise":
        return json.dumps({
            "selected_premises": [
                {"name": "Mathlib.Analysis.Hofer.hofer", "relevance": "Gradient blowup rescaling on complete metric spaces"},
                {"name": "dist_triangle", "relevance": "Triangle inequality for metric balls"},
                {"name": "Metric.closedBall", "relevance": "Rescaled closed balls containing points"}
            ]
        }, indent=2)
    elif mode == "autoformalize":
        return """structure AlmostComplexStructure (M : Type*) [MetricSpace M] where
  J : (x : M) → TangentSpace x →L[ℝ] TangentSpace x
  J_sq : ∀ (x : M) (v : TangentSpace x), J x (J x v) = -v"""
    else:
        return f"-- Proof skeleton for {mode}\nhave h1 : True := trivial\nsorry"


def execute_query(prompt: str, mode: str, host: str = DEFAULT_HOST, model: str = None, mock: bool = False) -> dict:
    profile = HYPERPARAMETER_PROFILES.get(mode, HYPERPARAMETER_PROFILES["tactic"])

    if mock:
        raw_resp = mock_gemma_response(prompt, mode)
        sanitized = sanitize_response(raw_resp)
        return {
            "status": "success",
            "mode": mode,
            "mock": True,
            "model_used": model or "gemma2:9b (mock)",
            "raw_response": raw_resp,
            "sanitized_response": sanitized,
            "parameters": profile
        }

    # Live connection check
    health = check_health(host)
    if health["status"] != "online":
        return {
            "status": "error",
            "error": health.get("error", "Ollama unreachable"),
            "host": host,
            "recommendation": health.get("recommendation", "Start Ollama daemon with 'ollama serve' or use --mock flag.")
        }

    chosen_model = resolve_model(health["available_models"], model)
    formatted_prompt = format_gemma_prompt(prompt)

    payload = {
        "model": chosen_model,
        "prompt": formatted_prompt,
        "stream": False,
        "options": profile
    }

    url = f"{host.rstrip('/')}/api/generate"
    try:
        req = urllib.request.Request(
            url,
            data=json.dumps(payload).encode("utf-8"),
            headers={"Content-Type": "application/json", "User-Agent": "Lean4GemmaProver/1.0"}
        )
        with urllib.request.urlopen(req, timeout=60.0) as resp:
            data = json.loads(resp.read().decode("utf-8"))
            raw_text = data.get("response", "")
            sanitized = sanitize_response(raw_text)
            return {
                "status": "success",
                "mode": mode,
                "mock": False,
                "model_used": chosen_model,
                "raw_response": raw_text,
                "sanitized_response": sanitized,
                "total_duration_ns": data.get("total_duration", 0),
                "eval_count": data.get("eval_count", 0),
                "eval_duration_ns": data.get("eval_duration", 0),
                "parameters": profile
            }
    except Exception as e:
        return {
            "status": "error",
            "error": str(e),
            "host": host,
            "model_requested": chosen_model,
            "recommendation": f"Query to Ollama failed. Check if {chosen_model} is downloaded with 'ollama pull {chosen_model}'."
        }


def run_healthcheck(args):
    result = check_health(args.host)
    if args.output:
        p = Path(args.output)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(result, indent=2), encoding="utf-8")
        print(f"Healthcheck written to: {args.output}")
    else:
        print(json.dumps(result, indent=2))
    return 0 if result["status"] == "online" else 1


def run_query(args):
    prompt = args.prompt
    if args.prompt_file:
        p = Path(args.prompt_file)
        if not p.exists():
            print(f"Error: Prompt file {p} does not exist.", file=sys.stderr)
            return 1
        prompt = p.read_text(encoding="utf-8")

    if not prompt:
        print("Error: Either --prompt or --prompt-file must be provided.", file=sys.stderr)
        return 1

    result = execute_query(
        prompt=prompt,
        mode=args.mode,
        host=args.host,
        model=args.model,
        mock=args.mock
    )

    if args.output:
        out_p = Path(args.output)
        out_p.parent.mkdir(parents=True, exist_ok=True)
        out_p.write_text(json.dumps(result, indent=2), encoding="utf-8")
        print(f"Success! Output written to: {out_p}")
    else:
        print(json.dumps(result, indent=2))

    return 0 if result["status"] == "success" else 1


def run_benchmark(args):
    print(f"Benchmarking Ollama host {args.host}...")
    health = check_health(args.host)
    if health["status"] != "online":
        print(f"Error: Host is offline ({health.get('error')})", file=sys.stderr)
        return 1

    model = resolve_model(health["available_models"], args.model)
    print(f"Selected model: {model}")

    test_prompt = "Suggest 3 tactics for metric space triangle inequality in Lean 4."
    start_t = time.time()
    result = execute_query(test_prompt, mode="tactic", host=args.host, model=model)
    duration = time.time() - start_t

    eval_count = result.get("eval_count", 0)
    tok_per_sec = round(eval_count / duration, 2) if duration > 0 else 0

    benchmark_data = {
        "host": args.host,
        "model": model,
        "tokens_generated": eval_count,
        "duration_seconds": round(duration, 3),
        "tokens_per_second": tok_per_sec,
        "status": result["status"]
    }

    if args.output:
        p = Path(args.output)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(benchmark_data, indent=2), encoding="utf-8")
        print(f"Benchmark results written to: {p}")
    else:
        print(json.dumps(benchmark_data, indent=2))
    return 0


def run_test(args):
    print("Running Ollama Lean 4 Gemma Prover self-test suite...")

    # Test 1: Turn formatting
    p = format_gemma_prompt("prove goal", "system rules")
    assert "<start_of_turn>user" in p
    assert "<end_of_turn>" in p
    assert "<start_of_turn>model" in p
    print("  [PASS] Test 1: Gemma 2 turn syntax wrapping")

    # Test 2: Fallback cascade resolution
    models = ["other-model", "gemma2:2b", "codegemma:7b"]
    resolved = resolve_model(models)
    assert resolved == "codegemma:7b", f"Expected codegemma:7b, got {resolved}"
    print("  [PASS] Test 2: Model fallback cascade hierarchy")

    # Test 3: Model prefix tag resolution
    prefix_resolved = resolve_model(["gemma2:9b"], "gemma2")
    assert prefix_resolved == "gemma2:9b", f"Expected gemma2:9b, got {prefix_resolved}"
    print("  [PASS] Test 3: Model prefix tag resolution (gemma2 -> gemma2:9b)")

    # Test 4: Hyperparameter profiles context window (num_ctx: 8192)
    for profile_name, prof in HYPERPARAMETER_PROFILES.items():
        assert prof.get("num_ctx") == 8192, f"Profile {profile_name} missing num_ctx: 8192"
    print("  [PASS] Test 4: Context window (num_ctx: 8192) in all hyperparameter profiles")

    # Test 5: Response sanitization
    raw = "```lean4\nexact Mathlib.Analysis.Hofer.hofer\n```"
    san = sanitize_response(raw)
    assert san == "exact Mathlib.Analysis.Hofer.hofer", f"Sanitization failed: {san}"
    print("  [PASS] Test 5: Code block markdown sanitization")

    # Test 6: Mock query execution with Unicode math symbols
    res = execute_query("test prompt ∀ x, ∃ y, ω(x, y) > 0 → L", mode="tactic", mock=True)
    assert res["status"] == "success"
    assert "Mathlib.Analysis.Hofer" in res["sanitized_response"]
    assert res["parameters"].get("num_ctx") == 8192
    print("  [PASS] Test 6: Offline mock query execution with Unicode tokens")

    test_report = {
        "status": "PASSED",
        "tests_run": 6,
        "failures": 0,
        "features_verified": [
            "Gemma 2 turn format wrapper",
            "Model fallback cascade resolution",
            "Model prefix tag resolution",
            "Context window num_ctx: 8192",
            "Markdown code delimiter sanitization",
            "Offline deterministic mock mode with Unicode safety"
        ]
    }

    if args.output:
        out_p = Path(args.output)
        out_p.parent.mkdir(parents=True, exist_ok=True)
        out_p.write_text(json.dumps(test_report, indent=2), encoding="utf-8")
        print(f"Self-test report written to: {out_p}")

    print("All Ollama prover tests passed successfully!")
    return 0


def main():
    parser = argparse.ArgumentParser(description="Ollama Lean 4 Gemma Prover CLI")
    subparsers = parser.add_subparsers(dest="subcommand")

    # Subcommand: healthcheck
    health_p = subparsers.add_parser("healthcheck", help="Check Ollama daemon status")
    health_p.add_argument("--host", default=DEFAULT_HOST, help="Ollama host endpoint")
    health_p.add_argument("--output", help="Output JSON path")

    # Subcommand: query
    query_p = subparsers.add_parser("query", help="Query Gemma model via Ollama")
    query_p.add_argument("--mode", choices=["autoformalize", "tactic", "proof_skeleton", "premise"], required=True)
    query_p.add_argument("--prompt", help="Inline prompt text")
    query_p.add_argument("--prompt-file", help="Path to file containing prompt")
    query_p.add_argument("--host", default=DEFAULT_HOST, help="Ollama host endpoint")
    query_p.add_argument("--model", help="Specific model name (defaults to fallback cascade)")
    query_p.add_argument("--mock", action="store_true", help="Execute in offline mock mode")
    query_p.add_argument("--output", help="Output JSON file path")

    # Subcommand: benchmark
    bench_p = subparsers.add_parser("benchmark", help="Measure generation speed and latency")
    bench_p.add_argument("--host", default=DEFAULT_HOST, help="Ollama host endpoint")
    bench_p.add_argument("--model", help="Specific model to benchmark")
    bench_p.add_argument("--output", help="Output JSON path")

    # Subcommand: test
    test_p = subparsers.add_parser("test", help="Run internal test suite")
    test_p.add_argument("--output", help="Output JSON test report path")

    args = parser.parse_args()

    if not getattr(args, "subcommand", None):
        parser.print_help()
        sys.exit(1)

    if args.subcommand == "healthcheck":
        sys.exit(run_healthcheck(args))
    elif args.subcommand == "query":
        sys.exit(run_query(args))
    elif args.subcommand == "benchmark":
        sys.exit(run_benchmark(args))
    elif args.subcommand == "test":
        sys.exit(run_test(args))


if __name__ == "__main__":
    main()
