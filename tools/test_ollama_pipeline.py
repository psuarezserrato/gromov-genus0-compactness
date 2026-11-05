#!/usr/bin/env python3
"""
test_ollama_pipeline.py — Comprehensive Test Suite for Local Gemma & Ollama Pipeline

Covers:
1. Health checks and dual-endpoint connectivity probes (/api/tags, /api/generate).
2. 7-tier model fallback cascade logic and user override resolution.
3. Task-specific parameter profiles (8192 context window, calibrated temperatures, stop tokens).
4. Official Google Gemma chat turn token formatting (<start_of_turn>, <end_of_turn>).
5. Lean 4 code extraction from markdown responses.
6. Dry-run query execution and realistic Lean 4 mock generation for Gromov compactness.
7. Error handling resilience (timeouts, HTTP errors, missing models, connection refusals).
8. CLI subcommand and legacy flag integration.

Compatible with Python 3.6+ without external dependencies.
"""

import sys
import os
import io
import json
import unittest
from unittest.mock import patch, MagicMock
import urllib.error

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

# Add parent directory to path so tools module can be imported
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from tools.ollama_lean4_client import (
    DEFAULT_OLLAMA_HOST,
    MODEL_PRIORITY_CASCADE,
    TASK_PARAMETER_PROFILES,
    check_connection,
    check_generate_endpoint,
    detect_best_model,
    format_gemma_prompt,
    build_autoformalize_prompt,
    build_tactic_prompt,
    build_premise_prompt,
    extract_lean_code,
    generate_mock_response,
    query_ollama,
    load_config,
    main as client_main
)


class TestHealthChecks(unittest.TestCase):
    """Verifies service liveness and readiness probe logic."""

    @patch("urllib.request.urlopen")
    def test_check_connection_success(self, mock_urlopen):
        mock_response = MagicMock()
        mock_response.status = 200
        mock_response.read.return_value = json.dumps({
            "models": [{"name": "gemma2:9b", "size": 5400000000}]
        }).encode("utf-8")
        mock_urlopen.return_value.__enter__.return_value = mock_response

        ok, msg, data = check_connection("http://localhost:11434")
        self.assertTrue(ok)
        self.assertIn("Successfully connected", msg)
        self.assertEqual(len(data.get("models", [])), 1)
        self.assertEqual(data["models"][0]["name"], "gemma2:9b")

    @patch("urllib.request.urlopen")
    def test_check_connection_refused(self, mock_urlopen):
        mock_urlopen.side_effect = urllib.error.URLError("Connection refused")

        ok, msg, data = check_connection("http://localhost:11434")
        self.assertFalse(ok)
        self.assertIn("Connection failed", msg)
        self.assertIn("ollama serve", msg)
        self.assertEqual(data, {})

    @patch("urllib.request.urlopen")
    def test_check_connection_http_error(self, mock_urlopen):
        mock_response = MagicMock()
        mock_response.status = 503
        mock_urlopen.return_value.__enter__.return_value = mock_response

        ok, msg, data = check_connection("http://localhost:11434")
        self.assertFalse(ok)
        self.assertIn("HTTP error 503", msg)

    @patch("urllib.request.urlopen")
    def test_check_generate_endpoint_active_via_version(self, mock_urlopen):
        mock_response = MagicMock()
        mock_response.status = 200
        mock_response.read.return_value = json.dumps({"version": "0.4.0"}).encode("utf-8")
        mock_urlopen.return_value.__enter__.return_value = mock_response

        ok, msg = check_generate_endpoint("http://localhost:11434")
        self.assertTrue(ok)
        self.assertIn("active", msg)

    @patch("urllib.request.urlopen")
    def test_check_generate_endpoint_unreachable(self, mock_urlopen):
        mock_urlopen.side_effect = urllib.error.URLError("Connection refused")

        ok, msg = check_generate_endpoint("http://localhost:11434")
        self.assertFalse(ok)
        self.assertIn("unreachable", msg)


class TestModelFallbackCascade(unittest.TestCase):
    """Verifies the strict 9B model cascade and preference detection."""

    def setUp(self):
        self.mock_full_catalog = {
            "models": [
                {"name": "mistral:7b"},
                {"name": "gemma2:2b"},
                {"name": "gemma:7b"},
                {"name": "gemma2:9b"},
                {"name": "llama3.1:8b"}
            ]
        }

    def test_primary_tier_selection(self):
        best, reason, catalog = detect_best_model(tags_data=self.mock_full_catalog)
        self.assertEqual(best, "gemma2:9b")
        self.assertIn("Selected optimal cascade 9B model", reason)
        self.assertEqual(len(catalog), 5)

    def test_fine_tuned_gemma_lean4_top_priority(self):
        catalog = {
            "models": [
                {"name": "gemma2:9b"},
                {"name": "gemma-lean4:latest"}
            ]
        }
        best, reason, _ = detect_best_model(tags_data=catalog)
        self.assertEqual(best, "gemma-lean4:latest")
        self.assertIn("Selected optimal cascade 9B model", reason)

    def test_fallback_when_lean4_missing(self):
        catalog = {
            "models": [
                {"name": "gemma2:9b-instruct-q5_K_M"},
                {"name": "gemma2:9b"}
            ]
        }
        best, reason, _ = detect_best_model(tags_data=catalog)
        self.assertEqual(best, "gemma2:9b-instruct-q5_K_M")

    def test_disallowed_model_redirection(self):
        best, reason, _ = detect_best_model(preferred_tag="gemma2:27b", tags_data=self.mock_full_catalog)
        self.assertEqual(best, "gemma2:9b")
        self.assertIn("Selected optimal cascade 9B model", reason)

    def test_explicit_user_override(self):
        best, reason, _ = detect_best_model(preferred_tag="gemma2:9b", tags_data=self.mock_full_catalog)
        self.assertEqual(best, "gemma2:9b")
        self.assertIn("Matched explicitly requested 9B model", reason)

    def test_empty_catalog(self):
        empty_catalog = {"models": []}
        best, reason, catalog = detect_best_model(tags_data=empty_catalog)
        self.assertIsNone(best)
        self.assertIn("No models found", reason)
        self.assertEqual(catalog, [])


class TestParameterProfiles(unittest.TestCase):
    """Verifies generation parameters configured for Lean 4 formal math."""

    def test_all_task_profiles_exist(self):
        required_tasks = ["autoformalize", "tactic", "proof_skeleton", "premise"]
        for task in required_tasks:
            self.assertIn(task, TASK_PARAMETER_PROFILES)

    def test_context_window_size(self):
        # 8192 tokens required to avoid premature truncation of Mathlib imports
        for task, profile in TASK_PARAMETER_PROFILES.items():
            self.assertEqual(profile["num_ctx"], 8192, f"Task {task} must use 8192 tokens context window")

    def test_calibrated_temperatures(self):
        self.assertEqual(TASK_PARAMETER_PROFILES["autoformalize"]["temperature"], 0.1)
        self.assertEqual(TASK_PARAMETER_PROFILES["tactic"]["temperature"], 0.4)
        self.assertEqual(TASK_PARAMETER_PROFILES["proof_skeleton"]["temperature"], 0.3)
        self.assertEqual(TASK_PARAMETER_PROFILES["premise"]["temperature"], 0.0)

    def test_stop_tokens_configured(self):
        for task, profile in TASK_PARAMETER_PROFILES.items():
            self.assertIn("stop", profile)
            self.assertIn("<end_of_turn>", profile["stop"])
            self.assertIn("<eos>", profile["stop"])


class TestGemmaTurnFormatting(unittest.TestCase):
    """Verifies Google Gemma control tokens (<start_of_turn>, <end_of_turn>)."""

    def test_format_single_turn(self):
        prompt = format_gemma_prompt("System rules here.", "User query here.")
        self.assertTrue(prompt.startswith("<start_of_turn>user\nSystem rules here.\n\nUser query here.<end_of_turn>\n"))
        self.assertTrue(prompt.endswith("<start_of_turn>model\n"))

    def test_format_few_shot_turns(self):
        few_shot = [
            ("Few shot user 1", "Few shot model 1"),
            ("Few shot user 2", "Few shot model 2")
        ]
        prompt = format_gemma_prompt("System rules.", "Target query.", few_shot)
        self.assertIn("<start_of_turn>user\nSystem rules.\n\nFew shot user 1<end_of_turn>", prompt)
        self.assertIn("<start_of_turn>model\nFew shot model 1<end_of_turn>", prompt)
        self.assertIn("<start_of_turn>user\nFew shot user 2<end_of_turn>", prompt)
        self.assertIn("<start_of_turn>model\nFew shot model 2<end_of_turn>", prompt)
        self.assertIn("<start_of_turn>user\nTarget query.<end_of_turn>", prompt)
        self.assertTrue(prompt.endswith("<start_of_turn>model\n"))

    def test_build_autoformalize_prompt(self):
        p = build_autoformalize_prompt("Let M be a symplectic manifold with form omega.")
        self.assertIn("symplectic geometry", p)
        self.assertIn("AlmostComplexStructure", p)
        self.assertIn("Let M be a symplectic manifold with form omega.", p)

    def test_build_tactic_prompt(self):
        p = build_tactic_prompt("Goal: |- 0 < eps", "type mismatch", "exact h")
        self.assertIn("interactive Lean 4 tactic reasoning engine", p)
        self.assertIn("Goal: |- 0 < eps", p)
        self.assertIn("type mismatch", p)
        self.assertIn("Failed Tactic Attempt:\n`exact h`", p)

    def test_build_premise_prompt(self):
        p = build_premise_prompt("dist x z < r")
        self.assertIn("Mathlib search assistant", p)
        self.assertIn("dist_triangle", p)
        self.assertIn("dist x z < r", p)


class TestLeanCodeExtraction(unittest.TestCase):
    """Verifies extraction of raw Lean 4 code from model responses."""

    def test_extract_lean4_code_fence(self):
        raw = "To solve this, use:\n```lean4\ntheorem foo : 1 = 1 := rfl\n```\nHope this helps!"
        extracted = extract_lean_code(raw)
        self.assertEqual(extracted, "theorem foo : 1 = 1 := rfl")

    def test_extract_lean_code_fence(self):
        raw = "```lean\ndef bar (x : Nat) : Nat := x + 1\n```"
        extracted = extract_lean_code(raw)
        self.assertEqual(extracted, "def bar (x : Nat) : Nat := x + 1")

    def test_extract_raw_code_without_fences(self):
        raw = "exact Mathlib.Analysis.Hofer.hofer hf x0 hε0"
        extracted = extract_lean_code(raw)
        self.assertEqual(extracted, "exact Mathlib.Analysis.Hofer.hofer hf x0 hε0")


class TestDryRunAndMockGeneration(unittest.TestCase):
    """Verifies offline dry-run query pipeline and mathematical mock outputs."""

    def test_dry_run_autoformalize_hofer(self):
        res = query_ollama(
            DEFAULT_OLLAMA_HOST,
            "gemma2:9b",
            "Translate Hofer's lemma into Lean 4",
            task_type="autoformalize",
            dry_run=True
        )
        self.assertEqual(res["status"], "mock")
        self.assertEqual(res["model"], "gemma2:9b")
        self.assertEqual(res["task_type"], "autoformalize")
        self.assertIn("hofer_lemma", res["lean_code"])
        self.assertIn("Mathlib.Analysis.Hofer.hofer", res["lean_code"])

    def test_dry_run_autoformalize_energy_quantization(self):
        res = query_ollama(
            DEFAULT_OLLAMA_HOST,
            "gemma2:9b",
            "State minimal energy gap and energy quantization for pseudo-holomorphic spheres",
            task_type="autoformalize",
            dry_run=True
        )
        self.assertEqual(res["status"], "mock")
        self.assertIn("energy_quantization_sphere", res["lean_code"])

    def test_dry_run_tactic_suggestion(self):
        res = query_ollama(
            DEFAULT_OLLAMA_HOST,
            "gemma2:9b",
            "Goal: Hofer's lemma application",
            task_type="tactic",
            dry_run=True
        )
        self.assertEqual(res["status"], "mock")
        self.assertIn("Mathlib.Analysis.Hofer.hofer", res["lean_code"])

    def test_dry_run_premise_selection(self):
        res = query_ollama(
            DEFAULT_OLLAMA_HOST,
            "gemma2:9b",
            "Closed metric balls and Hofer",
            task_type="premise",
            dry_run=True
        )
        self.assertEqual(res["status"], "mock")
        self.assertIn("Selected Premises:", res["raw_response"])
        self.assertIn("Mathlib.Analysis.Hofer.hofer", res["raw_response"])

    def test_dry_run_proof_skeleton(self):
        res = query_ollama(
            DEFAULT_OLLAMA_HOST,
            "gemma2:9b",
            "Decompose bubbling off proof",
            task_type="proof_skeleton",
            dry_run=True
        )
        self.assertEqual(res["status"], "mock")
        self.assertIn("Bubbling-off decomposition", res["lean_code"])


class TestConfigurationLoading(unittest.TestCase):
    """Verifies configuration discovery and loading."""

    def test_config_loader_returns_valid_dict(self):
        cfg = load_config()
        self.assertIsInstance(cfg, dict)
        self.assertIn("service", cfg)
        self.assertIn("model_fallback_cascade", cfg)
        self.assertIn("parameter_profiles", cfg)
        self.assertEqual(cfg["service"]["default_host"], "http://localhost:11434")


class TestErrorHandlingAndResilience(unittest.TestCase):
    """Verifies network and parsing failure resilience."""

    @patch("urllib.request.urlopen")
    def test_query_ollama_network_timeout(self, mock_urlopen):
        mock_urlopen.side_effect = urllib.error.URLError("timed out")
        res = query_ollama(DEFAULT_OLLAMA_HOST, "gemma2:9b", "Test prompt", timeout=1.0, dry_run=False)
        self.assertEqual(res["status"], "error")
        self.assertIn("timed out", res["error"])
        self.assertIn("Ensure Ollama is running", res["hint"])

    @patch("urllib.request.urlopen")
    def test_query_ollama_malformed_json_response(self, mock_urlopen):
        mock_resp = MagicMock()
        mock_resp.read.return_value = b"<html>502 Bad Gateway</html>"
        mock_urlopen.return_value.__enter__.return_value = mock_resp

        res = query_ollama(DEFAULT_OLLAMA_HOST, "gemma2:9b", "Test prompt", dry_run=False)
        self.assertEqual(res["status"], "error")


class TestCLIIntegration(unittest.TestCase):
    """Verifies that all CLI subcommands and legacy flags execute cleanly."""

    def test_subcommand_test(self):
        with patch.object(sys, "argv", ["ollama_lean4_client.py", "test"]):
            with patch("sys.stdout", new_callable=io.StringIO):
                with self.assertRaises(SystemExit) as cm:
                    client_main()
                self.assertEqual(cm.exception.code, 0)

    def test_subcommand_health_dry_run(self):
        with patch.object(sys, "argv", ["ollama_lean4_client.py", "health", "--dry-run"]):
            with patch("sys.stdout", new_callable=io.StringIO):
                with self.assertRaises(SystemExit) as cm:
                    client_main()
                self.assertEqual(cm.exception.code, 0)

    def test_subcommand_list_models_dry_run(self):
        with patch.object(sys, "argv", ["ollama_lean4_client.py", "list-models", "--dry-run"]):
            with patch("sys.stdout", new_callable=io.StringIO):
                with self.assertRaises(SystemExit) as cm:
                    client_main()
                self.assertEqual(cm.exception.code, 0)

    def test_subcommand_autoformalize_dry_run(self):
        with patch.object(sys, "argv", ["ollama_lean4_client.py", "autoformalize", "Hofer lemma", "--dry-run"]):
            with patch("sys.stdout", new_callable=io.StringIO):
                with self.assertRaises(SystemExit) as cm:
                    client_main()
                self.assertEqual(cm.exception.code, 0)

    def test_subcommand_suggest_tactic_dry_run(self):
        with patch.object(sys, "argv", [
            "ollama_lean4_client.py", "suggest-tactic",
            "--goal", "⊢ 0 < ε",
            "--error", "type mismatch",
            "--dry-run"
        ]):
            with patch("sys.stdout", new_callable=io.StringIO):
                with self.assertRaises(SystemExit) as cm:
                    client_main()
                self.assertEqual(cm.exception.code, 0)

    def test_subcommand_query_dry_run(self):
        with patch.object(sys, "argv", [
            "ollama_lean4_client.py", "query",
            "--prompt", "Minimal energy gap",
            "--task", "autoformalize",
            "--dry-run"
        ]):
            with patch("sys.stdout", new_callable=io.StringIO):
                with self.assertRaises(SystemExit) as cm:
                    client_main()
                self.assertEqual(cm.exception.code, 0)

    def test_legacy_flags_check_dry_run(self):
        with patch.object(sys, "argv", ["ollama_lean4_client.py", "--check", "--dry-run"]):
            with patch("sys.stdout", new_callable=io.StringIO):
                with self.assertRaises(SystemExit) as cm:
                    client_main()
                self.assertEqual(cm.exception.code, 0)

    def test_subcommand_autoformalize_json_clean(self):
        with patch.object(sys, "argv", ["ollama_lean4_client.py", "autoformalize", "Hofer lemma", "--dry-run", "--json"]):
            with patch("sys.stdout", new_callable=io.StringIO) as fake_out:
                with self.assertRaises(SystemExit) as cm:
                    client_main()
                self.assertEqual(cm.exception.code, 0)
                out_str = fake_out.getvalue()
                parsed = json.loads(out_str)
                self.assertIn("status", parsed)
                self.assertIn("lean_code", parsed)

    def test_subcommand_suggest_tactic_json_clean(self):
        with patch.object(sys, "argv", [
            "ollama_lean4_client.py", "suggest-tactic",
            "--goal", "⊢ 0 < ε",
            "--error", "type mismatch",
            "--dry-run", "--json"
        ]):
            with patch("sys.stdout", new_callable=io.StringIO) as fake_out:
                with self.assertRaises(SystemExit) as cm:
                    client_main()
                self.assertEqual(cm.exception.code, 0)
                out_str = fake_out.getvalue()
                parsed = json.loads(out_str)
                self.assertIn("status", parsed)
                self.assertIn("lean_code", parsed)

    def test_subcommand_query_json_clean(self):
        with patch.object(sys, "argv", [
            "ollama_lean4_client.py", "query",
            "--prompt", "Minimal energy gap",
            "--task", "autoformalize",
            "--dry-run", "--json"
        ]):
            with patch("sys.stdout", new_callable=io.StringIO) as fake_out:
                with self.assertRaises(SystemExit) as cm:
                    client_main()
                self.assertEqual(cm.exception.code, 0)
                out_str = fake_out.getvalue()
                parsed = json.loads(out_str)
                self.assertIn("status", parsed)
                self.assertIn("lean_code", parsed)

    def test_unicode_math_tokens_roundtrip(self):
        prompt_with_math = "∀ (x : M) (v : TangentSpace x), J x (J x v) = -v ∧ ω(v, J x v) > 0 →L[ℝ]"
        formatted = format_gemma_prompt("Mathematical system", prompt_with_math)
        self.assertIn("∀", formatted)
        self.assertIn("ω", formatted)
        self.assertIn("→L[ℝ]", formatted)


def suite():
    loader = unittest.TestLoader()
    s = unittest.TestSuite()
    s.addTests(loader.loadTestsFromTestCase(TestHealthChecks))
    s.addTests(loader.loadTestsFromTestCase(TestModelFallbackCascade))
    s.addTests(loader.loadTestsFromTestCase(TestParameterProfiles))
    s.addTests(loader.loadTestsFromTestCase(TestGemmaTurnFormatting))
    s.addTests(loader.loadTestsFromTestCase(TestLeanCodeExtraction))
    s.addTests(loader.loadTestsFromTestCase(TestDryRunAndMockGeneration))
    s.addTests(loader.loadTestsFromTestCase(TestConfigurationLoading))
    s.addTests(loader.loadTestsFromTestCase(TestErrorHandlingAndResilience))
    s.addTests(loader.loadTestsFromTestCase(TestCLIIntegration))
    return s


if __name__ == "__main__":
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite())
    sys.exit(0 if result.wasSuccessful() else 1)
