# Adversarial Challenge Report: Ollama Prover & Local Pipeline Verification

**Agent**: Challenger 1 (Ollama Prover & Pipeline Adversarial Verifier)  
**Date**: 2026-11-03  
**Target Artifacts**:
- `tools/ollama_lean4_client.py`
- `tools/test_ollama_pipeline.py`
- `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py`
- `config/ollama_gemma_config.json`
- `skills/ollama-lean4-gemma-prover/SKILL.md`

**Verdict**: `REQUEST_CHANGES`

---

## 1. Challenge Summary

**Overall Risk Assessment**: **HIGH**

While the standalone client `tools/ollama_lean4_client.py` and its test suite `tools/test_ollama_pipeline.py` demonstrate excellent architecture and offline mock fidelity for Gromov compactness math, empirical stress testing has revealed **critical breaking defects** in CLI compatibility, JSON output format, prefix model resolution, context window sizing, and stream encoding resilience.

Most critically:
1. `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py` **crashes fatally on Python 3.6** (the system's default `python3`) on all subcommands due to an incompatible keyword argument (`required=True` in `add_subparsers`).
2. `tools/ollama_lean4_client.py` **produces invalid JSON** when `--json` is specified, because informational progress banners are printed to `stdout` before the JSON payload, breaking any downstream JSON piping or programmatic consumer (`json.loads`, `jq`).
3. `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py` has a **model tag resolution bug** in `resolve_model()`: when matching by prefix (e.g., requesting `"gemma2"` against installed `"gemma2:9b"`), it returns the unresolvable prefix string `"gemma2"` instead of the installed tag `"gemma2:9b"`, triggering HTTP 404 from Ollama.
4. `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py` **omits `num_ctx: 8192`**, causing Ollama to silently fall back to its 2048-token default window, truncating lengthy Lean 4 few-shots and Mathlib proofs.
5. `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py` crashes with `UnicodeEncodeError` under non-UTF8 environments, unlike `tools/ollama_lean4_client.py`.

---

## 2. Challenges & Findings

### [Critical] Finding C1: Fatal Python 3.6 CLI Crash in `ollama_query.py`
- **File**: `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py:360`
- **Code**:
  ```python
  subparsers = parser.add_subparsers(dest="subcommand", required=True)
  ```
- **Observed Behavior**:
  Executing `python3 skills/ollama-lean4-gemma-prover/scripts/ollama_query.py --help` or `test` or `healthcheck` fails with:
  ```
  TypeError: __init__() got an unexpected keyword argument 'required'
  ```
- **Root Cause**:
  In Python 3.6 (which is the default `python3` binary `/usr/local/bin/python3` on this machine), `argparse.ArgumentParser.add_subparsers()` does not accept `required=True` (this parameter was added in Python 3.7). In contrast, `tools/ollama_lean4_client.py:778` correctly used `parser.add_subparsers(dest="subcommand", help="...")`.
- **Blast Radius**:
  The entire CLI interface of `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py` is 100% unusable on Python 3.6 systems, contradicting `SKILL.md` line 43 (`- Python 3.6+`).
- **Recommended Mitigation**:
  Remove `required=True` from `add_subparsers(dest="subcommand")` and enforce subcommands manually (e.g., `if args.subcommand is None: parser.print_help(); sys.exit(1)`), exactly as done in `tools/ollama_lean4_client.py`.

---

### [High] Finding C2: Corrupted JSON Output on `--json` Flag in `ollama_lean4_client.py`
- **File**: `tools/ollama_lean4_client.py:660, 697, 731`
- **Code**:
  ```python
  # Line 697 (cmd_autoformalize):
  print(f"Autoformalizing statement using model '{model}'...")
  res = query_ollama(...)
  if args.json:
      print(json.dumps(res, indent=2))
  ```
- **Observed Behavior**:
  Running `python3 tools/ollama_lean4_client.py autoformalize "Hofer lemma" --dry-run --json` outputs:
  ```
  Autoformalizing statement using model 'gemma2:9b'...
  {
    "status": "mock",
    ...
  }
  ```
  Piping this output to `json.loads(stdout)` or `jq .` raises:
  `json.decoder.JSONDecodeError: Expecting value: line 1 column 1 (char 0)`
- **Blast Radius**:
  Any agent, shell pipeline, or automated tool expecting machine-readable JSON output on `stdout` fails with a JSON decode error.
- **Recommended Mitigation**:
  Only print informational messages (`Autoformalizing statement...`, `Dispatching query...`, `Generating tactic...`) when `not args.json`, or redirect all non-data log messages to `sys.stderr` (`print(..., file=sys.stderr)`).

---

### [High] Finding C3: Model Prefix Resolution Bug in `ollama_query.py`
- **File**: `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py:109-111`
- **Code**:
  ```python
  def resolve_model(available_models: list, requested_model: str = None) -> str:
      if requested_model and (requested_model in available_models or any(m.startswith(requested_model) for m in available_models)):
          return requested_model
  ```
- **Observed Behavior**:
  When `available_models = ["gemma2:9b"]` and `requested_model = "gemma2"`, `resolve_model` returns `"gemma2"` rather than `"gemma2:9b"`.
  When `"gemma2"` is dispatched to Ollama `/api/generate`, Ollama returns HTTP 404 because no model with tag `"gemma2"` (or `"gemma2:latest"`) exists.
- **Blast Radius**:
  Short-form model requests (e.g. `--model gemma2` or `--model codegemma`) cause runtime HTTP 404 failures during live proving sessions.
- **Recommended Mitigation**:
  Return the matching model from `available_models`, matching the robust implementation in `tools/ollama_lean4_client.py:216`:
  ```python
  if requested_model:
      matched = [m for m in available_models if m == requested_model or m.startswith(f"{requested_model}:") or requested_model.startswith(m)]
      if matched:
          return matched[0]
  ```

---

### [Medium] Finding C4: Omission of `num_ctx: 8192` in `ollama_query.py`
- **File**: `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py:37-66`
- **Observed Behavior**:
  `HYPERPARAMETER_PROFILES` defines `temperature`, `top_p`, `top_k`, `num_predict`, and `stop`, but completely omits `num_ctx: 8192` and `repeat_penalty`.
- **Root Cause & Impact**:
  Ollama's server-side default context length is only 2048 tokens. For Lean 4 theorem proving, prompt templates with few-shots, imports, and math hypotheses exceed 1500 tokens. Without `num_ctx: 8192`, input prompts will be prematurely truncated, causing syntax truncation and missing premises.
  Note that `config/ollama_gemma_config.json` and `tools/ollama_lean4_client.py` both explicitly set `num_ctx: 8192`.
- **Recommended Mitigation**:
  Add `"num_ctx": 8192` and `"repeat_penalty": 1.10` to all profile definitions in `ollama_query.py`, or call `load_config_if_available()` to populate parameters from `config/ollama_gemma_config.json`.

---

### [Medium] Finding C5: Missing Stream UTF-8 Encoding Guard in `ollama_query.py`
- **File**: `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py`
- **Observed Behavior**:
  Executing mock queries under `PYTHONIOENCODING=ascii` raises:
  `UnicodeEncodeError: 'ascii' codec can't encode character '\u2192' in position 81`
- **Root Cause**:
  `tools/ollama_lean4_client.py:24-40` implements `ensure_utf8_streams()` to safely wrap `sys.stdout` and `sys.stderr` in UTF-8 TextIOWrapper. `ollama_query.py` lacks this guard, causing failures in headless CI or non-UTF8 terminal environments when printing Lean 4 math symbols (`→`, `∀`, `∃`, `ω`, `ℝ`, `ℂ`).
- **Recommended Mitigation**:
  Port `ensure_utf8_streams()` into `ollama_query.py`.

---

### [Low] Finding C6: Test Suite Blind Spots in `test_ollama_pipeline.py`
- **File**: `tools/test_ollama_pipeline.py`
- **Observed Behavior**:
  All 39 unit tests in `test_ollama_pipeline.py` pass, but the suite did not catch:
  1. Invalid JSON output when `--json` flag is supplied (no test parses `json.loads(stdout)`).
  2. Unicode mathematical symbol roundtripping.
  3. Integration with `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py`.
- **Recommended Mitigation**:
  Add unit tests to `test_ollama_pipeline.py` that execute CLI subcommands with `--json` and verify `json.loads(stdout)` parses cleanly, and add test cases validating Unicode mathematical tokens (`∀`, `∃`, `ω`, `∂̄`, `→L[ℝ]`).

---

## 3. Stress Test Results Summary

| Test Case | Scenario / Command | Expected Behavior | Actual Behavior | Result |
|---|---|---|---|---|
| **ST-01** | `ollama_query.py --help` on Python 3.6 | Displays help message, exit 0 | `TypeError: __init__() got an unexpected keyword argument 'required'`, exit 1 | **FAIL** |
| **ST-02** | `ollama_query.py test` on Python 3.6 | Runs 4 unit tests, exit 0 | Crashes with `TypeError`, exit 1 | **FAIL** |
| **ST-03** | `ollama_lean4_client.py autoformalize "Hofer" --dry-run --json` | Valid JSON on `stdout`, exit 0 | Plaintext banner prepended to JSON; `json.loads` fails | **FAIL** |
| **ST-04** | `ollama_lean4_client.py suggest-tactic ... --dry-run --json` | Valid JSON on `stdout`, exit 0 | Plaintext banner prepended to JSON; `json.loads` fails | **FAIL** |
| **ST-05** | `ollama_lean4_client.py query ... --dry-run --json` | Valid JSON on `stdout`, exit 0 | Plaintext banner prepended to JSON; `json.loads` fails | **FAIL** |
| **ST-06** | `ollama_query.py resolve_model(["gemma2:9b"], "gemma2")` | Returns `"gemma2:9b"` | Returns `"gemma2"` (triggers HTTP 404 in Ollama) | **FAIL** |
| **ST-07** | `ollama_query.py` hyperparameter profiles context window | `num_ctx == 8192` | `num_ctx` missing / `None` (server defaults to 2048) | **FAIL** |
| **ST-08** | `ollama_query.py` mock printing with `PYTHONIOENCODING=ascii` | Encodes/replaces safely | `UnicodeEncodeError: 'ascii' codec can't encode '\u2192'` | **FAIL** |
| **ST-09** | `ollama_lean4_client.py health` with offline port 11434 | Exit 1, clear hint to run `ollama serve` | Handled cleanly with actionable hint | **PASS** |
| **ST-10** | `ollama_lean4_client.py health --dry-run` | Exit 0, mocks healthy status | Exit 0, reports simulated status | **PASS** |
| **ST-11** | `ollama_lean4_client.py query` offline without `--dry-run` | Exit 1, error caught cleanly | Exit 1, error caught with hint | **PASS** |
| **ST-12** | `ollama_lean4_client.py autoformalize "Hofer" --dry-run` | Valid Lean 4 theorem with `Mathlib.Analysis.Hofer.hofer` | Extracted code matches Hofer theorem correctly | **PASS** |
| **ST-13** | `ollama_lean4_client.py autoformalize "energy" --dry-run` | Minimal energy gap theorem with `hbar > 0` and `sorry` | Extracted code matches energy theorem correctly | **PASS** |
| **ST-14** | `ollama_lean4_client.py test` | 8/8 self-tests pass | 8/8 self-tests pass (100% pass rate) | **PASS** |
| **ST-15** | `test_ollama_pipeline.py` test suite | 39 unit tests pass | 39 unit tests pass in 0.023s | **PASS** |
| **ST-16** | Lean 4 Unicode math symbols in prompt & code extraction | Handles `∀`, `∃`, `ω`, `∂̄`, `→L[ℝ]`, `⟨`, `⟩` | Characters preserved without corruption or crashes | **PASS** |

---

## 4. Unchallenged Areas

- **Live GPU generation with `gemma2:9b` on Apple Silicon Metal**: Unchallenged due to running in sandbox environment without local Ollama daemon actively bound to port 11434. Network connectivity, fallback logic, mock generation, parameter options, and turn templates were rigorously verified via mock and dry-run execution.
