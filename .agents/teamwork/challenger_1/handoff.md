# Handoff Report: Challenger 1 (Ollama Prover & Pipeline Adversarial Verification)

**Agent**: Challenger 1 (EMPIRICAL CHALLENGER / critic, specialist)  
**Date**: 2026-11-03  
**Verdict**: **`REQUEST_CHANGES`**

---

## 1. Observation

Direct empirical observations from executing verification code against the target codebase:

1. **Fatal Python 3.6 crash in `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py`**:
   - Command: `python3 skills/ollama-lean4-gemma-prover/scripts/ollama_query.py test`
   - File & line: `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py:360`
   - Verbatim traceback:
     ```
     Traceback (most recent call last):
       File "skills/ollama-lean4-gemma-prover/scripts/ollama_query.py", line 400, in <module>
         main()
       File "skills/ollama-lean4-gemma-prover/scripts/ollama_query.py", line 360, in main
         subparsers = parser.add_subparsers(dest="subcommand", required=True)
       File "/Library/Frameworks/Python.framework/Versions/3.6/lib/python3.6/argparse.py", line 1707, in add_subparsers
         action = parsers_class(option_strings=[], **kwargs)
     TypeError: __init__() got an unexpected keyword argument 'required'
     ```
   - Python version: `Python 3.6.6` (`/usr/local/bin/python3`).
   - Comparison: `tools/ollama_lean4_client.py:778` uses `parser.add_subparsers(dest="subcommand", help="Available subcommands")` without `required=True` and executes without error.

2. **Corrupted JSON Output on `--json` in `tools/ollama_lean4_client.py`**:
   - Command: `python3 tools/ollama_lean4_client.py autoformalize "Hofer lemma" --dry-run --json`
   - File & lines: `tools/ollama_lean4_client.py:660, 697, 731`
   - Verbatim stdout:
     ```
     Autoformalizing statement using model 'gemma2:9b'...
     {
       "status": "mock",
       "model": "gemma2:9b",
       ...
     ```
   - Verbatim error when passed to `json.loads(proc.stdout)`:
     ```
     json.decoder.JSONDecodeError: Expecting value: line 1 column 1 (char 0)
     ```

3. **Model Prefix Resolution Bug in `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py`**:
   - Function: `resolve_model(available_models, requested_model)` at lines 109-119.
   - Empirical call: `ollama_query.resolve_model(["gemma2:9b"], requested_model="gemma2")`
   - Verbatim returned value: `"gemma2"`
   - Expected value: `"gemma2:9b"`
   - Comparison: `tools/ollama_lean4_client.py:216` matches `gemma2` to `gemma2:9b` and returns the actual installed tag.

4. **Missing Context Window Specification in `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py`**:
   - File & lines: `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py:37-66`
   - Verbatim inspection:
     `[v.get("num_ctx") for v in HYPERPARAMETER_PROFILES.values()]` yields `[None, None, None, None]`.
   - In contrast: `tools/ollama_lean4_client.py:64-101` and `config/ollama_gemma_config.json` set `num_ctx: 8192`.

5. **Unicode Stream Encoding Vulnerability in `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py`**:
   - Command: `PYTHONIOENCODING=ascii /usr/bin/python3 -c "import sys; sys.path.insert(0, 'skills/ollama-lean4-gemma-prover/scripts'); import ollama_query; print(ollama_query.mock_gemma_response('', 'autoformalize'))"`
   - Verbatim error:
     ```
     UnicodeEncodeError: 'ascii' codec can't encode character '\u2192' in position 81: ordinal not in range(128)
     ```
   - In contrast: `tools/ollama_lean4_client.py` implements `ensure_utf8_streams()` (lines 24-40) and executes cleanly with exit code 0.

6. **Successful Existing Tests**:
   - `python3 tools/test_ollama_pipeline.py`: 39 tests ran in 0.023s, all passed (OK).
   - `python3 tools/ollama_lean4_client.py test`: 8 self-tests passed (100% pass rate).
   - Port 11434 offline behavior: Handled gracefully with exit code 1 and hint to run `ollama serve`.
   - `--dry-run` Lean 4 math accuracy: Hofer's lemma outputs `Mathlib.Analysis.Hofer.hofer`, energy quantization outputs `hbar > 0`, proof skeleton outputs bubbling-off lemmas with `sorry`.

---

## 2. Logic Chain

1. **Step 1 (Python 3.6 incompatibility)**: Observation 1 demonstrates that running `python3 skills/ollama-lean4-gemma-prover/scripts/ollama_query.py` under Python 3.6 raises an unhandled `TypeError` during argument parser setup. Because `SKILL.md` (Observation 1) specifies Python 3.6+ support, and `/usr/local/bin/python3` on macOS defaults to 3.6.6, the skill CLI is broken for users in this environment.
2. **Step 2 (JSON breakage)**: Observation 2 demonstrates that `tools/ollama_lean4_client.py` prints human-readable strings to `stdout` immediately before printing the JSON dictionary. Standard JSON parsers require that the entire standard output be valid JSON without leading unquoted text. Therefore, programmatic consumption of `--json` output will always crash.
3. **Step 3 (Model tag resolution)**: Observation 3 shows `ollama_query.resolve_model` returns the prefix substring instead of the installed full model name. If dispatched to Ollama's REST API `/api/generate`, Ollama will look up the model tag `"gemma2"` literally, which does not exist, and return HTTP 404.
4. **Step 4 (Context window truncation)**: Observation 4 shows `ollama_query.py` omits `num_ctx` in all generation requests. Ollama defaults to a 2048-token context length when unspecified. For Lean 4 theorem proving prompts that include few-shots and Mathlib definitions, the context exceeds 2048 tokens and will be silently truncated by Ollama.
5. **Step 5 (Unicode crash)**: Observation 5 shows `ollama_query.py` lacks stdout stream wrapping, crashing with `UnicodeEncodeError` in non-UTF8 environments when processing Lean 4 mathematical symbols like `→`, `∀`, `ℝ`.
6. **Step 6 (Verdict Synthesis)**: While `tools/ollama_lean4_client.py` and `tools/test_ollama_pipeline.py` pass their baseline tests, the combination of a fatal CLI crash in `ollama_query.py`, corrupted JSON output in `ollama_lean4_client.py`, and runtime model tag resolution defects necessitates requesting changes before deployment.

---

## 3. Caveats

- **No live Ollama daemon on port 11434**: Live inference with local weights (e.g. `ollama pull gemma2:9b`) was not tested against a running server because the current environment does not have the Ollama daemon running or port 11434 bound. Offline connectivity error handling, dry-run simulation, and mock responses were tested extensively instead.
- **Python version disparity**: The system has both Python 3.6.6 (`/usr/local/bin/python3`, default `python3`) and Python 3.9.6 (`/usr/bin/python3`). Both were tested.

---

## 4. Conclusion

**Verdict**: **`REQUEST_CHANGES`**

The local Ollama prover integration requires the following actionable fixes:

1. **Fix Python 3.6 compatibility in `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py:360`**:
   Replace:
   ```python
   subparsers = parser.add_subparsers(dest="subcommand", required=True)
   ```
   with:
   ```python
   subparsers = parser.add_subparsers(dest="subcommand", help="Available subcommands")
   ```
   and add manual validation after `parser.parse_args()`:
   ```python
   if args.subcommand is None:
       parser.print_help()
       sys.exit(1)
   ```

2. **Clean JSON output in `tools/ollama_lean4_client.py`**:
   In `cmd_autoformalize`, `cmd_suggest_tactic`, and `cmd_query`, ensure status banner messages are suppressed when `args.json` is True, or redirected to `sys.stderr`:
   ```python
   if not args.json:
       print(f"Autoformalizing statement using model '{model}'...")
   ```

3. **Fix model tag prefix resolution in `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py:109-119`**:
   Ensure `resolve_model` returns the matched model from `available_models`, not the prefix `requested_model`.

4. **Align `num_ctx: 8192` in `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py`**:
   Add `"num_ctx": 8192` and `"repeat_penalty": 1.10` to `HYPERPARAMETER_PROFILES`.

5. **Add UTF-8 stream guard to `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py`**:
   Port `ensure_utf8_streams()` from `tools/ollama_lean4_client.py`.

---

## 5. Verification Method

To independently verify these findings and confirm subsequent fixes:

1. **Verify Python 3.6 CLI execution**:
   ```bash
   python3 skills/ollama-lean4-gemma-prover/scripts/ollama_query.py test
   ```
   *Expected fix outcome*: Exits with code 0 and reports all tests passed, without `TypeError`.

2. **Verify JSON parsing from `tools/ollama_lean4_client.py`**:
   ```bash
   python3 -c "
   import subprocess, json
   res = subprocess.run(['python3', 'tools/ollama_lean4_client.py', 'autoformalize', 'Hofer lemma', '--dry-run', '--json'], stdout=subprocess.PIPE, universal_newlines=True)
   data = json.loads(res.stdout)
   assert data['status'] == 'mock'
   print('JSON Output Verified Valid!')
   "
   ```

3. **Verify model prefix resolution in `ollama_query.py`**:
   ```bash
   python3 -c "
   import sys; sys.path.insert(0, 'skills/ollama-lean4-gemma-prover/scripts'); import ollama_query
   resolved = ollama_query.resolve_model(['gemma2:9b'], requested_model='gemma2')
   assert resolved == 'gemma2:9b', f'Expected gemma2:9b, got {resolved}'
   print('Prefix resolution verified!')
   "
   ```

4. **Verify test suite pass rate**:
   ```bash
   python3 tools/test_ollama_pipeline.py
   python3 tools/ollama_lean4_client.py test
   ```
