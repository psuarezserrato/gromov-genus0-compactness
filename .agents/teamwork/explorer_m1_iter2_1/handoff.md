# Phase 5 Milestone 1 Iteration 2 Explorer Report: 9B Model Policy CLI Remediation

**Agent**: `teamwork_explorer_m1_iter2_1`  
**Date**: 2026-11-04  
**Target File**: `tools/ollama_lean4_client.py`  
**Related Test File**: `tools/test_ollama_pipeline.py`  
**Type**: Hard Handoff (Investigation Complete)

---

## 1. Observation

Direct empirical observations and verbatim code inspection from `tools/ollama_lean4_client.py` and local environment:

### Observation 1.1: Flawed CLI Model Resolution Branching
In `tools/ollama_lean4_client.py`:
- `cmd_query` (lines 936–947):
  ```python
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
  ```
- `cmd_autoformalize` (lines 990–1001) and `cmd_suggest_tactic` (lines 1042–1053) contain verbatim identical blocks.
- When `--model <tag>` is supplied (e.g. `--model gemma4:12B` or `--model gemma2:27b`), `not model` evaluates to `False`. The code skips `detect_best_model` and executes `else: model = model or "gemma2:9b"`, retaining the disallowed model without inspection.
- When `--dry-run` is supplied without `--model`, `not args.dry_run` evaluates to `False`. The code skips `detect_best_model` and falls through to `"gemma2:9b"` instead of top cascade model `gemma-lean4:latest`.

### Observation 1.2: Host Machine Ollama Inventory
Running `ollama list` on the host machine confirms that `gemma4:12B` is installed locally:
```text
NAME                         ID              SIZE      MODIFIED       
gemma-lean4:latest           031f913365cd    6.6 GB    45 minutes ago    
gemma2:9b-instruct-q5_K_M    272e1f3a41a6    6.6 GB    9 days ago        
gemma4:12B                   4eb23ef187e2    7.6 GB    4 months ago      
gemma4:e4b                   c6eb396dbd59    9.6 GB    5 months ago      
gemma2:9b                    ff02c3702f32    5.4 GB    5 months ago      
```
Passing `--model gemma4:12B` to CLI immediately dispatches requests to `gemma4:12B`, loading the 7.6 GB model into memory and violating the strict 9B memory requirement of COMPLETION_PLAN §5.1.

### Observation 1.3: Empirical Reproduction of CLI Model Bypass
Running:
```bash
python3 tools/ollama_lean4_client.py query --model gemma4:12B --prompt "test" --dry-run
```
Output:
```text
Dispatching query to 'gemma4:12B' (Task: autoformalize, Host: http://localhost:11434)...
```
Running:
```bash
python3 tools/ollama_lean4_client.py query --model gemma2:27b --prompt "test" --dry-run
```
Output:
```text
Dispatching query to 'gemma2:27b' (Task: autoformalize, Host: http://localhost:11434)...
```
Both outputs demonstrate that disallowed models pass directly through the CLI without warning or redirection.

### Observation 1.4: Empirical Live 404 Trigger Recorded by Challenger 1
Challenger 1 report (`challenger_m1_1/challenge.md:71-79`) documented live execution:
```bash
python3 tools/ollama_lean4_client.py query --model gemma2:27b --prompt "hello" --timeout 2.0
```
Server log entry from `~/.ollama/logs/server.log`:
```text
[GIN] 2026/11/04 - 14:25:57 | 404 | 504.875µs | 127.0.0.1 | POST "/api/generate"
```
Client output:
```text
Dispatching query to 'gemma2:27b' (Task: autoformalize, Host: http://localhost:11434)...
[ERROR] HTTP Error 404: Not Found
[HINT] Ensure Ollama is running ('ollama serve') and model is pulled ('ollama pull gemma2:27b'). Or pass --dry-run for offline testing.
```

### Observation 1.5: Missing Defense-in-Depth in `query_ollama`
In `tools/ollama_lean4_client.py`, lines 620–645:
```python
def query_ollama(base_url: str,
                 model: str,
                 prompt: str,
                 task_type: str = "autoformalize",
                 options_override: Optional[Dict[str, Any]] = None,
                 timeout: float = 60.0,
                 dry_run: bool = False,
                 declaration: Optional[str] = None,
                 record_usage: bool = True) -> Dict[str, Any]:
    options = TASK_PARAMETER_PROFILES.get(task_type, TASK_PARAMETER_PROFILES["autoformalize"]).copy()
    if options_override:
        options.update(options_override)

    payload = {
        "model": model,
        "prompt": prompt,
        "stream": False,
        "options": options,
        "keep_alive": "30m"
    }
```
`query_ollama` directly embeds `model` into the JSON payload dispatched to `{base_url}/api/generate`. It contains zero validation of `is_allowed_9b_model(model)` or `ACTIVE_CONFIG["enforce_9b_policy"]`.

### Observation 1.6: Pre-existing Redirection Logic in `detect_best_model`
In `tools/ollama_lean4_client.py`, lines 426–437:
```python
if preferred_tag:
    if not is_allowed_9b_model(preferred_tag):
        print(f"[WARNING] Model '{preferred_tag}' is disallowed by the strict 9B policy (12B/27B forbidden). Redirecting to optimal 9B model.", file=sys.stderr)
        preferred_tag = None
    else:
        matched = [m for m in models if m == preferred_tag or m.startswith(f"{preferred_tag}:") or preferred_tag.startswith(m)]
        if matched:
            return matched[0], f"Matched explicitly requested 9B model: {matched[0]}", models
        else:
            print(f"[WARNING] Requested model '{preferred_tag}' is not installed locally. Falling back to 9B cascade.", file=sys.stderr)
```
When invoked, `detect_best_model` already correctly redirects disallowed models (and uninstalled models) to the top installed 9B cascade model (`gemma-lean4:latest`) while printing an explicit warning to `sys.stderr`.

---

## 2. Logic Chain

1. **Premise 1 (Policy Requirement)**: COMPLETION_PLAN §5.1 requires using strictly 9B-class Gemma models (`gemma-lean4:latest` / `gemma2:9b-instruct-q5_K_M` / `gemma2:9b`), prohibiting `12B`, `27B`, and `70B` models to protect unified RAM during `lake build`.
2. **Premise 2 (Obs. 1.2)**: `gemma4:12B` is physically installed on the user's host machine. Therefore, any unvalidated CLI request specifying `--model gemma4:12B` will be executed by Ollama, loading 7.6 GB into VRAM.
3. **Premise 3 (Obs. 1.1)**: The condition `if not model and not args.dry_run:` in `cmd_query`, `cmd_autoformalize`, and `cmd_suggest_tactic` skips model validation whenever `--model` is supplied.
4. **Deduction 1 (CLI Vulnerability)**: From Premise 2 and Premise 3, passing `--model gemma4:12B` or `--model gemma2:27b` on the CLI completely bypasses the 9B model policy. This explains the failures observed by Reviewer 2 and Challenger 1 (Obs. 1.3, 1.4).
5. **Premise 4 (Obs. 1.5)**: `query_ollama` accepts `model: str` without validation and forwards it directly to `/api/generate`.
6. **Deduction 2 (API Vulnerability)**: Any internal programmatic caller or subagent that calls `query_ollama` directly can dispatch non-9B models or uninstalled models, generating 404s or executing 12B weights.
7. **Premise 5 (Obs. 1.6)**: `detect_best_model` already contains robust redirection logic that selects the top installed 9B model and prints the required warning to `sys.stderr`.
8. **Deduction 3 (Unified Solution)**:
   - Defining a centralized helper `resolve_model_for_task` that routes all CLI commands through `is_allowed_9b_model` and `detect_best_model` eliminates the CLI bypass.
   - Adding a defense-in-depth check in `query_ollama` that verifies `is_allowed_9b_model` and checks local installation eliminates programmatic bypasses and synthetic 404s.

---

## 3. Caveats

1. **Host Ollama Server State**: The live redirection of uninstalled models relies on Ollama `/api/tags` to discover installed models. If Ollama is offline and `dry_run=False`, `detect_best_model` reports connection failure and exits with code 1. In `--dry-run` mode, network calls are skipped and redirection uses `MODEL_PRIORITY_CASCADE[0]` without requiring a live Ollama daemon.
2. **`gemma4:e4b` on Host**: The host has `gemma4:e4b` (9.6 GB). This model does NOT match `ALLOWED_9B_PATTERNS` (`is_allowed_9b_model("gemma4:e4b") == False`), so it is correctly rejected and redirected to 9B under this policy.
3. **Auxiliary Script (`skills/ollama-lean4-gemma-prover/scripts/ollama_query.py`)**: While not invoked by the primary workflow CLI, `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py` also retains an older 7-tier cascade. The Worker should align its cascade with `tools/ollama_lean4_client.py`.

---

## 4. Conclusion & Concrete Code Changes

The Worker must apply the following specific code edits to `tools/ollama_lean4_client.py`:

### Code Change 1: Add Verified Model Cache
At line ~154 of `tools/ollama_lean4_client.py`:
```python
# Cached verified 9B models confirmed to be installed in Ollama daemon
_VERIFIED_INSTALLED_9B_MODELS = set()
```

### Code Change 2: Add Centralized Model Resolver `resolve_model_for_task`
At line ~452 of `tools/ollama_lean4_client.py` (after `detect_best_model`):
```python
def resolve_model_for_task(base_url: str = DEFAULT_OLLAMA_HOST,
                          preferred_tag: Optional[str] = None,
                          dry_run: bool = False,
                          timeout: float = 3.0) -> Tuple[Optional[str], str]:
    """
    Resolves the model to execute for a task under strict 9B policy.
    Guarantees that no forbidden model (12B/27B/70B) or uninstalled model is selected.

    - If dry_run is True:
        * If preferred_tag is supplied:
            - If allowed by 9B policy (is_allowed_9b_model), returns (preferred_tag, reason).
            - If disallowed, prints warning to sys.stderr and redirects to MODEL_PRIORITY_CASCADE[0].
        * If preferred_tag is not supplied, returns (MODEL_PRIORITY_CASCADE[0], reason).
    - If dry_run is False:
        * Always invokes detect_best_model(base_url, preferred_tag=preferred_tag, timeout=timeout).
        * If preferred_tag violates 9B policy or is uninstalled, detect_best_model
          warns and redirects to the installed 9B cascade model.
        * Returns (selected_model, reason).
    """
    if dry_run:
        if preferred_tag:
            if not is_allowed_9b_model(preferred_tag):
                print(
                    f"[WARNING] Model '{preferred_tag}' is disallowed by the strict 9B policy (12B/27B forbidden). Redirecting to optimal 9B model.",
                    file=sys.stderr
                )
                model = MODEL_PRIORITY_CASCADE[0]
                reason = f"Redirected disallowed model '{preferred_tag}' to cascade top '{model}' (dry-run)"
            else:
                model = preferred_tag
                reason = f"Using explicitly requested 9B model: {model} (dry-run)"
        else:
            model = MODEL_PRIORITY_CASCADE[0]
            reason = f"Selected default cascade 9B model: {model} (dry-run)"
        return model, reason

    # Live execution: always query daemon discovery to validate 9B policy and installation
    selected_model, reason, _ = detect_best_model(base_url, preferred_tag=preferred_tag, timeout=timeout)
    if selected_model:
        _VERIFIED_INSTALLED_9B_MODELS.add(selected_model)
    return selected_model, reason
```

### Code Change 3: Defense-in-Depth in `query_ollama`
In `query_ollama` (lines 620–645):
```python
    # Strict 9B policy enforcement and redirection
    if ACTIVE_CONFIG.get("enforce_9b_policy", True):
        if not is_allowed_9b_model(model):
            print(
                f"[WARNING] Model '{model}' violates strict 9B policy (12B/27B forbidden). Redirecting to optimal 9B model.",
                file=sys.stderr
            )
            if dry_run:
                model = MODEL_PRIORITY_CASCADE[0]
            else:
                detected, _, _ = detect_best_model(base_url, timeout=min(timeout, 3.0))
                model = detected or MODEL_PRIORITY_CASCADE[0]
                _VERIFIED_INSTALLED_9B_MODELS.add(model)
        elif not dry_run and model not in _VERIFIED_INSTALLED_9B_MODELS:
            # Check if requested allowed model is actually installed to prevent 404
            detected, _, _ = detect_best_model(base_url, preferred_tag=model, timeout=min(timeout, 3.0))
            if detected:
                model = detected
                _VERIFIED_INSTALLED_9B_MODELS.add(model)
```

### Code Change 4: Refactor `cmd_query`, `cmd_autoformalize`, `cmd_suggest_tactic`
Replace lines 936–947 in `cmd_query`:
```python
    model, reason = resolve_model_for_task(
        base_url=args.host,
        preferred_tag=args.model,
        dry_run=args.dry_run,
        timeout=args.timeout
    )
    if not model:
        if is_json:
            print(json.dumps({"status": "error", "error": f"No suitable model found: {reason}"}, indent=2))
        else:
            print(f"[ERROR] No suitable model found: {reason}")
        return 1
```
Replace lines 990–1001 in `cmd_autoformalize`:
```python
    model, reason = resolve_model_for_task(
        base_url=args.host,
        preferred_tag=args.model,
        dry_run=args.dry_run,
        timeout=args.timeout
    )
    if not model:
        if is_json:
            print(json.dumps({"status": "error", "error": f"No suitable model detected: {reason}"}, indent=2))
        else:
            print(f"[ERROR] No suitable model detected: {reason}")
        return 1
```
Replace lines 1042–1053 in `cmd_suggest_tactic`:
```python
    model, reason = resolve_model_for_task(
        base_url=args.host,
        preferred_tag=args.model,
        dry_run=args.dry_run,
        timeout=args.timeout
    )
    if not model:
        if is_json:
            print(json.dumps({"status": "error", "error": f"No suitable model detected: {reason}"}, indent=2))
        else:
            print(f"[ERROR] No suitable model detected: {reason}")
        return 1
```

### Code Change 5: Add Self-Tests to `run_self_test()`
Add tests 3b and 3c verifying `resolve_model_for_task` and `query_ollama` redirection across `gemma4:12B`, `gemma2:27b`, and `llama3:70b`.

---

## 5. Verification Method

The following exact verification commands must be executed after implementation to confirm that the issue is completely resolved:

### Test 1: Disallowed 12B Model Redirection in Dry-Run
```bash
python3 tools/ollama_lean4_client.py query --model gemma4:12B --prompt "State Hofer's lemma" --dry-run 2> stderr_12b.log
```
**Assertion**:
- `grep -q "disallowed by the strict 9B policy" stderr_12b.log` exits 0.
- Command stdout displays `Dispatching query to 'gemma-lean4:latest'`.
- Command exit code is 0.

### Test 2: Disallowed 27B Model Redirection in Live Run (Zero 404s)
```bash
python3 tools/ollama_lean4_client.py query --model gemma2:27b --prompt "State Hofer's lemma" --timeout 15.0 2> stderr_27b.log
```
**Assertion**:
- `grep -q "disallowed by the strict 9B policy" stderr_27b.log` exits 0.
- Command stdout displays `Dispatching query to 'gemma-lean4:latest'`.
- Command exit code is 0.
- Tail of `~/.ollama/logs/server.log` contains HTTP 200 on `gemma-lean4:latest`, with ZERO 404 status codes.

### Test 3: Autoformalize and Suggest-Tactic CLI Redirection
```bash
python3 tools/ollama_lean4_client.py autoformalize "Let M be a manifold" --model gemma4:12B --dry-run
python3 tools/ollama_lean4_client.py suggest-tactic --goal "⊢ True" --error "none" --model llama3:70b --dry-run
```
**Assertion**: Both commands warn about 9B policy violation and execute with model `gemma-lean4:latest`.

### Test 4: Internal Self-Test Suite Pass
```bash
python3 tools/ollama_lean4_client.py test
```
**Assertion**: Exits with code 0 and reports `ALL SELF-TESTS PASSED SUCCESSFULLY (100% PASS RATE)`.
