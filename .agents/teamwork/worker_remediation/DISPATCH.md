# Dispatch: Worker Remediation (Iteration 2)

## Objective
Apply the exact, concrete remediations identified by Reviewer 2, Challenger 1, Challenger 2, and Auditor 1:

1. **Python 3.6 Argparse Fix in Skill Scripts**:
   - `skills/lean4-symplectic-autoformalizer/scripts/autoformalize.py`
   - `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py`
   - `skills/lean4-proof-repair-engine/scripts/proof_repair.py`
   Remove `required=True` from `parser.add_subparsers(...)`. Check `if not args.subcommand: parser.print_help(); sys.exit(1)`.

2. **Ollama Prover Skill Enhancements (`skills/ollama-lean4-gemma-prover/scripts/ollama_query.py`)**:
   - In `resolve_model()`: return the matched model tag from `available_models` (e.g. return `"gemma2:9b"` when requested `"gemma2"`), not the prefix string.
   - Add `"num_ctx": 8192` to all profiles in `HYPERPARAMETER_PROFILES`.
   - Add `ensure_utf8_streams()` to guarantee UTF-8 output across all locales.

3. **Clean JSON Output in `tools/ollama_lean4_client.py`**:
   - In `cmd_autoformalize`, `cmd_suggest_tactic`, and `cmd_query`: suppress status print statements or send to `sys.stderr` when `args.json` is True, so stdout contains strictly valid parseable JSON.

4. **Thread Safety in `tools/workflow_control.py`**:
   - In `pause()`: include thread id and unique token in temporary file path:
     `temp_path = self.root_dir / f"{SENTINEL_FILENAME}.tmp.{os.getpid()}.{threading.get_ident()}.{uuid.uuid4().hex[:8]}"`
     ensuring thread-safe atomic swaps.

5. **Component Bound Formula in `GROMOV_COMPACTNESS_BLUEPRINT.md`**:
   - Update component bound formula to:
     `|V| <= max(1, 2 * floor(B / h) + k - 2)`
     matching Task G04 of `gromov_compactness.pdf`.

6. **Ghost Stability Documentation in `GromovCompactness/Topology/SphereTree.lean`**:
   - Update docstring for `stable` predicate to explicitly state that `3 <= tree.adj.degree v` applies to unmarked curves ($k = 0$), whereas marked curves are stabilized by `deg(v) + k_v >= 3`.

7. **Verification**:
   - Run `python3 skills/lean4-symplectic-autoformalizer/scripts/autoformalize.py test`
   - Run `python3 skills/ollama-lean4-gemma-prover/scripts/ollama_query.py test`
   - Run `python3 skills/lean4-proof-repair-engine/scripts/proof_repair.py test`
   - Run `python3 tools/test_ollama_pipeline.py`
   - Run `python3 tools/workflow_control.py test`
   - Run `python3 .agents/teamwork/challenger_1/test_runner.py` or verify JSON parsing:
     `python3 -c "import subprocess, json; res = subprocess.run(['python3', 'tools/ollama_lean4_client.py', 'autoformalize', 'Hofer', '--dry-run', '--json'], stdout=subprocess.PIPE, universal_newlines=True); json.loads(res.stdout); print('JSON clean!')"`
   - Run `python3 .agents/teamwork/challenger_2/test_workflow_control_adversarial.py` and verify all tests pass!

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

Write your handoff report to `.agents/teamwork/worker_remediation/handoff.md`.

## 2026-11-03T15:24:07Z
You are assigned as Worker Remediation (Iteration 2).
Your working directory is: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_remediation
Read your dispatch file at: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_remediation/DISPATCH.md
Read the original request at: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md
Read the reports from:
- /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/challenger_1/report.md
- /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/challenger_2/report.md
- /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/reviewer_2/report.md

Implement all 6 remediation items cleanly and rigorously:
1. Fix argparse Python 3.6 compatibility across all 3 skill scripts (`skills/*/scripts/*.py`).
2. Fix model prefix resolution, add `num_ctx: 8192`, and UTF-8 stream guard in `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py`.
3. Fix JSON output cleanliness in `tools/ollama_lean4_client.py` (suppress stdout banners on `--json`).
4. Fix multi-threaded temporary file race condition in `tools/workflow_control.py` using `threading.get_ident()` and `uuid.uuid4()`.
5. Fix component bound formula in `GROMOV_COMPACTNESS_BLUEPRINT.md` to `|V| <= max(1, 2 * floor(B / h) + k - 2)`.
6. Fix docstring in `GromovCompactness/Topology/SphereTree.lean` regarding unmarked vs marked stability.

Execute all unit and stress tests (including `test_workflow_control_adversarial.py` from challenger_2) and verify 100% pass rate!

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

Write your handoff report to:
/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_remediation/handoff.md
Send a message to orchestrator when complete.

## 2026-11-03T15:37:29Z
**Context**: Iteration 2 Remediation.
**Content**: We observed the successful updates in `tools/workflow_control.py` and `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py`.
**Action**: Please let us know if test executions are complete and when handoff.md will be finalized.

