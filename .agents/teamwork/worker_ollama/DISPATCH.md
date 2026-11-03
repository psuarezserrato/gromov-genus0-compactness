# Dispatch: Worker Ollama

## Objective
Author the operational local Gemma and Ollama execution tooling, configuration, and verification pipeline:
1. `/Users/pablosuarez/Desktop/SympTopAutoForm/tools/ollama_lean4_client.py`
2. `/Users/pablosuarez/Desktop/SympTopAutoForm/tools/test_ollama_pipeline.py`
3. `/Users/pablosuarez/Desktop/SympTopAutoForm/config/ollama_gemma_config.json`
4. `/Users/pablosuarez/Desktop/SympTopAutoForm/docs/OLLAMA_GEMMA_INTEGRATION.md`

## Input References
- Original request: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md` (MUST READ FIRST)
- User follow-up document: `/Users/pablosuarez/Desktop/SympTopAutoForm/gromov_compactness.pdf`
- Project plan: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/PROJECT.md`
- Survey Ollama report: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_survey_ollama/report.md`
- Working client prototype: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_survey_ollama/ollama_lean4_client.py`

## Exclusive File Ownership
You exclusively own and write:
- All files under `/Users/pablosuarez/Desktop/SympTopAutoForm/tools/`
- All files under `/Users/pablosuarez/Desktop/SympTopAutoForm/config/`
- `/Users/pablosuarez/Desktop/SympTopAutoForm/docs/OLLAMA_GEMMA_INTEGRATION.md`
- Metadata only in your directory `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_ollama/`

## Requirements & Content Obligations
1. Implement a complete, zero-external-dependency Python tool `tools/ollama_lean4_client.py`:
   - Full CLI interface: `health`, `list-models`, `query`, `autoformalize`, `suggest-tactic`, `test`.
   - Built-in connection check against `http://localhost:11434/api/tags` and `http://localhost:11434/api/generate`.
   - Multi-tier model fallback cascade (`gemma2:9b` -> `gemma2:27b` -> `gemma:7b` -> `gemma2:2b` -> `gemma:2b` -> local fallback -> dry-run mock).
   - Specialized prompt templates using Gemma turn tokens (`<start_of_turn>`, `<end_of_turn>`).
   - Hyperparameter management via `config/ollama_gemma_config.json`.
   - Offline dry-run and self-test suite mode.
2. Implement test harness `tools/test_ollama_pipeline.py` and run it via python3 to verify 100% test pass rate.
3. Write comprehensive documentation in `docs/OLLAMA_GEMMA_INTEGRATION.md` detailing:
   - Ollama installation and setup on macOS.
   - CLI and API curl commands.
   - Prompt engineering for Lean 4 theorem proving.
   - Connectivity verification and error troubleshooting.
4. Execute your test harness and record command outputs in your handoff report.

DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.


## 2026-11-03T14:34:40Z
You are assigned as Worker Ollama for Local Gemma & Ollama Pipeline Integration.
Your working directory is: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_ollama
Read your dispatch file at: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_ollama/DISPATCH.md
Read the original request at: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md
Read the survey Ollama report at: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_survey_ollama/report.md
Read the prototype script at: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_survey_ollama/ollama_lean4_client.py
Read the project plan at: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/PROJECT.md

Your exclusive file ownership is:
- All files under /Users/pablosuarez/Desktop/SympTopAutoForm/tools/
- All files under /Users/pablosuarez/Desktop/SympTopAutoForm/config/
- /Users/pablosuarez/Desktop/SympTopAutoForm/docs/OLLAMA_GEMMA_INTEGRATION.md

Implement:
1. /Users/pablosuarez/Desktop/SympTopAutoForm/tools/ollama_lean4_client.py:
   - Zero-external-dependency, standard library urllib/json tool.
   - Built-in connection check against http://localhost:11434/api/tags and /api/generate.
   - 7-tier model fallback cascade (gemma2:9b -> gemma2:27b -> gemma:7b -> gemma2:2b -> gemma:2b -> local fallback -> dry-run mock).
   - Official Gemma turn formatting (<start_of_turn>, <end_of_turn>).
   - CLI subcommands: health, list-models, query, autoformalize, suggest-tactic, test.
2. /Users/pablosuarez/Desktop/SympTopAutoForm/tools/test_ollama_pipeline.py:
   - Complete self-test suite covering health checks, model cascades, parameter profiles, dry-run queries, and error handling.
   - Execute the test suite and verify 100% pass rate!
3. /Users/pablosuarez/Desktop/SympTopAutoForm/config/ollama_gemma_config.json:
   - Full configuration file with endpoints, models, hyperparameters, and prompts.
4. /Users/pablosuarez/Desktop/SympTopAutoForm/docs/OLLAMA_GEMMA_INTEGRATION.md:
   - Complete setup guide, CLI/curl examples, prompt templates, and troubleshooting.

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

Write your handoff report to:
/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_ollama/handoff.md
Send a message to orchestrator when completed.


## 2026-11-03T14:45:02Z
**Context**: Milestone M3 (Local Gemma & Ollama Pipeline Integration).
**Content**: Checking in on progress for `worker_ollama`. We observed `tools/ollama_lean4_client.py`, `tools/test_ollama_pipeline.py`, and `config/ollama_gemma_config.json`.
**Action**: Please report status on test execution, authoring of `docs/OLLAMA_GEMMA_INTEGRATION.md`, and completion of `handoff.md`.
