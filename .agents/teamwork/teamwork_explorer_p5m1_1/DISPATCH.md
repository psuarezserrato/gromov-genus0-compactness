# Dispatch for Explorer 1 (Milestone 1)

## Identity
- Type: teamwork_explorer
- Role: Local 9B Ollama & Prover Infrastructure Explorer
- Working directory: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/teamwork_explorer_p5m1_1
- Parent: Phase 5 Orchestrator (8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0)

## Objective
Investigate the current Ollama client, model configuration, and Modelfile setup to plan:
1. Strict 9B-only Gemma policy: update `config/ollama_gemma_config.json` and `tools/ollama_lean4_client.py` to query `/api/tags` and restrict strictly to installed 9B models (`gemma-lean4:latest`, `gemma2:9b-instruct-q5_K_M`, `gemma2:9b`, or `gemma4:9B`), eliminating all HTTP 404 cascade calls.
2. Logging every real `/api/generate` proving call to `.agents/gemma_usage.jsonl` (excluding health checks).
3. Rebuilding `Modelfile.gromov-lean4` replacing the old "3DSymFlux" system prompt with a Gromov Compactness / Mathlib v4.16 system prompt + curated accepted proof exemplars, and registering it via `ollama create gemma-lean4:latest -f Modelfile.gromov-lean4`.
4. Check whether local fine-tuning via `mlx_lm` / `peft` is feasible and available in the local environment without exceeding memory.

## Scope Boundaries
- Read-only investigation. Do not edit source files.
- Document concrete recommendations and plan in `analysis.md` and `handoff.md`.

## Mandatory Reading
- ORIGINAL_REQUEST.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md`
- COMPLETION_PLAN.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/COMPLETION_PLAN.md` (specifically §5.1, §5.4, §5.5)
- SCOPE.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/orchestrator_phase5/SCOPE.md`


## 2026-11-04T21:42:32Z
Investigate:
1. Current Ollama setup and installed models (via tools or python checking localhost:11434/api/tags).
2. `config/ollama_gemma_config.json` and `tools/ollama_lean4_client.py` to enforce strict 9B-only policy and eliminate 404s.
3. System prompt in existing Modelfile and design `Modelfile.gromov-lean4` replacing 3DSymFlux with Gromov/Mathlib v4.16 system prompt + exemplars.
4. Logging all proving calls to `.agents/gemma_usage.jsonl`.
5. Availability of local fine-tuning (e.g. mlx_lm / peft) and memory constraints.

Write your report to `analysis.md` and `handoff.md` in your working directory, and message me when finished.
