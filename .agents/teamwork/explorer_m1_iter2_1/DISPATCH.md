# Dispatch for Remediation Explorer 1 (Milestone 1 Iteration 2)

## Identity
- Type: teamwork_explorer
- Role: 9B Model Policy CLI Remediation Explorer
- Working directory: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m1_iter2_1
- Parent: Phase 5 Orchestrator (8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0)

## Remediation Objective
Investigate how to fix the 9B model policy enforcement in `tools/ollama_lean4_client.py`:
1. In `cmd_query`, `cmd_autoformalize`, `cmd_suggest_tactic`, and `query_ollama`, inspect how `--model` is handled.
2. Ensure that whenever `--model` is supplied, `is_allowed_9b_model(model)` is strictly evaluated.
3. If a forbidden model (e.g. `gemma4:12B`, `gemma2:27b`, `llama3:70b`) or uninstalled model is requested, redirect to the detected allowed 9B model (`gemma-lean4:latest` or `gemma2:9b-instruct-q5_K_M`) with a warning, or cleanly raise an error.
4. Ensure no request to `/api/generate` ever carries a model outside the allowed 9B whitelist.
5. Provide exact patch specifications for the Worker.

## Mandatory Inputs to Read
- ORIGINAL_REQUEST.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md`
- GATE_STATUS.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/orchestrator_phase5/GATE_STATUS.md`
- Reviewer 2 Report: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/reviewer_m1_2/review.md`
- Challenger 1 Report: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/challenger_m1_1/challenge.md`


## 2026-11-04T22:37:59Z
Investigate remediation for 9B policy CLI enforcement in tools/ollama_lean4_client.py:
- Prevent --model from bypassing the 9B check in cmd_query, cmd_autoformalize, cmd_suggest_tactic, and query_ollama.
- Redirect disallowed models (12B/27B/70B) to detected 9B model with a warning.
- Ensure 0 synthetic 404s and no 12B model execution.
Write recommendations to analysis.md and handoff.md and message me.
