# Dispatch: Explorer Survey Ollama

## Objective
Investigate and design the operational configuration, prompt templates, API client tools, and fallback mechanisms for integrating a local Gemma model via Ollama (`http://localhost:11434`) for Lean 4 autoformalization without requiring external compute.

## Scope & Tasks
Analyze requirement R3 and acceptance criteria:
1. **Ollama Environment & Endpoints**:
   - Connection validation to `http://localhost:11434/api/tags` and `http://localhost:11434/api/generate`.
   - Detection of available Gemma models (`gemma:2b`, `gemma:7b`, `gemma2:2b`, `gemma2:9b`, `gemma2:27b`, or current local models).
   - Graceful fallback strategies when specific model tags are missing or when Ollama service is starting up.
2. **Lean 4 Proof Engineering Prompts**:
   - Specialized prompt structures for:
     a) Informal math -> Lean 4 signature extraction.
     b) Goal-directed tactic suggestion given Lean 4 error message and goal state.
     c) Subgoal lemma extraction.
   - Few-shot examples tailored to Gemma's prompt formatting (`<start_of_turn>user ... <end_of_turn><start_of_turn>model ...`).
3. **Execution Pipeline & CLI Tooling**:
   - Standalone Python / shell scripts or reusable CLI wrappers for running queries, parsing responses, and batching tactic evaluations.
   - Temperature, stop tokens, top_p, and context length configurations optimal for mathematical reasoning.

Write your comprehensive findings to `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_survey_ollama/report.md` and `handoff.md`.


## 2026-11-03T14:23:56Z
Investigate and design:
1. Operational configuration and connection validation for local Ollama on http://localhost:11434.
2. Model tag detection, support, and graceful fallback mechanisms (gemma:2b, gemma:7b, gemma2:2b, gemma2:9b, gemma2:27b, and general local fallback).
3. Concrete CLI / API curl / python invocation commands and parameter settings (temperature, top_p, num_ctx, num_predict, stop tokens) tuned for Lean 4 formal proving and tactic generation.
4. Specific prompt templates and conversation formats for:
   - Informal statement -> Lean 4 formal declaration.
   - Proof step / tactic suggestion from error state.
   - Premise selection from Lean context / Mathlib.
5. Standalone validation script / test pipeline architecture to verify local Gemma proving workflows end-to-end without external internet/compute dependencies.

Write your full investigation report to:
`/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_survey_ollama/report.md`
and write a self-contained handoff report to:
`/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_survey_ollama/handoff.md`.
Update `progress.md` with your timestamped progress.
When finished, send a message back to the orchestrator.
