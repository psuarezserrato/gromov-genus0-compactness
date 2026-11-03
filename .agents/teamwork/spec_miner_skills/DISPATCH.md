# Dispatch: Spec Miner Skills

## Objective
Extract detailed specifications for creating reusable agent skills designed to carry out the autoformalization of Gromov Compactness in Lean 4.

## Scope & Tasks
Analyze the requirements in `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md` (R2) and standard agent skill formats (frontmatter YAML, metadata, triggers, operational workflows, inputs/outputs, error handling):
1. **Skill 1: Informal to Lean 4 Autoformalizer** (`lean4-symplectic-autoformalizer` or similar):
   - Translates mathematical definitions, theorems, and proof arguments from Gromov (1985), Ivashkovich-Shevchishin (1999), and symplectic literature into syntactically valid Lean 4 types, structures, and proof skeletons (`sorry` stubs with step-by-step comments).
2. **Skill 2: Local Gemma/Ollama Interface for Lean 4** (`ollama-lean4-gemma-prover` or similar):
   - Queries local Gemma via Ollama API/CLI (`http://localhost:11434`) for premise selection, lemma extraction, and tactic suggestions.
   - Handles prompt engineering tailored for Lean 4, parameter tuning (temperature, num_predict), JSON/raw parsing, and connection validation with fallback detection.
3. **Skill 3: Lean 4 Proof Checking and Repair** (`lean4-proof-repair-engine` or similar):
   - Verifies Lean 4 files, analyzes Lean compiler errors (type mismatch, unknown identifier, unsolved goals), extracts context from Mathlib/TauCeti, and applies iterative repairs.

Extract exact file schemas, workflow diagrams, operational scripts/prompts, and acceptance criteria.
Write your comprehensive report to `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/spec_miner_skills/report.md` and `handoff.md`.

## 2026-11-03T14:23:48Z
You are assigned as Spec Miner Skills for the autoformalization of Gromov Compactness for genus 0 pseudo-holomorphic curves in Lean 4.
Your working directory is: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/spec_miner_skills
Read your dispatch file at: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/spec_miner_skills/DISPATCH.md
Read the original request at: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md

Investigate and specify the 3 required reusable agent skill artifacts:
1. Translating informal mathematical proofs from Gromov (1985), Ivashkovich-Shevchishin (1999), and symplectic literature into Lean 4 formal statements and proof skeletons.
2. Interfacing with local LLMs (Gemma via Ollama at http://localhost:11434) for lemma extraction, tactic search, and premise selection to conserve compute.
3. Checking and repairing formal Lean 4 declarations against Mathlib and TauCeti environments.

For each skill:
- Specify exact YAML frontmatter (name, description), triggers, parameters, operational workflows (step-by-step), input formats, output templates, and error recovery protocols.
- Include actionable prompt designs and script integration patterns.
- Ensure compliance with standard agent skill directory layout (SKILL.md, scripts, examples/references).

Write your full specification report to:
`/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/spec_miner_skills/report.md`
and write a self-contained handoff report to:
`/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/spec_miner_skills/handoff.md`.
Update `progress.md` with your timestamped progress.
When finished, send a message back to the orchestrator.
