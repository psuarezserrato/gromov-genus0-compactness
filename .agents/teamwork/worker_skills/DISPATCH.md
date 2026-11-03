# Dispatch: Worker Skills

## Objective
Author the 3 reusable agent skill packages adhering to standard skill architecture:
1. `skills/lean4-symplectic-autoformalizer/SKILL.md` (+ `scripts/autoformalize.py`, references)
2. `skills/ollama-lean4-gemma-prover/SKILL.md` (+ `scripts/ollama_query.py`, references)
3. `skills/lean4-proof-repair-engine/SKILL.md` (+ `scripts/proof_repair.py`, references)

## Input References
- Original request: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md` (MUST READ FIRST)
- User follow-up document: `/Users/pablosuarez/Desktop/SympTopAutoForm/gromov_compactness.pdf` (MUST READ AND INCORPORATE)
- Project plan: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/PROJECT.md`
- Spec miner skills report: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/spec_miner_skills/report.md`
- Standard skill creator instructions: `/Users/pablosuarez/.gemini/config/plugins/science/skills/workflow_skill_creator/SKILL.md`

## Exclusive File Ownership
You exclusively own and write all files under:
- `/Users/pablosuarez/Desktop/SympTopAutoForm/skills/`
- Metadata only in your directory `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_skills/`

## Requirements & Content Obligations
1. Standard Skill Structure:
   - YAML frontmatter with `name` (lowercase, hyphens, <= 64 chars) and `description` (<= 1024 chars).
   - Clear trigger descriptions (when to use, when not to use).
   - Detailed step-by-step operational workflows.
   - Actionable instructions, prompt designs, error handling, and parameter settings.
2. Skill 1: `lean4-symplectic-autoformalizer`:
   - Translates informal mathematical proofs from Gromov (1985), Ivashkovich-Shevchishin (1999), and `gromov_compactness.pdf` into Lean 4 declarations and structured proof skeletons.
   - Grounded in `Mathlib.Analysis.Hofer` and TauCeti Roadmap.
   - Includes helper script `skills/lean4-symplectic-autoformalizer/scripts/autoformalize.py` with CLI subcommands and tests.
3. Skill 2: `ollama-lean4-gemma-prover`:
   - Queries local Gemma via Ollama API (`http://localhost:11434`) for premise selection, tactic search, and lemma extraction.
   - Features health validation, fallback cascade (`gemma2:9b` -> `gemma2:2b`), parameter tuning matrix, and official Gemma turn syntax.
   - Includes helper script `skills/ollama-lean4-gemma-prover/scripts/ollama_query.py` with offline dry-run and test modes.
4. Skill 3: `lean4-proof-repair-engine`:
   - Closed-loop verification and repair of Lean 4 declarations against Mathlib and TauCeti.
   - Parses `lean --json` diagnostics, categorizes errors (type mismatch, missing instance, unknown identifier, etc.), and executes iterative patch-test loops.
   - Includes helper script `skills/lean4-proof-repair-engine/scripts/proof_repair.py`.

DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

## 2026-11-03T14:34:30Z
You are assigned as Worker Skills for Gromov Compactness Autoformalization in Lean 4.
Your working directory is: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_skills
Read your dispatch file at: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_skills/DISPATCH.md
Read the original request at: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md
Read the PDF specification at: /Users/pablosuarez/Desktop/SympTopAutoForm/gromov_compactness.pdf
Read the spec miner report at: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/spec_miner_skills/report.md
Read the project plan at: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/PROJECT.md

Your exclusive file ownership is all files under:
- /Users/pablosuarez/Desktop/SympTopAutoForm/skills/

Create the 3 reusable agent skills adhering to standard skill structure (frontmatter, description, workflows, triggers, scripts, examples):
1. skills/lean4-symplectic-autoformalizer/SKILL.md (+ scripts/autoformalize.py, references)
2. skills/ollama-lean4-gemma-prover/SKILL.md (+ scripts/ollama_query.py, references)
3. skills/lean4-proof-repair-engine/SKILL.md (+ scripts/proof_repair.py, references)

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

Write your handoff report to:
/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_skills/handoff.md
Send a message to orchestrator when completed.

## 2026-11-03T14:43:18Z
**Context**: Milestone M2 (Reusable Skill Artifacts) for Gromov Compactness in Lean 4.
**Content**: Checking in on progress for authoring the 3 reusable skills:
1. `skills/lean4-symplectic-autoformalizer/SKILL.md`
2. `skills/ollama-lean4-gemma-prover/SKILL.md`
3. `skills/lean4-proof-repair-engine/SKILL.md`
**Action**: Please provide an update on current implementation status and ETA for completion.

## 2026-11-03T14:44:45Z
**Context**: User Follow-up on Gromov Compactness Autoformalization.
**Content**: User instruction update (2026-11-03T14:44:05Z):
"as a first pass, if there is needed result that is not found, as a first pass leave the proofs with 'sorry', so that it can continue with the results that are available. Please ensure this 'sorry'-first-pass strategy (leaving unavailable prerequisite lemmas/proofs as 'sorry' so downstream proofs and declarations can proceed using available results) is incorporated into the autoformalization plan, blueprint, and skills."
**Action**: Incorporate this 'sorry'-first-pass strategy into `skills/lean4-symplectic-autoformalizer/SKILL.md` and `skills/lean4-proof-repair-engine/SKILL.md` (and their helper scripts/templates), so when prerequisite results are missing in Mathlib/TauCeti, the autoformalizer generates candidate declarations with structured `sorry` bodies to keep downstream proofs unblocked.

## 2026-11-03T14:48:39Z
**Context**: Milestone M2 (Reusable Skill Artifacts) for Gromov Compactness in Lean 4.
**Content**: Received your update. Great work incorporating the 'sorry'-first-pass strategy and structuring all 3 skills (`lean4-symplectic-autoformalizer`, `ollama-lean4-gemma-prover`, `lean4-proof-repair-engine`) with their respective `SKILL.md`, `scripts/`, `references/`, and `examples/`.
**Action**: Please proceed to finish all 3 skills, run your test executions, write your handoff report to `.agents/teamwork/worker_skills/handoff.md`, and notify when done.
