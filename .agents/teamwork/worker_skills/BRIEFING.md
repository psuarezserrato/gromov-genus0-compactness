# BRIEFING — 2026-11-03T14:35:00Z

## Mission
Author 3 production-grade, reusable agent skills for Lean 4 symplectic autoformalization, local Gemma/Ollama proof search, and automated proof repair incorporating Gromov (1985), Ivashkovich-Shevchishin (1999), and gromov_compactness.pdf.

## 🔒 My Identity
- Archetype: worker
- Roles: implementer, qa, specialist
- Working directory: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_skills
- Original parent: 19c37018-f3f0-48c7-a9ab-498269531593
- Milestone: M2 (Reusable Skill Artifacts)

## 🔒 Key Constraints
- Exclusively own and write to /Users/pablosuarez/Desktop/SympTopAutoForm/skills/
- Metadata only in /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_skills/
- DO NOT CHEAT: Genuine implementations only, no hardcoded test results, no facade implementations, real logic and error handling.
- Must strictly incorporate gromov_compactness.pdf, Gromov 1985, Ivashkovich-Shevchishin 1999, Mathlib (e.g. Mathlib.Analysis.Hofer), and TauCeti Roadmap.
- Each skill must adhere to standard skill structure: YAML frontmatter (name <= 64, description <= 1024), triggers, detailed workflows, scripts, references, examples.

## Current Parent
- Conversation ID: 19c37018-f3f0-48c7-a9ab-498269531593
- Updated: not yet

## Task Summary
- **What to build**:
  1. `skills/lean4-symplectic-autoformalizer/SKILL.md` (+ `scripts/autoformalize.py`, references, examples)
  2. `skills/ollama-lean4-gemma-prover/SKILL.md` (+ `scripts/ollama_query.py`, references, examples)
  3. `skills/lean4-proof-repair-engine/SKILL.md` (+ `scripts/proof_repair.py`, references, examples)
- **Success criteria**:
  - Reusable agent skills following standard specification.
  - Fully working executable Python scripts (`autoformalize.py`, `ollama_query.py`, `proof_repair.py`) with rich subcommands, offline/dry-run test modes, real parsing/classification logic.
  - Comprehensive reference files and examples covering Gromov compactness, Hofer's lemma, Ollama configurations, and Lean 4 diagnostics.
- **Interface contracts**: PROJECT.md, spec_miner_skills/report.md, gromov_compactness.pdf
- **Code layout**: /Users/pablosuarez/Desktop/SympTopAutoForm/skills/

## Key Decisions Made
- Build standalone executable CLI scripts with test/dry-run capabilities so that the test suite and auditor can test them offline as well as online.
- Incorporate exact contract definitions and mathematical objects from gromov_compactness.pdf (F00-F06, A01-A12, C01-C03, B01-B07, G01-G05, E01-E05) into skills/lean4-symplectic-autoformalizer.

## Artifact Index
- skills/lean4-symplectic-autoformalizer/SKILL.md — Main skill instructions for translating informal symplectic proofs to Lean 4.
- skills/lean4-symplectic-autoformalizer/scripts/autoformalize.py — CLI tool for autoformalization and skeleton generation.
- skills/ollama-lean4-gemma-prover/SKILL.md — Main skill instructions for querying local Gemma models via Ollama.
- skills/ollama-lean4-gemma-prover/scripts/ollama_query.py — CLI tool for Ollama Gemma querying with offline mock and healthcheck.
- skills/lean4-proof-repair-engine/SKILL.md — Main skill instructions for automated Lean 4 diagnostic parsing and repair.
- skills/lean4-proof-repair-engine/scripts/proof_repair.py — CLI tool for Lean 4 compiler error classification and iterative repair.

## Change Tracker
- **Files modified**:
  - `skills/lean4-symplectic-autoformalizer/` (SKILL.md, autoformalize.py, references, examples) — Symplectic autoformalizer adhering to Gromov (1985), Ivashkovich-Shevchishin (1999), gromov_compactness.pdf, and Mathlib.Analysis.Hofer.
  - `skills/ollama-lean4-gemma-prover/` (SKILL.md, ollama_query.py, references, examples) — Local Gemma/Ollama theorem proving interface with model cascade and parameter matrix.
  - `skills/lean4-proof-repair-engine/` (SKILL.md, proof_repair.py, references, examples) — Compiler-in-the-loop diagnostic parser and automated repair engine with 'sorry'-first-pass.
- **Build status**: All self-test suites passing (100% pass across autoformalize.py, ollama_query.py, proof_repair.py).
- **Pending issues**: none

## Quality Status
- **Build/test result**: PASS. All CLI test commands executed with exit code 0.
- **Lint status**: 0 violations. Code adheres strictly to Python stdlib.
- **Tests added/modified**: Built-in test suites in each CLI script (`autoformalize.py test`, `ollama_query.py test`, `proof_repair.py test`).

## Loaded Skills
- **Source**: /Users/pablosuarez/.gemini/config/plugins/science/skills/workflow_skill_creator/SKILL.md
- **Local copy**: None (standard system skill)
- **Core methodology**: Distill workflows into standard skills with YAML frontmatter, triggers, operational steps, scripts, and references.
