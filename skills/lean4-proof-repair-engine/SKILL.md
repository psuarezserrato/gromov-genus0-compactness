---
name: lean4-proof-repair-engine
description: >-
  Verifies Lean 4 files using Lake/Lean compiler, parses JSON diagnostics
  (type mismatch, unknown identifier, missing typeclass, unsolved goals),
  extracts localized AST snippets, and executes automated iterative patch-test
  repair loops against Mathlib and TauCeti environments.
---

# Lean 4 Proof Repair Engine

## Overview

The `lean4-proof-repair-engine` skill implements an autonomous, closed-loop compiler-in-the-loop diagnostic parser and automated repair system for Lean 4 theorem proving in symplectic topology.

Key capabilities:
1. **JSON Diagnostic Parsing**: Ingests structured JSON diagnostics directly from `lake env lean --json <file.lean>`.
2. **6-Class Error Taxonomy**: Classifies compiler errors into deterministic categories (`TYPE_MISMATCH`, `UNKNOWN_IDENTIFIER`, `MISSING_TYPECLASS`, `UNSOLVED_GOALS`, `TACTIC_FAILURE`, `MAX_RECURSION`, `SYNTAX_ERROR`).
3. **AST & Local Scope Slicing**: Extracts the exact error locus with 15–20 lines of surrounding declaration context, file header imports, and typeclass binders.
4. **Mathlib & TauCeti Alignment Shims**: Automatically resolves naming mismatches, missing imports, and typeclass requirements (e.g. `[MetricSpace M]`, `[CompleteSpace M]`).
5. **Iterative Auto-Patching Loop**: Applies candidate patches to a sandboxed copy of the source file, re-runs compiler checks, verifies error reduction, and automatically rolls back if error counts regress.
6. **'Sorry'-First-Pass Strategy**: Incorporates explicit user directive (2026-11-03) — when a prerequisite result is unavailable or an error stems from an unfinished deep analytic lemma, stubs the lemma with structured `sorry` bodies to keep downstream proofs unblocked.

---

## Triggers & Invocation Criteria

### Trigger When:
- A `.lean` file produces compilation errors under `lake build` or `lean --json`.
- Type mismatches, unsolved goals, or missing typeclass instances occur during autoformalization.
- Migrating formal proofs across Mathlib 4 releases or TauCeti roadmap updates.
- Verifying whether a patch successfully eliminated errors without regressions.

### Do Not Trigger When:
- Translating informal mathematical text from scratch (use `lean4-symplectic-autoformalizer`).
- Generating exploratory tactics on an open goal without compilation feedback (use `ollama-lean4-gemma-prover`).

---

## Dependencies & Environmental Requirements

- **Lean 4 / Lake Toolchain**: `lake env lean --json` on system PATH (or mock diagnostic mode for offline testing).
- **Mathlib 4**: Pinned repository checkout.
- **Python 3.6+** (Standard library: `argparse`, `json`, `subprocess`, `re`, `pathlib`, `sys`).
- **References**:
  - `references/error_taxonomy_catalog.md`
  - `references/typeclass_resolution_recipes.md`
  - `references/tau_ceti_api_shims.lean`
  - `references/common_mathlib_migration_patterns.md`

---

## Quick Start

### 1. Check a Lean File for Compiler Diagnostics
Execute compiler check and capture structured JSON diagnostics:
```bash
python3 skills/lean4-proof-repair-engine/scripts/proof_repair.py check \
  --file skills/lean4-proof-repair-engine/examples/broken_symplectic_form.lean \
  --output /tmp/diagnostics.json
```

### 2. Classify Compiler Errors
Classify error messages against the 6-class taxonomy:
```bash
python3 skills/lean4-proof-repair-engine/scripts/proof_repair.py classify \
  --error "failed to synthesize instance MetricSpace M" \
  --output /tmp/classification.json
```

### 3. Extract Contextual Code Slice
Slice 15 lines around the error line for LLM repair prompting:
```bash
python3 skills/lean4-proof-repair-engine/scripts/proof_repair.py slice \
  --file skills/lean4-proof-repair-engine/examples/broken_symplectic_form.lean \
  --line 18 \
  --output /tmp/code_slice.json
```

### 4. Execute Iterative Repair Loop
Run the automated repair loop with up to 3 repair iterations:
```bash
python3 skills/lean4-proof-repair-engine/scripts/proof_repair.py repair \
  --file /tmp/working_copy.lean \
  --max-iterations 3 \
  --mock \
  --output /tmp/repair_report.json
```

---

## Operational Workflows

### Workflow 1: Closed-Loop Compilation & Diagnostic Extraction

1. Invoke `lake env lean --json <file.lean>`.
2. Fallback to `lean --json <file.lean>` if Lake is not present.
3. Parse stdout line-by-line; filter records where `"severity": "error"`.
4. Extract `pos.line`, `pos.col`, `endPos`, and `data` (error message).

### Workflow 2: Diagnostic Categorization via 6-Class Error Taxonomy

Map compiler error string to category:
- `TYPE_MISMATCH`: Error mentions `type mismatch` or `has type ... but is expected to have type ...`.
- `UNKNOWN_IDENTIFIER`: Error mentions `unknown identifier` or `did you mean`.
- `MISSING_TYPECLASS`: Error mentions `failed to synthesize instance` (e.g. `MetricSpace`, `TopologicalSpace`).
- `UNSOLVED_GOALS`: Error mentions `unsolved goals`.
- `TACTIC_FAILURE`: Error mentions `tactic ... failed`.
- `MAX_RECURSION`: Error mentions `maximum recursion depth has been reached`.

### Workflow 3: Context-Aware AST Slicing & Symbol Resolution

For each diagnostic record:
1. Capture imports and open namespace statements at file top.
2. Capture lines $[line - 15, line + 15]$.
3. Match unknown identifiers against Mathlib/TauCeti shim databases (e.g. resolving `hofer` $\to$ `Mathlib.Analysis.Hofer.hofer`).
4. Generate repair prompt containing exact code slice, compiler diagnostic, and candidate resolution.

### Workflow 4: Bounded Iterative Auto-Patching with Rollback

1. Create a timestamped backup of the target file.
2. Apply proposed replacement lines to the source file.
3. Re-run `lean --json`.
4. **Evaluation**:
   - If error count decreased: commit patch and continue to next error.
   - If error count == 0: terminate with success report.
   - If error count increased or new errors introduced: revert file from backup and attempt alternative strategy.
5. Limit iteration count to `max_iterations = 3`.

### Workflow 5: 'Sorry'-First-Pass Strategy for Unfinished Analytic Goals

When encountering:
- Deep missing prerequisites (e.g. $W^{1,p}$ elliptic estimates, non-linear bootstrap).
- Complex intermediate steps where tactic search times out.
1. The repair engine replaces the failing tactic block with structured `sorry`:
   ```lean
   -- Step 4: Closed via 'sorry'-first-pass strategy to unblock downstream proof
   sorry
   ```
2. Re-runs compiler check to verify that all syntax, type signatures, and downstream theorems compile cleanly.
3. Flags the `sorry` location in the repair report for tracking.

---

## Utility Script: `scripts/proof_repair.py`

| Subcommand | Description | Arguments |
|------------|-------------|-----------|
| `check` | Runs `lean --json` and writes parsed diagnostics | `--file <path>`, `--output <path>`, `--mock` |
| `classify` | Classifies error strings into taxonomy | `--error <str>`, `--output <path>` |
| `slice` | Extracts code slice around an error line | `--file <path>`, `--line <int>`, `--window <int>`, `--output <path>` |
| `repair` | Executes automated iterative repair loop | `--file <path>`, `--max-iterations <int>`, `--mock`, `--output <path>` |
| `test` | Runs internal test suite | `--output <path>` |

### CLI Example:
```bash
python3 skills/lean4-proof-repair-engine/scripts/proof_repair.py test
```

---

## Common Mistakes & Edge Cases

1. **Typeclass Loop on Metric Instances**:
   - *Mistake*: Adding redundant `[MetricSpace M]` when `[NormedAddCommGroup M]` already provides it.
   - *Fix*: Check Mathlib hierarchy before injecting instances.
2. **Whitespace and Indentation Corruption in 'by' Blocks**:
   - *Mistake*: Patching Lean 4 tactic lines with mismatched indentation.
   - *Fix*: Match line-level indentation of preceding tactic.
3. **Cascading Syntax Errors**:
   - *Mistake*: Fixing downstream errors before resolving a file-header syntax error.
   - *Fix*: Sort errors by line number and resolve the first error first.
