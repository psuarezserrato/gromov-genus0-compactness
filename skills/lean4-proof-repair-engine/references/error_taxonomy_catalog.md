# Lean 4 Compiler Error Taxonomy & Repair Catalog

Authoritative catalog of compiler diagnostic categories, regular expressions, common root causes, and standard remediation recipes.

---

## 1. Error Categories & Regex Matchers

### 1. `TYPE_MISMATCH`
- **Regex Patterns:**
  - `type mismatch`
  - `has type\b.*?but is expected to have type`
  - `cannot synthesize\b.*?type mismatch`
- **Root Cause:** Unification failure between inferred type and expected type, often caused by missing type coercions, dimension mismatches, or swapped arguments.
- **Remediation:**
  - Inject explicit type ascriptions `(x : T)`.
  - Check implicit argument order in theorem application.
  - On 'sorry'-first-pass: stub the problematic expression with `sorry` to preserve surrounding proof flow.

### 2. `UNKNOWN_IDENTIFIER`
- **Regex Patterns:**
  - `unknown identifier\b`
  - `did you mean\b`
  - `unknown constant\b`
- **Root Cause:** Missing module import, obsolete Mathlib 3 naming, or missing `open` namespace.
- **Remediation:**
  - Add required import (e.g. `import Mathlib.Analysis.Hofer`).
  - Prefix with fully qualified namespace (e.g. `Mathlib.Analysis.Hofer.hofer`).
  - Add namespace opening `open Metric Set Filter`.

### 3. `MISSING_TYPECLASS`
- **Regex Patterns:**
  - `failed to synthesize instance\b`
  - `failed to synthesize\b.*?MetricSpace`
  - `failed to synthesize\b.*?TopologicalSpace`
- **Root Cause:** Typeclass instance resolution exhausted search without finding required algebraic or topological structure.
- **Remediation:**
  - Add instance binder to variable or theorem signature (e.g. `[MetricSpace M] [CompleteSpace M]`).
  - Check typeclass inheritance (e.g. `[NormedAddCommGroup E]` automatically implies `[MetricSpace E]`).

### 4. `UNSOLVED_GOALS`
- **Regex Patterns:**
  - `unsolved goals\b`
  - `declaration has 'sorry'`
  - `goals accomplished.*?\bextra`
- **Root Cause:** Tactic block finished with remaining subgoals, or tactic succeeded partially.
- **Remediation:**
  - Apply terminal tactics: `linarith`, `ring`, `positivity`, `assumption`.
  - In 'sorry'-first-pass mode: conclude goal with structured `sorry`.

### 5. `TACTIC_FAILURE`
- **Regex Patterns:**
  - `tactic '.*?' failed`
  - `tactic failed\b`
  - `linarith failed`
  - `ring failed`
  - `simp made no progress`
- **Root Cause:** Hypothesis prerequisites for tactic not satisfied (e.g. `linarith` called on non-linear equality).
- **Remediation:**
  - Replace tactic with `obtain`, `cases`, `rcases`, or manual rewrite `rw`.

### 6. `MAX_RECURSION`
- **Regex Patterns:**
  - `maximum recursion depth has been reached`
  - `deep recursion detected`
- **Root Cause:** Cyclic typeclass instances or infinite macro expansion.
- **Remediation:**
  - Increase recursion limit: `set_option maxRecDepth 200000`.
  - Break cyclic instance declarations by converting to explicit definitions.
