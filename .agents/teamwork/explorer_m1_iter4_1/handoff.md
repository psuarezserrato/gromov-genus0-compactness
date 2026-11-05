# Explorer Handoff Report: Trailing Comment & Block Delimiter Cleanup

**Author**: `explorer_m1_iter4_1`  
**Role**: Code Exploration & Analysis Agent  
**Date**: 2026-11-04  
**Working Directory**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m1_iter4_1`  
**Recipient**: Parent Orchestrator (`8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0`)  
**Type**: Hard Handoff (Investigation & Architecture Design Complete)  
**Status**: Read-Only Analysis Complete — Ready for Worker Implementation  

---

## 1. Observation

All observations below are directly verified from the codebase, Lean 4 compiler diagnostics, and empirical Python test executions.

### 1.1 The Verbatim Defect in `data/gemma_accepted_proofs.jsonl`
In `data/gemma_accepted_proofs.jsonl`, record index 704 (`tests.ChallengePhase2ModelA.challenge_query_B02`, sourced from `tests/ChallengePhase2ModelA.lean:253-284`) contains invalid Lean 4 syntax.

**Verbatim extracted `"proof"` in record 704**:
```lean
GromovCompactness.Bubbling.exists_calibrated_rescaling I u_seq thresh m_defect hm h_jhol h_defect h_ivt

--------------------------------------------------------------------------------
-- SECTION 2: Certification of Remediation and Invalidation of Failure Modes
--------------------------------------------------------------------------------

/-!
### Certification 1: Non-Triviality of Remediated Contract A04
The old facade 0 ≤ C allowed trivial 3-line proofs ignoring f, p, k, r, R.
In the remediated statements, the conclusion bounds genuine Sobolev seminorms and Hölder norms:
- interior_cauchy_riemann_estimate requires bounding sobolevNorm p (k + 1) f (closedBall 0 r)
  by C times the W^{k, p} norm of \bar\partial f plus the L^p norm of f.
- morrey_sobolev_embedding requires bounding pointwise differences ‖f z - f w‖
  by C (\operatorname{dist} z\ w)^\alpha \|f\|_{W^{1, p}}.
Both definitions now genuinely depend on all functional inputs and derivatives.
```

**Delimiters count in this extracted proof**:
- Opening block comment delimiters (`/-`): **1** (at `/-!`)
- Closing block comment delimiters (`-/`): **0**
- Block comment balance check: **FAIL** (`open = 1, close = 0`)

**Lean 4 Compiler Output**:
Passing this extracted declaration and proof body to `lake env lean --stdin` fails immediately with exit code 1:
```
<stdin>:38:0: error: unterminated comment
```

---

### 1.2 Anatomical Inspection of `tools/build_accepted_proofs_dataset.py:182-196`

The existing implementation of `clean_proof_trailing` is:
```python
def clean_proof_trailing(proof: str) -> str:
    """
    Strips trailing docstrings (/-- ... -/), block comments, section divider lines,
    and trailing empty lines from a harvested proof body.
    """
    proof = re.sub(r'(/--[\s\S]*?-\/\s*)$', '', proof)
    proof = re.sub(r'(/-[\s\S]*?-\/\s*)$', '', proof)
    lines = proof.splitlines()
    while lines:
        last = lines[-1].strip()
        if not last or last.startswith('--') or last.startswith('/-') or last.endswith('-/') or last.startswith('#'):
            lines.pop()
        else:
            break
    return '\n'.join(lines).strip()
```

### 1.3 Step-by-Step Execution Failure on `challenge_query_B02`

In `tests/ChallengePhase2ModelA.lean:263-281`, declaration `challenge_query_B02` is followed by:
1. Proof line: `  GromovCompactness.Bubbling.exists_calibrated_rescaling I u_seq thresh m_defect hm h_jhol h_defect h_ivt`
2. Divider lines: `--------------------------------------------------------------------------------`
3. Section comment: `-- SECTION 2: Certification of Remediation and Invalidation of Failure Modes`
4. Divider lines: `--------------------------------------------------------------------------------`
5. Empty line
6. Module docstring start: `/-!`
7. Module docstring text: `### Certification 1 ...` (lines 270–277)
8. Module docstring close: `-/` (line 278)
9. Empty line (line 279)
10. Line comment: `-- Sobolev norms evaluate non-trivially on non-zero constant functions:` (line 280)
11. Next declaration: `theorem challenge_remediation_A04_sobolev_norm_well_defined ...` (line 281)

Because `cmd_boundary_pat` does not recognize `/-!` module docstrings or section dividers as a boundary, it cuts at line 281, sending all of items 1–10 into `clean_proof_trailing` as `proof`.

Here is the exact line-by-line trace through `clean_proof_trailing`:
1. `proof = re.sub(r'(/--[\s\S]*?-\/\s*)$', '', proof)`:
   The end of `proof` is `-- Sobolev norms evaluate...` (a line comment), NOT `-/`. The regex anchored at `$` fails to match.
2. `proof = re.sub(r'(/-[\s\S]*?-\/\s*)$', '', proof)`:
   Again, fails to match because the trailing line is `-- Sobolev norms...`.
3. `lines = proof.splitlines()`:
   The list of lines ends with:
   - Line 277: `Both definitions now genuinely depend on all functional inputs and derivatives.`
   - Line 278: `-/`
   - Line 279: ` `
   - Line 280: `-- Sobolev norms evaluate non-trivially on non-zero constant functions:`
4. The loop `while lines:` executes:
   - **Iteration 1**: `last` is line 280 (`-- Sobolev norms...`). `last.startswith('--')` is True. `lines.pop()` drops line 280.
   - **Iteration 2**: `last` is line 279 (` `). `not last` is True. `lines.pop()` drops line 279.
   - **Iteration 3**: `last` is line 278 (`-/`). `last.endswith('-/')` is True. `lines.pop()` drops line 278!
   - **Iteration 4**: `last` is line 277 (`Both definitions now genuinely depend on all functional inputs and derivatives.`).
     - `not last`: False
     - `last.startswith('--')`: False
     - `last.startswith('/-')`: False
     - `last.endswith('-/')`: False
     - `last.startswith('#')`: False
     **All conditions are False. The `else: break` branch executes. The loop terminates!**
5. Result: The closing delimiter `-/` has been popped off, but lines 269–277 (`/-!` through docstring body) remain.
6. The resulting string is returned as the "clean" proof body, corrupted with an unterminated block comment.

---

### 1.4 Critical Secondary Finding: Divider Regex Danger on `[-=]{5,}`

During empirical testing of challenger-proposed regexes on the entire codebase, a critical secondary defect was discovered:
In `tests/ChallengeMilestone5Rescaling.lean:145-147`, there is a section block comment:
```lean
/- =========================================================================
   CATEGORY 2: ASYMPTOTIC CONVERGENCE OF MOVING CENTERS AND RADII
   ========================================================================= -/
```
If a divider regex is written with unconstrained trailing characters such as:
`re.sub(r'(\n\s*[-=]{5,}[^\n]*)+$', '', proof)`
The pattern `[-=]{5,}[^\n]*` matches the line `   ========================================================================= -/`, because `[^\n]*` consumes the closing delimiter ` -/`!
Popping that line deletes `-/` and leaves `/- =========================================================================` unterminated!
**Key Invariant**: Section divider lines must be strictly constrained to lines that consist **exclusively** of dashes or equals signs and optional whitespace:
`^[ \t]*[-=]{5,}[ \t]*$`

---

## 2. Logic Chain

1. **Why Line-by-Line Popping Breaks on Block Comments**:
   A block comment in Lean 4 is inherently multiline and delimited by an opening token (`/-`, `/--`, `/-!`) and a closing token (`-/`). Popping from the bottom inspects one line at a time. Once line-popping consumes the single line containing `-/' (line 278), the preceding lines are ordinary English text lines from the comment body. Because ordinary text lines do not start with `--` or end with `-/`, a line-by-line loop is structurally blind to multiline context and must either halt prematurely (leaving the opening `/-` unclosed) or pop valid code lines. Line-by-line popping of multiline delimiters is fundamentally unsound.

2. **Why Single-Pass Regex Fails When Interleaved**:
   In theorem development files, proof endings and subsequent declaration headers are commonly separated by an arbitrary sequence of:
   - Trailing whitespace
   - Single-line comments (`-- ...`)
   - Section divider rules (`----------------------------------------`)
   - Module docstrings (`/-! ... -/`)
   - Docstrings (`/-- ... -/`)
   - Directives (`#check ...`)
   A single-pass regex anchored at the end of the string (`$`) fails whenever element types are interleaved (e.g. `-- line` after `/-! ... -/`).

3. **Mathematical Solution: Iterative Fixpoint with Depth Tracking**:
   The correct architectural model is an **iterative backward fixpoint**:
   - In each cycle, strip trailing whitespace (`.rstrip()`).
   - Strip any trailing line comments (`-- ...`).
   - Strip any trailing pure section dividers (`[-=]{5,}`).
   - Strip any trailing Lean check commands (`#\w+ ...`).
   - If the string ends with a closing block delimiter `-/`, perform a backward character scan tracking nested block depth:
     - Each `-/` increments `depth` by 1.
     - Each `/-` decrements `depth` by 1.
     - When `depth == 0`, the exact opening delimiter has been located, and the entire block comment is sliced off in $O(K)$ time.
     - This naturally handles `/--`, `/-!`, `/-`, and nested block comments `/- outer /- inner -/ outer -/`.
   - Repeat until `proof == prev` (a clean fixpoint is reached).

4. **Integration of Block Comment Balance Check into Substantive Proof Validation**:
   - In `tools/build_accepted_proofs_dataset.py`, `mask_comments(content)` and `mask_comments_and_strings(content)` track comment depth. If a block comment is unterminated, `mask_comments` silently masks everything to the end of the file/chunk with spaces!
   - Consequently, `is_substantive_proof` and delimiter checks evaluated on masked content remain completely unaware of the unterminated block comment.
   - Enforcing `proof.count("/-") == proof.count("-/")` inside `is_substantive_proof` *before* comment masking immediately catches any unclosed or malformed block comments and rejects the invalid record.
   - Furthermore, adding `proof.count("/-") == proof.count("-/")` to `slice_source_proof` and `harvest_test_proofs` provides absolute defense in depth.

---

## 3. Caveats

1. **Top-Level Commands vs Trailing Comments**:
   `clean_proof_trailing` is responsible for removing comments, dividers, and directives trailing a proof body. It is NOT responsible for parsing syntax when non-comment commands (such as `set_option`) are leaked by `cmd_boundary_pat`. That issue is resolved by updating `cmd_boundary_pat` to include `set_option`.
2. **Lean 4 Block Comment Lexing**:
   In Lean 4's official lexer, block comments do not evaluate nested string literals (e.g. `/- "-/" -/` fails with an unterminated string literal in Lean 4). Therefore, standard depth-tracking `/-` vs `-/` exactly matches Lean 4's block comment grammar.
3. **Obsolete Tests**:
   Corrupted assertions in obsolete test files (`tests/ChallengeGeometry.lean`) are an issue of mathematical validity of test suites, distinct from the comment cleaning pipeline.

---

## 4. Conclusion & Concrete Recommended Code

The defect in `tools/build_accepted_proofs_dataset.py` can be fully, cleanly, and safely resolved by replacing `clean_proof_trailing` and updating `is_substantive_proof`.

### 4.1 Implementation Specification

#### Component 1: `strip_trailing_block_comment`
Add this helper function immediately above `clean_proof_trailing`:
```python
def strip_trailing_block_comment(s: str) -> str:
    """
    If the string ends with a closing block comment delimiter '-/',
    scans backward tracking nested depth to find the matching '/-',
    and strips the entire block comment.
    Handles /-- docstrings, /-! module docstrings, /- block comments,
    and nested block comments.
    """
    s = s.rstrip()
    if not s.endswith("-/"):
        return s
    depth = 0
    i = len(s)
    while i >= 2:
        if s[i-2:i] == "-/":
            depth += 1
            i -= 2
        elif s[i-2:i] == "/-":
            depth -= 1
            i -= 2
            if depth == 0:
                return s[:i].rstrip()
        else:
            i -= 1
    return s
```

#### Component 2: Iterative Fixpoint `clean_proof_trailing`
Replace lines 182–196 of `tools/build_accepted_proofs_dataset.py` with:
```python
def clean_proof_trailing(proof: str) -> str:
    """
    Iterative fixpoint backward cleaner for harvested proof bodies.
    Robustly removes trailing whitespace, line comments (-- ...),
    section divider lines (-{5,} or ={5,}), compiler check directives (#check, etc.),
    and all forms of Lean block comments (/- ... -/, /-- ... -/, /-! ... -/)
    including nested block comments.
    """
    while True:
        prev = proof
        proof = proof.rstrip()

        # 1. Strip trailing line comments (-- ...)
        proof = re.sub(r'((?:^|\n)[ \t]*--[^\n]*)+$', '', proof).rstrip()

        # 2. Strip trailing section divider lines that consist ONLY of - or =
        proof = re.sub(r'((?:^|\n)[ \t]*[-=]{5,}[ \t]*)+$', '', proof).rstrip()

        # 3. Strip trailing Lean commands (#check, #eval, etc.)
        proof = re.sub(r'((?:^|\n)[ \t]*#\w+[^\n]*)+$', '', proof).rstrip()

        # 4. Strip trailing block comments (/-, /--, /-!, and nested /-)
        stripped_bc = strip_trailing_block_comment(proof)
        if stripped_bc != proof:
            proof = stripped_bc.rstrip()

        if proof == prev:
            break

    return proof.strip()
```

#### Component 3: Block Comment Balance Verification in `is_substantive_proof`
Update `is_substantive_proof` (lines 199–221 of `tools/build_accepted_proofs_dataset.py`) to include:
```python
def is_substantive_proof(proof: str) -> bool:
    """
    Verifies that a proof body has substantive tactic or term content.
    Rejects:
    - Empty or whitespace-only proofs
    - Proofs that are just 'by' (even if followed by comments)
    - Truncated syntax fragments (e.g. 'M)')
    - Proofs containing sorry or admit
    - Proofs with unbalanced block comments (e.g. unclosed /- or -/)
    """
    if not proof or not proof.strip():
        return False
    if proof.strip() in ['by', 'M)', '']:
        return False

    # Strictly reject unbalanced block comments (e.g. unclosed /-, /-!, /--)
    if proof.count("/-") != proof.count("-/"):
        return False

    code_only = mask_comments(proof).strip()
    if not code_only or code_only == 'by':
        return False
    if re.match(r'^by\b', code_only):
        tactic_part = re.sub(r'^by\b', '', code_only).strip()
        if not tactic_part:
            return False
    if proof.startswith((")", "]", "}", ":", "|")):
        return False
    return True
```

#### Component 4: Defense-in-Depth Delimiter Checks in `slice_source_proof` and `harvest_test_proofs`
In `slice_source_proof`:
```python
    p_masked = mask_comments_and_strings(proof)
    if (p_masked.count("(") != p_masked.count(")") or
        p_masked.count("[") != p_masked.count("]") or
        p_masked.count("{") != p_masked.count("}") or
        proof.count("/-") != proof.count("-/")):
        return "", ""
```

In `harvest_test_proofs`:
```python
    p_masked = mask_comments_and_strings(clean_proof)
    if (p_masked.count("(") != p_masked.count(")") or
        p_masked.count("[") != p_masked.count("]") or
        p_masked.count("{") != p_masked.count("}") or
        clean_proof.count("/-") != clean_proof.count("-/")):
        continue
```

---

### 4.2 Empirical Verification of Recommended Code Across the Entire Repository

An empirical simulation testing this exact design against all 908 declarations in the project established:
- **Library proofs (395 records)**: **0 altered** (100% byte-identical preservation).
- **Test proofs (513 records)**: **Exactly 1 record altered** (`tests.ChallengePhase2ModelA.challenge_query_B02`), which changed from 991 characters (corrupted with section comments and unclosed `/-!`) to 103 characters:
  `GromovCompactness.Bubbling.exists_calibrated_rescaling I u_seq thresh m_defect hm h_jhol h_defect h_ivt`
- **Lean 4 compilation of cleaned `challenge_query_B02`**: Exit code **0** (verified clean with `lake env lean`).
- **Unbalanced block comment count across entire dataset**: **0**.

---

## 5. Verification Method

Any agent can independently verify this design with the following self-contained commands:

### Command 1: Unit Test Harness for `clean_proof_trailing` and Edge Cases
```bash
python3 -c "
import re

def strip_trailing_block_comment(s: str) -> str:
    s = s.rstrip()
    if not s.endswith('-/'):
        return s
    depth = 0
    i = len(s)
    while i >= 2:
        if s[i-2:i] == '-/':
            depth += 1
            i -= 2
        elif s[i-2:i] == '/-':
            depth -= 1
            i -= 2
            if depth == 0:
                return s[:i].rstrip()
        else:
            i -= 1
    return s

def clean_proof_trailing(proof: str) -> str:
    while True:
        prev = proof
        proof = proof.rstrip()
        proof = re.sub(r'((?:^|\n)[ \t]*--[^\n]*)+$', '', proof).rstrip()
        proof = re.sub(r'((?:^|\n)[ \t]*[-=]{5,}[ \t]*)+$', '', proof).rstrip()
        proof = re.sub(r'((?:^|\n)[ \t]*#\w+[^\n]*)+$', '', proof).rstrip()
        stripped_bc = strip_trailing_block_comment(proof)
        if stripped_bc != proof:
            proof = stripped_bc.rstrip()
        if proof == prev:
            break
    return proof.strip()

tests = [
    ('Simple rfl', 'by\n  rfl', 'by\n  rfl'),
    ('Trailing spaces', 'by\n  rfl\n\n   \t\n', 'by\n  rfl'),
    ('Single line comment', 'rfl\n-- comment', 'rfl'),
    ('Multiple line comments', 'rfl\n-- c1\n-- c2', 'rfl'),
    ('Section divider lines', 'rfl\n--------------------\n-- SECTION 2\n--------------------', 'rfl'),
    ('Module docstring', 'rfl\n/-!\n### Header\nText\n-/', 'rfl'),
    ('Docstring', 'rfl\n/-- docstring -/', 'rfl'),
    ('Nested block comments', 'rfl\n/- outer /- inner -/ outer -/', 'rfl'),
    ('Interleaved comments and dividers', 'rfl\n/-! c1 -/\n------------\n/- c2 -/\n-- line', 'rfl'),
    ('Preserve block comment inside proof', 'by\n  /- inner -/\n  rfl', 'by\n  /- inner -/\n  rfl'),
    ('Preserve line comment inside proof', 'by\n  -- inner\n  rfl', 'by\n  -- inner\n  rfl'),
    ('Category divider block comment', 'by\n  simp\n\n/- ==========================================\n   SECTION\n   ========================================== -/\n', 'by\n  simp'),
]

for name, inp, exp in tests:
    res = clean_proof_trailing(inp)
    assert res == exp, f'Test {name} failed: got {repr(res)}, expected {repr(exp)}'
print('All 12 edge case tests passed successfully!')
"
```

### Command 2: Verify Clean Compilation of `challenge_query_B02` Under Lean 4
```bash
python3 -c "
import subprocess
cleaned_proof = 'GromovCompactness.Bubbling.exists_calibrated_rescaling I u_seq thresh m_defect hm h_jhol h_defect h_ivt'
code = f'''
import GromovCompactness
open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness
open GromovCompactness.Analysis
open GromovCompactness.Bubbling
variable {{E : Type*}} [NormedAddCommGroup E] [NormedSpace ℝ E] {{H : Type*}} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {{M : Type*}} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
theorem challenge_query_B02
    (u_seq : ℕ → (CP1 → M)) (thresh : GromovCompactness.Bubbling.TargetThresholds I M)
    (m_defect : ℝ) (hm : thresh.h ≤ m_defect)
    (h_jhol : ∀ (n : ℕ), JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_defect : ∀ (n : ℕ), ∃ (a_n : ℂ) (R_n : ℝ),
      dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
      0 < R_n ∧ R_n ≤ 1 / ((n : ℝ) + 1) ∧
      m_defect - thresh.h / 2 ≤ energyMeasure I (u_seq n) (disk_at a_n R_n))
    (h_ivt : GromovCompactness.Bubbling.RadialEnergyIVT I (M := M)) :
    Nonempty (GromovCompactness.Bubbling.CalibratedRescaling I u_seq thresh m_defect) :=
  {cleaned_proof}
'''
res = subprocess.run(['lake', 'env', 'lean', '--stdin'], input=code, text=True, capture_output=True)
assert res.returncode == 0, f'Lean compilation failed with: {res.stdout}\n{res.stderr}'
print('Lean 4 compilation of cleaned proof succeeded with returncode 0!')
"
```
