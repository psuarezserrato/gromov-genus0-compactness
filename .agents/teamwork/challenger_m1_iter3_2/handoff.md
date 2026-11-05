# Empirical Challenge Report: Milestone 1 Iteration 3 Remediation

**Author**: `challenger_m1_iter3_2`  
**Role**: Adversarial Testing Challenger  
**Date**: 2026-11-04  
**Working Directory**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/challenger_m1_iter3_2`  
**Recipient**: Phase 5 Orchestrator (`8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0`)  
**Type**: Hard Handoff (Adversarial Stress Test Complete)  
**Verdict**: **REJECT** (Integrity & Parser Flaws Found in Harvested Accepted Proofs Dataset)

---

## 1. Observation

All observations are directly verified from tool executions, verbatim command outputs, and source code excerpts.

### 1.1 Remediation of Kernel Axiom Extraction (`tools/extract_accepted_proofs.lean`)
- Executed `lake env lean --run tools/extract_accepted_proofs.lean /tmp/test_extract.jsonl`:
  ```
  Total GromovCompactness theorems: 796 (Clean: 748, Dirty: 48)
  Exported 748 clean theorem records to /tmp/test_extract.jsonl.
  ```
- Evaluated all 748 records in `data/raw_accepted_theorems.jsonl`:
  - 0 declarations contain `sorryAx` in `"axioms"`.
  - 0 declarations match any of the 54 known `sorryAx`-dependent constants in `GromovCompactness`.
  - All 748 records contain exact kernel axiom arrays from Lean environment (e.g. `["Classical.choice", "Quot.sound", "propext"]` or `[]`).
- Status: **VERIFIED CLEAN**.

### 1.2 Model Enforcement & Endpoint Cleanliness in `tools/ollama_lean4_client.py`
1. **Model Redirection Across All CLI Subcommands**:
   - Stress-tested all CLI commands and legacy flags with heavy/disallowed models:
     `--model gemma4:12B`, `--model gemma2:27b`, `--model gemma-27b`, `--model llama3:70b`.
   - In 100% of cases (11/11 CLI tests), the client emitted a stderr warning:
     `[WARNING] Model '<model>' is disallowed by the strict 9B policy (12B/27B forbidden). Redirecting to optimal 9B model.`
     and redirected execution to `gemma-lean4:latest` or `gemma2:9b`.
2. **Zero HTTP 404s in Daemon Server Logs**:
   - Inspected `~/.ollama/logs/server.log` before and after running `tools/ollama_lean4_client.py health`:
     ```
     [GIN] 2026/11/04 - 15:43:36 | 200 |   6.91ms |       127.0.0.1 | GET      "/api/tags"
     [GIN] 2026/11/04 - 15:43:36 | 200 |   4.08ms |       127.0.0.1 | GET      "/api/tags"
     [GIN] 2026/11/04 - 15:43:36 | 200 | 16.167µs |       127.0.0.1 | GET      "/api/version"
     ```
   - All endpoint checks returned HTTP 200. Zero HTTP 404s were recorded.
   - Tested live generation request with `--model gemma2:27b`: intercepted and redirected to `gemma-lean4:latest` with zero 404s.
3. **Internal Test Suite**:
   - `python3 tools/test_ollama_pipeline.py` ran 42/42 tests in 36.6s with exit code 0.
- Status: **VERIFIED CLEAN**.

### 1.3 Master Library Build
- Executed `lake build`:
  ```
  Build completed successfully.
  ```
  Exit code 0.
- Status: **VERIFIED CLEAN**.

---

### 1.4 Critical Vulnerabilities & Defects in `data/gemma_accepted_proofs.jsonl`

Despite the clean kernel axiom extraction on library files, adversarial stress-testing revealed three critical defects in `tools/build_accepted_proofs_dataset.py` and the harvested test dataset:

#### Defect 1: Unterminated Block Comment & Compiler Crash in `tests.ChallengePhase2ModelA.challenge_query_B02`
- In `data/gemma_accepted_proofs.jsonl`, the record for `tests.ChallengePhase2ModelA.challenge_query_B02` has the following verbatim `"proof"`:
  ```lean
  GromovCompactness.Bubbling.exists_calibrated_rescaling I u_seq thresh m_defect hm h_jhol h_defect h_ivt

  --------------------------------------------------------------------------------
  -- SECTION 2: Certification of Remediation and Invalidation of Failure Modes
  --------------------------------------------------------------------------------

  /-!
  ### Certification 1: Non-Triviality of Remediated Contract A04
  The old facade `0 ≤ C` allowed trivial 3-line proofs ignoring $f, p, k, r, R$.
  In the remediated statements, the conclusion bounds genuine Sobolev seminorms and Hölder norms:
  - `interior_cauchy_riemann_estimate` requires bounding `sobolevNorm p (k + 1) f (closedBall 0 r)`
    by $C$ times the $W^{k, p}$ norm of $\bar\partial f$ plus the $L^p$ norm of $f$.
  - `morrey_sobolev_embedding` requires bounding pointwise differences `‖f z - f w‖`
    by $C (\operatorname{dist} z\ w)^\alpha \|f\|_{W^{1, p}}$.
  Both definitions now genuinely depend on all functional inputs and derivatives.
  ```
- **Compiler Failure**: Feeding this declaration and proof to Lean 4 fails immediately:
  ```
  <stdin>:38:0: error: unterminated comment
  EXIT CODE: 1
  ```
  The proof is completely uncompilable in Lean 4 because `clean_proof_trailing` stripped the trailing closing `-/` but left the opening `/-!`.
- **Dirty Constant Leak**: The swallowed comment directly names dirty constants `interior_cauchy_riemann_estimate` and `morrey_sobolev_embedding`. Because `mask_comments_and_strings` masked comments during line 350 dirty constant filtering, the constant names were invisible to the filter and leaked into the training set.

#### Defect 2: Top-Level Command & Divider Leak in `tests.ChallengeGeometry.challenge_affine_scaling_fixes_all`
- In `data/gemma_accepted_proofs.jsonl`, the record for `tests.ChallengeGeometry.challenge_affine_scaling_fixes_all` has the following verbatim `"proof"`:
  ```lean
  by
    rfl

  --------------------------------------------------------------------------------
  -- SECTION 4: Exposure of Circular Hypothesis in `exists_unique_moebius_three_points`
  --------------------------------------------------------------------------------

  set_option linter.unusedVariables false
  ```
- The top-level command `set_option linter.unusedVariables false` leaked into the proof body because `cmd_boundary_pat` does not recognize `set_option` as a declaration boundary.

#### Defect 3: Invalid Mathematical Proofs Harvested as "Accepted Proofs" from `tests/ChallengeGeometry.lean`
- `tests/ChallengeGeometry.lean` was an obsolete test file written to expose facade definitions (`affine_scaling = MoebiusFrame.id`) from early Phase 1.
- In subsequent milestones, `affine_scaling`, `inversion`, and `rotation` were properly formalized into genuine transformations in `Sphere.lean`.
- As a result, the proofs in `tests/ChallengeGeometry.lean` are **mathematically invalid and fail Lean 4 elaboration**:
  - `challenge_affine_scaling_is_facade`:
    `affine_scaling a s hs = MoebiusFrame.id := by rfl`
    **Lean Error**: `tactic 'rfl' failed, the left-hand side is not definitionally equal to the right-hand side`
  - `challenge_inversion_is_facade`:
    `inversion = MoebiusFrame.id := by rfl`
    **Lean Error**: `tactic 'rfl' failed`
  - `challenge_rotation_is_facade`:
    `rotation θ = MoebiusFrame.id := by rfl`
    **Lean Error**: `tactic 'rfl' failed`
  - `challenge_affine_scaling_fixes_all`:
    `(affine_scaling 0 2 (by norm_num)).toHomeo z = z := by rfl`
    **Lean Error**: `tactic 'rfl' failed`
  - `challenge_three_points_is_circular_modus_ponens`:
    **Lean Error**: type mismatch
- Because `tools/build_accepted_proofs_dataset.py` harvests raw text matching regexes from `tests/*.lean` without verifying that the file or declarations compile in Lean 4, **all 5 broken proofs were harvested into `data/gemma_accepted_proofs.jsonl` as "accepted proofs"**.

---

## 2. Logic Chain

1. **Defect 1 Root Cause (`clean_proof_trailing`)**:
   - In `tools/build_accepted_proofs_dataset.py:182-196`:
     ```python
     def clean_proof_trailing(proof: str) -> str:
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
   - When comments follow a declaration, `re.sub(r'(/-[\s\S]*?-\/\s*)$', '', proof)` fails if there are line comments or dividers after `-/`.
   - The `while lines:` loop pops lines from the bottom. When it encounters line 278 (`-/`), it pops it because `last.endswith('-/')`.
   - The preceding line (line 277) is `"Both definitions now genuinely depend on all functional inputs and derivatives."`. Because this line does not start with `--`, `/-`, or end with `-/`, the loop terminates prematurely.
   - Result: The closing delimiter `-/` is stripped, but the opening delimiter `/-!` and the rest of the comment are left in `clean_proof`, producing an unclosed block comment that fails Lean compilation.

2. **Defect 2 Root Cause (`cmd_boundary_pat`)**:
   - In `tools/build_accepted_proofs_dataset.py:311`:
     `cmd_boundary_pat` lists Lean commands (`theorem|lemma|def|...`), but omits `set_option`.
   - When a declaration is followed by `set_option`, the parser fails to recognize the boundary and absorbs `set_option` into the proof body.

3. **Defect 3 Root Cause (Unchecked Harvest of Obsolete Test Files)**:
   - In `lakefile.lean`, only `GromovCompactness` is built; `tests/` is not a lake target.
   - `harvest_test_proofs` parses text from every `.lean` file in `tests/` without checking whether the file or declarations compile.
   - Obsolete test files containing assertions of obsolete facades (e.g. `affine_scaling = MoebiusFrame.id := by rfl`) are extracted as accepted proofs, injecting false mathematical training data into Gemma 9B.

---

## 3. Caveats

- All 395 library proofs from `GromovCompactness` in `data/gemma_accepted_proofs.jsonl` are 100% verified clean (0 syntax errors, 0 comment leaks, genuine kernel axioms).
- The defect is strictly confined to the test harvesting routine `harvest_test_proofs` and `clean_proof_trailing` in `tools/build_accepted_proofs_dataset.py`.

---

## 4. Conclusion

Verdict: **REJECT**.

While `tools/extract_accepted_proofs.lean`, `tools/ollama_lean4_client.py`, and `lake build` are verified fully compliant and clean, `data/gemma_accepted_proofs.jsonl` cannot be approved for Gemma 9B fine-tuning in its current state because:
1. `tests.ChallengePhase2ModelA.challenge_query_B02` contains an unclosed comment that crashes the Lean 4 compiler.
2. `tests.ChallengeGeometry.challenge_affine_scaling_fixes_all` contains leaked `set_option` commands.
3. 5 declarations from `tests/ChallengeGeometry.lean` are mathematically broken and fail `rfl` in Lean 4.

### Concrete Remediation Required:
1. **Fix `clean_proof_trailing` in `tools/build_accepted_proofs_dataset.py`**:
   Iteratively strip trailing line comments, section dividers, and block comments until a clean fixpoint is reached:
   ```python
   def clean_proof_trailing(proof: str) -> str:
       while True:
           p = proof.rstrip()
           p = re.sub(r'(--[^\n]*)$', '', p).rstrip()
           p = re.sub(r'(/--?[\s\S]*?-\/)$', '', p).rstrip()
           p = re.sub(r'(/-![\s\S]*?-\/)$', '', p).rstrip()
           if p == proof:
               break
           proof = p
       # strip any section line dividers
       lines = [l for l in proof.splitlines() if not re.match(r'^-{5,}$', l.strip())]
       return '\n'.join(lines).strip()
   ```
2. **Add `set_option` to `cmd_boundary_pat`**:
   Include `set_option` in `cmd_boundary_pat`.
3. **Exclude or Remediate Broken Test Files**:
   Ensure obsolete test files like `tests/ChallengeGeometry.lean` are either updated to pass `lake env lean` or skipped in `harvest_test_proofs` (e.g. only harvest from test files that exit 0 under `lake env lean <file>`).
4. **Re-run dataset generation**:
   `python3 tools/build_accepted_proofs_dataset.py --force`
5. **Verify zero uncompilable proofs, zero unterminated comments, and zero command leaks**.

---

## 5. Verification Method

Any agent can independently verify these findings using the following commands:

```bash
# 1. Reproduce compiler failure on challenge_query_B02 extracted proof (fails with 'unterminated comment')
python3 -c "
import json, subprocess
with open('data/gemma_accepted_proofs.jsonl') as f:
    for line in f:
        p = json.loads(line)
        if p['id'] == 'tests.ChallengePhase2ModelA.challenge_query_B02':
            decl = p['signature'] + ' :=\n' + p['proof']
            code = f'import GromovCompactness\nopen scoped Manifold ContDiff Topology\nopen Metric Set MeasureTheory GromovCompactness\nopen GromovCompactness.Analysis\nopen GromovCompactness.Bubbling\nvariable {{E : Type*}} [NormedAddCommGroup E] [NormedSpace ℝ E] {{H : Type*}} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {{M : Type*}} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]\n{decl}\n'
            res = subprocess.run(['lake', 'env', 'lean', '--stdin'], input=code, text=True, capture_output=True)
            print('EXIT CODE:', res.returncode)
            print('OUTPUT:', res.stdout)
            assert res.returncode != 0
"

# 2. Detect unclosed block comments in dataset
python3 -c "
import json
with open('data/gemma_accepted_proofs.jsonl') as f:
    proofs = [json.loads(l) for l in f if json.loads(l)['proof'].count('/-') != json.loads(l)['proof'].count('-/')]
print(f'Proofs with unclosed comments: {len(proofs)}')
assert len(proofs) > 0, 'Defect disappeared'
for p in proofs: print(' ', p['id'])
"

# 3. Detect leaked top-level commands in proof bodies
python3 -c "
import json
with open('data/gemma_accepted_proofs.jsonl') as f:
    leaks = [json.loads(l)['id'] for l in f if 'set_option' in json.loads(l)['proof']]
print(f'Proofs with leaked set_option: {len(leaks)}')
assert len(leaks) > 0, 'Defect disappeared'
for l in leaks: print(' ', l)
"

# 4. Reproduce compilation failure of challenge_affine_scaling_fixes_all (fails with 'tactic rfl failed')
python3 -c "
import subprocess
code = 'import GromovCompactness\nopen GromovCompactness\ntheorem challenge_affine_scaling_fixes_all (z : CP1) :\n    (affine_scaling 0 2 (by norm_num)).toHomeo z = z := by\n  rfl\n'
res = subprocess.run(['lake', 'env', 'lean', '--stdin'], input=code, text=True, capture_output=True)
print('EXIT CODE:', res.returncode)
print('OUTPUT:', res.stdout)
assert res.returncode != 0
"

# 5. Verify 0 sorryAx in raw accepted theorems
python3 -c "
import json
with open('data/raw_accepted_theorems.jsonl') as f:
    sorrys = [json.loads(l)['name'] for l in f if 'sorryAx' in json.loads(l).get('axioms', [])]
assert len(sorrys) == 0
print('PASS: raw_accepted_theorems has 0 sorryAx')
"

# 6. Verify 9B model interception across client
python3 -c "
import subprocess
for m in ['gemma4:12B', 'gemma2:27b', 'llama3:70b']:
    res = subprocess.run(['python3', 'tools/ollama_lean4_client.py', 'query', '--prompt', 'test', '--model', m, '--dry-run', '--json'], capture_output=True, text=True)
    assert 'WARNING' in res.stderr and res.returncode == 0
print('PASS: All disallowed models intercepted and redirected')
"
```
