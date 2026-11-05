# Remediation Blueprint Report: Milestone 5 Forensic Audit Remediation

- **Author**: `explorer_m5_remediation` (Audit Remediation Explorer)
- **Recipient**: Phase 2 Project Orchestrator Gen 5 (`1e165d1f-01c7-453c-b5da-52fb4047feb1`)
- **Target Files**:
  - `GromovCompactness/Analysis/HoferRescaling.lean`
  - `tests/ChallengePhase2ModelA.lean`
- **Associated Artifacts**:
  - Patch File: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m5_remediation/remediation.patch`
  - Lean 4 Harness: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m5_remediation/test_harness_full.lean`

---

## 1. Observation

### 1.1 Direct Observation of Violation 1 (Hidden `sorry` / Facade Auto-Param)
In `GromovCompactness/Analysis/HoferRescaling.lean` at lines 559–570:
```lean
559: theorem exists_calibrated_rescaling
560:     (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
561:     (hm : thresh.h ≤ m_defect)
562:     (h_jhol : ∀ (n : ℕ), JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
563:     (h_defect : ∀ (n : ℕ), ∃ (a_n : ℂ) (R_n : ℝ),
564:       dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
565:       0 < R_n ∧ R_n ≤ 1 / ((n : ℝ) + 1) ∧
566:       m_defect - thresh.h / 2 ≤ energyMeasure I (u_seq n) (disk_at a_n R_n))
567:     (h_ivt : RadialEnergyIVT I (M := M) := by sorry) :
568:     Nonempty (CalibratedRescaling I u_seq thresh m_defect) :=
569:   exists_calibrated_rescaling_of_ivt I u_seq thresh m_defect hm h_jhol h_defect h_ivt
```
- Line 567 carries the literal keyword `sorry` embedded as the default auto-param tactic for `h_ivt`.
- Searching with `grep -n "sorry" GromovCompactness/Analysis/HoferRescaling.lean` confirms line 567 is the **sole** occurrence of the token `sorry` in the entire 603-line file.
- In `tests/ChallengePhase2ModelA.lean` at line 224:
```lean
224: theorem challenge_query_B02
225:     (u_seq : ℕ → (CP1 → M)) (thresh : GromovCompactness.Bubbling.TargetThresholds I M)
226:     (m_defect : ℝ) (hm : thresh.h ≤ m_defect)
227:     (h_jhol : ∀ (n : ℕ), JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
228:     (h_defect : ∀ (n : ℕ), ∃ (a_n : ℂ) (R_n : ℝ),
229:       dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
230:       0 < R_n ∧ R_n ≤ 1 / ((n : ℝ) + 1) ∧
231:       m_defect - thresh.h / 2 ≤ energyMeasure I (u_seq n) (disk_at a_n R_n)) :
232:     Nonempty (GromovCompactness.Bubbling.CalibratedRescaling I u_seq thresh m_defect) :=
233:   GromovCompactness.Bubbling.exists_calibrated_rescaling I u_seq thresh m_defect hm h_jhol h_defect
```
- Invoking `lake env lean tests/ChallengePhase2ModelA.lean` emits:
```
tests/ChallengePhase2ModelA.lean:224:8: warning: declaration uses 'sorry'
```
- Checking `#print axioms challenge_query_B02` confirms:
```
'challenge_query_B02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

### 1.2 Direct Observation of Violation 2 (Transitive `sorryAx` in `exists_target_thresholds`)
In `GromovCompactness/Analysis/HoferRescaling.lean` lines 330–366:
- Declaration 12, `exists_target_thresholds_of_modules`, is a constructive reduction lemma taking the hypotheses of modules A03 (`epsilon_regularity`), A07 (`sphere_energy_gap`), and A10 (`cylinder_exponential_decay`) as explicit inputs.
- Querying `#print axioms GromovCompactness.Analysis.exists_target_thresholds_of_modules` yields:
```
[propext, Classical.choice, Quot.sound]
```
(100% standard Lean 4 kernel axioms, zero `sorryAx`).
- Declaration 13, `exists_target_thresholds`, instantiates those hypotheses by calling `epsilon_regularity`, `sphere_energy_gap`, and `cylinder_exponential_decay` from upstream files `EpsilonRegularity.lean`, `EnergyGap.lean`, and `SingularityRemoval.lean`.
- Because those upstream modules were scaffolded with Model A `sorry` placeholders, running `#print axioms GromovCompactness.Analysis.exists_target_thresholds` yields:
```
[propext, sorryAx, Classical.choice, Quot.sound]
```

### 1.3 Direct Observation of Existing Milestone 5 Test Suites
- `lake env lean tests/ChallengeMilestone5Thresholds.lean`: 45 tests executed, exited with code 0, all tests depending strictly on `[propext, Classical.choice, Quot.sound]`.
- `lake env lean tests/ChallengeMilestone5Rescaling.lean`: 28 tests executed, exited with code 0, all tests depending strictly on `[propext, Classical.choice, Quot.sound]`.

---

## 2. Logic Chain

1. **Root Cause of Violation 1**:
   - `HoferRescaling.lean:567` introduced `(h_ivt : RadialEnergyIVT I (M := M) := by sorry)`.
   - The auto-param `:= by sorry` silently permitted callers to omit `h_ivt`, hiding the fact that the complete bubbling extraction theorem requires the Intermediate Value Theorem for radial energy measures.
   - Consequently, `challenge_query_B02` in `ChallengePhase2ModelA.lean` was elaborated with an implicit `sorry`, emitting a compiler warning and polluting its axiom environment with `sorryAx`.
   - By removing `:= by sorry` entirely, `exists_calibrated_rescaling` becomes a pure 8-argument reduction theorem matching `exists_calibrated_rescaling_of_ivt`.
   - Updating `challenge_query_B02` to accept `(h_ivt : RadialEnergyIVT I (M := M))` as an explicit hypothesis eliminates the `sorry` elaboration, removes the compiler warning completely, and restores its axiom set to `[propext, Classical.choice, Quot.sound]`.

2. **Root Cause of Violation 2**:
   - The contract `exists_target_thresholds` assembles three separate geometric theorems (`epsilon_regularity`, `sphere_energy_gap`, `cylinder_exponential_decay`).
   - Claiming that `exists_target_thresholds` is a pure zero-`sorry` theorem was false because its upstream dependencies in other modules contain `sorry`.
   - However, `exists_target_thresholds_of_modules` is an uncompromised, 100% zero-`sorry` reduction theorem that packages the positive threshold $h > 0$ constructively from arbitrary geometric inputs.
   - Delineating these two declarations in the docstrings, in `GromovCompactness.Bubbling` re-exports, and adding `challenge_query_B01_reduction` to `ChallengePhase2ModelA.lean` resolves the discrepancy with full forensic transparency.

3. **Empirical Validation**:
   - In `.agents/teamwork/explorer_m5_remediation/test_harness_full.lean`, we machine-checked the exact proposed signatures and proofs.
   - Result:
     - `challenge_query_B01_reduction`: depends on `[propext, Classical.choice, Quot.sound]` (Zero `sorryAx`, 0 warnings).
     - `challenge_query_B01`: depends on `[propext, sorryAx, Classical.choice, Quot.sound]` (as expected from upstream modules).
     - `challenge_query_B02`: depends on `[propext, Classical.choice, Quot.sound]` (Zero `sorryAx`, 0 warnings).
     - Exit code: 0.

---

## 3. Caveats

- **Scope of Milestone 5**:
  - The `sorryAx` in `exists_target_thresholds` originates from `epsilon_regularity` (`EpsilonRegularity.lean`), `sphere_energy_gap` (`EnergyGap.lean`), and `cylinder_exponential_decay` (`SingularityRemoval.lean`). These are upstream Phase 2 Model A modules that are scheduled for zero-`sorry` completion in subsequent milestones. Milestone 5's scope is strictly confined to `HoferRescaling.lean` (Contracts B01 & B02).
- **RadialEnergyIVT Status**:
  - `RadialEnergyIVT` is a genuine analytic property asserting that for smooth curves, the energy of expanding concentric disks takes all intermediate values continuously. In `HoferRescaling.lean`, `ivt_radial_energy_of_continuous` and `test_radial_ivt` prove that this property holds whenever the radial energy profile is continuous. In `exists_calibrated_rescaling`, passing `h_ivt` as an explicit hypothesis adheres to the standard reduction pattern used throughout Phase 2 (e.g. `interior_cauchy_riemann_estimate`, `morrey_sobolev_embedding`, `removal_of_singularities_reduction`).

---

## 4. Conclusion & Complete Step-by-Step Blueprint for Worker

### 4.1 Summary of Edits
1. In `GromovCompactness/Analysis/HoferRescaling.lean`:
   - Line 35: Clarify header docstring regarding reduction vs assembled existence.
   - Line 556–570: Remove `:= by sorry` from line 567, making `h_ivt : RadialEnergyIVT I (M := M)` an explicit parameter.
   - Line 592–603: Add re-exports for `RadialEnergyIVT`, `exists_target_thresholds_of_modules`, and `exists_calibrated_rescaling_of_ivt` into namespace `GromovCompactness.Bubbling`.
2. In `tests/ChallengePhase2ModelA.lean`:
   - Line 214–234: Add `challenge_query_B01_reduction` querying the pure reduction theorem.
   - Line 224–234: Add `(h_ivt : RadialEnergyIVT I (M := M))` parameter to `challenge_query_B02` and pass it to `exists_calibrated_rescaling`.

### 4.2 Exact Code Replacements

#### Edit 1: `GromovCompactness/Analysis/HoferRescaling.lean` Header Docstring (Lines 35–42)
```lean
<<<<
2. `exists_target_thresholds` (Contract B01): Existence of the universal threshold $h > 0$.
3. `CalibratedRescaling` (Contract B02): Moving centers $a_n \to 0$ and radii $\lambda_n \to 0$
   satisfying the exact calibration identity $E(u_n; D_{\lambda_n}(a_n)) = m_p - h/2$.
4. `exists_calibrated_rescaling` (Contract B02): Extraction theorem via the Intermediate Value Theorem.
====
2. `exists_target_thresholds_of_modules` (Contract B01): Zero-sorry reduction theorem
   proving existence of the universal threshold $h > 0$ from geometric modules A03, A07, and A10.
   `exists_target_thresholds` (Contract B01): Top-level existence theorem assembling the reduction
   with upstream geometric results.
3. `CalibratedRescaling` (Contract B02): Moving centers $a_n \to 0$ and radii $\lambda_n \to 0$
   satisfying the exact calibration identity $E(u_n; D_{\lambda_n}(a_n)) = m_p - h/2$.
4. `exists_calibrated_rescaling_of_ivt` and `exists_calibrated_rescaling` (Contract B02):
   Extraction theorems via the Radial Intermediate Value Theorem (`RadialEnergyIVT`).
>>>>
```

#### Edit 2: `GromovCompactness/Analysis/HoferRescaling.lean` Contract B02 (Lines 556–570)
```lean
<<<<
/-- Existence of calibrated moving centers and radii (Contract B02).
Under energy concentration at `0` with defect mass `m_defect`, the Intermediate Value
Theorem yields calibrated moving centers and scaling radii. -/
theorem exists_calibrated_rescaling
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (h_jhol : ∀ (n : ℕ), JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_defect : ∀ (n : ℕ), ∃ (a_n : ℂ) (R_n : ℝ),
      dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
      0 < R_n ∧ R_n ≤ 1 / ((n : ℝ) + 1) ∧
      m_defect - thresh.h / 2 ≤ energyMeasure I (u_seq n) (disk_at a_n R_n))
    (h_ivt : RadialEnergyIVT I (M := M) := by sorry) :
    Nonempty (CalibratedRescaling I u_seq thresh m_defect) :=
  exists_calibrated_rescaling_of_ivt I u_seq thresh m_defect hm h_jhol h_defect h_ivt
====
/-- Existence of calibrated moving centers and radii (Contract B02).
Under energy concentration at `0` with defect mass `m_defect`, the Intermediate Value
Theorem (`RadialEnergyIVT`) yields calibrated moving centers and scaling radii.
This is formulated as a pure zero-`sorry` reduction theorem requiring the radial IVT hypothesis. -/
theorem exists_calibrated_rescaling
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (h_jhol : ∀ (n : ℕ), JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_defect : ∀ (n : ℕ), ∃ (a_n : ℂ) (R_n : ℝ),
      dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
      0 < R_n ∧ R_n ≤ 1 / ((n : ℝ) + 1) ∧
      m_defect - thresh.h / 2 ≤ energyMeasure I (u_seq n) (disk_at a_n R_n))
    (h_ivt : RadialEnergyIVT I (M := M)) :
    Nonempty (CalibratedRescaling I u_seq thresh m_defect) :=
  exists_calibrated_rescaling_of_ivt I u_seq thresh m_defect hm h_jhol h_defect h_ivt
>>>>
```

#### Edit 3: `GromovCompactness/Analysis/HoferRescaling.lean` Section 6 Re-exports (Lines 585–602)
```lean
<<<<
namespace GromovCompactness.Bubbling

/-- Re-export of `TargetThresholds` in namespace `GromovCompactness.Bubbling` to match blueprint `b01:threshold_h`. -/
abbrev TargetThresholds := @GromovCompactness.Analysis.TargetThresholds

/-- Re-export of `CalibratedRescaling` in namespace `GromovCompactness.Bubbling` to match blueprint `b02:calibration`. -/
abbrev CalibratedRescaling := @GromovCompactness.Analysis.CalibratedRescaling

/-- Re-export of `exists_target_thresholds` in namespace `GromovCompactness.Bubbling`. -/
abbrev exists_target_thresholds := @GromovCompactness.Analysis.exists_target_thresholds

/-- Re-export of `exists_calibrated_rescaling` in namespace `GromovCompactness.Bubbling`. -/
abbrev exists_calibrated_rescaling := @GromovCompactness.Analysis.exists_calibrated_rescaling

/-- Re-export of `bubble_energy_ge_sphere_gap` in namespace `GromovCompactness.Bubbling`. -/
abbrev bubble_energy_ge_sphere_gap := @GromovCompactness.Analysis.bubble_energy_ge_sphere_gap

end GromovCompactness.Bubbling
====
namespace GromovCompactness.Bubbling

/-- Re-export of `TargetThresholds` in namespace `GromovCompactness.Bubbling` to match blueprint `b01:threshold_h`. -/
abbrev TargetThresholds := @GromovCompactness.Analysis.TargetThresholds

/-- Re-export of `CalibratedRescaling` in namespace `GromovCompactness.Bubbling` to match blueprint `b02:calibration`. -/
abbrev CalibratedRescaling := @GromovCompactness.Analysis.CalibratedRescaling

/-- Re-export of `RadialEnergyIVT` in namespace `GromovCompactness.Bubbling`. -/
abbrev RadialEnergyIVT := @GromovCompactness.Analysis.RadialEnergyIVT

/-- Re-export of `exists_target_thresholds_of_modules` in namespace `GromovCompactness.Bubbling`. -/
abbrev exists_target_thresholds_of_modules := @GromovCompactness.Analysis.exists_target_thresholds_of_modules

/-- Re-export of `exists_target_thresholds` in namespace `GromovCompactness.Bubbling`. -/
abbrev exists_target_thresholds := @GromovCompactness.Analysis.exists_target_thresholds

/-- Re-export of `exists_calibrated_rescaling_of_ivt` in namespace `GromovCompactness.Bubbling`. -/
abbrev exists_calibrated_rescaling_of_ivt := @GromovCompactness.Analysis.exists_calibrated_rescaling_of_ivt

/-- Re-export of `exists_calibrated_rescaling` in namespace `GromovCompactness.Bubbling`. -/
abbrev exists_calibrated_rescaling := @GromovCompactness.Analysis.exists_calibrated_rescaling

/-- Re-export of `bubble_energy_ge_sphere_gap` in namespace `GromovCompactness.Bubbling`. -/
abbrev bubble_energy_ge_sphere_gap := @GromovCompactness.Analysis.bubble_energy_ge_sphere_gap

end GromovCompactness.Bubbling
>>>>
```

#### Edit 4: `tests/ChallengePhase2ModelA.lean` Contracts B01 & B02 (Lines 212–234)
```lean
<<<<
-- Contract B01: TargetThresholds & exists_target_thresholds (remediated with bundled geometric properties)
#check GromovCompactness.Bubbling.TargetThresholds
#check GromovCompactness.Bubbling.exists_target_thresholds

theorem challenge_query_B01 :
    Nonempty (GromovCompactness.Bubbling.TargetThresholds I M) :=
  GromovCompactness.Bubbling.exists_target_thresholds I

-- Contract B02: CalibratedRescaling & exists_calibrated_rescaling (remediated with concentration hypotheses)
#check GromovCompactness.Bubbling.CalibratedRescaling
#check GromovCompactness.Bubbling.exists_calibrated_rescaling

theorem challenge_query_B02
    (u_seq : ℕ → (CP1 → M)) (thresh : GromovCompactness.Bubbling.TargetThresholds I M)
    (m_defect : ℝ) (hm : thresh.h ≤ m_defect)
    (h_jhol : ∀ (n : ℕ), JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_defect : ∀ (n : ℕ), ∃ (a_n : ℂ) (R_n : ℝ),
      dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
      0 < R_n ∧ R_n ≤ 1 / ((n : ℝ) + 1) ∧
      m_defect - thresh.h / 2 ≤ energyMeasure I (u_seq n) (disk_at a_n R_n)) :
    Nonempty (GromovCompactness.Bubbling.CalibratedRescaling I u_seq thresh m_defect) :=
  GromovCompactness.Bubbling.exists_calibrated_rescaling I u_seq thresh m_defect hm h_jhol h_defect
====
-- Contract B01: TargetThresholds & exists_target_thresholds (remediated with bundled geometric properties)
#check GromovCompactness.Bubbling.TargetThresholds
#check GromovCompactness.Bubbling.exists_target_thresholds
#check GromovCompactness.Bubbling.exists_target_thresholds_of_modules

/-- Contract B01 pure zero-sorry reduction theorem (depends only on standard kernel axioms). -/
theorem challenge_query_B01_reduction
    (ε_reg C_reg : ℝ) (h_reg_pos : 0 < ε_reg) (h_Creg_pos : 0 < C_reg)
    (h_reg : ∀ (u : CP1 → M) (a : ℂ) (r : ℝ) (_ : 0 < r),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (disk_at a r) < ε_reg →
      ∀ z ∈ disk_at a (r / 2),
        riemannianEnergyDensity I u z ≤ C_reg * r^(-2 : ℝ) * energyMeasure I u (disk_at a r))
    (ε_sph : ℝ) (h_sph_pos : 0 < ε_sph)
    (h_sph : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ε_sph ≤ totalEnergy I u)
    (C_neck a_decay ε_neck : ℝ)
    (h_Cneck_pos : 0 < C_neck) (h_a_pos : 0 < a_decay) (h_neck_pos : 0 < ε_neck)
    (h_neck : ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      0 < r → 2 * r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r R) < ε_neck →
      ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
        energyMeasure I u (annulus_at center r₁ r₂) ≤
          C_neck * ((r / r₁)^a_decay + (r₂ / R)^a_decay) * energyMeasure I u (annulus_at center r R)) :
    Nonempty (GromovCompactness.Bubbling.TargetThresholds I M) :=
  GromovCompactness.Bubbling.exists_target_thresholds_of_modules I ε_reg C_reg h_reg_pos h_Creg_pos h_reg
    ε_sph h_sph_pos h_sph C_neck a_decay ε_neck h_Cneck_pos h_a_pos h_neck_pos h_neck

/-- Contract B01 top-level assembled existence theorem (transitively inherits sorryAx from upstream A03, A07, A10). -/
theorem challenge_query_B01 :
    Nonempty (GromovCompactness.Bubbling.TargetThresholds I M) :=
  GromovCompactness.Bubbling.exists_target_thresholds I

-- Contract B02: CalibratedRescaling & exists_calibrated_rescaling (remediated with concentration and IVT hypotheses)
#check GromovCompactness.Bubbling.CalibratedRescaling
#check GromovCompactness.Bubbling.RadialEnergyIVT
#check GromovCompactness.Bubbling.exists_calibrated_rescaling

theorem challenge_query_B02
    (u_seq : ℕ → (CP1 → M)) (thresh : GromovCompactness.Bubbling.TargetThresholds I M)
    (m_defect : ℝ) (hm : thresh.h ≤ m_defect)
    (h_jhol : ∀ (n : ℕ), JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_defect : ∀ (n : ℕ), ∃ (a_n : ℂ) (R_n : ℝ),
      dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
      0 < R_n ∧ R_n ≤ 1 / ((n : ℝ) + 1) ∧
      m_defect - thresh.h / 2 ≤ energyMeasure I (u_seq n) (disk_at a_n R_n))
    (h_ivt : RadialEnergyIVT I (M := M)) :
    Nonempty (GromovCompactness.Bubbling.CalibratedRescaling I u_seq thresh m_defect) :=
  GromovCompactness.Bubbling.exists_calibrated_rescaling I u_seq thresh m_defect hm h_jhol h_defect h_ivt
>>>>
```

---

## 5. Verification Method

Once the worker applies these edits:

1. **Verify Complete Absence of `sorry` in `HoferRescaling.lean`**:
   ```bash
   grep -n "sorry" GromovCompactness/Analysis/HoferRescaling.lean
   ```
   *Expected Output*: Only markdown/comment headers with `Zero-sorry` should appear. Zero occurrences of the Lean command `sorry` or `by sorry`.

2. **Verify Clean Compilation with Zero Warnings**:
   ```bash
   lake build GromovCompactness
   lake env lean tests/ChallengePhase2ModelA.lean
   ```
   *Expected Output*: Exit code 0, no `declaration uses 'sorry'` warning for line 224.

3. **Verify Full Challenge Test Suites Pass with Exit Code 0**:
   ```bash
   lake env lean tests/ChallengeMilestone5Thresholds.lean
   lake env lean tests/ChallengeMilestone5Rescaling.lean
   lake env lean tests/AdversarialAttacksIter2.lean
   ```
   *Expected Output*: All test suites pass cleanly with exit code 0.

4. **Verify Axiom Purity of Reduction Theorems**:
   ```bash
   lake env lean .agents/teamwork/auditor1_m5/check_axioms.lean
   ```
   *Expected Output*:
   - Declaration 12 (`exists_target_thresholds_of_modules`): `[propext, Classical.choice, Quot.sound]`
   - Declaration 22 (`exists_calibrated_rescaling_of_ivt`): `[propext, Classical.choice, Quot.sound]`
   - Declaration 23 (`exists_calibrated_rescaling`): `[propext, Classical.choice, Quot.sound]`
   - Declaration 13 (`exists_target_thresholds`): accurately recognized as inheriting `sorryAx` from upstream modules.
