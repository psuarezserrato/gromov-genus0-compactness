import GromovCompactness.Geometry.Sphere
import Mathlib.Analysis.InnerProductSpace.PiL2

open GromovCompactness Metric Set

namespace TestDisks

-- =========================================================================
-- PART 1: DISK_AT CHALLENGE TESTS
-- =========================================================================

-- Test 1.1: Corner case that failed previously (north_pole ∈ disk_at 0 2)
theorem test_north_pole_not_mem_disk_0_2 : north_pole ∉ disk_at 0 2 :=
  north_pole_not_mem_disk_at 0 2

-- Test 1.2: North pole is excluded for all centers and radii
theorem test_north_pole_not_mem_disk_all (a : ℂ) (r : ℝ) : north_pole ∉ disk_at a r :=
  north_pole_not_mem_disk_at a r

-- Test 1.3: North pole is excluded for large disks (r = 100, r = 1000)
theorem test_north_pole_not_mem_disk_large :
    north_pole ∉ disk_at 0 100 ∧ north_pole ∉ disk_at (5 + 7 * Complex.I) 1000 :=
  ⟨north_pole_not_mem_disk_at 0 100, north_pole_not_mem_disk_at (5 + 7 * Complex.I) 1000⟩

-- Test 1.4: North pole is excluded for annuli
theorem test_north_pole_not_mem_annulus_all (a : ℂ) (r R : ℝ) :
    north_pole ∉ annulus_at a r R :=
  north_pole_not_mem_annulus_at a r R

-- Test 1.5: Monotonicity with abstract radii
theorem test_disk_at_mono_abstract (a : ℂ) {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
    disk_at a r₁ ⊆ disk_at a r₂ :=
  disk_at_mono a h

-- Test 1.6: Monotonicity with concrete radii
theorem test_disk_at_mono_concrete (a : ℂ) :
    disk_at a 1 ⊆ disk_at a 2 ∧
    disk_at a (1/2) ⊆ disk_at a 1 ∧
    disk_at a 2 ⊆ disk_at a 10 := by
  refine ⟨disk_at_mono a (by norm_num), disk_at_mono a (by norm_num), disk_at_mono a (by norm_num)⟩

-- Test 1.7: Non-emptiness and center containment for r > 0
theorem test_center_mem_disk_at_pos (a : ℂ) {r : ℝ} (hr : 0 < r) :
    stereo_chart.symm a ∈ disk_at a r :=
  center_mem_disk_at a hr

theorem test_disk_at_nonempty_pos (a : ℂ) {r : ℝ} (hr : 0 < r) :
    (disk_at a r).Nonempty :=
  ⟨stereo_chart.symm a, center_mem_disk_at a hr⟩

-- Test 1.8: Center is never the north pole
theorem test_center_ne_north_pole (a : ℂ) :
    stereo_chart.symm a ≠ north_pole := by
  intro h
  have h_mem : north_pole ∈ disk_at a 1 := by
    rw [← h]
    exact center_mem_disk_at a zero_lt_one
  exact north_pole_not_mem_disk_at a 1 h_mem

-- Test 1.9: Emptiness for nonpositive radius r ≤ 0
theorem test_disk_at_empty_of_nonpos (a : ℂ) {r : ℝ} (hr : r ≤ 0) :
    disk_at a r = ∅ := by
  dsimp [disk_at]
  rw [Metric.ball_eq_empty.mpr hr, Set.image_empty]

-- Test 1.10: Openness and Borel measurability of disks
theorem test_disk_at_is_open (a : ℂ) (r : ℝ) : IsOpen (disk_at a r) :=
  is_open_disk_at a r

theorem test_disk_at_measurable (a : ℂ) (r : ℝ) : MeasurableSet (disk_at a r) :=
  measurable_set_disk_at a r

-- Test 1.11: Annulus subset of disk
theorem test_annulus_subset_disk (a : ℂ) (r R : ℝ) :
    annulus_at a r R ⊆ disk_at a R :=
  annulus_subset_disk a r R

-- =========================================================================
-- PART 2: 3-POINT TRANSITIVITY & UNIQUENESS CHALLENGE TESTS
-- =========================================================================

-- Test 2.1: Verification that h_trans is absent from theorem statement
-- exists_unique_moebius_three_points produces an authentic MoebiusMatrix witness
-- without requiring any conditional hypothesis on Moebius group transitivity
theorem test_no_h_trans_in_exists_moebius (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ)
    (hv12 : ¬ ProjEquiv v₁ v₂) (hv23 : ¬ ProjEquiv v₂ v₃) (hv13 : ¬ ProjEquiv v₁ v₃)
    (hw12 : ¬ ProjEquiv w₁ w₂) (hw23 : ¬ ProjEquiv w₂ w₃) (hw13 : ¬ ProjEquiv w₁ w₃) :
    ∃ (M : MoebiusMatrix),
      ProjEquiv (M.act v₁) w₁ ∧
      ProjEquiv (M.act v₂) w₂ ∧
      ProjEquiv (M.act v₃) w₃ :=
  exists_unique_moebius_three_points v₁ v₂ v₃ w₁ w₂ w₃ hv12 hv23 hv13 hw12 hw23 hw13

-- Test 2.2: Explicit triplet (0, 1, ∞) ↦ (1, -1, i)
def trip_v1 : ℂ × ℂ := (0, 1)        -- represents 0
def trip_v2 : ℂ × ℂ := (1, 1)        -- represents 1
def trip_v3 : ℂ × ℂ := (1, 0)        -- represents ∞

def trip_w1 : ℂ × ℂ := (1, 1)        -- represents 1
def trip_w2 : ℂ × ℂ := (-1, 1)       -- represents -1
def trip_w3 : ℂ × ℂ := (Complex.I, 1)-- represents i

lemma test_hv12 : ¬ ProjEquiv trip_v1 trip_v2 := by
  intro h; dsimp [ProjEquiv, trip_v1, trip_v2] at h; norm_num at h

lemma test_hv23 : ¬ ProjEquiv trip_v2 trip_v3 := by
  intro h; dsimp [ProjEquiv, trip_v2, trip_v3] at h; norm_num at h

lemma test_hv13 : ¬ ProjEquiv trip_v1 trip_v3 := by
  intro h; dsimp [ProjEquiv, trip_v1, trip_v3] at h; norm_num at h

lemma test_hw12 : ¬ ProjEquiv trip_w1 trip_w2 := by
  intro h; dsimp [ProjEquiv, trip_w1, trip_w2] at h; norm_num at h

lemma test_hw23 : ¬ ProjEquiv trip_w2 trip_w3 := by
  intro h; dsimp [ProjEquiv, trip_w2, trip_w3] at h
  have hI : (-1 : ℂ) = Complex.I := by linear_combination h
  have hre := congr_arg Complex.re hI
  simp only [Complex.I_re, Complex.neg_re, Complex.one_re] at hre
  norm_num at hre

lemma test_hw13 : ¬ ProjEquiv trip_w1 trip_w3 := by
  intro h; dsimp [ProjEquiv, trip_w1, trip_w3] at h
  have hI : (1 : ℂ) = Complex.I := by linear_combination h
  have hre := congr_arg Complex.re hI
  simp only [Complex.I_re, Complex.one_re] at hre
  norm_num at hre

noncomputable def trip_M : MoebiusMatrix :=
  general_three_point_mat trip_v1 trip_v2 trip_v3 trip_w1 trip_w2 trip_w3
    test_hv12 test_hv23 test_hv13 test_hw12 test_hw23 test_hw13

-- Evaluation of the explicit matrix on all 3 points
theorem test_trip_eval_1 : ProjEquiv (trip_M.act trip_v1) trip_w1 :=
  general_three_point_eval_1 trip_v1 trip_v2 trip_v3 trip_w1 trip_w2 trip_w3
    test_hv12 test_hv23 test_hv13 test_hw12 test_hw23 test_hw13

theorem test_trip_eval_2 : ProjEquiv (trip_M.act trip_v2) trip_w2 :=
  general_three_point_eval_2 trip_v1 trip_v2 trip_v3 trip_w1 trip_w2 trip_w3
    test_hv12 test_hv23 test_hv13 test_hw12 test_hw23 test_hw13

theorem test_trip_eval_3 : ProjEquiv (trip_M.act trip_v3) trip_w3 :=
  general_three_point_eval_3 trip_v1 trip_v2 trip_v3 trip_w1 trip_w2 trip_w3
    test_hv12 test_hv23 test_hv13 test_hw12 test_hw23 test_hw13

-- Evaluation on a 4th point: z = 2, i.e. (2, 1) ↦ (1 - 3i, -3 + i)
theorem test_trip_eval_fourth_point :
    ProjEquiv (trip_M.act (2, 1)) (1 - 3 * Complex.I, -3 + Complex.I) := by
  dsimp [trip_M, general_three_point_mat, frame_mat, MoebiusMatrix.mul, MoebiusMatrix.adj,
         MoebiusMatrix.act, ProjEquiv, trip_v1, trip_v2, trip_v3, trip_w1, trip_w2, trip_w3]
  ring

-- Determinant of trip_M is strictly non-zero
theorem test_trip_det_ne_zero :
    trip_M.a * trip_M.d - trip_M.b * trip_M.c ≠ 0 :=
  trip_M.det_ne_zero

-- Test 2.3: Uniqueness via moebius_fix_three_standard
-- Standard fix implies projective equality with MoebiusMatrix.id
theorem test_moebius_fix_three_standard_is_id (M : MoebiusMatrix)
    (h0 : ProjEquiv (M.act (1, 0)) (1, 0))
    (h1 : ProjEquiv (M.act (0, 1)) (0, 1))
    (hinf : ProjEquiv (M.act (1, 1)) (1, 1)) :
    PglEquiv M MoebiusMatrix.id := by
  intro p
  have h_fix := moebius_fix_three_standard M h0 h1 hinf p
  dsimp [MoebiusMatrix.id, MoebiusMatrix.act, ProjEquiv] at *
  linear_combination h_fix

-- Algebraic rigidity of matrices fixing standard frame: b = 0, c = 0, a = d
theorem test_moebius_fix_standard_scalar (M : MoebiusMatrix)
    (h0 : ProjEquiv (M.act (1, 0)) (1, 0))
    (h1 : ProjEquiv (M.act (0, 1)) (0, 1))
    (hinf : ProjEquiv (M.act (1, 1)) (1, 1)) :
    M.b = 0 ∧ M.c = 0 ∧ M.a = M.d := by
  dsimp [MoebiusMatrix.act, ProjEquiv] at *
  have hc : M.c = 0 := by linear_combination -h0
  have hb : M.b = 0 := by linear_combination h1
  have had : M.a = M.d := by linear_combination hinf - hb + hc
  exact ⟨hb, hc, had⟩

-- Uniqueness: any two matrices fixing the standard frame are PglEquiv
theorem test_moebius_unique_fixing_standard (M₁ M₂ : MoebiusMatrix)
    (h0_1 : ProjEquiv (M₁.act (1, 0)) (1, 0))
    (h1_1 : ProjEquiv (M₁.act (0, 1)) (0, 1))
    (hinf_1 : ProjEquiv (M₁.act (1, 1)) (1, 1))
    (h0_2 : ProjEquiv (M₂.act (1, 0)) (1, 0))
    (h1_2 : ProjEquiv (M₂.act (0, 1)) (0, 1))
    (hinf_2 : ProjEquiv (M₂.act (1, 1)) (1, 1)) :
    PglEquiv M₁ M₂ := by
  intro p
  rcases test_moebius_fix_standard_scalar M₁ h0_1 h1_1 hinf_1 with ⟨hb1, hc1, had1⟩
  rcases test_moebius_fix_standard_scalar M₂ h0_2 h1_2 hinf_2 with ⟨hb2, hc2, had2⟩
  dsimp [MoebiusMatrix.act, ProjEquiv]
  linear_combination
    (p.1 * p.2 * M₂.d) * had1 -
    (p.1 * p.2 * M₁.d) * had2 +
    (p.1^2 * M₁.a) * hc2 -
    (p.1^2 * M₂.a) * hc1 +
    (p.2^2 * M₂.d + p.1 * p.2 * M₂.c) * hb1 -
    (p.2^2 * M₁.d + p.1 * p.2 * M₁.c) * hb2

end TestDisks
#print axioms TestDisks.test_north_pole_not_mem_disk_0_2
#print axioms TestDisks.test_north_pole_not_mem_disk_all
#print axioms TestDisks.test_north_pole_not_mem_disk_large
#print axioms TestDisks.test_north_pole_not_mem_annulus_all
#print axioms TestDisks.test_disk_at_mono_abstract
#print axioms TestDisks.test_disk_at_mono_concrete
#print axioms TestDisks.test_center_mem_disk_at_pos
#print axioms TestDisks.test_disk_at_nonempty_pos
#print axioms TestDisks.test_center_ne_north_pole
#print axioms TestDisks.test_disk_at_empty_of_nonpos
#print axioms TestDisks.test_disk_at_is_open
#print axioms TestDisks.test_disk_at_measurable
#print axioms TestDisks.test_annulus_subset_disk
#print axioms TestDisks.test_no_h_trans_in_exists_moebius
#print axioms TestDisks.test_hv12
#print axioms TestDisks.test_hv23
#print axioms TestDisks.test_hv13
#print axioms TestDisks.test_hw12
#print axioms TestDisks.test_hw23
#print axioms TestDisks.test_hw13
#print axioms TestDisks.test_trip_eval_1
#print axioms TestDisks.test_trip_eval_2
#print axioms TestDisks.test_trip_eval_3
#print axioms TestDisks.test_trip_eval_fourth_point
#print axioms TestDisks.test_trip_det_ne_zero
#print axioms TestDisks.test_moebius_fix_three_standard_is_id
#print axioms TestDisks.test_moebius_fix_standard_scalar
#print axioms TestDisks.test_moebius_unique_fixing_standard
