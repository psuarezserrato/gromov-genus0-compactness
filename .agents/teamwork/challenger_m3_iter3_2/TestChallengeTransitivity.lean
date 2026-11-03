import GromovCompactness.Geometry.Sphere

/-!
# Adversarial Challenge Test Harness: Three-Point Transitivity & Geometric Regions
Agent: `challenger_m3_iter3_2`
File under test: `GromovCompactness.Geometry.Sphere`

This test file adversarially challenges:
1. `PglEquiv`: equivalence relation axioms (reflexivity, symmetry, transitivity) and non-triviality
   (non-trivial quotient: identifies scalar multiples, but separates distinct operations like rotation/inversion).
2. `exists_unique_moebius_three_points` and `moebius_three_points_unique`:
   - Standard configuration $(\infty, 0, 1) \mapsto (\infty, 0, 1)$, confirming identity modulo `PglEquiv`.
   - Cyclic permutation configuration $(\infty, 0, 1) \mapsto (0, 1, \infty)$, confirming non-identity modulo `PglEquiv`.
   - General complex point configuration $(2, 1), (1, 2), (1, -1) \mapsto (\infty, 0, 1)$.
   - Scale-invariance stress test: scalar multiple matrices are projectively identified by uniqueness.
3. Geometric regions `disk_at`, `annulus_at`, `circle_at`:
   - North pole ($\infty$) exclusion across disk, annulus, and circle.
   - Center containment and non-positive radius emptiness for disks.
   - Center exclusion and degenerate emptiness for annuli.
   - Disjointness of boundary circle from disk interior and annulus.
   - Inclusions $\text{circle}(r) \subset \text{disk}(R)$ and $\text{annulus}(r, R) \subset \text{disk}(R)$.
-/

open GromovCompactness

namespace TestChallengeTransitivity

/- =========================================================================
   PART 1: PglEquiv ALGEBRAIC EQUIVALENCE AND NON-TRIVIALITY
   ========================================================================= -/

/-- Reflexivity of `PglEquiv`. -/
theorem challenge_pglEquiv_refl (M : MoebiusMatrix) : PglEquiv M M :=
  PglEquiv.refl M

/-- Symmetry of `PglEquiv`. -/
theorem challenge_pglEquiv_symm {M N : MoebiusMatrix} (h : PglEquiv M N) : PglEquiv N M :=
  PglEquiv.symm h

/-- Helper lemma: Nonzero vectors are mapped to nonzero vectors by invertible Möbius matrices. -/
lemma act_ne_zero (M : MoebiusMatrix) {p : ℂ × ℂ} (hp : p ≠ (0, 0)) : M.act p ≠ (0, 0) := by
  intro h_zero
  have h_adj : M.adj.act (M.act p) = (0, 0) := by
    rw [h_zero]
    dsimp [MoebiusMatrix.act]
    simp
  have h_comp : M.adj.act (M.act p) = ((M.a * M.d - M.b * M.c) * p.1, (M.a * M.d - M.b * M.c) * p.2) := by
    dsimp [MoebiusMatrix.adj, MoebiusMatrix.act]
    ext <;> ring
  rw [h_comp] at h_adj
  have h_det := M.det_ne_zero
  have hp1 : p.1 = 0 := by
    have h1 : (M.a * M.d - M.b * M.c) * p.1 = 0 := Prod.ext_iff.mp h_adj |>.1
    exact mul_eq_zero.mp h1 |>.resolve_left h_det
  have hp2 : p.2 = 0 := by
    have h2 : (M.a * M.d - M.b * M.c) * p.2 = 0 := Prod.ext_iff.mp h_adj |>.2
    exact mul_eq_zero.mp h2 |>.resolve_left h_det
  exact hp (Prod.ext hp1 hp2)

/-- Transitivity of `PglEquiv`. -/
theorem challenge_pglEquiv_trans {M N K : MoebiusMatrix} (hMN : PglEquiv M N) (hNK : PglEquiv N K) :
    PglEquiv M K := by
  intro p
  by_cases hp : p = (0, 0)
  · subst hp
    dsimp [MoebiusMatrix.act, ProjEquiv]
    ring
  · have hN_ne : N.act p ≠ (0, 0) := act_ne_zero N hp
    exact ProjEquiv.trans hN_ne (hMN p) (hNK p)

/-- Non-triviality check 1: Scalar multiple matrix $S_2 = 2 \cdot I$ is NOT equal to identity matrix in $GL(2, \mathbb{C})$. -/
def S2 : MoebiusMatrix where
  a := 2
  b := 0
  c := 0
  d := 2
  det_ne_zero := by norm_num

theorem challenge_S2_ne_id : S2 ≠ MoebiusMatrix.id := by
  intro h
  have : S2.a = MoebiusMatrix.id.a := by rw [h]
  dsimp [S2, MoebiusMatrix.id] at this
  norm_num at this

/-- Non-triviality check 1 (cont): Scalar multiple matrix $S_2$ IS equivalent to identity in $PGL(2, \mathbb{C})$. -/
theorem challenge_pglEquiv_S2_id : PglEquiv S2 MoebiusMatrix.id := by
  intro p
  dsimp [PglEquiv, ProjEquiv, S2, MoebiusMatrix.id, MoebiusMatrix.act]
  ring

/-- Non-triviality check 2 (Separation): Inversion/rotation matrix $J$ is NOT equivalent to identity in $PGL(2, \mathbb{C})$. -/
def J_mat : MoebiusMatrix where
  a := 0
  b := 1
  c := -1
  d := 0
  det_ne_zero := by norm_num

theorem challenge_not_pglEquiv_J_id : ¬ PglEquiv J_mat MoebiusMatrix.id := by
  intro h
  have h1 := h (1, 0)
  dsimp [PglEquiv, ProjEquiv, J_mat, MoebiusMatrix.id, MoebiusMatrix.act] at h1
  norm_num at h1

/- =========================================================================
   PART 2: THREE-POINT TRANSITIVITY & UNIQUENESS TEST CONFIGURATIONS
   ========================================================================= -/

def std_v1 : ℂ × ℂ := (1, 0)
def std_v2 : ℂ × ℂ := (0, 1)
def std_v3 : ℂ × ℂ := (1, 1)

lemma std_v12 : ¬ ProjEquiv std_v1 std_v2 := by
  intro h; dsimp [ProjEquiv, std_v1, std_v2] at h; norm_num at h

lemma std_v23 : ¬ ProjEquiv std_v2 std_v3 := by
  intro h; dsimp [ProjEquiv, std_v2, std_v3] at h; norm_num at h

lemma std_v13 : ¬ ProjEquiv std_v1 std_v3 := by
  intro h; dsimp [ProjEquiv, std_v1, std_v3] at h; norm_num at h

lemma std_v31 : ¬ ProjEquiv std_v3 std_v1 := by
  intro h; exact std_v13 (ProjEquiv.symm h)

lemma std_v21 : ¬ ProjEquiv std_v2 std_v1 := by
  intro h; exact std_v12 (ProjEquiv.symm h)

/-- Configuration 1: Standard triple $(\infty, 0, 1)$ mapped to itself.
    The resulting Möbius transformation must equal identity modulo `PglEquiv`. -/
theorem challenge_standard_configuration :
    ∃ (M : MoebiusMatrix),
      (ProjEquiv (M.act std_v1) std_v1 ∧
       ProjEquiv (M.act std_v2) std_v2 ∧
       ProjEquiv (M.act std_v3) std_v3) ∧
      PglEquiv M MoebiusMatrix.id := by
  obtain ⟨M, ⟨h1, h2, h3⟩, h_uniq⟩ :=
    exists_unique_moebius_three_points std_v1 std_v2 std_v3 std_v1 std_v2 std_v3
      std_v12 std_v23 std_v13 std_v12 std_v23 std_v13
  refine ⟨M, ⟨h1, h2, h3⟩, ?_⟩
  have h_id_1 : ProjEquiv (MoebiusMatrix.id.act std_v1) std_v1 := by
    dsimp [MoebiusMatrix.id, MoebiusMatrix.act, ProjEquiv, std_v1]; ring
  have h_id_2 : ProjEquiv (MoebiusMatrix.id.act std_v2) std_v2 := by
    dsimp [MoebiusMatrix.id, MoebiusMatrix.act, ProjEquiv, std_v2]; ring
  have h_id_3 : ProjEquiv (MoebiusMatrix.id.act std_v3) std_v3 := by
    dsimp [MoebiusMatrix.id, MoebiusMatrix.act, ProjEquiv, std_v3]; ring
  exact h_uniq MoebiusMatrix.id h_id_1 h_id_2 h_id_3

/-- Configuration 2: Cyclic permutation $(\infty, 0, 1) \mapsto (0, 1, \infty)$.
    The resulting Möbius transformation is provably NOT equivalent to the identity. -/
theorem challenge_cyclic_permutation_configuration :
    ∃ (M : MoebiusMatrix),
      (ProjEquiv (M.act std_v1) std_v2 ∧
       ProjEquiv (M.act std_v2) std_v3 ∧
       ProjEquiv (M.act std_v3) std_v1) ∧
      ¬ PglEquiv M MoebiusMatrix.id := by
  obtain ⟨M, ⟨h1, h2, h3⟩, _⟩ :=
    exists_unique_moebius_three_points std_v1 std_v2 std_v3 std_v2 std_v3 std_v1
      std_v12 std_v23 std_v13 std_v23 std_v31 std_v21
  refine ⟨M, ⟨h1, h2, h3⟩, ?_⟩
  intro h_id
  have h_act1 : ProjEquiv (M.act std_v1) (MoebiusMatrix.id.act std_v1) := h_id std_v1
  have h_id_act : ProjEquiv (MoebiusMatrix.id.act std_v1) std_v1 := by
    dsimp [MoebiusMatrix.id, MoebiusMatrix.act, ProjEquiv, std_v1]; ring
  have h_M_v1 : ProjEquiv (M.act std_v1) std_v1 := by
    have h_id_act_ne : MoebiusMatrix.id.act std_v1 ≠ (0, 0) := by
      dsimp [MoebiusMatrix.id, MoebiusMatrix.act, std_v1]; norm_num
    exact ProjEquiv.trans h_id_act_ne h_act1 h_id_act
  have h_v2_v1 : ProjEquiv std_v2 std_v1 := by
    have h_M_act_ne : M.act std_v1 ≠ (0, 0) := act_ne_zero M (by dsimp [std_v1]; norm_num)
    exact ProjEquiv.trans h_M_act_ne (ProjEquiv.symm h1) h_M_v1
  exact std_v21 h_v2_v1

/-- Configuration 3: General arbitrary complex points $(2, 1), (1, 2), (1, -1) \mapsto (\infty, 0, 1)$. -/
def u1 : ℂ × ℂ := (2, 1)
def u2 : ℂ × ℂ := (1, 2)
def u3 : ℂ × ℂ := (1, -1)

lemma u12 : ¬ ProjEquiv u1 u2 := by
  intro h; dsimp [ProjEquiv, u1, u2] at h; norm_num at h

lemma u23 : ¬ ProjEquiv u2 u3 := by
  intro h; dsimp [ProjEquiv, u2, u3] at h; norm_num at h

lemma u13 : ¬ ProjEquiv u1 u3 := by
  intro h; dsimp [ProjEquiv, u1, u3] at h; norm_num at h

theorem challenge_general_points_configuration :
    ∃ (M : MoebiusMatrix),
      (ProjEquiv (M.act u1) std_v1 ∧
       ProjEquiv (M.act u2) std_v2 ∧
       ProjEquiv (M.act u3) std_v3) ∧
      (∀ (M' : MoebiusMatrix),
        ProjEquiv (M'.act u1) std_v1 →
        ProjEquiv (M'.act u2) std_v2 →
        ProjEquiv (M'.act u3) std_v3 →
        PglEquiv M M') :=
  exists_unique_moebius_three_points u1 u2 u3 std_v1 std_v2 std_v3
    u12 u23 u13 std_v12 std_v23 std_v13

/-- Configuration 4: Stress-testing uniqueness with scaled matrices. -/
def scale_mat (c : ℂ) (hc : c ≠ 0) (M : MoebiusMatrix) : MoebiusMatrix where
  a := c * M.a
  b := c * M.b
  c := c * M.c
  d := c * M.d
  det_ne_zero := by
    have h1 : (c * M.a) * (c * M.d) - (c * M.b) * (c * M.c) = c^2 * (M.a * M.d - M.b * M.c) := by ring
    rw [h1]
    exact mul_ne_zero (pow_ne_zero 2 hc) M.det_ne_zero

lemma scale_mat_act (c : ℂ) (hc : c ≠ 0) (M : MoebiusMatrix) (p : ℂ × ℂ) :
    ProjEquiv ((scale_mat c hc M).act p) (M.act p) := by
  dsimp [scale_mat, MoebiusMatrix.act, ProjEquiv]
  ring

theorem challenge_scaled_matrix_uniqueness (M : MoebiusMatrix) (c : ℂ) (hc : c ≠ 0)
    (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ)
    (hv12 : ¬ ProjEquiv v₁ v₂) (hv23 : ¬ ProjEquiv v₂ v₃) (hv13 : ¬ ProjEquiv v₁ v₃)
    (hw12 : ¬ ProjEquiv w₁ w₂) (hw23 : ¬ ProjEquiv w₂ w₃) (hw13 : ¬ ProjEquiv w₁ w₃)
    (h1 : ProjEquiv (M.act v₁) w₁)
    (h2 : ProjEquiv (M.act v₂) w₂)
    (h3 : ProjEquiv (M.act v₃) w₃) :
    PglEquiv M (scale_mat c hc M) := by
  have hv1_ne : v₁ ≠ (0, 0) := ne_zero_of_not_projEquiv hv12
  have hv2_ne : v₂ ≠ (0, 0) := ne_zero_of_not_projEquiv hv23
  have hv3_ne : v₃ ≠ (0, 0) := ne_zero_of_not_projEquiv (fun h => hv13 (ProjEquiv.symm h))
  have hs1 : ProjEquiv ((scale_mat c hc M).act v₁) w₁ := by
    have hM_ne : M.act v₁ ≠ (0, 0) := act_ne_zero M hv1_ne
    exact ProjEquiv.trans hM_ne (scale_mat_act c hc M v₁) h1
  have hs2 : ProjEquiv ((scale_mat c hc M).act v₂) w₂ := by
    have hM_ne : M.act v₂ ≠ (0, 0) := act_ne_zero M hv2_ne
    exact ProjEquiv.trans hM_ne (scale_mat_act c hc M v₂) h2
  have hs3 : ProjEquiv ((scale_mat c hc M).act v₃) w₃ := by
    have hM_ne : M.act v₃ ≠ (0, 0) := act_ne_zero M hv3_ne
    exact ProjEquiv.trans hM_ne (scale_mat_act c hc M v₃) h3
  exact moebius_three_points_unique M (scale_mat c hc M) v₁ v₂ v₃ w₁ w₂ w₃
    hv12 hv23 hv13 hw12 hw23 hw13 h1 h2 h3 hs1 hs2 hs3

/- =========================================================================
   PART 3: GEOMETRIC REGIONS CHALLENGE (disk_at, annulus_at, circle_at)
   ========================================================================= -/

/-- Challenge north pole exclusion from disk. -/
theorem challenge_north_pole_exclusion_disk (a : ℂ) (r : ℝ) :
    north_pole ∉ disk_at a r :=
  north_pole_not_mem_disk_at a r

/-- Challenge north pole exclusion from annulus. -/
theorem challenge_north_pole_exclusion_annulus (a : ℂ) (r R : ℝ) :
    north_pole ∉ annulus_at a r R :=
  north_pole_not_mem_annulus_at a r R

/-- Challenge north pole exclusion from circle boundary. -/
theorem challenge_north_pole_exclusion_circle (a : ℂ) (r : ℝ) :
    north_pole ∉ circle_at a r := by
  intro h
  rcases h with ⟨w, _, hw_eq⟩
  have h_source := stereo_chart.map_target (show w ∈ stereo_chart.target by simp [stereo_chart])
  rw [hw_eq] at h_source
  dsimp [stereo_chart] at h_source
  simp only [PartialHomeomorph.transHomeomorph_source, stereographic'_source] at h_source
  exact h_source rfl

/-- Challenge disk center containment for positive radius. -/
theorem challenge_disk_center_containment_pos (a : ℂ) {r : ℝ} (hr : 0 < r) :
    stereo_chart.symm a ∈ disk_at a r :=
  center_mem_disk_at a hr

/-- Challenge disk emptiness for non-positive radius $r \le 0$. -/
theorem challenge_disk_empty_nonpos (a : ℂ) {r : ℝ} (hr : r ≤ 0) :
    disk_at a r = ∅ := by
  dsimp [disk_at]
  rw [Metric.ball_eq_empty.mpr hr]
  exact Set.image_empty _

/-- Challenge annulus center exclusion for $r \ge 0$. -/
theorem challenge_annulus_center_exclusion (a : ℂ) {r R : ℝ} (hr : 0 ≤ r) :
    stereo_chart.symm a ∉ annulus_at a r R := by
  intro h
  rcases h with ⟨z, hz, hz_eq⟩
  have h_target : z ∈ stereo_chart.target := by simp [stereo_chart_target]
  have h_a_target : a ∈ stereo_chart.target := by simp [stereo_chart_target]
  have h_inj : z = a := by
    have h1 := stereo_chart.right_inv h_target
    have h2 := stereo_chart.right_inv h_a_target
    rw [← h1, ← h2, hz_eq]
  rw [h_inj] at hz
  simp only [Set.mem_setOf_eq, dist_self] at hz
  linarith

/-- Challenge annulus emptiness when $R \le r$. -/
theorem challenge_annulus_empty_le (a : ℂ) {r R : ℝ} (h : R ≤ r) :
    annulus_at a r R = ∅ := by
  dsimp [annulus_at]
  have : {z : ℂ | r < dist z a ∧ dist z a < R} = ∅ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hr
    linarith
  rw [this, Set.image_empty]

/-- Challenge circle center exclusion for $r > 0$. -/
theorem challenge_circle_center_exclusion (a : ℂ) {r : ℝ} (hr : 0 < r) :
    stereo_chart.symm a ∉ circle_at a r := by
  intro h
  rcases h with ⟨z, hz, hz_eq⟩
  have h_target : z ∈ stereo_chart.target := by simp [stereo_chart_target]
  have h_a_target : a ∈ stereo_chart.target := by simp [stereo_chart_target]
  have h_inj : z = a := by
    have h1 := stereo_chart.right_inv h_target
    have h2 := stereo_chart.right_inv h_a_target
    rw [← h1, ← h2, hz_eq]
  rw [h_inj] at hz
  simp only [Metric.mem_sphere, dist_self] at hz
  linarith

/-- Challenge boundary disjointness: circle and disk of radius $r$ are disjoint. -/
theorem challenge_disjoint_circle_disk (a : ℂ) (r : ℝ) :
    Disjoint (circle_at a r) (disk_at a r) := by
  rw [Set.disjoint_left]
  rintro x ⟨z, hz, rfl⟩ ⟨w, hw, hw_eq⟩
  have h_inj : z = w := by
    have h1 := stereo_chart.right_inv (show z ∈ stereo_chart.target by simp [stereo_chart_target])
    have h2 := stereo_chart.right_inv (show w ∈ stereo_chart.target by simp [stereo_chart_target])
    rw [← h1, ← h2, hw_eq]
  rw [h_inj] at hz
  simp only [Metric.mem_sphere] at hz
  simp only [Metric.mem_ball] at hw
  linarith

/-- Challenge boundary disjointness: circle of radius $r$ and annulus $(r, R)$ are disjoint. -/
theorem challenge_disjoint_circle_annulus (a : ℂ) (r R : ℝ) :
    Disjoint (circle_at a r) (annulus_at a r R) := by
  rw [Set.disjoint_left]
  rintro x ⟨z, hz, rfl⟩ ⟨w, hw, hw_eq⟩
  have h_inj : z = w := by
    have h1 := stereo_chart.right_inv (show z ∈ stereo_chart.target by simp [stereo_chart_target])
    have h2 := stereo_chart.right_inv (show w ∈ stereo_chart.target by simp [stereo_chart_target])
    rw [← h1, ← h2, hw_eq]
  rw [h_inj] at hz
  simp only [Metric.mem_sphere] at hz
  simp only [Set.mem_setOf_eq] at hw
  linarith

/-- Challenge boundary inclusion: circle of radius $r$ is subset of disk of radius $R$ when $r < R$. -/
theorem challenge_circle_subset_disk (a : ℂ) {r R : ℝ} (h : r < R) :
    circle_at a r ⊆ disk_at a R := by
  dsimp [circle_at, disk_at]
  apply Set.image_subset
  intro z hz
  simp only [Metric.mem_sphere] at hz
  simp only [Metric.mem_ball]
  linarith

/-- Challenge annulus inclusion in disk. -/
theorem challenge_annulus_subset_disk (a : ℂ) (r R : ℝ) :
    annulus_at a r R ⊆ disk_at a R :=
  annulus_subset_disk a r R

end TestChallengeTransitivity

/- Axiom verification checks -/
#print axioms TestChallengeTransitivity.challenge_pglEquiv_refl
#print axioms TestChallengeTransitivity.challenge_pglEquiv_symm
#print axioms TestChallengeTransitivity.challenge_pglEquiv_trans
#print axioms TestChallengeTransitivity.challenge_S2_ne_id
#print axioms TestChallengeTransitivity.challenge_pglEquiv_S2_id
#print axioms TestChallengeTransitivity.challenge_not_pglEquiv_J_id
#print axioms TestChallengeTransitivity.challenge_standard_configuration
#print axioms TestChallengeTransitivity.challenge_cyclic_permutation_configuration
#print axioms TestChallengeTransitivity.challenge_general_points_configuration
#print axioms TestChallengeTransitivity.challenge_scaled_matrix_uniqueness
#print axioms TestChallengeTransitivity.challenge_north_pole_exclusion_disk
#print axioms TestChallengeTransitivity.challenge_north_pole_exclusion_annulus
#print axioms TestChallengeTransitivity.challenge_north_pole_exclusion_circle
#print axioms TestChallengeTransitivity.challenge_disk_center_containment_pos
#print axioms TestChallengeTransitivity.challenge_disk_empty_nonpos
#print axioms TestChallengeTransitivity.challenge_annulus_center_exclusion
#print axioms TestChallengeTransitivity.challenge_annulus_empty_le
#print axioms TestChallengeTransitivity.challenge_circle_center_exclusion
#print axioms TestChallengeTransitivity.challenge_disjoint_circle_disk
#print axioms TestChallengeTransitivity.challenge_disjoint_circle_annulus
#print axioms TestChallengeTransitivity.challenge_circle_subset_disk
#print axioms TestChallengeTransitivity.challenge_annulus_subset_disk
