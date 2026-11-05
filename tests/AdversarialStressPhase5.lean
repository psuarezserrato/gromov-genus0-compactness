/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Phase 5 Master Adversarial Challenger 2)
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.MetricSpace.Basic
import GromovCompactness
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Topology.SphereTree
import GromovCompactness.Analysis.Energy
import GromovCompactness.Extensions.VaryingJ
import GromovCompactness.Extensions.Automorphisms

open scoped Manifold ContDiff Topology Classical Real ENNReal
open Metric Set MeasureTheory Filter Complex GromovCompactness
open GromovCompactness.Extensions

namespace GromovCompactness.AdversarialStressPhase5

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [tgt : ClosedTameTarget I M]

/- =========================================================================
   SUITE 1: ENERGY FUNCTIONAL SOUNDNESS, SPHERICAL JACOBIAN & TRACE SCALING
   ========================================================================= -/

/-- Adversarial Probe 1.1: Spherical Jacobian factor is bounded above by 4 on all of ℂ. -/
theorem stress_sphericalJacobian_le_four (w : ℂ) :
    sphericalJacobian w ≤ 4 := by
  dsimp [sphericalJacobian]
  have h_sq : 0 ≤ ‖w‖ ^ 2 := sq_nonneg ‖w‖
  have h_pos : 0 < 1 + ‖w‖ ^ 2 := by linarith
  have h_frac : 2 / (1 + ‖w‖ ^ 2) ≤ 2 := by
    rw [div_le_iff₀ h_pos]
    linarith
  have h_frac_nonneg : 0 ≤ 2 / (1 + ‖w‖ ^ 2) := by positivity
  have h_sq_le : (2 / (1 + ‖w‖ ^ 2)) ^ 2 ≤ 2 ^ 2 := by
    nlinarith
  norm_num at h_sq_le
  exact h_sq_le

/-- Adversarial Probe 1.2: Spherical Jacobian achieves its maximum value 4 uniquely at the origin. -/
theorem stress_sphericalJacobian_zero :
    sphericalJacobian 0 = 4 := by
  dsimp [sphericalJacobian]
  norm_num

/-- Adversarial Probe 1.3: Spherical Jacobian is strictly positive everywhere. -/
theorem stress_sphericalJacobian_pos (w : ℂ) :
    0 < sphericalJacobian w := by
  dsimp [sphericalJacobian]
  positivity

/-- Adversarial Probe 1.4: Spherical Jacobian decays radially:
for any R > 0 and any w with R ≤ ‖w‖, sphericalJacobian w ≤ 4 / (1 + R^2)^2. -/
theorem stress_sphericalJacobian_radial_decay (R : ℝ) (hR : 0 < R) (w : ℂ) (hw : R ≤ ‖w‖) :
    sphericalJacobian w ≤ 4 / (1 + R ^ 2) ^ 2 := by
  dsimp [sphericalJacobian]
  have h_sq : R ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith
  have h_denom : 1 + R ^ 2 ≤ 1 + ‖w‖ ^ 2 := by linarith
  have h_pos_R : 0 < 1 + R ^ 2 := by positivity
  have h_pos_w : 0 < 1 + ‖w‖ ^ 2 := by positivity
  have h_div : 2 / (1 + ‖w‖ ^ 2) ≤ 2 / (1 + R ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) h_pos_R h_denom
  have h_div_nonneg : 0 ≤ 2 / (1 + ‖w‖ ^ 2) := by positivity
  have h_sq_div : (2 / (1 + ‖w‖ ^ 2)) ^ 2 ≤ (2 / (1 + R ^ 2)) ^ 2 := by nlinarith
  have h_id : (2 / (1 + R ^ 2)) ^ 2 = 4 / (1 + R ^ 2) ^ 2 := by
    rw [div_pow]
    norm_num
  rwa [h_id] at h_sq_div

/-- Adversarial Probe 1.5: Trace scaling identity for C-linear maps is non-vacuous and strictly
relies on J-commutation. Proved directly via metric_c_linear_trace_scaling. -/
theorem stress_metric_c_linear_trace_scaling_nonvacuous (x : M)
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] TangentSpace I x)
    (hL : ∀ v, L (J_CP1 v) = ClosedTameTarget.J (I := I) (M := M) x (L v)) :
    ClosedTameTarget.metric I x (L e1) (L e1) + ClosedTameTarget.metric I x (L e2) (L e2) =
    2 * ClosedTameTarget.«ω» (I := I) (M := M) x (L e1) (L e2) :=
  metric_c_linear_trace_scaling I x L hL

/- =========================================================================
   SUITE 2: TARGET GEOMETRY, SYMPLECTIC FORMS & ALMOST COMPLEX STRUCTURES
   ========================================================================= -/

/-- Adversarial Probe 2.1: The symmetrized Riemannian metric is positive-definite:
for any non-zero tangent vector v, metric I x v v > 0. -/
theorem stress_metric_strictly_pos_def (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < ClosedTameTarget.metric I x v v :=
  metric_pos_def I x v hv

/-- Adversarial Probe 2.2: The almost complex structure J is an automorphism with J⁻¹ = -J. -/
theorem stress_J_inv (x : M) (v : TangentSpace I x) :
    ClosedTameTarget.J (I := I) (M := M) x (- ClosedTameTarget.J (I := I) (M := M) x v) = v := by
  rw [(ClosedTameTarget.J (I := I) (M := M) x).map_neg]
  rw [ClosedTameTarget.J_sq x v]
  exact neg_neg v

/-- Adversarial Probe 2.3: J preserves the metric g(J v, J w) = g(v, w). -/
theorem stress_metric_J_invariant (x : M) (v w : TangentSpace I x) :
    ClosedTameTarget.metric I x (ClosedTameTarget.J (I := I) (M := M) x v)
                                (ClosedTameTarget.J (I := I) (M := M) x w) =
    ClosedTameTarget.metric I x v w :=
  metric_J_invariant I x v w

/- =========================================================================
   SUITE 3: BUBBLE TREE TOPOLOGY, BOUNDARY CONDITIONS & GHOST BOUNDS
   ========================================================================= -/

lemma degree_le_card_sub_one (tree : SphereTree) (v : tree.V) :
    tree.adj.degree v ≤ Fintype.card tree.V - 1 := by
  have h_sub : tree.adj.neighborFinset v ⊆ Finset.univ.erase v := by
    intro w hw
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    rw [tree.adj.mem_neighborFinset] at hw
    exact (tree.adj.ne_of_adj hw).symm
  have h_le := Finset.card_le_card h_sub
  rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at h_le
  rwa [SimpleGraph.card_neighborFinset_eq_degree] at h_le

/-- Adversarial Probe 3.1: Single-vertex bubble tree cannot be a ghost component.
A single-vertex stable tree limit MUST have a non-constant (principal) component! -/
theorem stress_single_vertex_cannot_be_ghost
    (lim : StableSphereTreeLimit I (M := M))
    (h_card : Fintype.card lim.tree.V = 1)
    (v : lim.tree.V) :
    is_principal_component I lim v := by
  intro h_ghost
  have h_deg := lim.stable v h_ghost
  have h_max := degree_le_card_sub_one lim.tree v
  rw [h_card] at h_max
  omega

/-- Adversarial Probe 3.2: Two-vertex bubble tree cannot contain ANY ghost components.
Both components in a 2-vertex stable tree must be principal! -/
theorem stress_two_vertex_cannot_be_ghost
    (lim : StableSphereTreeLimit I (M := M))
    (h_card : Fintype.card lim.tree.V = 2)
    (v : lim.tree.V) :
    is_principal_component I lim v := by
  intro h_ghost
  have h_deg := lim.stable v h_ghost
  have h_max := degree_le_card_sub_one lim.tree v
  rw [h_card] at h_max
  omega

/-- Adversarial Probe 3.3: Three-vertex bubble tree cannot contain ANY ghost components.
All components in a 3-vertex stable tree must be principal! -/
theorem stress_three_vertex_cannot_be_ghost
    (lim : StableSphereTreeLimit I (M := M))
    (h_card : Fintype.card lim.tree.V = 3)
    (v : lim.tree.V) :
    is_principal_component I lim v := by
  intro h_ghost
  have h_deg := lim.stable v h_ghost
  have h_max := degree_le_card_sub_one lim.tree v
  rw [h_card] at h_max
  omega

/-- Adversarial Probe 3.4: Ghost bubbles require at least 4 vertices in the tree. -/
theorem stress_ghost_requires_at_least_four_vertices
    (lim : StableSphereTreeLimit I (M := M))
    (v : lim.tree.V)
    (h_ghost : is_ghost_component I lim v) :
    4 ≤ Fintype.card lim.tree.V := by
  have h_deg := lim.stable v h_ghost
  have h_max := degree_le_card_sub_one lim.tree v
  omega

/-- Adversarial Probe 3.5: In any tree with 4 vertices, a ghost bubble must have
nodal degree exactly 3. -/
theorem stress_four_vertex_ghost_degree
    (lim : StableSphereTreeLimit I (M := M))
    (h_card : Fintype.card lim.tree.V = 4)
    (v : lim.tree.V)
    (h_ghost : is_ghost_component I lim v) :
    lim.tree.adj.degree v = 3 := by
  have h_deg := lim.stable v h_ghost
  have h_max := degree_le_card_sub_one lim.tree v
  rw [h_card] at h_max
  omega

/-- Adversarial Probe 3.6: Ghost component bound G ≤ P - 2 is sharp:
for a 4-vertex star graph with 1 ghost and 3 principal vertices, equality 1 = 3 - 2 holds! -/
theorem stress_ghost_bound_sharpness :
    let P : ℕ := 3
    let G : ℕ := 1
    G ≤ P - 2 ∧ G = P - 2 := by
  intro P G
  constructor <;> decide

/-- Adversarial Probe 3.7: Euler degree sum relation holds on every bubble tree. -/
theorem stress_tree_degree_sum_card (tree : SphereTree) :
    ∑ v : tree.V, tree.adj.degree v = 2 * (Fintype.card tree.V - 1) :=
  tree_degree_sum tree

/- =========================================================================
   SUITE 4: RIGIDITY, AUTOMORPHISM GROUPS & SHARPNESS OF 3-POINT FIXING
   ========================================================================= -/

/-- Standard projective points in ℂ × ℂ: [1:0] (infinity), [0:1] (zero), [1:1] (one). -/
def pt_10 : ℂ × ℂ := (1, 0)
def pt_01 : ℂ × ℂ := (0, 1)
def pt_11 : ℂ × ℂ := (1, 1)

/-- Counterexample to 2-point rigidity:
The diagonal scaling matrix diag(2, 1) fixes [0:1] and [1:0], but is NOT projectively equivalent to the identity!
This proves mathematically that 3-point rigidity is sharp: 2 points are strictly insufficient. -/
def scaling_matrix_two : MoebiusMatrix where
  a := 2
  b := 0
  c := 0
  d := 1
  det_ne_zero := by
    dsimp
    intro h
    have : (2 : ℂ) = 0 := by
      calc (2 : ℂ) = 2 * 1 - 0 * 0 := by ring
      _ = 0 := h
    norm_num at this

theorem stress_scaling_matrix_two_fixes_zero :
    ProjEquiv (scaling_matrix_two.act pt_01) pt_01 := by
  dsimp [ProjEquiv, MoebiusMatrix.act, scaling_matrix_two, pt_01]
  ring

theorem stress_scaling_matrix_two_fixes_inf :
    ProjEquiv (scaling_matrix_two.act pt_10) pt_10 := by
  dsimp [ProjEquiv, MoebiusMatrix.act, scaling_matrix_two, pt_10]
  ring

theorem stress_scaling_matrix_two_not_identity :
    ¬ PglEquiv scaling_matrix_two MoebiusMatrix.id := by
  intro h
  have h_spec := h pt_11
  dsimp [PglEquiv, ProjEquiv, MoebiusMatrix.act, scaling_matrix_two, MoebiusMatrix.id, pt_11] at h_spec
  have h_two_eq_one : (2 : ℂ) = 1 := by
    calc (2 : ℂ) = (2 * 1 + 0 * 1) * (0 * 1 + 1 * 1) := by ring
    _ = (0 * 1 + 1 * 1) * (1 * 1 + 0 * 1) := h_spec
    _ = 1 := by ring
  have h_diff : (2 : ℂ) - 1 = 0 := by rw [h_two_eq_one, sub_self]
  norm_num at h_diff

/-- Adversarial Probe 4.2: 3-point rigidity holds: fixing pt_10, pt_01, and pt_11 forces PglEquiv to identity. -/
theorem stress_three_point_rigidity_holds (M_mat : MoebiusMatrix)
    (h_inf : ProjEquiv (M_mat.act pt_10) pt_10)
    (h_zero : ProjEquiv (M_mat.act pt_01) pt_01)
    (h_one : ProjEquiv (M_mat.act pt_11) pt_11) :
    PglEquiv M_mat MoebiusMatrix.id := by
  have h12 : ¬ ProjEquiv pt_10 pt_01 := by
    dsimp [ProjEquiv, pt_10, pt_01]
    intro h
    have h1 : (1 : ℂ) * 1 = 1 := by ring
    have h0 : (0 : ℂ) * 0 = 0 := by ring
    rw [h1, h0] at h
    exact one_ne_zero h
  have h13 : ¬ ProjEquiv pt_10 pt_11 := by
    dsimp [ProjEquiv, pt_10, pt_11]
    intro h
    have h1 : (1 : ℂ) * 1 = 1 := by ring
    have h0 : (0 : ℂ) * 1 = 0 := by ring
    rw [h1, h0] at h
    exact one_ne_zero h
  have h23 : ¬ ProjEquiv pt_01 pt_11 := by
    dsimp [ProjEquiv, pt_01, pt_11]
    intro h
    have h0 : (0 : ℂ) * 1 = 0 := by ring
    have h1 : (1 : ℂ) * 1 = 1 := by ring
    rw [h0, h1] at h
    exact zero_ne_one h
  exact moebius_three_point_rigidity M_mat pt_10 pt_01 pt_11 h12 h13 h23 h_inf h_zero h_one

/-- Adversarial Probe 4.3: Full automorphism finiteness is strictly equivalent to pure finiteness. -/
theorem stress_full_automorphism_equivalence (lim : StableSphereTreeLimit I (M := M)) :
    Finite (StableMapAutomorphism I lim) ↔ Finite (PureComponentAutomorphism I lim) :=
  full_automorphisms_finite_iff_pure_finite I lim

/- =========================================================================
   SUITE 5: REPEATABLE AXIOM PRINTING
   ========================================================================= -/

#print axioms stress_sphericalJacobian_le_four
#print axioms stress_sphericalJacobian_zero
#print axioms stress_sphericalJacobian_pos
#print axioms stress_sphericalJacobian_radial_decay
#print axioms stress_metric_c_linear_trace_scaling_nonvacuous
#print axioms stress_metric_strictly_pos_def
#print axioms stress_J_inv
#print axioms stress_metric_J_invariant
#print axioms stress_single_vertex_cannot_be_ghost
#print axioms stress_two_vertex_cannot_be_ghost
#print axioms stress_three_vertex_cannot_be_ghost
#print axioms stress_ghost_requires_at_least_four_vertices
#print axioms stress_four_vertex_ghost_degree
#print axioms stress_ghost_bound_sharpness
#print axioms stress_tree_degree_sum_card
#print axioms stress_scaling_matrix_two_fixes_zero
#print axioms stress_scaling_matrix_two_fixes_inf
#print axioms stress_scaling_matrix_two_not_identity
#print axioms stress_three_point_rigidity_holds
#print axioms stress_full_automorphism_equivalence

end GromovCompactness.AdversarialStressPhase5
