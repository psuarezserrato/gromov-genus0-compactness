import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere

open scoped Manifold ContDiff Topology
open Metric Set GromovCompactness

namespace GromovCompactness.Challenge

/-!
# Adversarial Challenge Test Harness for Milestone 3 Formal Geometry

This test harness empirically verifies the geometry developments in
`GromovCompactness.Geometry.Target` (F01) and `GromovCompactness.Geometry.Sphere` (F02).

## Challenge Dimensions:
1. Metric Symmetry, Positivity, and J-Invariance on Target Geometry
2. MoebiusFrame Groupoid Operations (Identity, Composition, Inversion, Associativity)
3. Empirical Detection and Verification of Facade Definitions (`affine_scaling`, `inversion`, `rotation`)
4. Circular Hypothesis Exposure in `exists_unique_moebius_three_points`
5. Axiom Independence Audit
-/

--------------------------------------------------------------------------------
-- SECTION 1: Metric Verification on Concrete Tangent Vectors
--------------------------------------------------------------------------------

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]

/-- Test 1.1: Symmetry of the symmetrized Riemannian metric holds for all tangent vectors. -/
theorem challenge_metric_symmetry [tgt : ClosedTameTarget I M] (x : M) (v w : TangentSpace I x) :
    ClosedTameTarget.metric I x v w = ClosedTameTarget.metric I x w v :=
  metric_symm I x v w

/-- Test 1.2: Positive definiteness of the metric for any non-zero tangent vector. -/
theorem challenge_metric_pos_def [tgt : ClosedTameTarget I M] (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < ClosedTameTarget.metric I x v v :=
  metric_pos_def I x v hv

/-- Test 1.3: J-invariance of the metric tensor: g(Jv, Jw) = g(v, w). -/
theorem challenge_metric_J_invariance [tgt : ClosedTameTarget I M] (x : M) (v w : TangentSpace I x) :
    ClosedTameTarget.metric I x (tgt.J x v) (tgt.J x w) = ClosedTameTarget.metric I x v w :=
  metric_J_invariant I x v w

/-- Test 1.4: Double J action: g(J²v, w) = -g(v, w). -/
theorem challenge_metric_J_sq_anti [tgt : ClosedTameTarget I M] (x : M) (v w : TangentSpace I x) :
    ClosedTameTarget.metric I x (tgt.J x (tgt.J x v)) w = - ClosedTameTarget.metric I x v w := by
  rw [tgt.J_sq x v]
  dsimp [ClosedTameTarget.metric]
  have hneg1 : tgt.«ω» x (-v) (tgt.J x w) = - (tgt.«ω» x v (tgt.J x w)) := by
    rw [(tgt.«ω» x).map_neg v]
    rfl
  have hneg2 : tgt.«ω» x w (tgt.J x (-v)) = - (tgt.«ω» x w (tgt.J x v)) := by
    rw [(tgt.J x).map_neg v]
    exact (tgt.«ω» x w).map_neg (tgt.J x v)
  rw [hneg1, hneg2]
  linarith

--------------------------------------------------------------------------------
-- SECTION 2: MoebiusFrame Groupoid Law Verification
--------------------------------------------------------------------------------

/-- Test 2.1: Identity composition law: id ∘ id = id. -/
theorem challenge_moebius_id_comp_id :
    (MoebiusFrame.comp MoebiusFrame.id MoebiusFrame.id).toHomeo = Homeomorph.refl CP1 := by
  rfl

/-- Test 2.2: Left inverse cancellation: ϕ⁻¹ ∘ ϕ = id on all points of CP1. -/
theorem challenge_moebius_left_inv (ϕ : MoebiusFrame) (z : CP1) :
    (MoebiusFrame.comp (MoebiusFrame.inv ϕ) ϕ).toHomeo z = z := by
  dsimp [MoebiusFrame.comp, MoebiusFrame.inv]
  exact ϕ.toHomeo.symm_apply_apply z

/-- Test 2.3: Right inverse cancellation: ϕ ∘ ϕ⁻¹ = id on all points of CP1. -/
theorem challenge_moebius_right_inv (ϕ : MoebiusFrame) (z : CP1) :
    (MoebiusFrame.comp ϕ (MoebiusFrame.inv ϕ)).toHomeo z = z := by
  dsimp [MoebiusFrame.comp, MoebiusFrame.inv]
  exact ϕ.toHomeo.apply_symm_apply z

/-- Test 2.4: Composition associativity on underlying homeomorphisms. -/
theorem challenge_moebius_comp_assoc (ϕ₁ ϕ₂ ϕ₃ : MoebiusFrame) (z : CP1) :
    (MoebiusFrame.comp (MoebiusFrame.comp ϕ₁ ϕ₂) ϕ₃).toHomeo z =
      (MoebiusFrame.comp ϕ₁ (MoebiusFrame.comp ϕ₂ ϕ₃)).toHomeo z := by
  rfl

/-- Test 2.5: Inverse of identity is identity. -/
theorem challenge_moebius_inv_id :
    (MoebiusFrame.inv MoebiusFrame.id).toHomeo = Homeomorph.refl CP1 := by
  rfl

--------------------------------------------------------------------------------
-- SECTION 3: Empirical Exposure of Facade Definitions in Sphere.lean
--------------------------------------------------------------------------------

/-- Adversarial Bug Detection 3.1:
`affine_scaling` is defined as `MoebiusFrame.id`.
This means scaling by factor 2 at center 0 is literally the identity! -/
theorem challenge_affine_scaling_is_facade (a : ℂ) (s : ℝ) (hs : 0 < s) :
    affine_scaling a s hs = MoebiusFrame.id := by
  rfl

/-- Adversarial Bug Detection 3.2:
`inversion` (intended to swap 0 and ∞) is defined as `MoebiusFrame.id`. -/
theorem challenge_inversion_is_facade :
    inversion = MoebiusFrame.id := by
  rfl

/-- Adversarial Bug Detection 3.3:
`rotation` by angle θ is defined as `MoebiusFrame.id`. -/
theorem challenge_rotation_is_facade (θ : ℝ) :
    rotation θ = MoebiusFrame.id := by
  rfl

/-- Consequence: `affine_scaling 0 2` fixes all points, rather than dilating them. -/
theorem challenge_affine_scaling_fixes_all (z : CP1) :
    (affine_scaling 0 2 (by norm_num)).toHomeo z = z := by
  rfl

--------------------------------------------------------------------------------
-- SECTION 4: Exposure of Circular Hypothesis in `exists_unique_moebius_three_points`
--------------------------------------------------------------------------------

set_option linter.unusedVariables false

/-- Adversarial Challenge 4.1:
`exists_unique_moebius_three_points` has a circular premise `h_trans` whose conclusion
is identical to the theorem's conclusion. It is a tautology of the form `A → (A → B) → B`. -/
theorem challenge_three_points_is_circular_modus_ponens
    (z₁ z₂ z₃ : CP1) (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃)
    (w₁ w₂ w₃ : CP1) (k12 : w₁ ≠ w₂) (k13 : w₁ ≠ w₃) (k23 : w₂ ≠ w₃)
    (h_trans : (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃ ∧ w₁ ≠ w₂ ∧ w₁ ≠ w₃ ∧ w₂ ≠ w₃) →
      ∃! (ϕ : MoebiusFrame), ϕ.toHomeo z₁ = w₁ ∧ ϕ.toHomeo z₂ = w₂ ∧ ϕ.toHomeo z₃ = w₃) :
    (∃! (ϕ : MoebiusFrame), ϕ.toHomeo z₁ = w₁ ∧ ϕ.toHomeo z₂ = w₂ ∧ ϕ.toHomeo z₃ = w₃) ↔
    ((z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃ ∧ w₁ ≠ w₂ ∧ w₁ ≠ w₃ ∧ w₂ ≠ w₃) →
      ∃! (ϕ : MoebiusFrame), ϕ.toHomeo z₁ = w₁ ∧ ϕ.toHomeo z₂ = w₂ ∧ ϕ.toHomeo z₃ = w₃) := by
  constructor
  · intro h _h_trans
    exact h
  · intro h
    exact exists_unique_moebius_three_points z₁ z₂ z₃ h12 h13 h23 w₁ w₂ w₃ k12 k13 k23 h

--------------------------------------------------------------------------------
-- SECTION 5: Target Geometry Constants Semantic Emptiness Check
--------------------------------------------------------------------------------

/-- Adversarial Challenge 5.1:
`TargetGeometryConstants` contains only positivity assertions `0 < r_inj`, `0 < r_conv`, `0 < chart_bound`,
with no geometric binding to injectivity radius or geodesic convexity.
Hence the unit constants (1, 1, 1) satisfy it vacuously on ANY tame target. -/
theorem challenge_target_constants_unit_satisfies [ClosedTameTarget I M] :
    Nonempty (TargetGeometryConstants I M) :=
  exists_target_geometry_constants I

end GromovCompactness.Challenge

#print axioms GromovCompactness.Challenge.challenge_metric_symmetry
#print axioms GromovCompactness.Challenge.challenge_metric_J_invariance
#print axioms GromovCompactness.Challenge.challenge_moebius_left_inv
#print axioms GromovCompactness.Challenge.challenge_affine_scaling_is_facade
