import GromovCompactness.Geometry.Sphere
import GromovCompactness.Geometry.Target
import Mathlib.Analysis.InnerProductSpace.PiL2

open Metric Set

namespace GromovCompactness.Challenge

/-!
# Adversarial Challenge Test Harness for Task F01 & F02

This test file verifies the mathematical behavior and surfaces failure modes:
1. Challenge 1 (Integrity / Tautology): `exists_unique_moebius_three_points` relies on `h_trans`.
2. Challenge 2 (Integrity / Facade): `affine_scaling`, `inversion`, `rotation` are degenerate to `id`.
3. Challenge 3 (Geometric defect): `disk_at` includes antipodal / pole points.
4. Genuine Successes: `metric_J_invariant`, `J_CP1_sq`, `MoebiusFrame.comp`.
-/

-- Challenge 2 Demonstration: affine_scaling is identically identity regardless of scale
theorem affine_scaling_is_identity (a : ℂ) (scale : ℝ) (hscale : 0 < scale) :
    (affine_scaling a scale hscale).toHomeo = (MoebiusFrame.id).toHomeo := by
  rfl

theorem inversion_is_identity :
    inversion.toHomeo = (MoebiusFrame.id).toHomeo := by
  rfl

theorem rotation_is_identity (θ : ℝ) :
    (rotation θ).toHomeo = (MoebiusFrame.id).toHomeo := by
  rfl

-- Challenge 3 Demonstration: disk_at 0 2 contains the pole (0, 0, 1)
noncomputable def northPole : CP1 :=
  ⟨EuclideanSpace.single (2 : Fin 3) 1, by
    rw [mem_sphere_zero_iff_norm]
    simp [EuclideanSpace.norm_single]⟩

theorem north_pole_in_disk_at_zero_two :
    northPole ∈ disk_at 0 2 := by
  dsimp [disk_at, northPole]
  have h0 : (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (0 : Fin 3) = 0 := by
    simp [EuclideanSpace.single_apply]
  have h1 : (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (1 : Fin 3) = 0 := by
    simp [EuclideanSpace.single_apply]
  rw [h0, h1]
  norm_num

end GromovCompactness.Challenge
