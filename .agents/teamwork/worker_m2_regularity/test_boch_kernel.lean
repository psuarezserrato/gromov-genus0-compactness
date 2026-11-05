import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Complex.Basic
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.Monotonicity

open scoped Manifold ContDiff Topology
open Metric Set GromovCompactness GromovCompactness.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

theorem iteratedFDeriv_two_zero_of_not_diff (f : ℂ → ℝ) (w : ℂ)
    (h : ¬ DifferentiableAt ℝ (iteratedFDeriv ℝ 1 f) w) :
    iteratedFDeriv ℝ 2 f w = 0 := by
  ext m
  rw [iteratedFDeriv_succ_apply_left]
  have h0 : fderiv ℝ (iteratedFDeriv ℝ 1 f) w = 0 := fderiv_zero_of_not_differentiableAt h
  rw [h0]
  rfl

theorem laplacian2D_zero_of_not_diff (f : ℂ → ℝ) (w : ℂ)
    (h : ¬ DifferentiableAt ℝ (iteratedFDeriv ℝ 1 f) w) :
    laplacian2D f w = 0 := by
  dsimp [laplacian2D]
  have h2 := iteratedFDeriv_two_zero_of_not_diff f w h
  rw [h2]
  simp

theorem bochner_proof_attempt :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ),
        -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
          c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
        laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w := by
  use 1, 0
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro u hu w
  let e := fun z => riemannianEnergyDensity I u (stereo_chart.symm z)
  have he_nonneg : 0 ≤ e w := riemannianEnergyDensity_nonneg I u (stereo_chart.symm w)
  by_cases h : -1 * (e w)^2 - 0 * (e w) ≤ laplacian2D e w
  · exact h
  · push_neg at h
    have h_lap_neg : laplacian2D e w < 0 := by
      have : -1 * (e w)^2 ≤ 0 := by nlinarith
      linarith
    have h_diff : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 e) w := by
      by_contra h_nd
      have h0 := laplacian2D_zero_of_not_diff e w h_nd
      linarith
    sorry
