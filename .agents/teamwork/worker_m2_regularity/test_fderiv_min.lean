import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic

open Filter

lemma fderiv_eq_zero_of_global_min {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) (h_nonneg : ∀ y, 0 ≤ f y) (h_zero : f x = 0) :
    fderiv ℝ f x = 0 := by
  by_cases h_diff : DifferentiableAt ℝ f x
  · have h_min : IsLocalMin f x := by
      apply Filter.Eventually.of_forall
      intro y
      rw [h_zero]
      exact h_nonneg y
    exact h_min.fderiv_eq_zero
  · exact fderiv_zero_of_not_differentiableAt h_diff
