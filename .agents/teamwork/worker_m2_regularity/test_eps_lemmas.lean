import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp

open Metric Set MeasureTheory

/-- Translation invariance of Lebesgue integrals over Euclidean metric balls on ℂ. -/
lemma integral_translate_ball (a : ℂ) (r : ℝ) (g : ℂ → ℝ) :
    ∫ w in ball (0 : ℂ) r, g (a + w) = ∫ w in ball a r, g w := by
  have h_pres : MeasurePreserving (fun x => a + x) volume volume := measurePreserving_add_left volume a
  have h_emb : MeasurableEmbedding (fun x => a + x) := (Homeomorph.addLeft a).measurableEmbedding
  have h_pre : (fun x => a + x) ⁻¹' (ball a r) = ball (0 : ℂ) r := by
    ext w
    simp only [Set.mem_preimage, mem_ball, dist_zero_right, dist_eq_norm]
    ring_nf
  have h := MeasureTheory.MeasurePreserving.setIntegral_preimage_emb h_pres h_emb g (ball a r)
  rw [h_pre] at h
  exact h

/-- Point translation preserves inclusion from concentric half-radius ball to closed ball around 0. -/
lemma ball_translate_to_closedBall (a w₀ : ℂ) (r : ℝ) (hw : w₀ ∈ ball a (r / 2)) :
    w₀ - a ∈ closedBall (0 : ℂ) (r / 2) := by
  simp only [mem_ball, mem_closedBall, dist_zero_right] at *
  rw [dist_eq_norm] at hw
  exact hw.le
