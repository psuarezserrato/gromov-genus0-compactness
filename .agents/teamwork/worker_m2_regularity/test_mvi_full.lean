import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Hofer

open Metric Set MeasureTheory

noncomputable def laplacian2D (e : ℂ → ℝ) (z : ℂ) : ℝ :=
  (iteratedFDeriv ℝ 2 e z) ![1, 1] + (iteratedFDeriv ℝ 2 e z) ![Complex.I, Complex.I]

lemma mvi_branch_zero (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall (0 : ℂ) r))
    (h_int_zero : ∫ w in Metric.ball (0 : ℂ) r, e w = 0)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) (r / 2)) :
    e z = 0 := by
  have hz_in_ball : z ∈ Metric.ball (0 : ℂ) r := by
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith
  have h_sub : Metric.ball (0 : ℂ) r ⊆ Metric.closedBall (0 : ℂ) r := ball_subset_closedBall
  have he_cont_ball : ContinuousOn e (Metric.ball (0 : ℂ) r) := he_cont.mono h_sub
  have he_intble : IntegrableOn e (Metric.ball (0 : ℂ) r) volume := by
    have h_comp : IsCompact (Metric.closedBall (0 : ℂ) r) := isCompact_closedBall 0 r
    have h_intble_closed : IntegrableOn e (Metric.closedBall (0 : ℂ) r) volume :=
      he_cont.integrableOn_compact (μ := volume) h_comp
    exact h_intble_closed.mono_set h_sub
  have he_ae_nonneg : 0 ≤ᵐ[volume.restrict (Metric.ball (0 : ℂ) r)] e := by
    apply Filter.Eventually.of_forall
    intro w
    exact he_nonneg w
  have he_ae_zero : e =ᵐ[volume.restrict (Metric.ball (0 : ℂ) r)] 0 := by
    rw [← setIntegral_eq_zero_iff_of_nonneg_ae he_ae_nonneg he_intble]
    exact h_int_zero
  have he_eq : EqOn e 0 (Metric.ball (0 : ℂ) r) :=
    Measure.eqOn_open_of_ae_eq he_ae_zero isOpen_ball he_cont_ball continuousOn_const
  exact he_eq hz_in_ball
