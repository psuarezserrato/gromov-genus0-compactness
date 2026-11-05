import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Hofer
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness

namespace TestAssembly

noncomputable def laplacian2D (e : ℂ → ℝ) (z : ℂ) : ℝ :=
  (iteratedFDeriv ℝ 2 e z) ![1, 1] + (iteratedFDeriv ℝ 2 e z) ![Complex.I, Complex.I]

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

lemma laplacian2D_of_iterated_one_zero (f : ℂ → ℝ) (w : ℂ)
    (h1 : iteratedFDeriv ℝ 1 f = fun _ => 0) :
    laplacian2D f w = 0 := by
  dsimp [laplacian2D]
  have h2 : iteratedFDeriv ℝ 2 f w = 0 := by
    ext m
    rw [iteratedFDeriv_succ_apply_left, h1]
    have h0 : fderiv ℝ (fun _ : ℂ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => ℂ) ℝ)) w = 0 :=
      fderiv_const_apply 0
    rw [h0]
    rfl
  rw [h2]
  simp

lemma laplacian2D_const (c : ℝ) (w : ℂ) :
    laplacian2D (fun _ => c) w = 0 := by
  apply laplacian2D_of_iterated_one_zero
  ext z v
  rw [iteratedFDeriv_one_apply]
  have : fderiv ℝ (fun _ : ℂ => c) z = 0 := fderiv_const_apply c
  rw [this]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

theorem energy_density_const_map (x₀ : M) (z : CP1) :
    riemannianEnergyDensity I (fun _ => x₀) z = 0 := by
  dsimp [riemannianEnergyDensity]
  have h1 : mfderiv I_CP1 I (fun _ => x₀) z e1 = 0 := by
    rw [mfderiv_const]
    rfl
  have h2 : mfderiv I_CP1 I (fun _ => x₀) z e2 = 0 := by
    rw [mfderiv_const]
    rfl
  rw [h1, h2]
  dsimp [ClosedTameTarget.metric]
  simp

end TestAssembly
