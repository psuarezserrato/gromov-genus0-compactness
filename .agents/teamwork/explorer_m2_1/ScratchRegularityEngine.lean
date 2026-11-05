import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Hofer
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.Monotonicity
import GromovCompactness.Analysis.Bochner

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness
open GromovCompactness.Analysis

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/- =========================================================================
   PART 1: Machine-Checked Lemmas for Laplacian of Non-Differentiable Functions
   ========================================================================= -/

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

/- =========================================================================
   PART 2: Constant and Trivial Curves
   ========================================================================= -/

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

/- =========================================================================
   PART 3: Machine-Checked Hofer Lemma Invocation for 2D Disks
   ========================================================================= -/

theorem hofer_disk_application (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_cont : Continuous e) (he_nonneg : ∀ y, 0 ≤ e y) :
    ∃ (ε' : ℝ), 0 < ε' ∧ ∃ (x' : ℂ),
      ε' ≤ r / 4 ∧
      dist x' 0 ≤ r / 2 ∧
      (r / 4) * e 0 ≤ ε' * e x' ∧
      ∀ y, dist x' y ≤ ε' → e y ≤ 2 * e x' := by
  have hr4_pos : 0 < r / 4 := by linarith
  obtain ⟨ε', hε'_pos, x', hε'_le, hdist, h_val, h_double⟩ :=
    hofer (0 : ℂ) (r / 4) hr4_pos he_cont he_nonneg
  refine ⟨ε', hε'_pos, x', hε'_le, ?_, h_val, h_double⟩
  linarith

#print axioms hofer_disk_application
