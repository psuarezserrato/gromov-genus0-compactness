/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Analysis.HoferRescaling
import Mathlib.Topology.MetricSpace.Bounded

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory Filter GromovCompactness GromovCompactness.Analysis

namespace GromovCompactness.Bubbling

/-!
# Task B03: Vanishing Neck Energy and Diameter

This module formalizes the vanishing of symplectic energy and target metric diameter on the
annular neck connecting the base curve to the rescaled bubble, following Gromov (1985, §2.2),
Ivashkovich-Shevchishin (1999, §2.3), and `gromov_compactness.pdf` §4.6 (Task `B03`).

## Key Theorem
- `neck_vanishing_quantified`: Quantified $\forall \eta > 0, \exists R_0, \dots$ vanishing of neck energy and diameter.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-- The target distance between two points in any subset is controlled by the diameter of its image (Zero-sorry). -/
lemma dist_le_diam_of_mem_image (u : CP1 → M) (s : Set CP1) {z w : CP1} (hz : z ∈ s) (hw : w ∈ s) :
    dist (u z) (u w) ≤ Metric.diam (u '' s) := by
  have hz_im : u z ∈ u '' s := mem_image_of_mem _ hz
  have hw_im : u w ∈ u '' s := mem_image_of_mem _ hw
  have h_bdd : Bornology.IsBounded (u '' s) := isCompact_univ.isBounded.subset (subset_univ _)
  exact dist_le_diam_of_mem h_bdd hz_im hw_im

/-- Any concentric annulus is contained within the outer disk (Zero-sorry). -/
lemma annulus_at_subset_disk_at (a : ℂ) (r₁ r₂ : ℝ) :
    annulus_at a r₁ r₂ ⊆ disk_at a r₂ := by
  dsimp [annulus_at, disk_at]
  apply image_subset
  intro z hz
  simp only [mem_setOf_eq] at hz
  simp only [mem_ball]
  exact hz.2

/-- An annulus with degenerate or reversed radii is empty (Zero-sorry). -/
lemma annulus_at_empty_of_ge (a : ℂ) {r₁ r₂ : ℝ} (h : r₂ ≤ r₁) :
    annulus_at a r₁ r₂ = ∅ := by
  dsimp [annulus_at]
  have h_empty : {w : ℂ | r₁ < dist w a ∧ dist w a < r₂} = ∅ := by
    ext w
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    intro h1
    linarith
  rw [h_empty]
  exact image_empty _

/-- Vanishing Neck Energy and Target Diameter (Contract B03).
For every target margin `η > 0`, there exist a scaling ratio threshold `R₀ > 1` and an outer radius `δ₀ > 0`
such that for any `R ≥ R₀` and `δ ∈ (0, δ₀)`, the annular neck `A(Rλ_n, δ; a_n)` asymptotically has
symplectic energy `< η` and image diameter `< η`. -/
theorem neck_vanishing_quantified
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  sorry

/-- Pointwise distance oscillation bound from diameter bound on an annulus (Zero-sorry Foundation). -/
lemma neck_pointwise_oscillation_of_diam_bound
    (u : CP1 → M) (a : ℂ) (r δ : ℝ) (η : ℝ)
    (h_diam : Metric.diam (Set.image u (annulus_at a r δ)) < η) :
    ∀ z w, z ∈ annulus_at a r δ → w ∈ annulus_at a r δ → dist (u z) (u w) < η := by
  intro z w hz hw
  have h_le := dist_le_diam_of_mem_image (u := u) (s := annulus_at a r δ) hz hw
  exact lt_of_le_of_lt h_le h_diam

/-- Companion Pointwise Distance Oscillation Bound on Neck Annuli (Contract B03, Zero-sorry).
The pointwise distance between any two points on the neck annulus vanishes asymptotically.
This is proved as a direct corollary of the diameter bound in `neck_vanishing_quantified`. -/
theorem neck_pointwise_oscillation_bound
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η := by
  have h_neck := neck_vanishing_quantified I u_seq thresh m_defect res η hη
  obtain ⟨R₀, hR₀, hR⟩ := h_neck
  refine ⟨R₀, hR₀, fun R hR_ge => ?_⟩
  obtain ⟨δ₀, hδ₀, hδ⟩ := hR R hR_ge
  refine ⟨δ₀, hδ₀, fun δ hδ_in => ?_⟩
  obtain ⟨N, hN⟩ := hδ δ hδ_in
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h_scale, _h_en, h_diam⟩ := hN n hn
  refine ⟨h_scale, neck_pointwise_oscillation_of_diam_bound (u_seq n) (res.a n) (R * res.«λ» n) δ η h_diam⟩

end GromovCompactness.Bubbling

