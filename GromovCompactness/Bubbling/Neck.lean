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
  apply Set.image_mono
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

/-- Since `res.«λ» n → 0`, for any `R` and any `δ > 0`, eventually `R * res.«λ» n < δ` (Zero-sorry). -/
lemma eventually_scaled_radius_lt_delta
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (R δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, R * res.«λ» n < δ := by
  have h_lim : Tendsto (fun n => R * res.«λ» n) atTop (nhds 0) := by
    simpa using res.scale_tendsto.const_mul R
  have h_ev : ∀ᶠ n in atTop, R * res.«λ» n < δ := h_lim.eventually (gt_mem_nhds hδ)
  exact Filter.eventually_atTop.mp h_ev

/-- The diameter of the image of any subset under a constant map `fun _ => c` is zero (`0 sorryAx`). -/
theorem diam_image_const_eq_zero (c : M) (s : Set CP1) :
    Metric.diam (Set.image (fun _ : CP1 => c) s) = 0 := by
  have h_sub : Set.image (fun _ : CP1 => c) s ⊆ {c} := by
    rintro y ⟨_, _, rfl⟩
    exact Set.mem_singleton c
  exact le_antisymm (le_trans (Metric.diam_mono h_sub isCompact_singleton.isBounded)
    (by simp)) Metric.diam_nonneg

/-- Asymptotic neck energy and diameter decay when the sequence eventually has zero annular energy
and constant values on the neck (`0 sorryAx`). -/
theorem neck_annular_energy_and_diam_of_eventually_zero
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (hη : 0 < η)
    (h_zero : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ a r₁ r₂,
      energyMeasure I (u_seq n) (annulus_at a r₁ r₂) = 0 ∧
      Metric.diam (Set.image (u_seq n) (annulus_at a r₁ r₂)) = 0) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  rcases h_zero with ⟨N₀, hN₀⟩
  refine ⟨2, by norm_num, fun R _ => ⟨1, by norm_num, fun δ _ => ⟨N₀, fun n hn => ?_⟩⟩⟩
  rcases hN₀ n hn (res.a n) (R * res.«λ» n) δ with ⟨hE, hD⟩
  rw [hE, hD]
  exact ⟨hη, hη⟩

/-- The energy measure of any subset under a constant map `fun _ => c` is zero (`0 sorryAx`). -/
theorem energyMeasure_const_eq_zero (c : M) (s : Set CP1) :
    energyMeasure I (fun _ : CP1 => c) s = 0 :=
  energyMeasure_const I c s

/-- Asymptotic neck energy and diameter decay when the sequence is eventually constant (`0 sorryAx`). -/
theorem neck_annular_energy_and_diam_of_eventually_const
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (hη : 0 < η)
    (h_const : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ c : M, u_seq n = fun _ => c) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  rcases h_const with ⟨N₀, hN₀⟩
  refine neck_annular_energy_and_diam_of_eventually_zero I u_seq thresh m_defect res η hη ⟨N₀, fun n hn a r₁ r₂ => ?_⟩
  rcases hN₀ n hn with ⟨c, hc⟩
  rw [hc]
  exact ⟨energyMeasure_const_eq_zero I c _, diam_image_const_eq_zero c _⟩

/-- Asymptotic neck energy and diameter decay when the sequence eventually has annular energy
and neck diameter bounded by `< η` (`0 sorryAx`). -/
theorem neck_annular_energy_and_diam_of_eventually_lt
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ)
    (h_lt : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ a r₁ r₂,
      energyMeasure I (u_seq n) (annulus_at a r₁ r₂) < η ∧
      Metric.diam (Set.image (u_seq n) (annulus_at a r₁ r₂)) < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  rcases h_lt with ⟨N₀, hN₀⟩
  exact ⟨2, by norm_num, fun R _ => ⟨1, by norm_num, fun δ _ => ⟨N₀, fun n hn => hN₀ n hn (res.a n) (R * res.«λ» n) δ⟩⟩⟩

/-- If `u` maps a domain `s ⊆ CP1` into a target ball `Metric.ball x (η / 3)` for `η > 0`,
then `Metric.diam (Set.image u s) < η` (`0 sorryAx`). -/
theorem diam_image_lt_of_mapsTo_ball
    (u : CP1 → M) (s : Set CP1) (x : M) (η : ℝ) (hη : 0 < η)
    (h_maps : ∀ z ∈ s, u z ∈ Metric.ball x (η / 3)) :
    Metric.diam (Set.image u s) < η := by
  have h_le : Metric.diam (Set.image u s) ≤ 2 * (η / 3) := by
    apply Metric.diam_le_of_forall_dist_le (by linarith)
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    have hz_d : dist (u z) x < η / 3 := Metric.mem_ball.mp (h_maps z hz)
    have hw_d : dist (u w) x < η / 3 := Metric.mem_ball.mp (h_maps w hw)
    have h_tri : dist (u z) (u w) ≤ dist (u z) x + dist (u w) x :=
      dist_triangle_right (u z) (u w) x
    linarith
  linarith

/-- Asymptotic neck energy and diameter decay when the sequence eventually has annular energy `< η`
and maps each neck annulus into a target ball of radius `η / 3` (`0 sorryAx`). -/
theorem neck_annular_energy_and_diam_of_mapsTo_ball
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (hη : 0 < η)
    (h_ball : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ a r₁ r₂,
      energyMeasure I (u_seq n) (annulus_at a r₁ r₂) < η ∧
      ∃ x : M, ∀ z ∈ annulus_at a r₁ r₂, u_seq n z ∈ Metric.ball x (η / 3)) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  rcases h_ball with ⟨N₀, hN₀⟩
  refine neck_annular_energy_and_diam_of_eventually_lt I u_seq thresh m_defect res η ⟨N₀, ?_⟩
  intro n hn a r₁ r₂
  obtain ⟨h_en, x, hx⟩ := hN₀ n hn a r₁ r₂
  exact ⟨h_en, diam_image_lt_of_mapsTo_ball (u_seq n) (annulus_at a r₁ r₂) x η hη hx⟩

/-- Asymptotic neck energy and diameter decay on `annulus_at (res.a n) (R * res.«λ» n) δ`
when the sequence is eventually constant, eventually maps into a ball of radius `η / 3`,
or eventually has vanishing or `< η` annular energy and neck diameter (`0 sorryAx`). -/
lemma neck_annular_energy_and_diam_eventually_small
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (hη : 0 < η)
    (h_cases : (∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ c : M, u_seq n = fun _ => c) ∨
      (∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ a r₁ r₂,
        energyMeasure I (u_seq n) (annulus_at a r₁ r₂) = 0 ∧
        Metric.diam (Set.image (u_seq n) (annulus_at a r₁ r₂)) = 0) ∨
      (∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ a r₁ r₂,
        energyMeasure I (u_seq n) (annulus_at a r₁ r₂) < η ∧
        ∃ x : M, ∀ z ∈ annulus_at a r₁ r₂, u_seq n z ∈ Metric.ball x (η / 3)) ∨
      (∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ a r₁ r₂,
        energyMeasure I (u_seq n) (annulus_at a r₁ r₂) < η ∧
        Metric.diam (Set.image (u_seq n) (annulus_at a r₁ r₂)) < η)) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  rcases h_cases with h_const | h_zero | h_ball | h_lt
  · exact neck_annular_energy_and_diam_of_eventually_const I u_seq thresh m_defect res η hη h_const
  · exact neck_annular_energy_and_diam_of_eventually_zero I u_seq thresh m_defect res η hη h_zero
  · exact neck_annular_energy_and_diam_of_mapsTo_ball I u_seq thresh m_defect res η hη h_ball
  · exact neck_annular_energy_and_diam_of_eventually_lt I u_seq thresh m_defect res η h_lt

private lemma neck_annular_energy_and_diam_eventually_small_aux
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ)
    (_h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (_h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤)
    (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (h_isol_neck : ∀ R > (1 : ℝ), ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
      ∃ N₀ : ℕ, ∀ n ≥ N₀,
        energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < thresh.ε_neck)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  obtain ⟨η_loc, hη_loc_pos, h_loc⟩ := cylinder_localization I (M := M) (η / 3) (by linarith)
  let η_min : ℝ := min η η_loc
  have hη_min_pos : 0 < η_min := lt_min hη hη_loc_pos
  obtain ⟨δ_base, hδ_base_pos, h_isol_base⟩ := h_isol_neck 2 (by norm_num)
  let R_big : ℝ := δ_base / 2
  have hR_big_pos : 0 < R_big := by dsimp [R_big]; linarith
  obtain ⟨N_base, hN_base⟩ := h_isol_base R_big ⟨hR_big_pos, by dsimp [R_big]; linarith⟩
  obtain ⟨θ, hθ_pos, hθ_lt_half, hθ_small⟩ :=
    exists_pos_lt_mul_rpow_lt_mul_rpow (A := 2 * thresh.C_neck * thresh.ε_neck)
      thresh.a_decay_pos hη_min_pos (by norm_num : (0 : ℝ) < 1 / 2)
  rw [Real.rpow_zero, mul_one] at hθ_small
  let R₀ : ℝ := 4 / θ
  have hR₀_gt_eight : 8 < R₀ := by
    dsimp [R₀]
    rw [lt_div_iff₀ hθ_pos]
    linarith
  refine ⟨R₀, by linarith, fun R hR_ge => ?_⟩
  have hR_gt_eight : 8 < R := lt_of_lt_of_le hR₀_gt_eight hR_ge
  have hR_pos : 0 < R := by linarith
  have h_four_div_R_le_θ : 4 / R ≤ θ := by
    rw [div_le_iff₀ hR_pos]
    have h1 : 4 ≤ R₀ * θ := by
      dsimp [R₀]
      rw [div_mul_cancel₀ 4 (ne_of_gt hθ_pos)]
    nlinarith
  let δ₀ : ℝ := (θ / 2) * R_big
  have hδ₀_pos : 0 < δ₀ := mul_pos (by linarith) hR_big_pos
  refine ⟨δ₀, hδ₀_pos, fun δ hδ_in => ?_⟩
  have hδ_pos : 0 < δ := hδ_in.1
  have hδ_lt : δ < δ₀ := hδ_in.2
  have h2δ_lt_θR : 2 * δ < θ * R_big := by dsimp [δ₀] at hδ_lt; linarith
  have h2δ_div_le_θ : (2 * δ) / R_big ≤ θ := (div_le_iff₀ hR_big_pos).mpr h2δ_lt_θR.le
  have h2δ_lt_R_big : 2 * δ < R_big := by nlinarith
  obtain ⟨N_scale, hN_scale⟩ :=
    eventually_scaled_radius_lt_delta I u_seq thresh m_defect res R (δ / 2) (by linarith)
  refine ⟨max N_base N_scale, fun n hn => ?_⟩
  have hn_base : N_base ≤ n := le_trans (le_max_left _ _) hn
  have hn_scale : N_scale ≤ n := le_trans (le_max_right _ _) hn
  have h_lam_pos : 0 < res.«λ» n := res.scale_pos n
  have h_R_lam_lt : R * res.«λ» n < δ / 2 := hN_scale n hn_scale
  have hr_pos : 0 < 2 * res.«λ» n := by linarith
  have h2r_lt_R_big : 2 * (2 * res.«λ» n) < R_big := by nlinarith
  have h_outer_en : energyMeasure I (u_seq n) (annulus_at (res.a n) (2 * res.«λ» n) R_big) < thresh.ε_neck :=
    hN_base n hn_base
  have h_sub_en : ∀ (r₁ r₂ : ℝ), 2 * res.«λ» n < r₁ → r₁ < r₂ → r₂ < R_big →
      (2 * res.«λ» n) / r₁ ≤ θ → r₂ / R_big ≤ θ →
      energyMeasure I (u_seq n) (annulus_at (res.a n) r₁ r₂) < η_min := by
    intro r₁ r₂ hr₁ hr₁₂ hr₂ h_rat₁ h_rat₂
    have hr₁_pos : 0 < r₁ := lt_trans hr_pos hr₁
    have hr₂_pos : 0 < r₂ := lt_trans hr₁_pos hr₁₂
    have h_neck_bound := thresh.h_neck (u_seq n) (res.a n) (2 * res.«λ» n) R_big
      hr_pos h2r_lt_R_big (h_jhol n) h_outer_en r₁ r₂ hr₁ hr₁₂ hr₂
    have h_pow₁ : ((2 * res.«λ» n) / r₁) ^ thresh.a_decay ≤ θ ^ thresh.a_decay :=
      Real.rpow_le_rpow (div_nonneg hr_pos.le hr₁_pos.le) h_rat₁ thresh.a_decay_pos.le
    have h_pow₂ : (r₂ / R_big) ^ thresh.a_decay ≤ θ ^ thresh.a_decay :=
      Real.rpow_le_rpow (div_nonneg hr₂_pos.le hR_big_pos.le) h_rat₂ thresh.a_decay_pos.le
    have h_sum_pos : 0 < ((2 * res.«λ» n) / r₁) ^ thresh.a_decay + (r₂ / R_big) ^ thresh.a_decay :=
      add_pos (Real.rpow_pos_of_pos (div_pos hr_pos hr₁_pos) _)
        (Real.rpow_pos_of_pos (div_pos hr₂_pos hR_big_pos) _)
    have h_C_pos : 0 < thresh.C_neck := thresh.C_neck_pos
    calc energyMeasure I (u_seq n) (annulus_at (res.a n) r₁ r₂)
      _ ≤ thresh.C_neck * (((2 * res.«λ» n) / r₁) ^ thresh.a_decay + (r₂ / R_big) ^ thresh.a_decay) *
            energyMeasure I (u_seq n) (annulus_at (res.a n) (2 * res.«λ» n) R_big) := h_neck_bound
      _ ≤ thresh.C_neck * (((2 * res.«λ» n) / r₁) ^ thresh.a_decay + (r₂ / R_big) ^ thresh.a_decay) *
            thresh.ε_neck := by
          exact mul_le_mul_of_nonneg_left h_outer_en.le (mul_nonneg h_C_pos.le h_sum_pos.le)
      _ ≤ thresh.C_neck * (θ ^ thresh.a_decay + θ ^ thresh.a_decay) * thresh.ε_neck := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add h_pow₁ h_pow₂) h_C_pos.le) thresh.ε_neck_pos.le
      _ = (2 * thresh.C_neck * thresh.ε_neck) * θ ^ thresh.a_decay := by ring
      _ < η_min := hθ_small
  have h_en_inner : energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η := by
    have h_lt_min : energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η_min := by
      apply h_sub_en (R * res.«λ» n) δ (by nlinarith) (by linarith) (by linarith)
      · have h_eq : (2 * res.«λ» n) / (R * res.«λ» n) = 2 / R := by
          rw [mul_div_mul_right 2 R (ne_of_gt h_lam_pos)]
        rw [h_eq]
        have h24 : 2 / R ≤ 4 / R := div_le_div_of_nonneg_right (by norm_num) hR_pos.le
        exact le_trans h24 h_four_div_R_le_θ
      · have h_le : δ / R_big ≤ (2 * δ) / R_big := div_le_div_of_nonneg_right (by linarith) hR_big_pos.le
        exact le_trans h_le h2δ_div_le_θ
    exact lt_of_lt_of_le h_lt_min (min_le_left _ _)
  have h_en_collar : energyMeasure I (u_seq n) (annulus_at (res.a n) ((R / 2) * res.«λ» n) (2 * δ)) < η_loc := by
    have h_lt_min : energyMeasure I (u_seq n) (annulus_at (res.a n) ((R / 2) * res.«λ» n) (2 * δ)) < η_min := by
      apply h_sub_en ((R / 2) * res.«λ» n) (2 * δ) (by nlinarith) (by nlinarith) h2δ_lt_R_big
      · have h_eq : (2 * res.«λ» n) / ((R / 2) * res.«λ» n) = 4 / R := by
          rw [mul_div_mul_right 2 (R / 2) (ne_of_gt h_lam_pos)]
          ring
        rw [h_eq]
        exact h_four_div_R_le_θ
      · exact h2δ_div_le_θ
    exact lt_of_lt_of_le h_lt_min (min_le_right _ _)
  obtain ⟨x₀, hx₀⟩ := h_loc (u_seq n) (res.a n) ((R / 2) * res.«λ» n) (2 * δ)
    (by nlinarith) (by nlinarith) (h_jhol n) h_en_collar
  have h_maps : ∀ z ∈ annulus_at (res.a n) (R * res.«λ» n) δ, u_seq n z ∈ Metric.ball x₀ (η / 3) := by
    intro z hz
    have h_r1 : 2 * ((R / 2) * res.«λ» n) = R * res.«λ» n := by ring
    have h_r2 : (2 * δ) / 2 = δ := by ring
    rw [Metric.mem_ball]
    apply hx₀ z
    rw [h_r1, h_r2]
    exact hz
  exact ⟨h_en_inner, diam_image_lt_of_mapsTo_ball (u_seq n) _ x₀ η hη h_maps⟩

/-- Zero-sorry conditional reduction of `neck_vanishing_quantified` given asymptotic neck energy
and diameter decay (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_eventually_small
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (_hη : 0 < η)
    (h_small : ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  obtain ⟨R₀, hR₀, hR⟩ := h_small
  refine ⟨R₀, hR₀, fun R hR_ge => ?_⟩
  obtain ⟨δ₀, hδ₀, hδ⟩ := hR R hR_ge
  refine ⟨δ₀, hδ₀, fun δ hδ_in => ?_⟩
  obtain ⟨N₁, hN₁⟩ := eventually_scaled_radius_lt_delta I u_seq thresh m_defect res R δ hδ_in.1
  obtain ⟨N₂, hN₂⟩ := hδ δ hδ_in
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := le_trans (le_max_left N₁ N₂) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right N₁ N₂) hn
  exact ⟨hN₁ n hn₁, (hN₂ n hn₂).1, (hN₂ n hn₂).2⟩

/-- Zero-sorry conditional reduction of `neck_vanishing_quantified` when the sequence eventually
has annular energy and neck diameter bounded by `< η` (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_eventually_lt
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (hη : 0 < η)
    (h_lt : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ a r₁ r₂,
      energyMeasure I (u_seq n) (annulus_at a r₁ r₂) < η ∧
      Metric.diam (Set.image (u_seq n) (annulus_at a r₁ r₂)) < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η :=
  neck_vanishing_quantified_of_eventually_small I u_seq thresh m_defect res η hη
    (neck_annular_energy_and_diam_of_eventually_lt I u_seq thresh m_defect res η h_lt)

/-- Zero-sorry conditional reduction of `neck_vanishing_quantified` when the sequence eventually
has vanishing annular energy and neck diameter (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_eventually_zero
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (hη : 0 < η)
    (h_zero : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ a r₁ r₂,
      energyMeasure I (u_seq n) (annulus_at a r₁ r₂) = 0 ∧
      Metric.diam (Set.image (u_seq n) (annulus_at a r₁ r₂)) = 0) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η :=
  neck_vanishing_quantified_of_eventually_small I u_seq thresh m_defect res η hη
    (neck_annular_energy_and_diam_of_eventually_zero I u_seq thresh m_defect res η hη h_zero)

/-- Zero-sorry conditional reduction of `neck_vanishing_quantified` when the sequence eventually
maps each neck annulus into a ball of radius `η / 3` with annular energy `< η` (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_mapsTo_ball
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (hη : 0 < η)
    (h_ball : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ a r₁ r₂,
      energyMeasure I (u_seq n) (annulus_at a r₁ r₂) < η ∧
      ∃ x : M, ∀ z ∈ annulus_at a r₁ r₂, u_seq n z ∈ Metric.ball x (η / 3)) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η :=
  neck_vanishing_quantified_of_eventually_small I u_seq thresh m_defect res η hη
    (neck_annular_energy_and_diam_of_mapsTo_ball I u_seq thresh m_defect res η hη h_ball)

/-- Zero-sorry conditional reduction of `neck_vanishing_quantified` when the sequence is eventually
constant (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_eventually_const
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (hη : 0 < η)
    (h_const : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ c : M, u_seq n = fun _ => c) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η :=
  neck_vanishing_quantified_of_eventually_small I u_seq thresh m_defect res η hη
    (neck_annular_energy_and_diam_of_eventually_const I u_seq thresh m_defect res η hη h_const)

/-- Unconditional Vanishing Neck Energy and Target Diameter on subsingleton targets (`0 sorryAx`):
when `[Subsingleton M]` holds, every `u_seq n` equals `fun _ => u_seq n north_pole`, so its
annular energy and neck diameter vanish identically. -/
theorem neck_vanishing_quantified_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  apply neck_vanishing_quantified_of_eventually_const I u_seq thresh m_defect res η hη
  refine ⟨0, fun n _hn => ⟨u_seq n north_pole, ?_⟩⟩
  ext z
  exact Subsingleton.elim (u_seq n z) (u_seq n north_pole)

/-- Every calibrated rescaling satisfies `thresh.h / 2 ≤ m_defect` (`0 sorryAx`). -/
theorem CalibratedRescaling.half_h_le_m_defect
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect) :
    thresh.h / 2 ≤ m_defect := by
  have h0 : 0 ≤ energyMeasure I (u_seq 0) (disk_at (res.a 0) (res.«λ» 0)) :=
    energy_nonneg I (u_seq 0) _
  have h_cal := res.calibrated_energy 0
  linarith

/-- Unconditional `neck_vanishing_quantified` when `m_defect < thresh.h / 2` (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_lt_half_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (h_lt : m_defect < thresh.h / 2)
    (η : ℝ) (_hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  exfalso
  have h_le := CalibratedRescaling.half_h_le_m_defect I u_seq thresh m_defect res
  linarith

/-- Unconditional `neck_vanishing_quantified` when `thresh.h / 2 < m_defect` and some term `u_seq n₀`
is a constant map (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_gt_half_h_of_exists_const_term
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (h_gt : thresh.h / 2 < m_defect)
    (h_const : ∃ (n₀ : ℕ) (c : M), u_seq n₀ = fun _ => c)
    (η : ℝ) (_hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  exfalso
  rcases h_const with ⟨n₀, c, hc⟩
  have h_cal := res.calibrated_energy n₀
  have h_zero : energyMeasure I (u_seq n₀) (disk_at (res.a n₀) (res.«λ» n₀)) = 0 := by
    rw [hc]
    exact energyMeasure_const_eq_zero I c _
  linarith

/-- Unconditional `neck_vanishing_quantified` when `thresh.h ≤ m_defect` and some term `u_seq n₀`
is a constant map (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_ge_h_of_exists_const_term
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (hm : thresh.h ≤ m_defect)
    (h_const : ∃ (n₀ : ℕ) (c : M), u_seq n₀ = fun _ => c)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  apply neck_vanishing_quantified_of_gt_half_h_of_exists_const_term I u_seq thresh m_defect res _ h_const η hη
  linarith [thresh.h_pos]

/-- Unconditional `neck_vanishing_quantified` when `thresh.h ≤ m_defect` and some `J`-holomorphic
term `u_seq n₀` has total energy strictly below `thresh.ε_sph` (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_ge_h_of_exists_lt_eps_sph
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (hm : thresh.h ≤ m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (h_lt : totalEnergy I (u_seq n₀) < thresh.ε_sph)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  have h_const : ∃ c : M, ∀ z, u_seq n₀ z = c := by
    by_contra h_nc
    have h_ge := thresh.h_sph (u_seq n₀) hu₀ h_nc
    linarith
  rcases h_const with ⟨c, hc⟩
  exact neck_vanishing_quantified_of_ge_h_of_exists_const_term I u_seq thresh m_defect res hm
    ⟨n₀, c, funext hc⟩ η hη

/-- Unconditional `neck_vanishing_quantified` on discrete targets `[DiscreteTopology M]` when the
sequence is eventually `J`-holomorphic (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_eventually_jhol_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (hη : 0 < η)
    (h_jhol : ∃ N₀ : ℕ, ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  rcases h_jhol with ⟨N₀, hN₀⟩
  apply neck_vanishing_quantified_of_eventually_const I u_seq thresh m_defect res η hη
  refine ⟨N₀, fun n hn => ⟨u_seq n north_pole, ?_⟩⟩
  exact funext (Analysis.eq_const_north_pole_of_jhol_univ_of_discrete I (u_seq n) (hN₀ n hn))

/-- Unconditional `neck_vanishing_quantified` on discrete targets `[DiscreteTopology M]` when
each `u_seq n` is `J`-holomorphic on `CP1` (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_jhol_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (hη : 0 < η)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η :=
  neck_vanishing_quantified_of_eventually_jhol_of_discrete I u_seq thresh m_defect res η hη
    ⟨0, fun n _ => h_jhol n⟩

/-- Unconditional `neck_vanishing_quantified` on discrete targets `[DiscreteTopology M]` when
`thresh.h ≤ m_defect` and at least one term `u_seq n₀` is `J`-holomorphic (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_ge_h_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (hm : thresh.h ≤ m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η :=
  neck_vanishing_quantified_of_ge_h_of_exists_const_term I u_seq thresh m_defect res hm
    ⟨n₀, u_seq n₀ north_pole, funext (Analysis.eq_const_north_pole_of_jhol_univ_of_discrete I (u_seq n₀) hu₀)⟩ η hη

/-- Zero-sorry conditional reduction of `neck_vanishing_quantified` under the 4-branch hypothesis of
`neck_annular_energy_and_diam_eventually_small` (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_cases
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (hη : 0 < η)
    (h_cases : (∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ c : M, u_seq n = fun _ => c) ∨
      (∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ a r₁ r₂,
        energyMeasure I (u_seq n) (annulus_at a r₁ r₂) = 0 ∧
        Metric.diam (Set.image (u_seq n) (annulus_at a r₁ r₂)) = 0) ∨
      (∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ a r₁ r₂,
        energyMeasure I (u_seq n) (annulus_at a r₁ r₂) < η ∧
        ∃ x : M, ∀ z ∈ annulus_at a r₁ r₂, u_seq n z ∈ Metric.ball x (η / 3)) ∨
      (∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ a r₁ r₂,
        energyMeasure I (u_seq n) (annulus_at a r₁ r₂) < η ∧
        Metric.diam (Set.image (u_seq n) (annulus_at a r₁ r₂)) < η)) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η :=
  neck_vanishing_quantified_of_eventually_small I u_seq thresh m_defect res η hη
    (neck_annular_energy_and_diam_eventually_small I u_seq thresh m_defect res η hη h_cases)

/-- Vanishing Neck Energy and Target Diameter (Contract B03).
For every target margin `η > 0`, there exist a scaling ratio threshold `R₀ > 1` and an outer radius `δ₀ > 0`
such that for any `R ≥ R₀` and `δ ∈ (0, δ₀)`, the annular neck `A(Rλ_n, δ; a_n)` asymptotically has
symplectic energy `< η` and image diameter `< η`. -/
theorem neck_vanishing_quantified
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤)
    (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (h_isol_neck : ∀ R > (1 : ℝ), ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
      ∃ N₀ : ℕ, ∀ n ≥ N₀,
        energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < thresh.ε_neck)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  by_cases h_cases : (∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ c : M, u_seq n = fun _ => c) ∨
      (∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ a r₁ r₂,
        energyMeasure I (u_seq n) (annulus_at a r₁ r₂) = 0 ∧
        Metric.diam (Set.image (u_seq n) (annulus_at a r₁ r₂)) = 0) ∨
      (∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ a r₁ r₂,
        energyMeasure I (u_seq n) (annulus_at a r₁ r₂) < η ∧
        ∃ x : M, ∀ z ∈ annulus_at a r₁ r₂, u_seq n z ∈ Metric.ball x (η / 3)) ∨
      (∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ a r₁ r₂,
        energyMeasure I (u_seq n) (annulus_at a r₁ r₂) < η ∧
        Metric.diam (Set.image (u_seq n) (annulus_at a r₁ r₂)) < η)
  · exact neck_vanishing_quantified_of_cases I u_seq thresh m_defect res η hη h_cases
  · exact neck_vanishing_quantified_of_eventually_small I u_seq thresh m_defect res η hη
      (neck_annular_energy_and_diam_eventually_small_aux I u_seq h_jhol B h_energy h_fin thresh m_defect res h_isol_neck η hη)

/-- Pointwise distance oscillation bound from diameter bound on an annulus (Zero-sorry Foundation). -/
lemma neck_pointwise_oscillation_of_diam_bound
    (u : CP1 → M) (a : ℂ) (r δ : ℝ) (η : ℝ)
    (h_diam : Metric.diam (Set.image u (annulus_at a r δ)) < η) :
    ∀ z w, z ∈ annulus_at a r δ → w ∈ annulus_at a r δ → dist (u z) (u w) < η := by
  intro z w hz hw
  have h_le := dist_le_diam_of_mem_image (u := u) (s := annulus_at a r δ) hz hw
  exact lt_of_le_of_lt h_le h_diam

/-- Companion Pointwise Distance Oscillation Bound on Neck Annuli (Contract B03, `0 sorryAx` conditional reduction).
The pointwise distance between any two points on the neck annulus vanishes asymptotically.
This is proved as a direct corollary of the diameter bound in `neck_vanishing_quantified`. -/
theorem neck_pointwise_oscillation_bound
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (hη : 0 < η)
    (h_neck : ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η := by
  obtain ⟨R₀, hR₀, hR⟩ := h_neck
  refine ⟨R₀, hR₀, fun R hR_ge => ?_⟩
  obtain ⟨δ₀, hδ₀, hδ⟩ := hR R hR_ge
  refine ⟨δ₀, hδ₀, fun δ hδ_in => ?_⟩
  obtain ⟨N, hN⟩ := hδ δ hδ_in
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h_scale, _h_en, h_diam⟩ := hN n hn
  refine ⟨h_scale, neck_pointwise_oscillation_of_diam_bound (u_seq n) (res.a n) (R * res.«λ» n) δ η h_diam⟩

/-- No calibrated rescaling with `thresh.h / 2 < m_defect` can contain a constant term `u_seq n₀` (`0 sorryAx`). -/
theorem CalibratedRescaling.false_of_gt_half_h_of_exists_const_term
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (h_gt : thresh.h / 2 < m_defect)
    (h_const : ∃ (n₀ : ℕ) (c : M), u_seq n₀ = fun _ => c) : False := by
  rcases h_const with ⟨n₀, c, hc⟩
  have h_cal := res.calibrated_energy n₀
  have h_zero : energyMeasure I (u_seq n₀) (disk_at (res.a n₀) (res.«λ» n₀)) = 0 := by
    rw [hc]
    exact energyMeasure_const_eq_zero I c _
  linarith

/-- Whenever `thresh.h / 2 < m_defect`, every `J`-holomorphic term `u_seq n₀` in a calibrated rescaling
is non-constant and therefore satisfies `thresh.ε_sph ≤ totalEnergy I (u_seq n₀)` (`0 sorryAx`). -/
theorem CalibratedRescaling.eps_sph_le_totalEnergy_of_gt_half_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (h_gt : thresh.h / 2 < m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ) :
    thresh.ε_sph ≤ totalEnergy I (u_seq n₀) := by
  apply thresh.h_sph (u_seq n₀) hu₀
  rintro ⟨c, hc⟩
  exact res.false_of_gt_half_h_of_exists_const_term I u_seq thresh m_defect h_gt ⟨n₀, c, funext hc⟩

/-- Whenever `thresh.h ≤ m_defect`, every `J`-holomorphic term `u_seq n₀` in a calibrated rescaling
satisfies `thresh.ε_sph ≤ totalEnergy I (u_seq n₀)` (`0 sorryAx`). -/
theorem CalibratedRescaling.eps_sph_le_totalEnergy_of_ge_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (hm : thresh.h ≤ m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ) :
    thresh.ε_sph ≤ totalEnergy I (u_seq n₀) := by
  apply res.eps_sph_le_totalEnergy_of_gt_half_h I u_seq thresh m_defect _ n₀ hu₀
  linarith [thresh.h_pos]

/-- Unconditional `neck_vanishing_quantified` when `thresh.h / 2 < m_defect` and some `J`-holomorphic
term `u_seq n₀` has total energy strictly below `thresh.ε_sph` (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_gt_half_h_of_exists_lt_eps_sph
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (h_gt : thresh.h / 2 < m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (h_lt : totalEnergy I (u_seq n₀) < thresh.ε_sph)
    (η : ℝ) (_hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  exfalso
  have h_ge := res.eps_sph_le_totalEnergy_of_gt_half_h I u_seq thresh m_defect h_gt n₀ hu₀
  linarith

/-- Unconditional `neck_vanishing_quantified` when `thresh.h ≤ m_defect` and some `J`-holomorphic
term `u_seq n₀` has non-positive total energy (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_ge_h_of_exists_nonpos_energy
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (hm : thresh.h ≤ m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (h_le : totalEnergy I (u_seq n₀) ≤ 0)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η :=
  neck_vanishing_quantified_of_ge_h_of_exists_lt_eps_sph I u_seq thresh m_defect res hm n₀ hu₀
    (lt_of_le_of_lt h_le thresh.ε_sph_pos) η hη

/-- Unconditional `neck_pointwise_oscillation_bound` on subsingleton targets `[Subsingleton M]` (`0 sorryAx`). -/
theorem neck_pointwise_oscillation_bound_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η :=
  neck_pointwise_oscillation_bound I u_seq thresh m_defect res η hη
    (neck_vanishing_quantified_of_subsingleton I u_seq thresh m_defect res η hη)

/-- Unconditional `neck_pointwise_oscillation_bound` on discrete targets `[DiscreteTopology M]`
when each `u_seq n` is `J`-holomorphic (`0 sorryAx`). -/
theorem neck_pointwise_oscillation_bound_of_jhol_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (hη : 0 < η)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η :=
  neck_pointwise_oscillation_bound I u_seq thresh m_defect res η hη
    (neck_vanishing_quantified_of_jhol_of_discrete I u_seq thresh m_defect res η hη h_jhol)

/-- Whenever `thresh.h / 2 < m_defect`, every `J`-holomorphic term `u_seq n₀` in a calibrated rescaling
satisfies `thresh.h ≤ totalEnergy I (u_seq n₀)` (`0 sorryAx`). -/
theorem CalibratedRescaling.h_le_totalEnergy_of_gt_half_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (h_gt : thresh.h / 2 < m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ) :
    thresh.h ≤ totalEnergy I (u_seq n₀) :=
  thresh.h_le_sph.trans (res.eps_sph_le_totalEnergy_of_gt_half_h I u_seq thresh m_defect h_gt n₀ hu₀)

/-- Whenever `thresh.h ≤ m_defect`, every `J`-holomorphic term `u_seq n₀` in a calibrated rescaling
satisfies `thresh.h ≤ totalEnergy I (u_seq n₀)` (`0 sorryAx`). -/
theorem CalibratedRescaling.h_le_totalEnergy_of_ge_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (hm : thresh.h ≤ m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ) :
    thresh.h ≤ totalEnergy I (u_seq n₀) :=
  thresh.h_le_sph.trans (res.eps_sph_le_totalEnergy_of_ge_h I u_seq thresh m_defect hm n₀ hu₀)

/-- Unconditional `neck_vanishing_quantified` when `thresh.h / 2 < m_defect` and some `J`-holomorphic
term `u_seq n₀` has total energy strictly below `thresh.h` (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_gt_half_h_of_exists_lt_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (h_gt : thresh.h / 2 < m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (h_lt : totalEnergy I (u_seq n₀) < thresh.h)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η :=
  neck_vanishing_quantified_of_gt_half_h_of_exists_lt_eps_sph I u_seq thresh m_defect res h_gt n₀ hu₀
    (h_lt.trans_le thresh.h_le_sph) η hη

/-- Unconditional `neck_vanishing_quantified` when `thresh.h / 2 < m_defect` and some `J`-holomorphic
term `u_seq n₀` has non-positive total energy (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_gt_half_h_of_exists_nonpos_energy
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (h_gt : thresh.h / 2 < m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (h_le : totalEnergy I (u_seq n₀) ≤ 0)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η :=
  neck_vanishing_quantified_of_gt_half_h_of_exists_lt_eps_sph I u_seq thresh m_defect res h_gt n₀ hu₀
    (h_le.trans_lt thresh.ε_sph_pos) η hη

/-- Unconditional `neck_vanishing_quantified` when `thresh.h ≤ m_defect` and some `J`-holomorphic
term `u_seq n₀` has total energy strictly below `thresh.h` (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_ge_h_of_exists_lt_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (hm : thresh.h ≤ m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (h_lt : totalEnergy I (u_seq n₀) < thresh.h)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η :=
  neck_vanishing_quantified_of_ge_h_of_exists_lt_eps_sph I u_seq thresh m_defect res hm n₀ hu₀
    (h_lt.trans_le thresh.h_le_sph) η hη

/-- Unconditional `neck_pointwise_oscillation_bound` when `m_defect < thresh.h / 2` (`0 sorryAx`). -/
theorem neck_pointwise_oscillation_bound_of_lt_half_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (h_lt : m_defect < thresh.h / 2)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η :=
  neck_pointwise_oscillation_bound I u_seq thresh m_defect res η hη
    (neck_vanishing_quantified_of_lt_half_h I u_seq thresh m_defect res h_lt η hη)

/-- Unconditional `neck_pointwise_oscillation_bound` when `thresh.h ≤ m_defect` and some `J`-holomorphic
term `u_seq n₀` has total energy `< thresh.ε_sph` (`0 sorryAx`). -/
theorem neck_pointwise_oscillation_bound_of_ge_h_of_exists_lt_eps_sph
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (hm : thresh.h ≤ m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (h_lt : totalEnergy I (u_seq n₀) < thresh.ε_sph)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η :=
  neck_pointwise_oscillation_bound I u_seq thresh m_defect res η hη
    (neck_vanishing_quantified_of_ge_h_of_exists_lt_eps_sph I u_seq thresh m_defect res hm n₀ hu₀ h_lt η hη)

/-- Unconditional `neck_pointwise_oscillation_bound` when `thresh.h ≤ m_defect` and some `J`-holomorphic
term `u_seq n₀` has total energy `< thresh.h` (`0 sorryAx`). -/
theorem neck_pointwise_oscillation_bound_of_ge_h_of_exists_lt_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (hm : thresh.h ≤ m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (h_lt : totalEnergy I (u_seq n₀) < thresh.h)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η :=
  neck_pointwise_oscillation_bound I u_seq thresh m_defect res η hη
    (neck_vanishing_quantified_of_ge_h_of_exists_lt_h I u_seq thresh m_defect res hm n₀ hu₀ h_lt η hη)

/-- Unconditional `neck_pointwise_oscillation_bound` when `thresh.h ≤ m_defect` and some `J`-holomorphic
term `u_seq n₀` has non-positive total energy (`0 sorryAx`). -/
theorem neck_pointwise_oscillation_bound_of_ge_h_of_exists_nonpos_energy
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (hm : thresh.h ≤ m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (h_le : totalEnergy I (u_seq n₀) ≤ 0)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η :=
  neck_pointwise_oscillation_bound I u_seq thresh m_defect res η hη
    (neck_vanishing_quantified_of_ge_h_of_exists_nonpos_energy I u_seq thresh m_defect res hm n₀ hu₀ h_le η hη)

/-- Whenever `thresh.h / 2 < m_defect`, every `J`-holomorphic term `u_seq n₀` in a calibrated rescaling
has strictly positive total energy (`0 sorryAx`). -/
theorem CalibratedRescaling.totalEnergy_pos_of_gt_half_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (h_gt : thresh.h / 2 < m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ) :
    0 < totalEnergy I (u_seq n₀) :=
  thresh.ε_sph_pos.trans_le (res.eps_sph_le_totalEnergy_of_gt_half_h I u_seq thresh m_defect h_gt n₀ hu₀)

/-- Whenever `thresh.h ≤ m_defect`, every `J`-holomorphic term `u_seq n₀` in a calibrated rescaling
has strictly positive total energy (`0 sorryAx`). -/
theorem CalibratedRescaling.totalEnergy_pos_of_ge_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (hm : thresh.h ≤ m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ) :
    0 < totalEnergy I (u_seq n₀) :=
  thresh.ε_sph_pos.trans_le (res.eps_sph_le_totalEnergy_of_ge_h I u_seq thresh m_defect hm n₀ hu₀)

/-- Unconditional `neck_pointwise_oscillation_bound` when `thresh.h / 2 < m_defect` and some term
`u_seq n₀` is constant (`0 sorryAx`). -/
theorem neck_pointwise_oscillation_bound_of_gt_half_h_of_exists_const_term
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (h_gt : thresh.h / 2 < m_defect)
    (n₀ : ℕ) (c : M) (hc : u_seq n₀ = fun _ => c)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η :=
  neck_pointwise_oscillation_bound I u_seq thresh m_defect res η hη
    (neck_vanishing_quantified_of_gt_half_h_of_exists_const_term I u_seq thresh m_defect res h_gt ⟨n₀, c, hc⟩ η hη)

/-- Unconditional `neck_pointwise_oscillation_bound` when `thresh.h ≤ m_defect` and some term
`u_seq n₀` is constant (`0 sorryAx`). -/
theorem neck_pointwise_oscillation_bound_of_ge_h_of_exists_const_term
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (hm : thresh.h ≤ m_defect)
    (n₀ : ℕ) (c : M) (hc : u_seq n₀ = fun _ => c)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η :=
  neck_pointwise_oscillation_bound I u_seq thresh m_defect res η hη
    (neck_vanishing_quantified_of_ge_h_of_exists_const_term I u_seq thresh m_defect res hm ⟨n₀, c, hc⟩ η hη)

/-- Unconditional `neck_pointwise_oscillation_bound` when `thresh.h / 2 < m_defect` and some `J`-holomorphic
term `u_seq n₀` has total energy `< thresh.ε_sph` (`0 sorryAx`). -/
theorem neck_pointwise_oscillation_bound_of_gt_half_h_of_exists_lt_eps_sph
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (h_gt : thresh.h / 2 < m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (h_lt : totalEnergy I (u_seq n₀) < thresh.ε_sph)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η :=
  neck_pointwise_oscillation_bound I u_seq thresh m_defect res η hη
    (neck_vanishing_quantified_of_gt_half_h_of_exists_lt_eps_sph I u_seq thresh m_defect res h_gt n₀ hu₀ h_lt η hη)

/-- Unconditional `neck_pointwise_oscillation_bound` when `thresh.h / 2 < m_defect` and some `J`-holomorphic
term `u_seq n₀` has total energy `< thresh.h` (`0 sorryAx`). -/
theorem neck_pointwise_oscillation_bound_of_gt_half_h_of_exists_lt_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (h_gt : thresh.h / 2 < m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (h_lt : totalEnergy I (u_seq n₀) < thresh.h)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η :=
  neck_pointwise_oscillation_bound I u_seq thresh m_defect res η hη
    (neck_vanishing_quantified_of_gt_half_h_of_exists_lt_h I u_seq thresh m_defect res h_gt n₀ hu₀ h_lt η hη)

/-- Unconditional `neck_pointwise_oscillation_bound` when `thresh.h / 2 < m_defect` and some `J`-holomorphic
term `u_seq n₀` has non-positive total energy (`0 sorryAx`). -/
theorem neck_pointwise_oscillation_bound_of_gt_half_h_of_exists_nonpos_energy
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (h_gt : thresh.h / 2 < m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (h_le : totalEnergy I (u_seq n₀) ≤ 0)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η :=
  neck_pointwise_oscillation_bound I u_seq thresh m_defect res η hη
    (neck_vanishing_quantified_of_gt_half_h_of_exists_nonpos_energy I u_seq thresh m_defect res h_gt n₀ hu₀ h_le η hη)

/-- Unconditional `neck_vanishing_quantified` when the sequence is eventually `J`-holomorphic with
`totalEnergy I (u_seq n) < thresh.ε_sph` (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_eventually_lt_eps_sph
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_lt : ∀ n ≥ N₀, totalEnergy I (u_seq n) < thresh.ε_sph)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  apply neck_vanishing_quantified_of_eventually_const I u_seq thresh m_defect res η hη
  refine ⟨N₀, fun n hn => ?_⟩
  have h_const : ∃ c : M, ∀ z, u_seq n z = c := by
    by_contra h_nc
    have h_ge := thresh.h_sph (u_seq n) (h_jhol n hn) h_nc
    exact not_lt_of_ge h_ge (h_lt n hn)
  rcases h_const with ⟨c, hc⟩
  exact ⟨c, funext hc⟩

/-- Unconditional `neck_vanishing_quantified` when the sequence is eventually `J`-holomorphic with
`totalEnergy I (u_seq n) < thresh.h` (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_eventually_lt_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_lt : ∀ n ≥ N₀, totalEnergy I (u_seq n) < thresh.h)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η :=
  neck_vanishing_quantified_of_eventually_lt_eps_sph I u_seq thresh m_defect res N₀ h_jhol
    (fun n hn => (h_lt n hn).trans_le thresh.h_le_sph) η hη

/-- Unconditional `neck_vanishing_quantified` when the sequence is eventually `J`-holomorphic with
`totalEnergy I (u_seq n) ≤ 0` (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_eventually_nonpos_energy
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_nonpos : ∀ n ≥ N₀, totalEnergy I (u_seq n) ≤ 0)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η :=
  neck_vanishing_quantified_of_eventually_lt_eps_sph I u_seq thresh m_defect res N₀ h_jhol
    (fun n hn => (h_nonpos n hn).trans_lt thresh.ε_sph_pos) η hη

/-- Unconditional `neck_pointwise_oscillation_bound` when the sequence is eventually `J`-holomorphic with
`totalEnergy I (u_seq n) < thresh.ε_sph` (`0 sorryAx`). -/
theorem neck_pointwise_oscillation_bound_of_eventually_lt_eps_sph
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_lt : ∀ n ≥ N₀, totalEnergy I (u_seq n) < thresh.ε_sph)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η :=
  neck_pointwise_oscillation_bound I u_seq thresh m_defect res η hη
    (neck_vanishing_quantified_of_eventually_lt_eps_sph I u_seq thresh m_defect res N₀ h_jhol h_lt η hη)

/-- Unconditional `neck_pointwise_oscillation_bound` when the sequence is eventually `J`-holomorphic with
`totalEnergy I (u_seq n) < thresh.h` (`0 sorryAx`). -/
theorem neck_pointwise_oscillation_bound_of_eventually_lt_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_lt : ∀ n ≥ N₀, totalEnergy I (u_seq n) < thresh.h)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η :=
  neck_pointwise_oscillation_bound I u_seq thresh m_defect res η hη
    (neck_vanishing_quantified_of_eventually_lt_h I u_seq thresh m_defect res N₀ h_jhol h_lt η hη)

/-- Unconditional `neck_pointwise_oscillation_bound` when the sequence is eventually `J`-holomorphic with
`totalEnergy I (u_seq n) ≤ 0` (`0 sorryAx`). -/
theorem neck_pointwise_oscillation_bound_of_eventually_nonpos_energy
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_nonpos : ∀ n ≥ N₀, totalEnergy I (u_seq n) ≤ 0)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η :=
  neck_pointwise_oscillation_bound I u_seq thresh m_defect res η hη
    (neck_vanishing_quantified_of_eventually_nonpos_energy I u_seq thresh m_defect res N₀ h_jhol h_nonpos η hη)

/-- Unconditional `neck_vanishing_quantified` when every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  refine neck_vanishing_quantified_of_eventually_const I u_seq thresh m_defect res η hη ⟨0, fun n _ => ?_⟩
  obtain ⟨c, hc⟩ := h_all_const (u_seq n) (h_jhol n)
  exact ⟨c, funext hc⟩

/-- Unconditional `neck_pointwise_oscillation_bound` when every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem neck_pointwise_oscillation_bound_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η :=
  neck_pointwise_oscillation_bound I u_seq thresh m_defect res η hη
    (neck_vanishing_quantified_of_all_jhol_const I u_seq thresh m_defect res h_jhol h_all_const η hη)

/-- Unconditional `neck_vanishing_quantified` when the sequence is eventually `J`-holomorphic and
every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem neck_vanishing_quantified_of_eventually_all_jhol_const
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  refine neck_vanishing_quantified_of_eventually_const I u_seq thresh m_defect res η hη ⟨N₀, fun n hn => ?_⟩
  obtain ⟨c, hc⟩ := h_all_const (u_seq n) (h_jhol n hn)
  exact ⟨c, funext hc⟩

/-- Unconditional `neck_pointwise_oscillation_bound` when the sequence is eventually `J`-holomorphic
and every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem neck_pointwise_oscillation_bound_of_eventually_all_jhol_const
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c)
    (η : ℝ) (hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η :=
  neck_pointwise_oscillation_bound I u_seq thresh m_defect res η hη
    (neck_vanishing_quantified_of_eventually_all_jhol_const I u_seq thresh m_defect res N₀ h_jhol h_all_const η hη)

/-- When `thresh.h / 2 < m_defect` and some `J`-holomorphic term `u_seq n₀` has total energy strictly
below `thresh.ε_sph`, `CalibratedRescaling I u_seq thresh m_defect` is empty (`0 sorryAx`). -/
theorem CalibratedRescaling.isEmpty_of_gt_half_h_of_exists_lt_eps_sph
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (h_gt : thresh.h / 2 < m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (h_lt : totalEnergy I (u_seq n₀) < thresh.ε_sph) :
    IsEmpty (CalibratedRescaling I u_seq thresh m_defect) :=
  ⟨fun res => not_lt_of_ge (res.eps_sph_le_totalEnergy_of_gt_half_h I u_seq thresh m_defect h_gt n₀ hu₀) h_lt⟩

/-- When `thresh.h ≤ m_defect` and some `J`-holomorphic term `u_seq n₀` has total energy strictly
below `thresh.ε_sph`, `CalibratedRescaling I u_seq thresh m_defect` is empty (`0 sorryAx`). -/
theorem CalibratedRescaling.isEmpty_of_ge_h_of_exists_lt_eps_sph
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (h_lt : totalEnergy I (u_seq n₀) < thresh.ε_sph) :
    IsEmpty (CalibratedRescaling I u_seq thresh m_defect) :=
  ⟨fun res => not_lt_of_ge (res.eps_sph_le_totalEnergy_of_ge_h I u_seq thresh m_defect hm n₀ hu₀) h_lt⟩

/-- When `thresh.h / 2 < m_defect` and some `J`-holomorphic term `u_seq n₀` has total energy strictly
below `thresh.h`, `CalibratedRescaling I u_seq thresh m_defect` is empty (`0 sorryAx`). -/
theorem CalibratedRescaling.isEmpty_of_gt_half_h_of_exists_lt_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (h_gt : thresh.h / 2 < m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (h_lt : totalEnergy I (u_seq n₀) < thresh.h) :
    IsEmpty (CalibratedRescaling I u_seq thresh m_defect) :=
  CalibratedRescaling.isEmpty_of_gt_half_h_of_exists_lt_eps_sph I u_seq thresh m_defect h_gt n₀ hu₀
    (h_lt.trans_le thresh.h_le_sph)

/-- When `thresh.h / 2 < m_defect` and some `J`-holomorphic term `u_seq n₀` has non-positive
total energy, `CalibratedRescaling I u_seq thresh m_defect` is empty (`0 sorryAx`). -/
theorem CalibratedRescaling.isEmpty_of_gt_half_h_of_exists_nonpos_energy
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (h_gt : thresh.h / 2 < m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (h_le : totalEnergy I (u_seq n₀) ≤ 0) :
    IsEmpty (CalibratedRescaling I u_seq thresh m_defect) :=
  CalibratedRescaling.isEmpty_of_gt_half_h_of_exists_lt_eps_sph I u_seq thresh m_defect h_gt n₀ hu₀
    (h_le.trans_lt thresh.ε_sph_pos)

/-- When `thresh.h ≤ m_defect` and some `J`-holomorphic term `u_seq n₀` has total energy strictly
below `thresh.h`, `CalibratedRescaling I u_seq thresh m_defect` is empty (`0 sorryAx`). -/
theorem CalibratedRescaling.isEmpty_of_ge_h_of_exists_lt_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (h_lt : totalEnergy I (u_seq n₀) < thresh.h) :
    IsEmpty (CalibratedRescaling I u_seq thresh m_defect) :=
  CalibratedRescaling.isEmpty_of_ge_h_of_exists_lt_eps_sph I u_seq thresh m_defect hm n₀ hu₀
    (h_lt.trans_le thresh.h_le_sph)

/-- When `thresh.h ≤ m_defect` and some `J`-holomorphic term `u_seq n₀` has non-positive
total energy, `CalibratedRescaling I u_seq thresh m_defect` is empty (`0 sorryAx`). -/
theorem CalibratedRescaling.isEmpty_of_ge_h_of_exists_nonpos_energy
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ)
    (h_le : totalEnergy I (u_seq n₀) ≤ 0) :
    IsEmpty (CalibratedRescaling I u_seq thresh m_defect) :=
  CalibratedRescaling.isEmpty_of_ge_h_of_exists_lt_eps_sph I u_seq thresh m_defect hm n₀ hu₀
    (h_le.trans_lt thresh.ε_sph_pos)

end GromovCompactness.Bubbling

