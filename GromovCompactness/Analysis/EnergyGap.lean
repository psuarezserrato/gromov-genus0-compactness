/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.EpsilonRegularity
import GromovCompactness.Analysis.Monotonicity

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness

namespace GromovCompactness.Analysis

/-!
# Task A07: Minimal Energy Gap of Non-Constant Spheres

This module formalizes `sphere_energy_gap` (Contract A07):
There exists a strictly positive constant $\varepsilon_{\mathrm{sph}} > 0$ depending only on
the target manifold $(M, \omega, J)$ such that every non-constant $J$-holomorphic sphere
$u : \mathbb{CP}^1 \to M$ satisfies $E(u) \ge \varepsilon_{\mathrm{sph}}$.

The proof proceeds by covering $\mathbb{CP}^1$ by finitely many disks with small energy,
bounding the image diameter by $O(\sqrt{E})$ via epsilon-regularity (`A03`), showing the
image lies in a contractible Darboux chart, and integrating $u^* d\alpha = 0$ via Stokes'
theorem without requiring rationality assumptions on $[\omega]$.
Alternatively, target monotonicity (`A08`) forces $E(u) \ge c r_0^2$ as soon as the image
exits a ball of radius $r_0$.

References:
- Mikhail Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Math. 82 (1985), §1.2.
- Sergei Ivashkovich & Vsevolod Shevchishin, arXiv:math/9912046, Corollary 2.1.3.
- `gromov_compactness.pdf` §4.2 (Contract A07).
-/

/-!
### 1. Characterizations of Non-Constancy (Zero-sorry)
-/

/-- Non-constancy of a map from a nonempty type is equivalent to the existence of two points with distinct values. -/
lemma nonconstant_iff_exists_ne {M : Type*} (u : CP1 → M) :
    (¬ ∃ c : M, ∀ z, u z = c) ↔ ∃ z w : CP1, u z ≠ u w := by
  constructor
  · intro h
    by_contra h_all_eq
    push_neg at h_all_eq
    apply h
    obtain ⟨z₀⟩ : Nonempty CP1 := inferInstance
    refine ⟨u z₀, fun z => ?_⟩
    exact (h_all_eq z₀ z).symm
  · rintro ⟨z, w, hne⟩ ⟨c, hc⟩
    have hz : u z = c := hc z
    have hw : u w = c := hc w
    apply hne
    rw [hz, hw]

lemma exists_ne_of_nonconstant {M : Type*} (u : CP1 → M) (h : ¬ ∃ c : M, ∀ z, u z = c) :
    ∃ z w : CP1, u z ≠ u w :=
  (nonconstant_iff_exists_ne u).mp h

/-- Non-constancy yields a point in the image and an outside point for small radii. -/
lemma exists_outside_of_nonconstant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (h : ¬ ∃ c : M, ∀ z, u z = c) :
    ∃ (x : M) (w : CP1), x ∈ Set.range u ∧ 0 < dist (u w) x ∧
      ∀ r, 0 < r → r < dist (u w) x → u w ∉ Metric.ball x r := by
  obtain ⟨z, w, hne⟩ := exists_ne_of_nonconstant u h
  let x := u z
  have hx : x ∈ Set.range u := ⟨z, rfl⟩
  have hpos : 0 < dist (u w) x := dist_pos.mpr (Ne.symm hne)
  refine ⟨x, w, hx, hpos, fun r _ hr => ?_⟩
  rw [Metric.mem_ball]
  push_neg
  exact le_of_lt hr

/-!
### 2. Energy Properties of Constant Maps (Zero-sorry)
-/

/-- The Riemannian energy density of a constant map vanishes identically. -/
theorem riemannianEnergyDensity_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (c : M) (z : CP1) :
    riemannianEnergyDensity I (fun _ => c) z = 0 := by
  dsimp [riemannianEnergyDensity]
  simp only [mfderiv_const]
  dsimp [ClosedTameTarget.metric]
  simp

/-- The extended energy measure of a constant map is the zero measure. -/
theorem energyMeasureExtended_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (c : M) :
    energyMeasureExtended I (fun _ : CP1 => c) = 0 := by
  dsimp [energyMeasureExtended, chartPush]
  have h_dens : (fun w : ℂ => ENNReal.ofReal (riemannianEnergyDensity I (fun _ => c) (stereo_chart.symm w) * sphericalJacobian w)) = 0 := by
    ext w
    rw [riemannianEnergyDensity_const]
    simp [ENNReal.ofReal_zero]
  rw [h_dens]
  simp [withDensity_zero]

/-- The energy measure of any set for a constant map vanishes. -/
theorem energyMeasure_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (c : M) (A : Set CP1) :
    energyMeasure I (fun _ => c) A = 0 := by
  dsimp [energyMeasure]
  rw [energyMeasureExtended_const]
  simp

/-- The total energy of a constant map vanishes. -/
theorem totalEnergy_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (c : M) :
    totalEnergy I (fun _ : CP1 => c) = 0 :=
  energyMeasure_const I c Set.univ

/-- If `u` is constant (equal to `c` everywhere), its total energy vanishes. -/
theorem totalEnergy_eq_zero_of_forall_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (c : M) (hc : ∀ z, u z = c) :
    totalEnergy I u = 0 := by
  have hu : u = fun _ => c := funext hc
  rw [hu]
  exact totalEnergy_const I c

/-!
### 3. Total Energy Non-Negativity and Subset Monotonicity (Zero-sorry)
-/

/-- Total energy is non-negative. -/
theorem totalEnergy_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) :
    0 ≤ totalEnergy I u :=
  energy_nonneg I u Set.univ

/-- Monotonicity of energy measure with respect to subset inclusion. -/
lemma energyMeasure_le_totalEnergy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (A : Set CP1)
    (h_fin : energyMeasureExtended I u Set.univ ≠ ⊤) :
    energyMeasure I u A ≤ totalEnergy I u := by
  dsimp [energyMeasure, totalEnergy]
  have h_mono : energyMeasureExtended I u A ≤ energyMeasureExtended I u Set.univ :=
    measure_mono (subset_univ A)
  exact ENNReal.toReal_mono h_fin h_mono

/-!
### 4. Conditional Reduction Theorems for Sphere Energy Gap
-/

/-- Conditional Reduction theorem: Target monotonicity and image exit together imply the minimal energy gap.
Note (Conditional Reduction per COMPLETION_PLAN.md §0 & §2 P0-9):
Takes open geometric contract hypotheses (`h_mono`, `h_exit`) and does not count as closing
Contract A07 unconditionally. -/
theorem sphere_energy_gap_of_monotonicity_and_exit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (c r₀ : ℝ) (hc : 0 < c) (hr₀ : 0 < r₀)
    (h_mono : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)))
    (h_exit : ∀ (u : CP1 → M) (x : M),
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ∃ z, u z ∉ Metric.ball x r₀)
    (h_en_le : ∀ (u : CP1 → M) (s : Set CP1),
      energyMeasure I u s ≤ totalEnergy I u) :
    ∃ (ε_sph : ℝ), 0 < ε_sph ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ε_sph ≤ totalEnergy I u := by
  refine ⟨c * r₀^2, by positivity, ?_⟩
  intro u hu h_nonconst
  obtain ⟨z₀⟩ : Nonempty CP1 := inferInstance
  let x := u z₀
  have hx : x ∈ Set.range u := ⟨z₀, rfl⟩
  obtain ⟨z_out, hz_out⟩ := h_exit u x hx hu h_nonconst
  have h_bound := h_mono u x r₀ hr₀ le_rfl hx hu h_nonconst ⟨z_out, hz_out⟩
  have h_sub := h_en_le u (u ⁻¹' Metric.ball x r₀)
  linarith

/-- Conditional Reduction theorem: Epsilon-regularity / diameter bound and Stokes exactness together
imply the minimal energy gap.
Note (Conditional Reduction per COMPLETION_PLAN.md §0 & §2 P0-9):
Takes open analytical contract hypotheses (`h_diam`, `h_stokes`) and does not count as closing
Contract A07 unconditionally. -/
theorem sphere_energy_gap_of_stokes_and_diameter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (ε_diam : ℝ) (hε : 0 < ε_diam) (r_inj : ℝ) (_hr_inj : 0 < r_inj)
    (h_diam : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      totalEnergy I u < ε_diam →
      Metric.diam (Set.range u) < r_inj)
    (h_stokes : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      Metric.diam (Set.range u) < r_inj →
      totalEnergy I u = 0)
    (h_const_of_zero : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      totalEnergy I u = 0 →
      ∃ c : M, ∀ z, u z = c) :
    ∃ (ε_sph : ℝ), 0 < ε_sph ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ε_sph ≤ totalEnergy I u := by
  refine ⟨ε_diam, hε, ?_⟩
  intro u hu h_nonconst
  by_contra h_lt
  push_neg at h_lt
  have hdiam := h_diam u hu h_lt
  have hzero := h_stokes u hu hdiam
  have hconst := h_const_of_zero u hu hzero
  exact h_nonconst hconst

/-!
### 5. Minimal Energy Gap (Contract A07)
-/

/-- Minimal Energy Gap for Non-Constant Spheres (Contract A07).
There exists a strictly positive constant `ε_sph > 0` depending only on `(M, ω, J)` such that
every non-constant `J`-holomorphic sphere `u : CP1 → M` satisfies `E(u) ≥ ε_sph`. -/
theorem sphere_energy_gap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (ε_sph : ℝ), 0 < ε_sph ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ε_sph ≤ totalEnergy I u := by
  obtain ⟨c, r₀, hc, hr₀, h_mono⟩ := target_monotonicity (M := M) I
  apply sphere_energy_gap_of_monotonicity_and_exit I c r₀ hc hr₀ h_mono
  · intro u x hx hu h_nonconst
    sorry
  · intro u s
    sorry

end GromovCompactness.Analysis
