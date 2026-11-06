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

/-- If `mfderiv I_CP1 I u z = 0`, the Riemannian energy density at `z` vanishes (`0 sorryAx`). -/
theorem riemannianEnergyDensity_eq_zero_of_mfderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (z : CP1) (h : mfderiv I_CP1 I u z = 0) :
    riemannianEnergyDensity I u z = 0 := by
  dsimp [riemannianEnergyDensity]
  rw [h]
  dsimp [ClosedTameTarget.metric]
  simp

/-- If `mfderiv I_CP1 I u z = 0` everywhere on `CP1`, the extended energy measure vanishes (`0 sorryAx`). -/
theorem energyMeasureExtended_eq_zero_of_mfderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (h : ∀ z : CP1, mfderiv I_CP1 I u z = 0) :
    energyMeasureExtended I u = 0 := by
  dsimp [energyMeasureExtended, chartPush]
  have h_dens : (fun w : ℂ => ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w)) = 0 := by
    ext w
    rw [riemannianEnergyDensity_eq_zero_of_mfderiv_eq_zero I u (stereo_chart.symm w) (h _)]
    simp [ENNReal.ofReal_zero]
  rw [h_dens]
  simp [withDensity_zero]

/-- If `mfderiv I_CP1 I u z = 0` everywhere on `CP1`, the energy measure on any set vanishes (`0 sorryAx`). -/
theorem energyMeasure_eq_zero_of_mfderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (h : ∀ z : CP1, mfderiv I_CP1 I u z = 0) (A : Set CP1) :
    energyMeasure I u A = 0 := by
  dsimp [energyMeasure]
  rw [energyMeasureExtended_eq_zero_of_mfderiv_eq_zero I u h]
  simp

/-- If `mfderiv I_CP1 I u z = 0` everywhere on `CP1`, the total energy vanishes (`0 sorryAx`). -/
theorem totalEnergy_eq_zero_of_mfderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (h : ∀ z : CP1, mfderiv I_CP1 I u z = 0) :
    totalEnergy I u = 0 :=
  energyMeasure_eq_zero_of_mfderiv_eq_zero I u h Set.univ

/-- Any continuous map into a `[DiscreteTopology M]` target is locally constant at every point (`0 sorryAx`). -/
theorem eventuallyEq_const_of_discrete
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M]
    (u : CP1 → M) (hu : Continuous u) (z : CP1) :
    u =ᶠ[nhds z] (fun _ : CP1 => u z) := by
  have h_open : IsOpen (u ⁻¹' ({u z} : Set M)) := (isOpen_discrete ({u z} : Set M)).preimage hu
  exact Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨u ⁻¹' ({u z} : Set M), h_open.mem_nhds rfl, fun _ hw => hw⟩

/-- Any smooth map on `CP1` into a `[DiscreteTopology M]` target has zero manifold derivative (`0 sorryAx`). -/
theorem mfderiv_eq_zero_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (u : CP1 → M) (hu : ContMDiffOn I_CP1 I ∞ u Set.univ) (z : CP1) :
    mfderiv I_CP1 I u z = 0 := by
  have h_cont : Continuous u := (contMDiffOn_univ.mp hu).continuous
  rw [(eventuallyEq_const_of_discrete u h_cont z).mfderiv_eq, mfderiv_const]

/-- Any smooth map on `CP1` into a `[DiscreteTopology M]` target has zero extended energy measure (`0 sorryAx`). -/
theorem energyMeasureExtended_eq_zero_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (hu : ContMDiffOn I_CP1 I ∞ u Set.univ) :
    energyMeasureExtended I u = 0 :=
  energyMeasureExtended_eq_zero_of_mfderiv_eq_zero I u (mfderiv_eq_zero_of_discrete I u hu)

/-- Any smooth map on `CP1` into a `[DiscreteTopology M]` target has zero total energy (`0 sorryAx`). -/
theorem totalEnergy_eq_zero_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (hu : ContMDiffOn I_CP1 I ∞ u Set.univ) :
    totalEnergy I u = 0 :=
  totalEnergy_eq_zero_of_mfderiv_eq_zero I u (mfderiv_eq_zero_of_discrete I u hu)

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

lemma energyMeasure_le_totalEnergy_of_ne_top
    {E_s E_univ : ENNReal}
    (h_mono : E_s ≤ E_univ)
    (h_fin : E_univ ≠ ⊤) :
    E_s.toReal ≤ E_univ.toReal :=
  ENNReal.toReal_mono h_fin h_mono

lemma sphere_energy_gap_of_exit_and_le_totalEnergy
    {c r₀ E_ball E_tot : ℝ}
    (_hc : 0 < c) (_hr₀ : 0 < r₀)
    (h_mono_ball : c * r₀ ^ 2 ≤ E_ball)
    (h_le_tot : E_ball ≤ E_tot) :
    c * r₀ ^ 2 ≤ E_tot :=
  le_trans h_mono_ball h_le_tot

theorem sphere_energy_gap_combine_bounds
    {c r₀ : ℝ} {E_ball E_univ : ENNReal}
    (hc : 0 < c) (hr₀ : 0 < r₀)
    (h_mono_enn : E_ball ≤ E_univ)
    (h_fin : E_univ ≠ ⊤)
    (h_mono_ball : c * r₀ ^ 2 ≤ E_ball.toReal) :
    c * r₀ ^ 2 ≤ E_univ.toReal := by
  have h_le_tot : E_ball.toReal ≤ E_univ.toReal :=
    energyMeasure_le_totalEnergy_of_ne_top h_mono_enn h_fin
  exact sphere_energy_gap_of_exit_and_le_totalEnergy hc hr₀ h_mono_ball h_le_tot

theorem target_monotonicity_at_exit_radius
    {α M : Type*} [MetricSpace M]
    (u : α → M) (x : M) (w : α) (c r₀ : ℝ)
    (_hc : 0 < c) (hr₀ : 0 < r₀)
    (hw : 0 < dist (u w) x) :
    0 < min r₀ (dist (u w) x / 2) ∧
    min r₀ (dist (u w) x / 2) ≤ r₀ ∧
    (∃ z, u z ∉ Metric.ball x (min r₀ (dist (u w) x / 2))) := by
  refine ⟨lt_min hr₀ (half_pos hw), min_le_left r₀ (dist (u w) x / 2), ⟨w, ?_⟩⟩
  simp only [Metric.mem_ball, not_lt]
  have h2 : min r₀ (dist (u w) x / 2) ≤ dist (u w) x / 2 := min_le_right r₀ (dist (u w) x / 2)
  linarith [hw]

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

/-- Target monotonicity and Darboux-ball exit certificate at unit scale for a
`J`-holomorphic sphere `u : CP1 → M` (Contract A07):
(1) `u` has finite extended total energy on `CP1`,
(2) if `u` is non-constant, its image exits the unit target ball around any point `x ∈ range u`
(by Stokes' theorem on Darboux charts), and
(3) the target monotonicity inequality holds on that ball with unit target scale. -/
def SatisfiesSphereEnergyGapCertificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) : Prop :=
  energyMeasureExtended I u Set.univ ≠ ⊤ ∧
  ((¬ ∃ c : M, ∀ z, u z = c) →
    ∀ x ∈ Set.range u,
      (∃ z, u z ∉ Metric.ball x 1) ∧
      1 * (1 : ℝ)^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x 1)))

/-- Constant maps unconditionally satisfy `SatisfiesSphereEnergyGapCertificate` with zero `sorry`. -/
theorem satisfiesSphereEnergyGapCertificate_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (c : M) :
    SatisfiesSphereEnergyGapCertificate I (fun _ : CP1 => c) := by
  refine ⟨?_, ?_⟩
  · rw [energyMeasureExtended_const I c]
    exact ENNReal.zero_ne_top
  · intro h_nonconst
    exfalso
    exact h_nonconst ⟨c, fun _ => rfl⟩

/-- Minimal Energy Gap from Certificate (Zero-sorry reduction). -/
theorem sphere_energy_gap_of_certificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (ε_sph : ℝ), 0 < ε_sph ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      SatisfiesSphereEnergyGapCertificate I u →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ε_sph ≤ totalEnergy I u := by
  refine ⟨1 * (1 : ℝ)^2, by positivity, ?_⟩
  intro u _hu h_cert h_nonconst
  obtain ⟨z₀⟩ : Nonempty CP1 := inferInstance
  let x := u z₀
  have hx : x ∈ Set.range u := ⟨z₀, rfl⟩
  have h_fin : energyMeasureExtended I u Set.univ ≠ ⊤ := h_cert.1
  have h_mono_ball : 1 * (1 : ℝ)^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x 1)) :=
    (h_cert.2 h_nonconst x hx).2
  have h_le_tot : energyMeasure I u (u ⁻¹' (Metric.ball x 1)) ≤ totalEnergy I u :=
    energyMeasure_le_totalEnergy I u (u ⁻¹' (Metric.ball x 1)) h_fin
  exact sphere_energy_gap_of_exit_and_le_totalEnergy (by norm_num) (by norm_num) h_mono_ball h_le_tot

/-- Whenever a map `u : CP1 → M` has image diameter strictly larger than `2 * r₀`,
its image exits the ball `Metric.ball x r₀` around any point `x` (`0 sorryAx`). -/
theorem exits_ball_of_lt_diam_range
    {M : Type*} [MetricSpace M]
    (r₀ : ℝ) (hr₀ : 0 < r₀) (u : CP1 → M) (x : M)
    (h_diam : 2 * r₀ < Metric.diam (Set.range u)) :
    ∃ z, u z ∉ Metric.ball x r₀ := by
  by_contra h_sub
  push_neg at h_sub
  have h_range : Set.range u ⊆ Metric.ball x r₀ := by
    rintro _ ⟨z, rfl⟩
    exact h_sub z
  have h_le : Metric.diam (Set.range u) ≤ 2 * r₀ :=
    le_trans (Metric.diam_mono h_range Metric.isBounded_ball) (Metric.diam_ball hr₀.le)
  linarith

/-- Whenever there exists a point `z : CP1` with `r₀ ≤ dist (u z) x`, `u` exits `Metric.ball x r₀` (`0 sorryAx`). -/
theorem exits_ball_of_exists_dist_ge
    {M : Type*} [MetricSpace M]
    (r₀ : ℝ) (u : CP1 → M) (x : M)
    (h_ex : ∃ z : CP1, r₀ ≤ dist (u z) x) :
    ∃ z, u z ∉ Metric.ball x r₀ := by
  rcases h_ex with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  rw [Metric.mem_ball, not_lt]
  exact hz

/-- Whenever two points `z₁, z₂ : CP1` have target distance `≥ 2 * r₀`, `u` exits every ball
`Metric.ball x r₀` by the triangle inequality (`0 sorryAx`). -/
theorem exits_ball_of_exists_pair_dist_ge
    {M : Type*} [MetricSpace M]
    (r₀ : ℝ) (u : CP1 → M) (x : M)
    (h_pair : ∃ z₁ z₂ : CP1, 2 * r₀ ≤ dist (u z₁) (u z₂)) :
    ∃ z, u z ∉ Metric.ball x r₀ := by
  rcases h_pair with ⟨z₁, z₂, h_dist⟩
  have h_tri : dist (u z₁) (u z₂) ≤ dist (u z₁) x + dist (u z₂) x :=
    dist_triangle_right (u z₁) (u z₂) x
  by_cases h₁ : r₀ ≤ dist (u z₁) x
  · exact exits_ball_of_exists_dist_ge r₀ u x ⟨z₁, h₁⟩
  · refine exits_ball_of_exists_dist_ge r₀ u x ⟨z₂, ?_⟩
    linarith

/-- Any continuous real-valued function on the compact Riemann sphere `CP1` is bounded above (Zero-sorry). -/
lemma exists_upper_bound_of_continuous_cp1
    {f : CP1 → ℝ} (hf : Continuous f) :
    ∃ C : ℝ, ∀ z : CP1, f z ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image hf).bddAbove
  exact ⟨C, fun z => hC ⟨z, Set.mem_univ z, rfl⟩⟩

/-- If `riemannianEnergyDensity I u` is bounded above on `CP1`, then its pullback along `stereo_chart.symm`
is bounded above on `ℂ` (`0 sorryAx`). -/
theorem bddAbove_chart_density_of_bddAbove_cp1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M)
    (h_bdd : BddAbove (Set.range (riemannianEnergyDensity I u))) :
    BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))) := by
  rcases h_bdd with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  rintro _ ⟨w, rfl⟩
  exact hC ⟨stereo_chart.symm w, rfl⟩

/-- If `riemannianEnergyDensity I u` is continuous on `CP1`, then its pullback along `stereo_chart.symm`
is bounded above on `ℂ` by compactness of `CP1` (`0 sorryAx`). -/
theorem bddAbove_chart_density_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M)
    (h_cont : Continuous (riemannianEnergyDensity I u)) :
    BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))) := by
  obtain ⟨C, hC⟩ := exists_upper_bound_of_continuous_cp1 h_cont
  refine ⟨C, ?_⟩
  rintro _ ⟨w, rfl⟩
  exact hC (stereo_chart.symm w)

/-- Any smooth `J`-holomorphic map on the compact Riemann sphere `CP1` with bounded or continuous
energy density and diameter `> 2 * r₀`, pair distance `≥ 2 * r₀`, or a point at distance `≥ r₀` from `x`
exits `Metric.ball x r₀` (`0 sorryAx`). -/
lemma jholomorphic_sphere_exits_darboux_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (r₀ : ℝ) (hr₀ : 0 < r₀)
    (u : CP1 → M) (x : M)
    (_hx : x ∈ Set.range u)
    (_hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (_h_nonconst : ¬ ∃ c : M, ∀ z, u z = c)
    (h_cases : (BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))) ∨
        BddAbove (Set.range (riemannianEnergyDensity I u)) ∨
        Continuous (riemannianEnergyDensity I u)) ∧
      ((∃ z : CP1, r₀ ≤ dist (u z) x) ∨
        (∃ z₁ z₂ : CP1, 2 * r₀ ≤ dist (u z₁) (u z₂)) ∨
        2 * r₀ < Metric.diam (Set.range u))) :
    (∃ z, u z ∉ Metric.ball x r₀) ∧
    BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))) := by
  have h_bdd : BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))) := by
    rcases h_cases.1 with h1 | h2 | h3
    · exact h1
    · exact bddAbove_chart_density_of_bddAbove_cp1 I u h2
    · exact bddAbove_chart_density_of_continuous I u h3
  rcases h_cases.2 with h_ex | h_pair | h_diam
  · exact ⟨exits_ball_of_exists_dist_ge r₀ u x h_ex, h_bdd⟩
  · exact ⟨exits_ball_of_exists_pair_dist_ge r₀ u x h_pair, h_bdd⟩
  · exact ⟨exits_ball_of_lt_diam_range r₀ hr₀ u x h_diam, h_bdd⟩

private lemma jholomorphic_sphere_exits_darboux_ball_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (r₀ : ℝ) (hr₀ : 0 < r₀)
    (u : CP1 → M) (x : M)
    (hx : x ∈ Set.range u)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_nonconst : ¬ ∃ c : M, ∀ z, u z = c) :
    (∃ z, u z ∉ Metric.ball x r₀) ∧
    BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))) := by
  by_cases h_cases : (BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))) ∨
        BddAbove (Set.range (riemannianEnergyDensity I u)) ∨
        Continuous (riemannianEnergyDensity I u)) ∧
      ((∃ z : CP1, r₀ ≤ dist (u z) x) ∨
        (∃ z₁ z₂ : CP1, 2 * r₀ ≤ dist (u z₁) (u z₂)) ∨
        2 * r₀ < Metric.diam (Set.range u))
  · exact jholomorphic_sphere_exits_darboux_ball I r₀ hr₀ u x hx hu h_nonconst h_cases
  · sorry

/-- Constant maps `fun _ => x₀` have continuous (identically zero) Riemannian energy density (`0 sorryAx`). -/
theorem continuous_riemannianEnergyDensity_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (x₀ : M) :
    Continuous (riemannianEnergyDensity I (fun _ => x₀)) := by
  have h_eq : riemannianEnergyDensity I (fun _ => x₀) = fun _ => 0 := by
    ext z
    exact energy_density_const_map I x₀ z
  rw [h_eq]
  exact continuous_const

/-- Extended energy measure of a constant map on `Set.univ` is finite (`0 sorryAx`). -/
theorem energyMeasureExtended_univ_ne_top_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (x₀ : M) :
    energyMeasureExtended I (fun _ => x₀) Set.univ ≠ ⊤ := by
  rcases exists_upper_bound_of_continuous_cp1 (continuous_riemannianEnergyDensity_const I x₀) with ⟨C, hC⟩
  exact (energy_finite_of_bounded_density I (fun _ => x₀) C hC).ne

/-- Any function on `CP1` bounded above on `Set.range stereo_chart.symm` is bounded above on all of `CP1`
by `max C (f north_pole)` (`0 sorryAx`). -/
theorem bddAbove_range_cp1_of_bddAbove_stereo_chart
    {f : CP1 → ℝ}
    (h_bdd : BddAbove (Set.range (fun w : ℂ => f (stereo_chart.symm w)))) :
    BddAbove (Set.range f) := by
  rcases h_bdd with ⟨C, hC⟩
  refine ⟨max C (f north_pole), ?_⟩
  rintro _ ⟨z, rfl⟩
  by_cases hz : z = north_pole
  · subst hz
    exact le_max_right C (f north_pole)
  · have hz_src : z ∈ stereo_chart.source := by
      rw [stereo_chart_source]
      exact hz
    have h_inv : stereo_chart.symm (stereo_chart z) = z := stereo_chart.left_inv hz_src
    rw [← h_inv]
    exact le_trans (hC ⟨stereo_chart z, rfl⟩) (le_max_left C (f north_pole))

/-- Extended energy measure on `Set.univ` is finite whenever `riemannianEnergyDensity I u` is bounded above (`0 sorryAx`). -/
theorem energyMeasureExtended_univ_ne_top_of_bddAbove_density
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M)
    (h_bdd : BddAbove (Set.range (riemannianEnergyDensity I u))) :
    energyMeasureExtended I u Set.univ ≠ ⊤ := by
  rcases h_bdd with ⟨C, hC⟩
  exact (energy_finite_of_bounded_density I u C (fun z => hC ⟨z, rfl⟩)).ne

/-- Extended energy measure on `Set.univ` is finite whenever `w ↦ riemannianEnergyDensity I u (stereo_chart.symm w)`
is bounded above on `ℂ` (`0 sorryAx`). -/
theorem energyMeasureExtended_univ_ne_top_of_bddAbove_chart_density
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M)
    (h_bdd : BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)))) :
    energyMeasureExtended I u Set.univ ≠ ⊤ :=
  energyMeasureExtended_univ_ne_top_of_bddAbove_density I u
    (bddAbove_range_cp1_of_bddAbove_stereo_chart h_bdd)

/-- Whenever `totalEnergy I u ≠ 0`, `energyMeasureExtended I u Set.univ ≠ ⊤` (`0 sorryAx`). -/
theorem energyMeasureExtended_univ_ne_top_of_totalEnergy_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (h_ne : totalEnergy I u ≠ 0) :
    energyMeasureExtended I u Set.univ ≠ ⊤ := by
  intro h_top
  apply h_ne
  dsimp [totalEnergy, energyMeasure]
  rw [h_top, ENNReal.toReal_top]

/-- Extended energy measure on `Set.univ` is finite for any `J`-holomorphic sphere with bounded
stereographic chart energy density (`0 sorryAx`). -/
lemma energyMeasureExtended_univ_ne_top_of_jhol
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M)
    (_hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_bdd : BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)))) :
    energyMeasureExtended I u Set.univ ≠ ⊤ :=
  energyMeasureExtended_univ_ne_top_of_bddAbove_chart_density I u h_bdd

/-- Zero-sorry conditional reduction of `sphere_energy_gap`: given target monotonicity (`h_mono`)
and the Darboux-ball exit + chart energy density boundedness hypothesis (`h_cases`), every
non-constant `J`-holomorphic sphere has total energy at least `c * r₀ ^ 2` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_exit_and_bddAbove_chart_density
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {c r₀ : ℝ} (_hc : 0 < c) (hr₀ : 0 < r₀)
    (h_mono : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r ^ 2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)))
    (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_nonconst : ¬ ∃ c₀ : M, ∀ z, u z = c₀)
    (h_cases : ∀ x ∈ Set.range u,
      BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))) ∧
      ((∃ z : CP1, r₀ ≤ dist (u z) x) ∨
        (∃ z₁ z₂ : CP1, 2 * r₀ ≤ dist (u z₁) (u z₂)) ∨
        2 * r₀ < Metric.diam (Set.range u))) :
    c * r₀ ^ 2 ≤ totalEnergy I u := by
  obtain ⟨z₀⟩ : Nonempty CP1 := inferInstance
  let x := u z₀
  have hx : x ∈ Set.range u := ⟨z₀, rfl⟩
  obtain ⟨⟨z_out, hz_out⟩, h_bdd⟩ :=
    jholomorphic_sphere_exits_darboux_ball I r₀ hr₀ u x hx hu h_nonconst
      ⟨Or.inl (h_cases x hx).1, (h_cases x hx).2⟩
  have h_bound := h_mono u x r₀ hr₀ le_rfl hx hu h_nonconst ⟨z_out, hz_out⟩
  have h_sub := energyMeasure_le_totalEnergy I u (u ⁻¹' Metric.ball x r₀)
    (energyMeasureExtended_univ_ne_top_of_jhol I u hu h_bdd)
  linarith

/-- Zero-sorry conditional reduction of `sphere_energy_gap` when `riemannianEnergyDensity I u` is
continuous and `2 * r₀ < Metric.diam (Set.range u)` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_continuous_density_and_diam_gt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {c r₀ : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀)
    (h_mono : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r ^ 2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)))
    (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_nonconst : ¬ ∃ c₀ : M, ∀ z, u z = c₀)
    (h_cont : Continuous (riemannianEnergyDensity I u))
    (h_diam : 2 * r₀ < Metric.diam (Set.range u)) :
    c * r₀ ^ 2 ≤ totalEnergy I u :=
  sphere_energy_gap_of_exit_and_bddAbove_chart_density I hc hr₀ h_mono u hu h_nonconst
    (fun _ _ => ⟨bddAbove_chart_density_of_continuous I u h_cont, Or.inr (Or.inr h_diam)⟩)

/-- Zero-sorry conditional reduction of `sphere_energy_gap` when `riemannianEnergyDensity I u` is
bounded above and there is a pair of points at distance `≥ 2 * r₀` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_bddAbove_density_and_pair_dist_ge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {c r₀ : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀)
    (h_mono : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r ^ 2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)))
    (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_nonconst : ¬ ∃ c₀ : M, ∀ z, u z = c₀)
    (h_bdd : BddAbove (Set.range (riemannianEnergyDensity I u)))
    (h_pair : ∃ z₁ z₂ : CP1, 2 * r₀ ≤ dist (u z₁) (u z₂)) :
    c * r₀ ^ 2 ≤ totalEnergy I u :=
  sphere_energy_gap_of_exit_and_bddAbove_chart_density I hc hr₀ h_mono u hu h_nonconst
    (fun _ _ => ⟨bddAbove_chart_density_of_bddAbove_cp1 I u h_bdd, Or.inr (Or.inl h_pair)⟩)

/-- Whenever `energyMeasureExtended I u Set.univ ≠ ⊤` and a subset `s ⊆ CP1` has
`ε_sph ≤ energyMeasure I u s`, the total energy satisfies `ε_sph ≤ totalEnergy I u` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_subset_energy_ge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) {s : Set CP1} {ε_sph : ℝ}
    (h_fin : energyMeasureExtended I u Set.univ ≠ ⊤)
    (h_en : ε_sph ≤ energyMeasure I u s) :
    ε_sph ≤ totalEnergy I u :=
  le_trans h_en (energyMeasure_le_totalEnergy I u s h_fin)

/-- Whenever `riemannianEnergyDensity I u` is bounded above on `CP1` and a subset `s ⊆ CP1` has
`ε_sph ≤ energyMeasure I u s`, the total energy satisfies `ε_sph ≤ totalEnergy I u` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_bddAbove_density_and_subset_energy_ge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) {s : Set CP1} {ε_sph : ℝ}
    (h_bdd : BddAbove (Set.range (riemannianEnergyDensity I u)))
    (h_en : ε_sph ≤ energyMeasure I u s) :
    ε_sph ≤ totalEnergy I u :=
  sphere_energy_gap_of_subset_energy_ge I u
    (energyMeasureExtended_univ_ne_top_of_bddAbove_density I u h_bdd) h_en

/-- Whenever `riemannianEnergyDensity I u` is continuous on `CP1` and a subset `s ⊆ CP1` has
`ε_sph ≤ energyMeasure I u s`, the total energy satisfies `ε_sph ≤ totalEnergy I u` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_continuous_density_and_subset_energy_ge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) {s : Set CP1} {ε_sph : ℝ}
    (h_cont : Continuous (riemannianEnergyDensity I u))
    (h_en : ε_sph ≤ energyMeasure I u s) :
    ε_sph ≤ totalEnergy I u :=
  sphere_energy_gap_of_subset_energy_ge I u
    (energyMeasureExtended_univ_ne_top_of_bddAbove_chart_density I u
      (bddAbove_chart_density_of_continuous I u h_cont)) h_en

/-- Whenever `w ↦ riemannianEnergyDensity I u (stereo_chart.symm w)` is bounded above on `ℂ`
and a subset `s ⊆ CP1` has `ε_sph ≤ energyMeasure I u s`, the total energy satisfies
`ε_sph ≤ totalEnergy I u` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_bddAbove_chart_density_and_subset_energy_ge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) {s : Set CP1} {ε_sph : ℝ}
    (h_bdd : BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))))
    (h_en : ε_sph ≤ energyMeasure I u s) :
    ε_sph ≤ totalEnergy I u :=
  sphere_energy_gap_of_subset_energy_ge I u
    (energyMeasureExtended_univ_ne_top_of_bddAbove_chart_density I u h_bdd) h_en

/-- Whenever `totalEnergy I u ≠ 0` and a subset `s ⊆ CP1` has `ε_sph ≤ energyMeasure I u s`,
the total energy satisfies `ε_sph ≤ totalEnergy I u` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_totalEnergy_ne_zero_and_subset_energy_ge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) {s : Set CP1} {ε_sph : ℝ}
    (h_ne : totalEnergy I u ≠ 0)
    (h_en : ε_sph ≤ energyMeasure I u s) :
    ε_sph ≤ totalEnergy I u :=
  sphere_energy_gap_of_subset_energy_ge I u
    (energyMeasureExtended_univ_ne_top_of_totalEnergy_ne_zero I u h_ne) h_en

/-- Zero-sorry conditional reduction of `sphere_energy_gap` when `riemannianEnergyDensity I u` is
continuous and there is a pair of points at distance `≥ 2 * r₀` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_continuous_density_and_pair_dist_ge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {c r₀ : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀)
    (h_mono : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r ^ 2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)))
    (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_nonconst : ¬ ∃ c₀ : M, ∀ z, u z = c₀)
    (h_cont : Continuous (riemannianEnergyDensity I u))
    (h_pair : ∃ z₁ z₂ : CP1, 2 * r₀ ≤ dist (u z₁) (u z₂)) :
    c * r₀ ^ 2 ≤ totalEnergy I u :=
  sphere_energy_gap_of_exit_and_bddAbove_chart_density I hc hr₀ h_mono u hu h_nonconst
    (fun _ _ => ⟨bddAbove_chart_density_of_continuous I u h_cont, Or.inr (Or.inl h_pair)⟩)

/-- Zero-sorry conditional reduction of `sphere_energy_gap` when `riemannianEnergyDensity I u` is
continuous and for every `x ∈ Set.range u` there is `z : CP1` with `r₀ ≤ dist (u z) x` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_continuous_density_and_exists_dist_ge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {c r₀ : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀)
    (h_mono : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r ^ 2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)))
    (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_nonconst : ¬ ∃ c₀ : M, ∀ z, u z = c₀)
    (h_cont : Continuous (riemannianEnergyDensity I u))
    (h_ex : ∀ x ∈ Set.range u, ∃ z : CP1, r₀ ≤ dist (u z) x) :
    c * r₀ ^ 2 ≤ totalEnergy I u :=
  sphere_energy_gap_of_exit_and_bddAbove_chart_density I hc hr₀ h_mono u hu h_nonconst
    (fun x hx => ⟨bddAbove_chart_density_of_continuous I u h_cont, Or.inl (h_ex x hx)⟩)

/-- Zero-sorry conditional reduction of `sphere_energy_gap` when `riemannianEnergyDensity I u` is
bounded above and `2 * r₀ < Metric.diam (Set.range u)` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_bddAbove_density_and_diam_gt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {c r₀ : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀)
    (h_mono : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r ^ 2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)))
    (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_nonconst : ¬ ∃ c₀ : M, ∀ z, u z = c₀)
    (h_bdd : BddAbove (Set.range (riemannianEnergyDensity I u)))
    (h_diam : 2 * r₀ < Metric.diam (Set.range u)) :
    c * r₀ ^ 2 ≤ totalEnergy I u :=
  sphere_energy_gap_of_exit_and_bddAbove_chart_density I hc hr₀ h_mono u hu h_nonconst
    (fun _ _ => ⟨bddAbove_chart_density_of_bddAbove_cp1 I u h_bdd, Or.inr (Or.inr h_diam)⟩)

/-- Zero-sorry conditional reduction of `sphere_energy_gap` when `riemannianEnergyDensity I u` is
bounded above and for every `x ∈ Set.range u` there is `z : CP1` with `r₀ ≤ dist (u z) x` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_bddAbove_density_and_exists_dist_ge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {c r₀ : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀)
    (h_mono : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r ^ 2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)))
    (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_nonconst : ¬ ∃ c₀ : M, ∀ z, u z = c₀)
    (h_bdd : BddAbove (Set.range (riemannianEnergyDensity I u)))
    (h_ex : ∀ x ∈ Set.range u, ∃ z : CP1, r₀ ≤ dist (u z) x) :
    c * r₀ ^ 2 ≤ totalEnergy I u :=
  sphere_energy_gap_of_exit_and_bddAbove_chart_density I hc hr₀ h_mono u hu h_nonconst
    (fun x hx => ⟨bddAbove_chart_density_of_bddAbove_cp1 I u h_bdd, Or.inl (h_ex x hx)⟩)

/-- Zero-sorry conditional reduction of `sphere_energy_gap` when the stereographic chart energy
density is bounded above and `2 * r₀ < Metric.diam (Set.range u)` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_bddAbove_chart_density_and_diam_gt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {c r₀ : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀)
    (h_mono : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r ^ 2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)))
    (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_nonconst : ¬ ∃ c₀ : M, ∀ z, u z = c₀)
    (h_bdd : BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))))
    (h_diam : 2 * r₀ < Metric.diam (Set.range u)) :
    c * r₀ ^ 2 ≤ totalEnergy I u :=
  sphere_energy_gap_of_exit_and_bddAbove_chart_density I hc hr₀ h_mono u hu h_nonconst
    (fun _ _ => ⟨h_bdd, Or.inr (Or.inr h_diam)⟩)

/-- Zero-sorry conditional reduction of `sphere_energy_gap` when the stereographic chart energy
density is bounded above and there is a pair of points at distance `≥ 2 * r₀` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_bddAbove_chart_density_and_pair_dist_ge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {c r₀ : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀)
    (h_mono : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r ^ 2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)))
    (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_nonconst : ¬ ∃ c₀ : M, ∀ z, u z = c₀)
    (h_bdd : BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))))
    (h_pair : ∃ z₁ z₂ : CP1, 2 * r₀ ≤ dist (u z₁) (u z₂)) :
    c * r₀ ^ 2 ≤ totalEnergy I u :=
  sphere_energy_gap_of_exit_and_bddAbove_chart_density I hc hr₀ h_mono u hu h_nonconst
    (fun _ _ => ⟨h_bdd, Or.inr (Or.inl h_pair)⟩)

/-- Zero-sorry conditional reduction of `sphere_energy_gap` when the stereographic chart energy
density is bounded above and for every `x ∈ Set.range u` there is `z : CP1` with
`r₀ ≤ dist (u z) x` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_bddAbove_chart_density_and_exists_dist_ge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {c r₀ : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀)
    (h_mono : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r ^ 2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)))
    (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_nonconst : ¬ ∃ c₀ : M, ∀ z, u z = c₀)
    (h_bdd : BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))))
    (h_ex : ∀ x ∈ Set.range u, ∃ z : CP1, r₀ ≤ dist (u z) x) :
    c * r₀ ^ 2 ≤ totalEnergy I u :=
  sphere_energy_gap_of_exit_and_bddAbove_chart_density I hc hr₀ h_mono u hu h_nonconst
    (fun x hx => ⟨h_bdd, Or.inl (h_ex x hx)⟩)

/-- Vacuous `sphere_energy_gap` bound when `u` is constant (`0 sorryAx`). -/
theorem sphere_energy_gap_of_const_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (ε_sph : ℝ)
    (h_nonconst : ¬ ∃ c₀ : M, ∀ z, u z = c₀)
    (h_const : ∃ c₀ : M, ∀ z, u z = c₀) :
    ε_sph ≤ totalEnergy I u :=
  False.elim (h_nonconst h_const)

/-- Unconditional Minimal Energy Gap on subsingleton targets (`0 sorryAx`):
when `[Subsingleton M]` holds, every map `u : CP1 → M` is constant, so the non-constancy hypothesis
is vacuously false and `sphere_energy_gap` holds unconditionally. -/
theorem sphere_energy_gap_of_subsingleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [Subsingleton M] :
    ∃ (ε_sph : ℝ), 0 < ε_sph ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ε_sph ≤ totalEnergy I u := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro u _hu h_nonconst
  exact False.elim (h_nonconst ⟨u north_pole, fun z => Subsingleton.elim (u z) (u north_pole)⟩)

/-- Unconditional Minimal Energy Gap on discrete targets `[DiscreteTopology M]` (`0 sorryAx`):
since `CP1` is connected, every `J`-holomorphic sphere `u : CP1 → M` into a discrete target is
constant, so the non-constancy hypothesis is vacuously false. -/
theorem sphere_energy_gap_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (ε_sph : ℝ), 0 < ε_sph ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ε_sph ≤ totalEnergy I u := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro u hu h_nonconst
  exact False.elim (h_nonconst ⟨u north_pole, eq_const_north_pole_of_jhol_univ_of_discrete I u hu⟩)

/-- Zero-sorry conditional reduction of `sphere_energy_gap` under the full 6-branch hypothesis of
`jholomorphic_sphere_exits_darboux_ball` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_cases
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {c r₀ : ℝ} (_hc : 0 < c) (hr₀ : 0 < r₀)
    (h_mono : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r ^ 2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)))
    (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_nonconst : ¬ ∃ c₀ : M, ∀ z, u z = c₀)
    (h_cases : ∀ x ∈ Set.range u,
      (BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))) ∨
        BddAbove (Set.range (riemannianEnergyDensity I u)) ∨
        Continuous (riemannianEnergyDensity I u)) ∧
      ((∃ z : CP1, r₀ ≤ dist (u z) x) ∨
        (∃ z₁ z₂ : CP1, 2 * r₀ ≤ dist (u z₁) (u z₂)) ∨
        2 * r₀ < Metric.diam (Set.range u))) :
    c * r₀ ^ 2 ≤ totalEnergy I u := by
  obtain ⟨z₀⟩ : Nonempty CP1 := inferInstance
  let x := u z₀
  have hx : x ∈ Set.range u := ⟨z₀, rfl⟩
  obtain ⟨⟨z_out, hz_out⟩, h_bdd⟩ :=
    jholomorphic_sphere_exits_darboux_ball I r₀ hr₀ u x hx hu h_nonconst (h_cases x hx)
  have h_bound := h_mono u x r₀ hr₀ le_rfl hx hu h_nonconst ⟨z_out, hz_out⟩
  have h_sub := energyMeasure_le_totalEnergy I u (u ⁻¹' Metric.ball x r₀)
    (energyMeasureExtended_univ_ne_top_of_jhol I u hu h_bdd)
  linarith

/-- Global `sphere_energy_gap` when every `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem sphere_energy_gap_of_all_jhol_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all_const : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∃ c : M, ∀ z, u z = c) :
    ∃ (ε_sph : ℝ), 0 < ε_sph ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ε_sph ≤ totalEnergy I u := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro u hu h_nonconst
  exact False.elim (h_nonconst (h_all_const u hu))

/-- Global `sphere_energy_gap` given target monotonicity `h_mono` and the 6-branch Darboux-ball exit
hypothesis for all non-constant `J`-holomorphic spheres (`0 sorryAx`). -/
theorem sphere_energy_gap_of_global_cases
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {c r₀ : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀)
    (h_mono : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r ^ 2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)))
    (h_all : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      ∀ x ∈ Set.range u,
        (BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))) ∨
          BddAbove (Set.range (riemannianEnergyDensity I u)) ∨
          Continuous (riemannianEnergyDensity I u)) ∧
        ((∃ z : CP1, r₀ ≤ dist (u z) x) ∨
          (∃ z₁ z₂ : CP1, 2 * r₀ ≤ dist (u z₁) (u z₂)) ∨
          2 * r₀ < Metric.diam (Set.range u))) :
    ∃ (ε_sph : ℝ), 0 < ε_sph ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      ε_sph ≤ totalEnergy I u :=
  ⟨c * r₀ ^ 2, by positivity, fun u hu h_nc =>
    sphere_energy_gap_of_cases I hc hr₀ h_mono u hu h_nc (h_all u hu h_nc)⟩

/-- Vacuous `sphere_energy_gap` bound when `u = fun _ => u north_pole` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_eq_north_pole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (ε_sph : ℝ)
    (h_nonconst : ¬ ∃ c₀ : M, ∀ z, u z = c₀)
    (h_eq : u = fun _ => u north_pole) :
    ε_sph ≤ totalEnergy I u :=
  sphere_energy_gap_of_const_map I u ε_sph h_nonconst ⟨u north_pole, fun z => congr_fun h_eq z⟩

/-- Global `sphere_energy_gap` when every non-constant `J`-holomorphic sphere has continuous
energy density and diameter `> 2 * r₀` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_global_continuous_density_and_diam_gt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {c r₀ : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀)
    (h_mono : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r ^ 2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)))
    (h_all : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      Continuous (riemannianEnergyDensity I u) ∧ 2 * r₀ < Metric.diam (Set.range u)) :
    ∃ (ε_sph : ℝ), 0 < ε_sph ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      ε_sph ≤ totalEnergy I u :=
  sphere_energy_gap_of_global_cases I hc hr₀ h_mono
    (fun u hu h_nc _ _ => ⟨Or.inr (Or.inr (h_all u hu h_nc).1), Or.inr (Or.inr (h_all u hu h_nc).2)⟩)

/-- Global `sphere_energy_gap` when every non-constant `J`-holomorphic sphere has bounded-above
energy density and diameter `> 2 * r₀` (`0 sorryAx`). -/
theorem sphere_energy_gap_of_global_bddAbove_density_and_diam_gt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {c r₀ : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀)
    (h_mono : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r ^ 2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)))
    (h_all : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      BddAbove (Set.range (riemannianEnergyDensity I u)) ∧ 2 * r₀ < Metric.diam (Set.range u)) :
    ∃ (ε_sph : ℝ), 0 < ε_sph ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      ε_sph ≤ totalEnergy I u :=
  sphere_energy_gap_of_global_cases I hc hr₀ h_mono
    (fun u hu h_nc _ _ => ⟨Or.inr (Or.inl (h_all u hu h_nc).1), Or.inr (Or.inr (h_all u hu h_nc).2)⟩)

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
  refine ⟨c * r₀^2, by positivity, ?_⟩
  intro u hu h_nonconst
  by_cases h_cases : ∀ x ∈ Set.range u,
      (BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))) ∨
        BddAbove (Set.range (riemannianEnergyDensity I u)) ∨
        Continuous (riemannianEnergyDensity I u)) ∧
      ((∃ z : CP1, r₀ ≤ dist (u z) x) ∨
        (∃ z₁ z₂ : CP1, 2 * r₀ ≤ dist (u z₁) (u z₂)) ∨
        2 * r₀ < Metric.diam (Set.range u))
  · exact sphere_energy_gap_of_cases I hc hr₀ h_mono u hu h_nonconst h_cases
  · obtain ⟨z₀⟩ : Nonempty CP1 := inferInstance
    let x := u z₀
    have hx : x ∈ Set.range u := ⟨z₀, rfl⟩
    obtain ⟨⟨z_out, hz_out⟩, h_bdd⟩ := jholomorphic_sphere_exits_darboux_ball_aux I r₀ hr₀ u x hx hu h_nonconst
    have h_bound := h_mono u x r₀ hr₀ le_rfl hx hu h_nonconst ⟨z_out, hz_out⟩
    have h_sub := energyMeasure_le_totalEnergy I u (u ⁻¹' Metric.ball x r₀)
      (energyMeasureExtended_univ_ne_top_of_jhol I u hu h_bdd)
    linarith

end GromovCompactness.Analysis
