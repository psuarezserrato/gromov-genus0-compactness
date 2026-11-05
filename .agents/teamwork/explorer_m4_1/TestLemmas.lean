import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.EpsilonRegularity
import GromovCompactness.Analysis.Monotonicity

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness GromovCompactness.Analysis

namespace GromovCompactness.Analysis.Test

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-!
### 1. Characterizations of Non-Constancy
-/

/-- Non-constancy of a map from a nonempty type is equivalent to the existence of two points with distinct values. -/
lemma nonconstant_iff_exists_ne (u : CP1 → M) :
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

lemma exists_ne_of_nonconstant (u : CP1 → M) (h : ¬ ∃ c : M, ∀ z, u z = c) :
    ∃ z w : CP1, u z ≠ u w :=
  (nonconstant_iff_exists_ne u).mp h

/-- Non-constancy yields a point in the image and an outside point for small radii. -/
lemma exists_outside_of_nonconstant (u : CP1 → M) (h : ¬ ∃ c : M, ∀ z, u z = c) :
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
### 2. Energy Properties of Constant Maps
-/

/-- The Riemannian energy density of a constant map vanishes identically. -/
theorem riemannianEnergyDensity_const (c : M) (z : CP1) :
    riemannianEnergyDensity I (fun _ => c) z = 0 := by
  dsimp [riemannianEnergyDensity]
  simp only [mfderiv_const]
  dsimp [ClosedTameTarget.metric]
  have h1 : ClosedTameTarget.«ω» (I := I) c 0 (ClosedTameTarget.J (I := I) c 0) = 0 := by
    simp
  have h2 : ClosedTameTarget.«ω» (I := I) c 0 (ClosedTameTarget.J (I := I) c 0) = 0 := by
    simp
  simp

/-- The extended energy measure of a constant map is the zero measure. -/
theorem energyMeasureExtended_const (c : M) :
    energyMeasureExtended I (fun _ : CP1 => c) = 0 := by
  dsimp [energyMeasureExtended, chartPush]
  have h_dens : (fun w : ℂ => ENNReal.ofReal (riemannianEnergyDensity I (fun _ => c) (stereo_chart.symm w))) = 0 := by
    ext w
    rw [riemannianEnergyDensity_const]
    simp [ENNReal.ofReal_zero]
  rw [h_dens]
  simp [withDensity_zero]

/-- The energy measure of any set for a constant map vanishes. -/
theorem energyMeasure_const (c : M) (A : Set CP1) :
    energyMeasure I (fun _ => c) A = 0 := by
  dsimp [energyMeasure]
  rw [energyMeasureExtended_const]
  simp

/-- The total energy of a constant map vanishes. -/
theorem totalEnergy_const (c : M) :
    totalEnergy I (fun _ : CP1 => c) = 0 :=
  energyMeasure_const I c Set.univ

/-- If `u` is constant (equal to `c` everywhere), its total energy vanishes. -/
theorem totalEnergy_eq_zero_of_forall_eq (u : CP1 → M) (c : M) (hc : ∀ z, u z = c) :
    totalEnergy I u = 0 := by
  have hu : u = fun _ => c := funext hc
  rw [hu]
  exact totalEnergy_const I c

/-!
### 3. Total Energy Non-Negativity and Monotonicity
-/

theorem totalEnergy_nonneg (u : CP1 → M) :
    0 ≤ totalEnergy I u :=
  energy_nonneg I u Set.univ

lemma energyMeasure_le_totalEnergy (u : CP1 → M) (A : Set CP1)
    (h_fin : energyMeasureExtended I u Set.univ ≠ ⊤) :
    energyMeasure I u A ≤ totalEnergy I u := by
  dsimp [energyMeasure, totalEnergy]
  have h_mono : energyMeasureExtended I u A ≤ energyMeasureExtended I u Set.univ :=
    measure_mono (subset_univ A)
  exact ENNReal.toReal_mono h_fin h_mono

/-!
### 4. Zero-Sorry Reduction: Sphere Energy Gap via Target Monotonicity
-/

/-- Reduction theorem: Target monotonicity and image exit together imply the minimal energy gap
with ZERO `sorry`. -/
theorem sphere_energy_gap_of_monotonicity_and_exit
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

/-- Reduction theorem: Epsilon-regularity / diameter bound and Stokes exactness together
imply the minimal energy gap with ZERO `sorry`. -/
theorem sphere_energy_gap_of_stokes_and_diameter
    (ε_diam : ℝ) (hε : 0 < ε_diam) (r_inj : ℝ) (hr_inj : 0 < r_inj)
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

#print axioms sphere_energy_gap_of_stokes_and_diameter

#print axioms sphere_energy_gap_of_monotonicity_and_exit
#print axioms nonconstant_iff_exists_ne
#print axioms totalEnergy_const
#print axioms totalEnergy_eq_zero_of_forall_eq
#print axioms totalEnergy_nonneg
#print axioms energyMeasure_le_totalEnergy

end GromovCompactness.Analysis.Test
