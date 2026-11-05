import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.EpsilonRegularity
import GromovCompactness.Analysis.Monotonicity
import GromovCompactness.Analysis.EnergyGap
import GromovCompactness.Analysis.SingularityRemoval

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness
open GromovCompactness.Analysis

-- Edge-case stress tests for SingularityRemoval

-- Test 1: Conformal ratio edge cases: alpha = 0
example (r L : ℝ) (hr : 0 < r) :
    (r / (r * Real.exp L))^(0 : ℝ) = Real.exp (-(0 : ℝ) * L) :=
  annulus_ratio_rpow_eq_exp_neg r L 0 hr

-- Test 2: Conformal ratio edge cases: L = 0
example (r α : ℝ) (hr : 0 < r) :
    (r / (r * Real.exp 0))^α = Real.exp (-α * 0) :=
  annulus_ratio_rpow_eq_exp_neg r 0 α hr

-- Test 3: Grönwall on exact boundary function F(t) = exp(t / c)
lemma test_gronwall_exact (c L : ℝ) (hc : 0 < c) (hL : 0 ≤ L) :
    (fun t => Real.exp (t / c)) 0 * Real.exp (-0 / c) ≤
    (fun t => Real.exp (t / c)) L * Real.exp (-L / c) := by
  have hF : Differentiable ℝ (fun t => Real.exp (t / c)) := by
    apply Differentiable.exp
    apply Differentiable.div_const
    exact differentiable_id
  apply exp_decay_of_diff_ineq hF hc (fun t => ?_) hL
  have h_deriv : deriv (fun s => Real.exp (s / c)) t = (1 / c) * Real.exp (t / c) := by
    have h1 : HasDerivAt (fun s => s / c) (1 / c) t := by
      have := (hasDerivAt_id t).div_const c
      simpa using this
    have h2 := h1.exp
    rw [h2.deriv]
    ring
  rw [h_deriv]
  have hc_ne : c ≠ 0 := hc.ne'
  calc
    Real.exp (t / c) = c * ((1 / c) * Real.exp (t / c)) := by
      field_simp
    _ ≤ c * ((1 / c) * Real.exp (t / c)) := le_rfl

-- Test 4: Cauchy-Schwarz quadratic on exact square (t - 1)^2 = t^2 - 2t + 1 ≥ 0
example : (-1 : ℝ)^2 ≤ 1 * 1 := by
  have h_quad : ∀ t : ℝ, 0 ≤ (1 : ℝ) * t^2 + 2 * (-1) * t + 1 := by
    intro t
    have : (1 : ℝ) * t^2 + 2 * (-1) * t + 1 = (t - 1)^2 := by ring
    rw [this]
    exact sq_nonneg (t - 1)
  exact cauchy_schwarz_quadratic 1 (-1) 1 (by norm_num) h_quad

-- Test 5: Neck energy threshold for extreme values
example : ∃ η > 0, (1000 : ℝ) * Real.sqrt η < (1 / 1000 : ℝ) / 2 :=
  exists_neck_energy_threshold (1 / 1000) 1000 (by norm_num) (by norm_num)

-- Test 6: Empty degenerate collar
example : ({z : ℂ | 2 < dist z 0 ∧ dist z 0 < 1} : Set ℂ) = ∅ :=
  annulus_set_empty_of_le 0 (by norm_num)

-- Test 7: Target typeclass test: instantiate with MetricSpace M
section TargetMetricConsistency
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

-- Can we instantiate sphere_energy_gap_of_monotonicity_and_exit with target_monotonicity?
theorem test_energy_gap_reduction_links_with_monotonicity :
    (∃ (c r₀ : ℝ), 0 < c ∧ 0 < r₀ ∧
      ∀ (u : CP1 → M) (x : M) (r : ℝ),
        0 < r → r ≤ r₀ →
        x ∈ Set.range u →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        (¬ ∃ c : M, ∀ z, u z = c) →
        (∃ z, u z ∉ Metric.ball x r) →
        c * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r))) →
    (∀ (u : CP1 → M) (x : M),
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ∃ z, u z ∉ Metric.ball x 1) →
    (∀ (u : CP1 → M) (s : Set CP1),
      energyMeasure I u s ≤ totalEnergy I u) →
    ∃ (ε_sph : ℝ), 0 < ε_sph ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ε_sph ≤ totalEnergy I u := by
  intro ⟨c, r₀, hc, hr₀, h_mono⟩ h_exit h_en_le
  exact sphere_energy_gap_of_monotonicity_and_exit I c r₀ hc hr₀ h_mono (by
    intro u x hx hu hnc
    sorry
  ) h_en_le

-- Test 8: Uniqueness of constant extensions across puncture
theorem test_uniqueness_const (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [ClosedTameTarget I M] [T2Space M]
    (c₁ c₂ : M) (p : CP1)
    (h_dense : Dense (punctured_sphere {p}))
    (h_eq : EqOn (fun _ : CP1 => c₁) (fun _ : CP1 => c₂) (punctured_sphere {p})) :
    c₁ = c₂ := by
  have hu_eq : (fun _ : CP1 => c₁) = (fun _ : CP1 => c₂) :=
    removal_of_singularities_unique (I := I) p h_dense (fun _ => c₁) (fun _ => c₁) (fun _ => c₂)
      ⟨fun _ _ => rfl, jholomorphicOn_const I c₁ Set.univ⟩
      ⟨h_eq.symm, jholomorphicOn_const I c₂ Set.univ⟩
  have : (fun _ : CP1 => c₁) p = (fun _ : CP1 => c₂) p := by rw [hu_eq]
  exact this

end TargetMetricConsistency

-- Check axioms of our test
#print axioms annulus_ratio_rpow_eq_exp_neg
#print axioms exp_decay_of_diff_ineq
#print axioms cauchy_schwarz_quadratic
#print axioms exists_neck_energy_threshold
#print axioms annulus_set_empty_of_le
#print axioms sphere_energy_gap_of_monotonicity_and_exit
#print axioms test_uniqueness_const
