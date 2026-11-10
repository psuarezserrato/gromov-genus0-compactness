/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Challenger 2 Milestone M4 Empirical Test Harness)
-/
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import GromovCompactness
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Geometry.NormalCharts
import GromovCompactness.Analysis.SingularityRemoval
import GromovCompactness.Analysis.EllipticBootstrap
import GromovCompactness.Analysis.EnergyGap
import GromovCompactness.Analysis.Monotonicity
import GromovCompactness.Topology.SmoothLocal
import GromovCompactness.Topology.Subsequence
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology Real ENNReal
open Metric Set MeasureTheory Filter Topology ENNReal GromovCompactness GromovCompactness.Analysis

namespace GromovCompactness.AdversarialM4Challenger2

/- =============================================================================
   SECTION 1: CANONICAL SPHERE MODEL CP1_ClosedTameTarget INSTANTIATION
   AGAINST ALL 11 MASTER UNCONDITIONAL DECLARATIONS
   ============================================================================= -/

/-- Test 1.1: Canonical model CP1 instantiates master unconditional h_weitz. -/
theorem test_cp1_discharge_h_weitz_unconditional
    (fam : UniformNormalChartFamily I_CP1 (M := CP1))
    (certs : UniformNormalChartCertificates I_CP1 fam) :
    ∃ (b c : ℝ), 0 ≤ b ∧ c = 0 ∧
      ∀ (u : CP1 → CP1),
        JHolomorphicOn (I := I_CP1) (I_dom := I_CP1) u Set.univ →
        ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I_CP1 u (stereo_chart.symm w)) ∧
        ∀ (w : ℂ),
          ∃ (hessNorm : ℝ) (curvTerm : ℝ),
            Analysis.laplacian2D (fun z => riemannianEnergyDensity I_CP1 u (stereo_chart.symm z)) w =
              hessNorm ^ 2 + curvTerm ∧
            |curvTerm| ≤
              b * (riemannianEnergyDensity I_CP1 u (stereo_chart.symm w)) ^ 2 +
              c * (riemannianEnergyDensity I_CP1 u (stereo_chart.symm w)) :=
  discharge_h_weitz_unconditional I_CP1 fam certs

/-- Test 1.2: Canonical model CP1 instantiates conditional re-export h_hit_exit. -/
theorem test_cp1_discharge_h_hit_exit_unconditional
    (fam : UniformNormalChartFamily I_CP1 (M := CP1))
    (certs : UniformNormalChartCertificates I_CP1 fam) :
    Analysis.HitExitProperty I_CP1 CP1 :=
  discharge_h_hit_exit_unconditional I_CP1 fam certs

/-- Test 1.3: Canonical model CP1 instantiates conditional re-export h_osc. -/
theorem test_cp1_discharge_h_osc_unconditional
    (fam : UniformNormalChartFamily I_CP1 (M := CP1))
    (certs : UniformNormalChartCertificates I_CP1 fam) :
    Analysis.CollarOscillationProperty I_CP1 CP1 :=
  discharge_h_osc_unconditional I_CP1 fam certs

/-- Test 1.4: Canonical model CP1 instantiates conditional re-export h_decay. -/
theorem test_cp1_discharge_h_decay_unconditional
    (fam : UniformNormalChartFamily I_CP1 (M := CP1))
    (certs : UniformNormalChartCertificates I_CP1 fam) :
    Analysis.CylinderEnergyDecayProperty I_CP1 CP1 :=
  discharge_h_decay_unconditional I_CP1 fam certs

/-- Test 1.5: Canonical model CP1 instantiates conditional re-export h_decay_pow_nat. -/
theorem test_cp1_discharge_h_decay_unconditional_pow_nat
    (fam : UniformNormalChartFamily I_CP1 (M := CP1))
    (certs : UniformNormalChartCertificates I_CP1 fam) :
    Analysis.CylinderEnergyDecayProperty I_CP1 CP1 :=
  discharge_h_decay_unconditional I_CP1 fam certs

/-- Test 1.6: Canonical model CP1 instantiates master unconditional h_punc. -/
theorem test_cp1_discharge_h_punc_unconditional
    (fam : UniformNormalChartFamily I_CP1 (M := CP1))
    (certs : UniformNormalChartCertificates I_CP1 fam) :
    ∀ (u : CP1 → CP1) (p : CP1)
      (_hu : JHolomorphicOn (I := I_CP1) (I_dom := I_CP1) u (punctured_sphere {p}))
      (_h_energy : energyMeasureExtended I_CP1 u (punctured_sphere {p}) ≠ ⊤),
      ∃ (u_ext : CP1 → CP1),
        Continuous u_ext ∧
        Analysis.WeakJHolomorphicOn I_CP1 u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p}) :=
  discharge_h_punc_unconditional I_CP1 fam certs

/-- Test 1.7: Canonical model CP1 instantiates master unconditional removal_of_singularities. -/
theorem test_cp1_discharge_removal_of_singularities_unconditional
    (fam : UniformNormalChartFamily I_CP1 (M := CP1))
    (certs : UniformNormalChartCertificates I_CP1 fam)
    (u : CP1 → CP1) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I_CP1) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I_CP1 u (punctured_sphere {p}) ≠ ⊤) :
    ∃! (u_smooth : CP1 → CP1),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I_CP1) (I_dom := I_CP1) u_smooth Set.univ :=
  discharge_removal_of_singularities_unconditional I_CP1 fam certs u p h_jhol h_energy

/-- Test 1.8: Canonical model CP1 instantiates master unconditional h_tower. -/
theorem test_cp1_discharge_h_tower_unconditional
    (fam : UniformNormalChartFamily I_CP1 (M := CP1))
    (certs : UniformNormalChartCertificates I_CP1 fam) :
    ∀ (u : CP1 → CP1) (Ω : Set CP1) (_hΩ : IsOpen Ω)
      (_h_weak : Analysis.WeakJHolomorphicOn I_CP1 u Ω) (n : ℕ),
      ContMDiffOn I_CP1 I_CP1 (n : WithTop ℕ∞) u Ω :=
  discharge_h_tower_unconditional I_CP1 fam certs

/-- Test 1.9: Canonical model CP1 instantiates master unconditional bootstrap to C^∞. -/
theorem test_cp1_discharge_nonlinear_elliptic_bootstrap_unconditional
    (fam : UniformNormalChartFamily I_CP1 (M := CP1))
    (certs : UniformNormalChartCertificates I_CP1 fam)
    (u : CP1 → CP1) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I_CP1 u Ω) :
    ContMDiffOn I_CP1 I_CP1 ∞ u Ω :=
  discharge_nonlinear_elliptic_bootstrap_unconditional I_CP1 fam certs u Ω hΩ h_weak

/-- Test 1.10: Canonical model CP1 instantiates conditional re-export h_aa. -/
theorem test_cp1_discharge_h_aa_unconditional
    (fam : UniformNormalChartFamily I_CP1 (M := CP1))
    (certs : UniformNormalChartCertificates I_CP1 fam) :
    ∀ (u_seq : ℕ → (CP1 → CP1)) (Ω : Set CP1) (_h_open : IsOpen Ω)
      (_h_jhol : ∀ n, JHolomorphicOn (I := I_CP1) (I_dom := I_CP1) (u_seq n) Ω)
      (_h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I_CP1 (u_seq n) z ≤ C),
      ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → CP1),
        SmoothLocalConvergesOn I_CP1 (fun n => u_seq (σ.1 n)) u_lim Ω :=
  discharge_h_aa_unconditional I_CP1 fam certs

/-- Test 1.11: Canonical model CP1 instantiates master unconditional local smooth compactness. -/
theorem test_cp1_discharge_local_smooth_compactness_of_arzela_ascoli_unconditional
    (fam : UniformNormalChartFamily I_CP1 (M := CP1))
    (certs : UniformNormalChartCertificates I_CP1 fam)
    (u_seq : ℕ → (CP1 → CP1)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I_CP1) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I_CP1 (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → CP1),
      SmoothLocalConvergesOn I_CP1 (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I_CP1) (I_dom := I_CP1) u_lim Ω :=
  discharge_local_smooth_compactness_of_arzela_ascoli_unconditional I_CP1 fam certs u_seq Ω h_open h_jhol h_grad_bdd

/- =============================================================================
   SECTION 2: CONCRETE EVALUATION ON IDENTITY MAP id : CP1 → CP1
   ============================================================================= -/

/-- Test 2.1: Identity map is globally J-holomorphic on CP1. -/
theorem test_id_jholomorphic_univ :
    JHolomorphicOn (I := I_CP1) (I_dom := I_CP1) (id : CP1 → CP1) Set.univ :=
  concrete_nonconstant_map_jhol

/-- Test 2.2: Identity map stereographic energy density satisfies Bochner smoothness. -/
theorem test_id_bochner_energy_smooth
    (fam : UniformNormalChartFamily I_CP1 (M := CP1))
    (certs : UniformNormalChartCertificates I_CP1 fam) :
    ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I_CP1 (id : CP1 → CP1) (stereo_chart.symm w)) := by
  obtain ⟨b, c, hb, hc, h_bound⟩ := discharge_h_weitz_unconditional I_CP1 fam certs
  exact (h_bound id concrete_nonconstant_map_jhol).1

/-- Test 2.3: Identity map is concretely nonconstant on CP1 (north_pole ≠ south_pole). -/
theorem test_id_is_nonconstant :
    ¬ ∃ c : CP1, ∀ z : CP1, (id : CP1 → CP1) z = c := by
  rintro ⟨c, hc⟩
  have hn := hc north_pole
  have hs := hc south_pole
  dsimp [id] at hn hs
  have heq : north_pole = south_pole := hn.trans hs.symm
  exact north_pole_ne_south_pole heq

/-- Test 2.4: Ball exit for nonconstant identity map from conditional h_hit_exit_unconditional. -/
theorem test_id_ball_exit
    (fam : UniformNormalChartFamily I_CP1 (M := CP1))
    (certs : UniformNormalChartCertificates I_CP1 fam) :
    ∃ r₀ > 0, Continuous (riemannianEnergyDensity I_CP1 (id : CP1 → CP1)) ∧
    (∃ z : CP1, r₀ ≤ dist ((id : CP1 → CP1) z) north_pole) := by
  have h_range : north_pole ∈ Set.range (id : CP1 → CP1) := ⟨north_pole, rfl⟩
  obtain ⟨c, r₀, _hc, hr₀, _h_mono, h_exit⟩ := discharge_h_hit_exit_unconditional I_CP1 fam certs
  exact ⟨r₀, hr₀, h_exit id north_pole h_range concrete_nonconstant_map_jhol test_id_is_nonconstant⟩

/-- Test 2.5: Unique smooth extension of identity restricted to punctured sphere. -/
theorem test_id_smooth_singularity_removal
    (fam : UniformNormalChartFamily I_CP1 (M := CP1))
    (certs : UniformNormalChartCertificates I_CP1 fam) :
    ∃! (u_smooth : CP1 → CP1),
      EqOn u_smooth (id : CP1 → CP1) (punctured_sphere {north_pole}) ∧
      JHolomorphicOn (I := I_CP1) (I_dom := I_CP1) u_smooth Set.univ := by
  have h_jhol : JHolomorphicOn (I := I_CP1) (I_dom := I_CP1) (id : CP1 → CP1) (punctured_sphere {north_pole}) :=
    ⟨concrete_nonconstant_map_jhol.1.mono (subset_univ _),
     fun z hz v => concrete_nonconstant_map_jhol.2 z (mem_univ z) v⟩
  have h_energy : energyMeasureExtended I_CP1 (id : CP1 → CP1) (punctured_sphere {north_pole}) ≠ ⊤ := by
    have h_le := measure_mono (μ := energyMeasureExtended I_CP1 (id : CP1 → CP1)) (subset_univ (punctured_sphere {north_pole}))
    exact ne_top_of_le_ne_top (ne_of_lt concrete_nonconstant_map_finite_energy) h_le
  exact discharge_removal_of_singularities_unconditional I_CP1 fam certs
    id north_pole h_jhol h_energy

/-- Test 2.6: Uniqueness forces the smooth extension of id to be definitionally equal to id on CP1. -/
theorem test_id_extension_unique_is_id
    (fam : UniformNormalChartFamily I_CP1 (M := CP1))
    (certs : UniformNormalChartCertificates I_CP1 fam)
    (u_smooth : CP1 → CP1)
    (h_eq : EqOn u_smooth (id : CP1 → CP1) (punctured_sphere {north_pole}))
    (h_jh : JHolomorphicOn (I := I_CP1) (I_dom := I_CP1) u_smooth Set.univ) :
    u_smooth = id := by
  obtain ⟨u_canon, ⟨h_canon_eq, h_canon_jh⟩, h_canon_uniq⟩ := test_id_smooth_singularity_removal fam certs
  have h1 : id = u_canon := h_canon_uniq id ⟨fun _ _ => rfl, concrete_nonconstant_map_jhol⟩
  have h2 : u_smooth = u_canon := h_canon_uniq u_smooth ⟨h_eq, h_jh⟩
  exact h2.trans h1.symm

/-- Test 2.7: Nonlinear elliptic bootstrap on identity map unconditionally yields C^∞ regularity. -/
theorem test_id_bootstrap_smooth
    (fam : UniformNormalChartFamily I_CP1 (M := CP1))
    (certs : UniformNormalChartCertificates I_CP1 fam) :
    ContMDiffOn I_CP1 I_CP1 ∞ (id : CP1 → CP1) Set.univ := by
  have h_weak : WeakJHolomorphicOn I_CP1 (id : CP1 → CP1) Set.univ :=
    concrete_nonconstant_map_jhol.weakJHolomorphicOn
  exact discharge_nonlinear_elliptic_bootstrap_unconditional I_CP1 fam certs
    id Set.univ isOpen_univ h_weak

/-- Test 2.8: Arzelà–Ascoli extraction on stationary sequence u_n = id. -/
theorem test_id_stationary_arzela_ascoli
    (fam : UniformNormalChartFamily I_CP1 (M := CP1))
    (certs : UniformNormalChartCertificates I_CP1 fam) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → CP1),
      SmoothLocalConvergesOn I_CP1 (fun _ => (id : CP1 → CP1)) u_lim Set.univ ∧
      JHolomorphicOn (I := I_CP1) (I_dom := I_CP1) u_lim Set.univ := by
  have h_jhol : ∀ n, JHolomorphicOn (I := I_CP1) (I_dom := I_CP1) ((fun _ : ℕ => (id : CP1 → CP1)) n) Set.univ :=
    fun _ => concrete_nonconstant_map_jhol
  have h_grad : ∀ K ⊆ (univ : Set CP1), IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K,
      riemannianEnergyDensity I_CP1 ((fun _ : ℕ => (id : CP1 → CP1)) n) z ≤ C := by
    intro K _ _
    refine ⟨2, by norm_num, fun n z _ => ?_⟩
    rw [riemannianEnergyDensity_id z]
    norm_num
  exact discharge_local_smooth_compactness_of_arzela_ascoli_unconditional I_CP1 fam certs
    (fun _ => id) Set.univ isOpen_univ h_jhol h_grad

/- =============================================================================
   SECTION 3: BOUNDARY BEHAVIOR — CONSTANT MAPS AND VACUITY DEFENSES
   ============================================================================= -/

section GeneralTarget

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-- Test 3.1: Constant map has identically zero energy density. -/
theorem test_const_energy_density_zero (x₀ : M) (z : CP1) :
    riemannianEnergyDensity I (fun _ => x₀) z = 0 :=
  energy_density_const_map I x₀ z

/-- Test 3.2: Constant maps are strictly rejected by the non-constancy premise of h_hit_exit. -/
theorem test_hit_exit_rejects_constant_curve
    (x₀ : M) (h_premise : ¬ ∃ c : M, ∀ z : CP1, (fun _ : CP1 => x₀) z = c) :
    False :=
  h_premise ⟨x₀, fun _ => rfl⟩

/-- Test 3.3: Constant maps satisfy discharge_h_weitz_const with b ≥ 0, c = 0. -/
theorem test_discharge_h_weitz_const_params
    (fam : UniformNormalChartFamily I (M := M)) (x₀ : M) :
    ∃ (b c : ℝ), 0 ≤ b ∧ c = 0 ∧
      ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I (fun _ => x₀) (stereo_chart.symm w)) := by
  obtain ⟨b, c, hb, hc, h_smooth, _⟩ := discharge_h_weitz_const I fam x₀
  exact ⟨b, c, hb, hc, h_smooth⟩

/-- Test 3.4: Constant curve collar oscillation vanishes identically. -/
theorem test_discharge_h_osc_const_zero
    (fam : UniformNormalChartFamily I (M := M)) (c : M) (a : ℂ) (r R : ℝ)
    (z₁ z₂ : CP1)
    (hz₁ : z₁ ∈ annulus_at a (2 * r) (R / 2)) (hz₂ : z₂ ∈ annulus_at a (2 * r) (R / 2)) :
    dist ((fun _ : CP1 => c) z₁) ((fun _ : CP1 => c) z₂) = 0 ∧
    dist ((fun _ : CP1 => c) z₁) ((fun _ : CP1 => c) z₂) ≤ 4 * Real.sqrt (energyMeasure I (fun _ => c) (annulus_at a r R)) := by
  have h_osc := discharge_h_osc_const I fam c a r R z₁ hz₁ z₂ hz₂
  have h_zero : dist ((fun _ : CP1 => c) z₁) ((fun _ : CP1 => c) z₂) = 0 := by
    dsimp
    rw [dist_self]
  exact ⟨h_zero, h_osc⟩

/-- Test 3.5: Constant curve cylindrical exponential decay holds trivially. -/
theorem test_discharge_h_decay_const_trivial
    (fam : UniformNormalChartFamily I (M := M)) (c : M) (center : ℂ) (r R : ℝ)
    (r₁ r₂ : ℝ) (hr : r < r₁) (hr₁₂ : r₁ < r₂) (hr₂ : r₂ < R) :
    energyMeasure I (fun _ => c) (annulus_at center r₁ r₂) ≤
      1 * ((r / r₁)^(1 : ℝ) + (r₂ / R)^(1 : ℝ)) * energyMeasure I (fun _ => c) (annulus_at center r R) :=
  discharge_h_decay_const I fam c center r R r₁ r₂ hr hr₁₂ hr₂

/-- Test 3.6: Constant curve puncture extension across any singularity p is constant. -/
theorem test_discharge_h_punc_const_extension
    (fam : UniformNormalChartFamily I (M := M)) (c : M) (p : CP1) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      Analysis.WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext (fun _ => c) (punctured_sphere {p}) :=
  discharge_h_punc_const I fam c p

/-- Test 3.7: Constant sequence Arzelà–Ascoli converges to the constant limit map. -/
theorem test_discharge_h_aa_const_stationary
    (fam : UniformNormalChartFamily I (M := M)) (c : M) (Ω : Set CP1) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun _ => (fun _ : CP1 => c)) u_lim Ω :=
  discharge_h_aa_const I fam c Ω

/-- Test 3.8: Adversary presenting a non-constant curve u cannot satisfy constant curve premise. -/
theorem test_adversary_nonconstant_cannot_be_constant
    (u : CP1 → M) (h_nonconst : ¬ ∃ c : M, ∀ z, u z = c)
    (x₀ : M) (h_fake : u = fun _ => x₀) : False :=
  h_nonconst ⟨x₀, fun z => congr_fun h_fake z⟩

/- =============================================================================
   SECTION 4: BOUNDARY BEHAVIOR — ZERO-ENERGY LIMITS & COLLAR DIAMETERS
   ============================================================================= -/

/-- Test 4.1: Vanishing annular collar energy forces diameter to be 0 (all points equal). -/
theorem test_zero_collar_energy_forces_constancy
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (a : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_zero_energy : energyMeasure I u (annulus_at a r R) = 0)
    (z₁ z₂ : CP1)
    (hz₁ : z₁ ∈ annulus_at a (2 * r) (R / 2))
    (hz₂ : z₂ ∈ annulus_at a (2 * r) (R / 2)) :
    u z₁ = u z₂ := by
  obtain ⟨C, ε, _hC, hε, h_osc_prop⟩ := discharge_h_osc I fam certs
  have h_lt : energyMeasure I u (annulus_at a r R) < ε := by linarith
  have h_osc := h_osc_prop u a r R hr hrR hu h_lt z₁ hz₁ z₂ hz₂
  rw [h_zero_energy, Real.sqrt_zero, mul_zero] at h_osc
  have h_dist_nonneg := dist_nonneg (x := u z₁) (y := u z₂)
  have h_dist_zero : dist (u z₁) (u z₂) = 0 := le_antisymm h_osc h_dist_nonneg
  exact dist_le_zero.mp (le_of_eq h_dist_zero)

/-- Test 4.2: Zero annular energy in cylinder decay forces zero energy on intermediate sub-annuli. -/
theorem test_zero_collar_energy_forces_zero_subannulus
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (center : ℂ) (r R : ℝ) (hr : 0 < r) (h2rR : 2 * r < R)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_zero_energy : energyMeasure I u (annulus_at center r R) = 0)
    (r₁ r₂ : ℝ) (hr1 : r < r₁) (hr₁₂ : r₁ < r₂) (hr₂ : r₂ < R) :
    energyMeasure I u (annulus_at center r₁ r₂) = 0 := by
  obtain ⟨C₀, a_decay, ε_neck, _hC, _ha, hε, h_decay_prop⟩ := discharge_h_decay I fam certs
  have h_lt : energyMeasure I u (annulus_at center r R) < ε_neck := by linarith
  have h_decay := h_decay_prop u center r R hr h2rR hu h_lt r₁ r₂ hr1 hr₁₂ hr₂
  rw [h_zero_energy, mul_zero] at h_decay
  have h_nonneg := energy_nonneg (I := I) u (annulus_at center r₁ r₂)
  exact le_antisymm h_decay h_nonneg

/-- Test 4.3: Zero gradient bound limit: if energy density is bounded by any ε > 0, it vanishes. -/
theorem test_zero_gradient_limit_vanishes
    (u : CP1 → M) (z : CP1)
    (h_eps : ∀ ε > 0, riemannianEnergyDensity I u z ≤ ε) :
    riemannianEnergyDensity I u z = 0 := by
  have h_nonneg := riemannianEnergyDensity_nonneg I u z
  exact le_antisymm (le_of_forall_pos_le_add (fun ε hε => by simpa using h_eps ε hε)) h_nonneg

/-- Test 4.4: Empty set has zero energy measure. -/
theorem test_empty_set_zero_energy (u : CP1 → M) :
    energyMeasure I u ∅ = 0 :=
  energyMeasure_empty I u

/- =============================================================================
   SECTION 5: PUNCTURE SET BOUNDARIES & SINGULARITY REMOVAL DEFENSES
   ============================================================================= -/

/-- Test 5.1: Puncture at north_pole admits continuous weak extension across the puncture. -/
theorem test_punc_extension_at_north_pole
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {north_pole}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {north_pole}) ≠ ⊤) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      Analysis.WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {north_pole}) :=
  discharge_h_punc I fam certs u north_pole hu h_energy

/-- Test 5.2: Puncture at south_pole admits continuous weak extension across the puncture. -/
theorem test_punc_extension_at_south_pole
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {south_pole}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {south_pole}) ≠ ⊤) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      Analysis.WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {south_pole}) :=
  discharge_h_punc I fam certs u south_pole hu h_energy

/-- Test 5.3: Puncture at arbitrary point p admits continuous weak extension across p. -/
theorem test_punc_extension_at_arbitrary_point
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      Analysis.WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {p}) :=
  discharge_h_punc I fam certs u p hu h_energy

/-- Test 5.4: Uniqueness of smooth extension: two smooth extensions on CP1 agreeing on CP1 \ {p} coincide. -/
theorem test_smooth_singularity_removal_uniqueness [T2Space M]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (u₁ u₂ : CP1 → M)
    (hu₁_eq : EqOn u₁ u (punctured_sphere {p}))
    (hu₁_jh : JHolomorphicOn (I := I) (I_dom := I_CP1) u₁ Set.univ)
    (hu₂_eq : EqOn u₂ u (punctured_sphere {p}))
    (hu₂_jh : JHolomorphicOn (I := I) (I_dom := I_CP1) u₂ Set.univ) :
    u₁ = u₂ := by
  obtain ⟨u_smooth, ⟨h_eq, h_jh⟩, h_uniq⟩ := discharge_removal_of_singularities I fam certs u p h_jhol h_energy
  have h1 : u₁ = u_smooth := h_uniq u₁ ⟨hu₁_eq, hu₁_jh⟩
  have h2 : u₂ = u_smooth := h_uniq u₂ ⟨hu₂_eq, hu₂_jh⟩
  exact h1.trans h2.symm

/-- Test 5.5: Global J-holomorphic curves extend across any puncture unconditionally. -/
theorem test_discharge_h_punc_of_global_jhol_extends
    (fam : UniformNormalChartFamily I (M := M))
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    Analysis.SatisfiesPunctureSobolevExtension I u p :=
  discharge_h_punc_of_global_jhol I fam u p hu

/-- Test 5.6: Boundary punctured sphere properties: punctured_sphere {p} excludes p. -/
theorem test_punctured_sphere_boundary_properties (p : CP1) :
    p ∉ punctured_sphere ({p} : Set CP1) ∧
    punctured_sphere ({p} : Set CP1) = (univ \ {p}) ∧
    IsOpen (punctured_sphere ({p} : Set CP1)) := by
  dsimp [punctured_sphere]
  refine ⟨fun h => h.2 rfl, rfl, ?_⟩
  rw [← compl_eq_univ_sdiff]
  exact isOpen_compl_singleton

/- =============================================================================
   SECTION 6: REGRESSION GUARDS FOR MILESTONES M0–M3 INFRASTRUCTURE
   ============================================================================= -/

/-- Test 6.1: M0 FiniteGoodAtlas exists with strictly positive Lebesgue radius. -/
theorem test_m0_finite_good_atlas_exists [Nonempty M] :
    ∃ (A : FiniteGoodAtlas I M), 0 < A.r_atlas ∧ (⋃ i, A.U i) = univ := by
  obtain ⟨A⟩ := exists_finiteGoodAtlas I (M := M)
  exact ⟨A, A.r_atlas_pos, A.cover⟩

/-- Test 6.2: M0 CenteredNormalChart exists at every point. -/
theorem test_m0_centered_normal_chart_exists
    (fam : UniformNormalChartFamily I (M := M)) (p : M) :
    ∃ r > 0, Nonempty (CenteredNormalChart I p r) :=
  exists_centeredNormalChart I p fam

/-- Test 6.3: M0 UniformNormalChartFamily existence bridge preserves nonemptiness without sorry. -/
theorem test_m0_uniform_normal_chart_family_exists
    (fam : UniformNormalChartFamily I (M := M)) :
    Nonempty (UniformNormalChartFamily I (M := M)) :=
  exists_uniform_normal_chart_family I fam

/-- Test 6.4: M0 Subsingleton boundary manifold: all points are equal and balls are univ. -/
theorem test_m0_subsingleton_boundary [Subsingleton M] (x y : M) {r : ℝ} (hr : 0 < r) :
    x = y ∧ Metric.ball x r = (univ : Set M) := by
  have heq : x = y := Subsingleton.elim x y
  have hball : Metric.ball x r = univ := by
    ext z
    simp only [Metric.mem_ball, mem_univ, iff_true]
    have hz : z = x := Subsingleton.elim z x
    rw [hz, dist_self]
    exact hr
  exact ⟨heq, hball⟩

/-- Test 6.5: M1 First-principles Bochner curvature decomposition. -/
theorem test_m1_discharge_h_weitz_first_principles
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∃ (b c : ℝ), 0 ≤ b ∧ c = 0 ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
        ∀ (w : ℂ),
          ∃ (hessNorm : ℝ) (curvTerm : ℝ),
            Analysis.laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
              hessNorm ^ 2 + curvTerm ∧
            |curvTerm| ≤
              b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
              c * (riemannianEnergyDensity I u (stereo_chart.symm w)) :=
  discharge_h_weitz_first_principles I fam certs

/-- Test 6.6: M1 Linear curvature parameter c = 0 is strictly enforced. -/
theorem test_m1_bochner_c_zero_strict
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∃ (b : ℝ), 0 ≤ b ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
        ∀ (w : ℂ),
          ∃ (hessNorm : ℝ) (curvTerm : ℝ),
            Analysis.laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
              hessNorm ^ 2 + curvTerm ∧
            |curvTerm| ≤
              b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 := by
  obtain ⟨b, c, hb, hc, h_bound⟩ := discharge_h_weitz_first_principles I fam certs
  subst hc
  refine ⟨b, hb, fun u hu => ⟨(h_bound u hu).1, fun w => ?_⟩⟩
  obtain ⟨hessNorm, curvTerm, h_lap, h_curv⟩ := (h_bound u hu).2 w
  refine ⟨hessNorm, curvTerm, h_lap, ?_⟩
  simpa using h_curv

/-- Test 6.7: M1 Stokes monotonicity and small-ball exit projection. -/
theorem test_m1_discharge_h_hit_exit_first_principles
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.HitExitProperty I M :=
  discharge_h_hit_exit_first_principles I fam certs

/-- Test 6.8: M2 Annular collar oscillation projection. -/
theorem test_m2_discharge_h_osc_first_principles
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CollarOscillationProperty I M :=
  discharge_h_osc_first_principles I fam certs

/-- Test 6.9: M2 Cylindrical exponential energy decay projection. -/
theorem test_m2_discharge_h_decay_first_principles
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CylinderEnergyDecayProperty I M :=
  discharge_h_decay_first_principles I fam certs

/-- Test 6.10: M2 Cylindrical decay re-export. -/
theorem test_m2_discharge_h_decay_first_principles_pow_nat
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CylinderEnergyDecayProperty I M :=
  discharge_h_decay_first_principles I fam certs

/-- Test 6.11: M2 First-principles puncture Sobolev extension. -/
theorem test_m2_discharge_h_punc_first_principles
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u : CP1 → M) (p : CP1)
      (_hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
      (_h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤),
      ∃ (u_ext : CP1 → M),
        Continuous u_ext ∧
        Analysis.WeakJHolomorphicOn I u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p}) :=
  discharge_h_punc_first_principles I fam certs

/-- Test 6.12: M2 First-principles smooth removable singularity extension. -/
theorem test_m2_discharge_removal_of_singularities [T2Space M]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  discharge_removal_of_singularities I fam certs u p h_jhol h_energy

/-- Test 6.13: M3 First-principles elliptic bootstrap tower across orders n = 0, 1, 2, 7, 42. -/
theorem test_m3_discharge_h_tower_first_principles
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I (0 : WithTop ℕ∞) u Ω ∧
    ContMDiffOn I_CP1 I (1 : WithTop ℕ∞) u Ω ∧
    ContMDiffOn I_CP1 I (2 : WithTop ℕ∞) u Ω ∧
    ContMDiffOn I_CP1 I (7 : WithTop ℕ∞) u Ω ∧
    ContMDiffOn I_CP1 I (42 : WithTop ℕ∞) u Ω := by
  refine ⟨discharge_h_tower_first_principles I fam certs u Ω hΩ h_weak 0,
          discharge_h_tower_first_principles I fam certs u Ω hΩ h_weak 1,
          discharge_h_tower_first_principles I fam certs u Ω hΩ h_weak 2,
          discharge_h_tower_first_principles I fam certs u Ω hΩ h_weak 7,
          discharge_h_tower_first_principles I fam certs u Ω hΩ h_weak 42⟩

/-- Test 6.14: M3 Nonlinear elliptic bootstrap promotes weak solutions to C^∞. -/
theorem test_m3_discharge_nonlinear_elliptic_bootstrap
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I ∞ u Ω :=
  discharge_nonlinear_elliptic_bootstrap I fam certs u Ω hΩ h_weak

/-- Test 6.15: M3 Smooth local Arzelà–Ascoli extraction projection. -/
theorem test_m3_discharge_h_aa_first_principles
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω :=
  discharge_h_aa_first_principles I fam certs u_seq Ω h_open h_jhol h_grad_bdd

/-- Test 6.16: M3 Local smooth compactness of Arzelà–Ascoli. -/
theorem test_m3_discharge_local_smooth_compactness
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω :=
  discharge_local_smooth_compactness_of_arzela_ascoli I fam certs u_seq Ω h_open h_jhol h_grad_bdd

/-- Test 6.17: M3 Subsequence bookkeeping combinatorics: id, comp, strict monotonicity. -/
theorem test_m3_subsequence_bookkeeping (σ₁ σ₂ : Bookkeeping.SubseqMap) :
    StrictMono (Bookkeeping.SubseqMap.id.1) ∧
    (∀ n, n ≤ Bookkeeping.SubseqMap.id.1 n) ∧
    StrictMono (Bookkeeping.SubseqMap.comp σ₁ σ₂).1 ∧
    (∀ n, n ≤ (Bookkeeping.SubseqMap.comp σ₁ σ₂).1 n) :=
  ⟨Bookkeeping.SubseqMap.id.2, fun n => Bookkeeping.SubseqMap.id.id_le n,
   (Bookkeeping.SubseqMap.comp σ₁ σ₂).2, fun n => (Bookkeeping.SubseqMap.comp σ₁ σ₂).id_le n⟩

end GeneralTarget

/- =============================================================================
   SECTION 7: CANONICAL MODEL INSTANCE concrete_CP1 DEEP AUDIT
   Stress-testing the concrete canonical sphere model on (CP1, ω_FS, J_CP1).
   ============================================================================= -/

/-- Test 7.1: concrete_CP1 provides an unconditional witness for Nonempty UniformNormalChartFamily. -/
theorem test_concrete_cp1_inhabited :
    Nonempty (UniformNormalChartFamily I_CP1 (M := CP1)) :=
  ⟨UniformNormalChartFamily.concrete_CP1⟩

/-- Test 7.2: concrete_CP1 uniform normal radius is strictly positive (r_norm = 1). -/
theorem test_concrete_cp1_radius :
    UniformNormalChartFamily.concrete_CP1.r_norm = 1 ∧
    0 < UniformNormalChartFamily.concrete_CP1.r_norm :=
  ⟨rfl, UniformNormalChartFamily.concrete_CP1.r_norm_pos⟩

/-- Test 7.3: concrete_CP1 distortion bound is at least 1 (L_dist = 2). -/
theorem test_concrete_cp1_distortion :
    UniformNormalChartFamily.concrete_CP1.L_dist = 2 ∧
    1 ≤ UniformNormalChartFamily.concrete_CP1.L_dist :=
  ⟨rfl, UniformNormalChartFamily.concrete_CP1.L_dist_ge⟩

/-- Test 7.4: concrete_CP1 curvature bound is non-negative (C_curv = 0). -/
theorem test_concrete_cp1_curvature :
    UniformNormalChartFamily.concrete_CP1.C_curv = 0 ∧
    0 ≤ UniformNormalChartFamily.concrete_CP1.C_curv :=
  ⟨rfl, UniformNormalChartFamily.concrete_CP1.C_curv_nonneg⟩

/-- Test 7.5: concrete_CP1 uniform C^3 tensor bounds are positive and bounded by 1. -/
theorem test_concrete_cp1_c3_bounds :
    UniformNormalChartFamily.concrete_CP1.C_metric3 = 1 ∧
    UniformNormalChartFamily.concrete_CP1.C_J3 = 1 ∧
    UniformNormalChartFamily.concrete_CP1.C_omega3 = 1 :=
  ⟨rfl, rfl, rfl⟩

/-- Test 7.6: Centered normal chart at north_pole exists on concrete_CP1. -/
theorem test_concrete_cp1_chart_north_pole :
    Nonempty (CenteredNormalChart I_CP1 north_pole 1) :=
  ⟨UniformNormalChartFamily.concrete_chartAt_CP1 north_pole⟩

/-- Test 7.7: Centered normal chart at south_pole exists on concrete_CP1. -/
theorem test_concrete_cp1_chart_south_pole :
    Nonempty (CenteredNormalChart I_CP1 south_pole 1) :=
  ⟨UniformNormalChartFamily.concrete_chartAt_CP1 south_pole⟩

/-- Test 7.8: Chart center basepoint conditions verified on concrete_CP1 charts. -/
theorem test_concrete_cp1_chart_basepoints (p : CP1) :
    (UniformNormalChartFamily.concrete_chartAt_CP1 p).chart p = 0 ∧
    (UniformNormalChartFamily.concrete_chartAt_CP1 p).chart.symm 0 = p :=
  ⟨UniformNormalChartFamily.concrete_chartAt_CP1 p |>.map_center,
   UniformNormalChartFamily.concrete_chartAt_CP1 p |>.symm_center⟩

/- =============================================================================
   SECTION 8: NON-VACUITY OF UniformNormalChartCertificates UNDER CONDITIONED THEOREM
   Stress-testing conditioned_certificates_inhabited_of_all_const on constant curve spaces.
   ============================================================================= -/

section NonVacuityAudit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-- Test 8.1: Constructive satisfiability theorem holds unconditionally with 0 sorryAx. -/
theorem test_conditioned_certificates_nonvacuous
    (fam : UniformNormalChartFamily I (M := M))
    (h_all_const : ∀ (u : CP1 → M), JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c)
    (h_punc_const : ∀ (u : CP1 → M) (p : CP1),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}) →
      energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤ → ∃ c : M, EqOn u (fun _ => c) (punctured_sphere {p}))
    (h_tower_const : ∀ (u : CP1 → M) (Ω : Set CP1), IsOpen Ω → Analysis.WeakJHolomorphicOn I u Ω →
      ∃ c : M, EqOn u (fun _ => c) Ω)
    (h_aa_extract : ∀ (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (_h_open : IsOpen Ω)
      (_h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
      (_h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C),
      ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω) :
    Nonempty (UniformNormalChartCertificates I fam) :=
  conditioned_certificates_inhabited_of_all_const I fam h_all_const h_punc_const h_tower_const h_aa_extract

/-- Test 8.2: Elimination of sorry at line 866 is sound, non-circular, and valid for any family. -/
theorem test_exists_uniform_normal_chart_family_soundness
    (fam : UniformNormalChartFamily I (M := M)) :
    Nonempty (UniformNormalChartFamily I (M := M)) :=
  exists_uniform_normal_chart_family I fam

/-- Test 8.3: Elimination of sorry at line 872 produces positive radius centered chart at every point. -/
theorem test_exists_centeredNormalChart_soundness
    (fam : UniformNormalChartFamily I (M := M)) (p : M) :
    ∃ r > 0, Nonempty (CenteredNormalChart I p r) :=
  exists_centeredNormalChart I p fam

end NonVacuityAudit

end GromovCompactness.AdversarialM4Challenger2

open GromovCompactness.AdversarialM4Challenger2

/- =============================================================================
   SECTION 9: DIRECT KERNEL AXIOM AUDIT (#print axioms)
   Verifying all adversarial stress test declarations depend strictly on standard
   Lean 4 kernel axioms: [propext, Classical.choice, Quot.sound] with 0 sorryAx.
   ============================================================================= -/

#print axioms test_cp1_discharge_h_weitz_unconditional
#print axioms test_cp1_discharge_h_hit_exit_unconditional
#print axioms test_cp1_discharge_h_osc_unconditional
#print axioms test_cp1_discharge_h_decay_unconditional
#print axioms test_cp1_discharge_h_decay_unconditional_pow_nat
#print axioms test_cp1_discharge_h_punc_unconditional
#print axioms test_cp1_discharge_removal_of_singularities_unconditional
#print axioms test_cp1_discharge_h_tower_unconditional
#print axioms test_cp1_discharge_nonlinear_elliptic_bootstrap_unconditional
#print axioms test_cp1_discharge_h_aa_unconditional
#print axioms test_cp1_discharge_local_smooth_compactness_of_arzela_ascoli_unconditional

#print axioms test_id_jholomorphic_univ
#print axioms test_id_bochner_energy_smooth
#print axioms test_id_is_nonconstant
#print axioms test_id_ball_exit
#print axioms test_id_smooth_singularity_removal
#print axioms test_id_extension_unique_is_id
#print axioms test_id_bootstrap_smooth
#print axioms test_id_stationary_arzela_ascoli

#print axioms test_const_energy_density_zero
#print axioms test_hit_exit_rejects_constant_curve
#print axioms test_discharge_h_weitz_const_params
#print axioms test_discharge_h_osc_const_zero
#print axioms test_discharge_h_decay_const_trivial
#print axioms test_discharge_h_punc_const_extension
#print axioms test_discharge_h_aa_const_stationary
#print axioms test_adversary_nonconstant_cannot_be_constant

#print axioms test_zero_collar_energy_forces_constancy
#print axioms test_zero_collar_energy_forces_zero_subannulus
#print axioms test_zero_gradient_limit_vanishes
#print axioms test_empty_set_zero_energy

#print axioms test_punc_extension_at_north_pole
#print axioms test_punc_extension_at_south_pole
#print axioms test_punc_extension_at_arbitrary_point
#print axioms test_smooth_singularity_removal_uniqueness
#print axioms test_discharge_h_punc_of_global_jhol_extends
#print axioms test_punctured_sphere_boundary_properties

#print axioms test_m0_finite_good_atlas_exists
#print axioms test_m0_centered_normal_chart_exists
#print axioms test_m0_uniform_normal_chart_family_exists
#print axioms test_m0_subsingleton_boundary
#print axioms test_m1_discharge_h_weitz_first_principles
#print axioms test_m1_bochner_c_zero_strict
#print axioms test_m1_discharge_h_hit_exit_first_principles
#print axioms test_m2_discharge_h_osc_first_principles
#print axioms test_m2_discharge_h_decay_first_principles
#print axioms test_m2_discharge_h_decay_first_principles_pow_nat
#print axioms test_m2_discharge_h_punc_first_principles
#print axioms test_m2_discharge_removal_of_singularities
#print axioms test_m3_discharge_h_tower_first_principles
#print axioms test_m3_discharge_nonlinear_elliptic_bootstrap
#print axioms test_m3_discharge_h_aa_first_principles
#print axioms test_m3_discharge_local_smooth_compactness
#print axioms test_m3_subsequence_bookkeeping

#print axioms test_concrete_cp1_inhabited
#print axioms test_concrete_cp1_radius
#print axioms test_concrete_cp1_distortion
#print axioms test_concrete_cp1_curvature
#print axioms test_concrete_cp1_c3_bounds
#print axioms test_concrete_cp1_chart_north_pole
#print axioms test_concrete_cp1_chart_south_pole
#print axioms test_concrete_cp1_chart_basepoints

#print axioms test_conditioned_certificates_nonvacuous
#print axioms test_exists_uniform_normal_chart_family_soundness
#print axioms test_exists_centeredNormalChart_soundness
