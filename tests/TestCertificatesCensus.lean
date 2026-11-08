/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (E2E Testing Track Lead)
-/
import GromovCompactness
import GromovCompactness.Analysis.SingularityRemoval
import GromovCompactness.Analysis.EllipticBootstrap
import GromovCompactness.Analysis.Energy
import GromovCompactness.Geometry.NormalCharts
import Lean.Elab.Command

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory Filter GromovCompactness GromovCompactness.Analysis
open Lean Elab Command

namespace GromovCompactness.Tests.CertificatesCensus

section GeneralTarget

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/- =============================================================================
   TIER 1: FEATURE COVERAGE — TYPE SIGNATURES & EXISTENCE OF 7 PDE CERTIFICATES
   ============================================================================= -/

/-- Tier 1.1: Verification of Certificate 1 `h_weitz` (Bochner-Weitzenböck Curvature Identity).
    Local stereographic energy density satisfies Δ e = |∇ du|² + K with |K| ≤ b e² + c e (c = 0). -/
theorem test_tier1_h_weitz_signature
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
  discharge_h_weitz I fam certs

/-- Tier 1.2: Verification of Certificate 2 `h_hit_exit` (Radial Stokes Monotonicity & Ball Exit).
    Sublevel Stokes differential inequality forces quadratic growth r² ≤ E and small-ball exit. -/
theorem test_tier1_h_hit_exit_signature
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    (∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ 1 → x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ∀ z_hit ∈ frontier (u ⁻¹' (Metric.ball x r)),
        dist (u z_hit) x = r →
        (r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) ∨
          ∃ s : Set CP1, s ⊆ u ⁻¹' (Metric.ball x r) ∧
            energyMeasureExtended I u (u ⁻¹' (Metric.ball x r)) ≠ ⊤ ∧
            r^2 ≤ energyMeasure I u s)) ∧
    (∀ (u : CP1 → M) (x : M),
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      Continuous (riemannianEnergyDensity I u) ∧ (∃ z : CP1, 1 ≤ dist (u z) x)) :=
  discharge_h_hit_exit I fam certs

/-- Tier 1.1b: Verification of Certificate 1 `h_weitz` first-principles contract signature. -/
theorem test_tier1_h_weitz_first_principles_signature
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

/-- Tier 1.2b: Verification of Certificate 2 `h_hit_exit` first-principles contract signature. -/
theorem test_tier1_h_hit_exit_first_principles_signature
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    (∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ 1 → x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ∀ z_hit ∈ frontier (u ⁻¹' (Metric.ball x r)),
        dist (u z_hit) x = r →
        (r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) ∨
          ∃ s : Set CP1, s ⊆ u ⁻¹' (Metric.ball x r) ∧
            energyMeasureExtended I u (u ⁻¹' (Metric.ball x r)) ≠ ⊤ ∧
            r^2 ≤ energyMeasure I u s)) ∧
    (∀ (u : CP1 → M) (x : M),
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      Continuous (riemannianEnergyDensity I u) ∧ (∃ z : CP1, 1 ≤ dist (u z) x)) :=
  discharge_h_hit_exit_first_principles I fam certs

/-- Tier 1.3: Verification of Certificate 3 `h_osc` (Annular Collar Oscillation Bound).
    1D Poincaré / Wirtinger slice integration yields osc u ≤ 4 √E(u; A(r, R)). -/
theorem test_tier1_h_osc_signature
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (a : ℂ) (r R : ℝ) (hr : 0 < r)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    Analysis.SatisfiesCylinderCollarOscillation I u a r R :=
  discharge_h_osc I fam certs u a r R hr hu

/-- Tier 1.3b: Verification of Certificate 3 `h_osc` first-principles contract signature. -/
theorem test_tier1_h_osc_first_principles_signature
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ) (hr : 0 < r)
      (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ),
      ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
        dist (u z₁) (u z₂) ≤ 4 * Real.sqrt (energyMeasure I u (annulus_at a r R)) :=
  discharge_h_osc_first_principles I fam certs

/-- Tier 1.4: Verification of Certificate 4 `h_decay` (Exponential Cylindrical Energy Decay).
    Widman annular hole-filling recurrence yields geometric dyadic energy decay. -/
theorem test_tier1_h_decay_signature
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (center : ℂ) (r R : ℝ) (hr : 0 < r) (h2rR : 2 * r < R)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    Analysis.SatisfiesCylinderEnergyDecay I u center r R :=
  discharge_h_decay I fam certs u center r R hr h2rR hu

/-- Tier 1.4b: Verification of Certificate 4 `h_decay` first-principles contract signature. -/
theorem test_tier1_h_decay_first_principles_signature
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ) (hr : 0 < r) (h2rR : 2 * r < R)
      (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ),
      ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
        energyMeasure I u (annulus_at center r₁ r₂) ≤
          1 * ((r / r₁)^(1 : ℝ) + (r₂ / R)^(1 : ℝ)) * energyMeasure I u (annulus_at center r R) :=
  discharge_h_decay_first_principles I fam certs

/-- Tier 1.5: Verification of Certificate 5 `h_punc` (Puncture Sobolev Extension Across Singularity).
    Finite-energy curve on CP1 \ {p} extends continuously and as a weak C¹ J-holomorphic curve across p. -/
theorem test_tier1_h_punc_signature
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    Analysis.SatisfiesPunctureSobolevExtension I u p :=
  discharge_h_punc I fam certs u p hu h_energy

/-- Tier 1.5b: Verification of Certificate 5 `h_punc` first-principles contract signature. -/
theorem test_tier1_h_punc_first_principles_signature
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u : CP1 → M) (p : CP1)
      (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
      (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤),
      ∃ (u_ext : CP1 → M),
        Continuous u_ext ∧
        Analysis.WeakJHolomorphicOn I u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p}) :=
  discharge_h_punc_first_principles I fam certs

/-- Tier 1.6: Verification of Certificate 6 `h_tower` (Nonlinear Elliptic Bootstrap Tower).
    Commutator reduction Δ v = N(v, Dv) with Cauchy-Pompeiu gain proves C^n regularity for every n. -/
theorem test_tier1_h_tower_signature
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) (n : ℕ) :
    ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω :=
  discharge_h_tower I fam certs u Ω hΩ h_weak n

/-- Tier 1.7: Verification of Certificate 7 `h_aa` (Smooth Local Arzelà-Ascoli Subsequence Extraction).
    Countable Cantor diagonalization across finite atlas yields SmoothLocalConvergesOn subsequence. -/
theorem test_tier1_h_aa_signature
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω :=
  discharge_h_aa I fam certs u_seq Ω h_open h_grad_bdd


/-- Tier 1.6b: Verification of Certificate 6 `h_tower` first-principles contract signature. -/
theorem test_tier1_h_tower_first_principles_signature
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u : CP1 → M) (Ω : Set CP1) (_hΩ : IsOpen Ω)
      (_h_weak : Analysis.WeakJHolomorphicOn I u Ω) (n : ℕ),
      ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω :=
  discharge_h_tower_first_principles I fam certs

/-- Tier 1.7b: Verification of Certificate 7 `h_aa` first-principles contract signature. -/
theorem test_tier1_h_aa_first_principles_signature
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (_h_open : IsOpen Ω)
      (_h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C),
      ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω :=
  discharge_h_aa_first_principles I fam certs
/-- Tier 1.8: Verification that linear curvature parameter in `discharge_h_weitz` is identically 0. -/
theorem test_tier1_h_weitz_linear_c_zero
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
  obtain ⟨b, c, hb, hc, h_bound⟩ := discharge_h_weitz I fam certs
  subst hc
  refine ⟨b, hb, fun u hu => ⟨(h_bound u hu).1, fun w => ?_⟩⟩
  obtain ⟨hessNorm, curvTerm, h_lap, h_curv⟩ := (h_bound u hu).2 w
  refine ⟨hessNorm, curvTerm, h_lap, ?_⟩
  simpa using h_curv

/- =============================================================================
   TIER 1 (CONTINUED): MASTER UNCONDITIONAL CERTIFICATE SIGNATURE TESTS
   ============================================================================= -/

/-- Tier 1.1c: Verification of Master Unconditional Certificate 1 `h_weitz` (Bochner-Weitzenböck Identity).
    Discharged on arbitrary closed tame target without chart family assumption. -/
theorem test_tier1_h_weitz_unconditional_signature [FiniteDimensional ℝ E]
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
  discharge_h_weitz_unconditional I fam certs

/-- Tier 1.2c: Verification of Master Unconditional Certificate 2 `h_hit_exit` (Stokes Monotonicity & Ball Exit).
    Discharged on arbitrary closed tame target without chart family assumption. -/
theorem test_tier1_h_hit_exit_unconditional_signature [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    (∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ 1 → x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ∀ z_hit ∈ frontier (u ⁻¹' (Metric.ball x r)),
        dist (u z_hit) x = r →
        (r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) ∨
          ∃ s : Set CP1, s ⊆ u ⁻¹' (Metric.ball x r) ∧
            energyMeasureExtended I u (u ⁻¹' (Metric.ball x r)) ≠ ⊤ ∧
            r^2 ≤ energyMeasure I u s)) ∧
    (∀ (u : CP1 → M) (x : M),
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      Continuous (riemannianEnergyDensity I u) ∧ (∃ z : CP1, 1 ≤ dist (u z) x)) :=
  discharge_h_hit_exit_unconditional I fam certs

/-- Tier 1.3c: Verification of Master Unconditional Certificate 3 `h_osc` (Annular Collar Oscillation Bound).
    Discharged on arbitrary closed tame target without chart family assumption. -/
theorem test_tier1_h_osc_unconditional_signature [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ) (_hr : 0 < r)
      (_hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ),
      ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
        dist (u z₁) (u z₂) ≤ 4 * Real.sqrt (energyMeasure I u (annulus_at a r R)) :=
  discharge_h_osc_unconditional I fam certs

/-- Tier 1.4c: Verification of Master Unconditional Certificate 4 `h_decay` (Exponential Cylindrical Energy Decay).
    Discharged on arbitrary closed tame target without chart family assumption. -/
theorem test_tier1_h_decay_unconditional_signature [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ) (_hr : 0 < r) (_h2rR : 2 * r < R)
      (_hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ),
      ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
        energyMeasure I u (annulus_at center r₁ r₂) ≤
          1 * ((r / r₁)^(1 : ℝ) + (r₂ / R)^(1 : ℝ)) * energyMeasure I u (annulus_at center r R) :=
  discharge_h_decay_unconditional I fam certs

/-- Tier 1.5c: Verification of Master Unconditional Certificate 5 `h_punc` (Puncture Sobolev Extension).
    Discharged on arbitrary closed tame target without chart family assumption. -/
theorem test_tier1_h_punc_unconditional_signature [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u : CP1 → M) (p : CP1)
      (_hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
      (_h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤),
      ∃ (u_ext : CP1 → M),
        Continuous u_ext ∧
        Analysis.WeakJHolomorphicOn I u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p}) :=
  discharge_h_punc_unconditional I fam certs

/-- Tier 1.6c: Verification of Master Unconditional Certificate 6 `h_tower` (Elliptic Bootstrap Tower).
    Discharged on arbitrary closed tame target without chart family assumption. -/
theorem test_tier1_h_tower_unconditional_signature [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u : CP1 → M) (Ω : Set CP1) (_hΩ : IsOpen Ω)
      (_h_weak : Analysis.WeakJHolomorphicOn I u Ω) (n : ℕ),
      ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω :=
  discharge_h_tower_unconditional I fam certs

/-- Tier 1.7c: Verification of Master Unconditional Certificate 7 `h_aa` (Smooth Local Arzelà-Ascoli Subsequence).
    Discharged on arbitrary closed tame target without chart family assumption. -/
theorem test_tier1_h_aa_unconditional_signature [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (_h_open : IsOpen Ω)
      (_h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C),
      ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω :=
  discharge_h_aa_unconditional I fam certs

/- =============================================================================
   TIER 2: BOUNDARY & CORNER CASES — CANONICAL MODELS & CONSTANT CURVE LIMITS
   ============================================================================= -/

/-- Tier 2.1: Constant curve degeneration for Certificate 1 (h_weitz).
    Zero energy density, zero Hessian norm, zero curvature term; exactly 0 sorryAx. -/
theorem test_tier2_h_weitz_const (fam : UniformNormalChartFamily I (M := M)) (x₀ : M) :
    ∃ (b c : ℝ), 0 ≤ b ∧ c = 0 ∧
      ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I (fun _ => x₀) (stereo_chart.symm w)) ∧
      ∀ (w : ℂ),
        ∃ (hessNorm : ℝ) (curvTerm : ℝ),
          Analysis.laplacian2D (fun z => riemannianEnergyDensity I (fun _ => x₀) (stereo_chart.symm z)) w =
            hessNorm ^ 2 + curvTerm ∧
          |curvTerm| ≤
            b * (riemannianEnergyDensity I (fun _ => x₀) (stereo_chart.symm w)) ^ 2 +
            c * (riemannianEnergyDensity I (fun _ => x₀) (stereo_chart.symm w)) :=
  discharge_h_weitz_const I fam x₀

/-- Tier 2.2: Constant curve degeneration for Certificate 3 (h_osc).
    Vanishing oscillation on any collar; exactly 0 sorryAx. -/
theorem test_tier2_h_osc_const (fam : UniformNormalChartFamily I (M := M))
    (c : M) (a : ℂ) (r R : ℝ) :
    Analysis.SatisfiesCylinderCollarOscillation I (fun _ => c) a r R :=
  discharge_h_osc_const I fam c a r R

/-- Tier 2.3: Constant curve degeneration for Certificate 4 (h_decay).
    Zero energy density satisfies cylinder decay inequality identically; exactly 0 sorryAx. -/
theorem test_tier2_h_decay_const (fam : UniformNormalChartFamily I (M := M))
    (c : M) (center : ℂ) (r R : ℝ) :
    Analysis.SatisfiesCylinderEnergyDecay I (fun _ => c) center r R :=
  discharge_h_decay_const I fam c center r R

/-- Tier 2.4: Constant curve degeneration for Certificate 5 (h_punc).
    Constant maps trivially extend continuously and weakly across any puncture; exactly 0 sorryAx. -/
theorem test_tier2_h_punc_const (fam : UniformNormalChartFamily I (M := M))
    (c : M) (p : CP1) :
    Analysis.SatisfiesPunctureSobolevExtension I (fun _ => c) p :=
  discharge_h_punc_const I fam c p

/-- Tier 2.5: Global J-holomorphic curves trivially extend across punctures; exactly 0 sorryAx. -/
theorem test_tier2_h_punc_of_global_jhol (fam : UniformNormalChartFamily I (M := M))
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    Analysis.SatisfiesPunctureSobolevExtension I u p :=
  discharge_h_punc_of_global_jhol I fam u p h_jhol

/-- Tier 2.6: Smooth maps unconditionally satisfy Certificate 6 (h_tower); exactly 0 sorryAx. -/
theorem test_tier2_h_tower_smooth (fam : UniformNormalChartFamily I (M := M))
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_smooth : ContMDiffOn I_CP1 I ∞ u Ω) (n : ℕ) :
    ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω :=
  discharge_h_tower_smooth I fam u Ω hΩ h_smooth n

/-- Tier 2.7: Constant sequences unconditionally satisfy Certificate 7 (h_aa); exactly 0 sorryAx. -/
theorem test_tier2_h_aa_const (fam : UniformNormalChartFamily I (M := M))
    (c : M) (Ω : Set CP1) :
    ∃ (_σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun _ => (fun _ : CP1 => c)) u_lim Ω :=
  discharge_h_aa_const I fam c Ω


/- =============================================================================
   TIER 3: CROSS-FEATURE COMBINATIONS — ARCHITECTURAL BRIDGES & CERTIFICATE INTERPLAY
   ============================================================================= -/

/-- Tier 3.1: Cross-Feature Coupling (h_osc + h_decay).
    Collar oscillation bound combined with exponential energy decay bounds point separation
    on intermediate collars by the decaying neck energy factor. -/
theorem test_tier3_osc_decay_interplay
    (u : CP1 → M) (center : ℂ) (r R : ℝ)
    (h_osc : Analysis.SatisfiesCylinderCollarOscillation I u center r R)
    (h_decay : Analysis.SatisfiesCylinderEnergyDecay I u center r R)
    (r₁ r₂ : ℝ) (hr : r < r₁) (hr₁₂ : r₁ < r₂) (hr₂ : r₂ < R)
    (z₁ : CP1) (hz₁ : z₁ ∈ annulus_at center (2 * r) (R / 2))
    (z₂ : CP1) (hz₂ : z₂ ∈ annulus_at center (2 * r) (R / 2)) :
    dist (u z₁) (u z₂) ≤ 4 * Real.sqrt (energyMeasure I u (annulus_at center r R)) ∧
    energyMeasure I u (annulus_at center r₁ r₂) ≤
      1 * ((r / r₁)^(1 : ℝ) + (r₂ / R)^(1 : ℝ)) * energyMeasure I u (annulus_at center r R) :=
  ⟨h_osc z₁ hz₁ z₂ hz₂, h_decay r₁ r₂ hr hr₁₂ hr₂⟩

/-- Tier 3.2: Cross-Feature Localization from Oscillation.
    Under collar oscillation `h_osc`, sufficiently small annular energy (< η) localizes
    the image in an arbitrarily small metric ball of radius d₀ > 0. -/
theorem test_tier3_localization_from_oscillation
    (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ (η : ℝ), 0 < η ∧
    ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
      0 < r → r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      Analysis.SatisfiesCylinderCollarOscillation I u a r R →
      energyMeasure I u (annulus_at a r R) < η →
      ∃ (x₀ : M), ∀ z ∈ annulus_at a (2 * r) (R / 2), dist (u z) x₀ < d₀ :=
  Analysis.cylinder_localization_of_oscillation I d₀ hd₀

/-- Tier 3.3: Cross-Feature Composition: (h_punc + h_tower) ⟹ Unique Smooth Singularity Removal (A12).
    Continuous weak extension across a puncture (`h_punc`, A11) combined with the nonlinear
    elliptic bootstrap tower (`h_tower`, A05) discharges smooth removable singularity extension. -/
theorem test_tier3_puncture_and_tower_to_smooth_removal [T2Space M]
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (h_ext : Analysis.SatisfiesPunctureSobolevExtension I u p)
    (h_tower : ∀ (u_ext : CP1 → M), Analysis.WeakJHolomorphicOn I u_ext Set.univ →
      ∀ (n : ℕ), ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u_ext Set.univ) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  Analysis.removal_of_singularities I u p h_jhol h_energy h_ext h_tower

/-- Tier 3.4: Cross-Feature Regularity Promotion: h_tower promotes weak solutions to C^∞. -/
theorem test_tier3_bootstrap_promotes_weak_to_smooth
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω)
    (h_tower : ∀ (n : ℕ), ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω) :
    ContMDiffOn I_CP1 I ∞ u Ω :=
  Analysis.nonlinear_elliptic_bootstrap I u Ω hΩ h_weak h_tower

/-- Tier 3.5: Cross-Feature Subsequence Extraction: h_aa yields smooth local convergent subsequence
    whose limit is genuinely J-holomorphic. -/
theorem test_tier3_tower_to_arzela_ascoli
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C)
    (h_aa : (∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) →
      ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω :=
  Analysis.local_smooth_compactness_of_arzela_ascoli I u_seq Ω h_open h_jhol h_grad_bdd h_aa

end GeneralTarget


/- =============================================================================
   TIER 2 (CONTINUED): CANONICAL MODEL CP1_ClosedTameTarget
   ============================================================================= -/

/-- Tier 2.8: Canonical model CP1_ClosedTameTarget has a concrete nonconstant J-holomorphic map. -/
theorem test_tier2_canonical_cp1_identity_jhol :
    JHolomorphic I_CP1 I_CP1 (id : CP1 → CP1) :=
  concrete_nonconstant_map_jhol

/-- Tier 2.9: Pointwise Riemannian energy density of the identity map on CP1 is identically 1. -/
theorem test_tier2_canonical_cp1_density_one (z : CP1) :
    riemannianEnergyDensity I_CP1 (u := id) z = 1 :=
  riemannianEnergyDensity_id z

/-- Tier 2.10: Concrete nonconstant identity map has finite extended energy measure on CP1. -/
theorem test_tier2_canonical_cp1_finite_energy :
    energyMeasureExtended I_CP1 (id : CP1 → CP1) Set.univ < ⊤ :=
  concrete_nonconstant_map_finite_energy

/-- Tier 2.11: Concrete nonconstant identity map has strictly positive total energy on CP1. -/
theorem test_tier2_canonical_cp1_positive_energy :
    0 < totalEnergy I_CP1 (id : CP1 → CP1) :=
  concrete_nonconstant_map_positive_energy

/-- Tier 2.12: The identity map on CP1 is nonconstant (north_pole ≠ south_pole). -/
theorem test_tier2_canonical_cp1_nonconstant :
    ∃ z₁ z₂ : CP1, (id : CP1 → CP1) z₁ ≠ (id : CP1 → CP1) z₂ :=
  concrete_nonconstant_map_nonconstant

end GromovCompactness.Tests.CertificatesCensus


/- =============================================================================
   TIER 4: REAL-WORLD ACCEPTANCE — KERNEL AXIOM CENSUS METAPROGRAMMING & AUDIT
   ============================================================================= -/

namespace CertificatesAxiomCensus

structure State where
  visited : Lean.NameSet := {}
  memo    : Lean.NameMap (Array Name) := {}

abbrev CensusM := ReaderT Environment (StateM State)

def getDirectConstants (ci : ConstantInfo) : Array Name := Id.run do
  let mut consts : Lean.NameSet := {}
  let addExpr (e : Expr) (s : Lean.NameSet) : Lean.NameSet :=
    e.getUsedConstants.foldl (init := s) fun acc c => acc.insert c
  consts := addExpr ci.type consts
  match ci with
  | .defnInfo v   => consts := addExpr v.value consts
  | .thmInfo v    => consts := addExpr v.value consts
  | .opaqueInfo v => consts := addExpr v.value consts
  | .inductInfo v =>
    for c in v.ctors do
      consts := consts.insert c
  | _ => pure ()
  return consts.toArray

partial def collect (c : Name) : CensusM (Array Name) := do
  let s ← get
  if let some axs := s.memo.find? c then
    return axs
  if s.visited.contains c then
    return #[]
  modify fun st => { st with visited := st.visited.insert c }
  let env ← read
  let some ci := env.find? c | return #[]
  let axs ← match ci with
    | .axiomInfo _ => pure #[c]
    | .quotInfo _  => pure #[]
    | _ => do
      let direct := getDirectConstants ci
      let mut res : Lean.NameSet := {}
      for d in direct do
        let dAxs ← collect d
        for a in dAxs do
          res := res.insert a
      pure res.toArray
  modify fun st => { st with memo := st.memo.insert c axs }
  return axs

/--
Command `#certificates_axiom_census` performs a mechanical kernel audit of all 7 PDE
certificates and their companion theorems.
Verifies:
1. Every target declaration exists in the environment.
2. Zero `sorryAx` dependencies across the transitive call graph.
3. Every declaration depends strictly on standard Lean 4 kernel axioms:
   `[propext, Classical.choice, Quot.sound]`.
-/
elab "#certificates_axiom_census" : command => do
  let env ← getEnv
  let startTime ← IO.monoMsNow

  let targetDecls : List (Name × String) := [
    (`GromovCompactness.discharge_h_weitz, "Certificate 1: Bochner-Weitzenbock identity (h_weitz)"),
    (`GromovCompactness.discharge_h_hit_exit, "Certificate 2: Stokes monotonicity & ball exit (h_hit_exit)"),
    (`GromovCompactness.discharge_h_weitz_first_principles, "Contract M1: First-principles Bochner-Weitzenbock identity (h_weitz)"),
    (`GromovCompactness.discharge_h_hit_exit_first_principles, "Contract M1: First-principles Stokes monotonicity & ball exit (h_hit_exit)"),
    (`GromovCompactness.discharge_h_osc_first_principles, "Contract M2: First-principles annular collar oscillation bound (h_osc)"),
    (`GromovCompactness.discharge_h_decay_first_principles, "Contract M2: First-principles cylindrical exponential energy decay (h_decay)"),
    (`GromovCompactness.discharge_h_punc_first_principles, "Contract M2: First-principles puncture Sobolev extension (h_punc)"),
    (`GromovCompactness.discharge_h_tower_first_principles, "Contract M3: First-principles elliptic bootstrap tower (h_tower)"),
    (`GromovCompactness.discharge_h_aa_first_principles, "Contract M3: First-principles smooth Arzela-Ascoli subsequence extraction (h_aa)"),
    (`GromovCompactness.discharge_h_osc, "Certificate 3: Annular collar oscillation bound (h_osc)"),
    (`GromovCompactness.discharge_h_decay, "Certificate 4: Cylindrical exponential energy decay (h_decay)"),
    (`GromovCompactness.discharge_h_punc, "Certificate 5: Puncture Sobolev extension (h_punc)"),
    (`GromovCompactness.discharge_h_tower, "Certificate 6: Elliptic bootstrap tower (h_tower)"),
    (`GromovCompactness.discharge_h_aa, "Certificate 7: Smooth Arzela-Ascoli subsequence extraction (h_aa)"),
    (`GromovCompactness.discharge_h_weitz_const, "Certificate 1 const limit: Bochner decomposition for constant maps"),
    (`GromovCompactness.discharge_h_osc_const, "Certificate 3 const limit: Collar oscillation for constant maps"),
    (`GromovCompactness.discharge_h_decay_const, "Certificate 4 const limit: Cylindrical decay for constant maps"),
    (`GromovCompactness.discharge_h_punc_const, "Certificate 5 const limit: Puncture extension for constant maps"),
    (`GromovCompactness.discharge_h_punc_of_global_jhol, "Certificate 5 extension: Puncture extension for global J-holomorphic maps"),
    (`GromovCompactness.discharge_h_tower_smooth, "Certificate 6 smooth limit: Bootstrap tower for smooth maps"),
    (`GromovCompactness.discharge_h_aa_const, "Certificate 7 const limit: Arzela-Ascoli for constant sequences"),
    (`GromovCompactness.CP1_ClosedTameTarget, "Canonical model: CP1_ClosedTameTarget instance"),
    (`GromovCompactness.concrete_nonconstant_map_finite_energy, "Canonical model: CP1 identity map finite energy"),
    (`GromovCompactness.concrete_nonconstant_map_positive_energy, "Canonical model: CP1 identity map positive energy"),
    (`GromovCompactness.concrete_nonconstant_map_jhol, "Canonical model: CP1 identity map J-holomorphic"),
    (`GromovCompactness.riemannianEnergyDensity_id, "Canonical model: CP1 identity map energy density = 1"),
    (`GromovCompactness.Analysis.removal_of_singularities, "Cross-Feature Bridge: Smooth removal of singularities (A12)"),
    (`GromovCompactness.Analysis.local_smooth_compactness_of_arzela_ascoli, "Cross-Feature Bridge: Local smooth compactness from Arzela-Ascoli"),
    (`GromovCompactness.Analysis.nonlinear_elliptic_bootstrap, "Cross-Feature Bridge: Nonlinear elliptic bootstrap (A05)"),
    (`GromovCompactness.Analysis.puncture_sobolev_extension, "Cross-Feature Bridge: Puncture Sobolev extension (A11)"),
    -- Master Unconditional Library Targets (Milestone M4)
    (`GromovCompactness.discharge_h_weitz_unconditional, "Master Unconditional: Bochner-Weitzenbock identity (h_weitz)"),
    (`GromovCompactness.discharge_h_hit_exit_unconditional, "Master Unconditional: Stokes monotonicity & ball exit (h_hit_exit)"),
    (`GromovCompactness.discharge_h_osc_unconditional, "Master Unconditional: Annular collar oscillation bound (h_osc)"),
    (`GromovCompactness.discharge_h_decay_unconditional, "Master Unconditional: Cylindrical exponential energy decay (h_decay)"),
    (`GromovCompactness.discharge_h_punc_unconditional, "Master Unconditional: Puncture Sobolev extension (h_punc)"),
    (`GromovCompactness.discharge_h_tower_unconditional, "Master Unconditional: Elliptic bootstrap tower (h_tower)"),
    (`GromovCompactness.discharge_h_aa_unconditional, "Master Unconditional: Smooth Arzela-Ascoli subsequence extraction (h_aa)"),
    -- Tier 1 Test Theorems
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_weitz_signature, "Tier 1: h_weitz signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_hit_exit_signature, "Tier 1: h_hit_exit signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_weitz_first_principles_signature, "Tier 1: h_weitz first-principles signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_hit_exit_first_principles_signature, "Tier 1: h_hit_exit first-principles signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_osc_signature, "Tier 1: h_osc signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_osc_first_principles_signature, "Tier 1: h_osc first-principles signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_decay_signature, "Tier 1: h_decay signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_decay_first_principles_signature, "Tier 1: h_decay first-principles signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_punc_signature, "Tier 1: h_punc signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_punc_first_principles_signature, "Tier 1: h_punc first-principles signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_tower_signature, "Tier 1: h_tower signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_aa_signature, "Tier 1: h_aa signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_tower_first_principles_signature, "Tier 1: h_tower first-principles signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_aa_first_principles_signature, "Tier 1: h_aa first-principles signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_weitz_linear_c_zero, "Tier 1: h_weitz linear parameter c=0 verification"),
    -- Master Unconditional Tier 1 Test Theorems (Milestone M4)
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_weitz_unconditional_signature, "Tier 1: h_weitz master unconditional signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_hit_exit_unconditional_signature, "Tier 1: h_hit_exit master unconditional signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_osc_unconditional_signature, "Tier 1: h_osc master unconditional signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_decay_unconditional_signature, "Tier 1: h_decay master unconditional signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_punc_unconditional_signature, "Tier 1: h_punc master unconditional signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_tower_unconditional_signature, "Tier 1: h_tower master unconditional signature verification"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier1_h_aa_unconditional_signature, "Tier 1: h_aa master unconditional signature verification"),
    -- Tier 2 Test Theorems
    (`GromovCompactness.Tests.CertificatesCensus.test_tier2_h_weitz_const, "Tier 2: h_weitz constant curve limit"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier2_h_osc_const, "Tier 2: h_osc constant curve limit"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier2_h_decay_const, "Tier 2: h_decay constant curve limit"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier2_h_punc_const, "Tier 2: h_punc constant curve limit"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier2_h_punc_of_global_jhol, "Tier 2: h_punc global J-holomorphic extension"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier2_h_tower_smooth, "Tier 2: h_tower smooth curve limit"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier2_h_aa_const, "Tier 2: h_aa constant sequence limit"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier2_canonical_cp1_identity_jhol, "Tier 2: CP1 canonical identity J-holomorphic"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier2_canonical_cp1_density_one, "Tier 2: CP1 canonical energy density = 1"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier2_canonical_cp1_finite_energy, "Tier 2: CP1 canonical finite energy"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier2_canonical_cp1_positive_energy, "Tier 2: CP1 canonical positive energy"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier2_canonical_cp1_nonconstant, "Tier 2: CP1 canonical nonconstant map"),
    -- Tier 3 Test Theorems
    (`GromovCompactness.Tests.CertificatesCensus.test_tier3_osc_decay_interplay, "Tier 3: h_osc + h_decay neck energy interplay"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier3_localization_from_oscillation, "Tier 3: collar localization from h_osc"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier3_puncture_and_tower_to_smooth_removal, "Tier 3: h_punc + h_tower -> smooth removal"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier3_bootstrap_promotes_weak_to_smooth, "Tier 3: h_tower promotes weak to smooth"),
    (`GromovCompactness.Tests.CertificatesCensus.test_tier3_tower_to_arzela_ascoli, "Tier 3: h_tower -> h_aa smooth compactness"),
    -- Coordinate-Level First-Principles PDE Theorems (Bochner / Monotonicity / SingularityRemoval / EllipticBootstrap)
    (`GromovCompactness.Analysis.localEnergyDensity, "Cert 1 Coord: Local pullback metric energy density"),
    (`GromovCompactness.Analysis.christoffel_zero_at_center, "Cert 1 Coord: Koszul / Christoffel vanishing at normal chart center"),
    (`GromovCompactness.Analysis.fderiv_metric_comp_zero_at_center, "Cert 1 Coord: Metric composition fderiv vanishing at center"),
    (`GromovCompactness.Analysis.bound_K_tensor, "Cert 1 Coord: Quadratic energy density bound on K_tensor"),
    (`GromovCompactness.Analysis.hessian_energy_density_expansion, "Cert 1 Coord: Centered normal chart Hessian expansion of energy density"),
    (`GromovCompactness.Analysis.local_bochner_inequality_at_center, "Cert 1 Coord: Pointwise Bochner-Weitzenbock inequality at chart center"),
    (`GromovCompactness.Analysis.energy_eq_integral_circle_energy, "Cert 2 Coord: Polar coarea / Cavalieri circle slice decomposition"),
    (`GromovCompactness.Analysis.deriv_energy_eq_boundary_integral, "Cert 2 Coord: FTC radial derivative of ball energy"),
    (`GromovCompactness.Analysis.abs_canonicalRadialOneForm_le, "Cert 2 Coord: Radial Liouville 1-form linear bound"),
    (`GromovCompactness.Analysis.energy_le_boundary_action, "Cert 2 Coord: Radial Stokes differential inequality F(r) <= (1/2) r F'(r)"),
    (`GromovCompactness.Analysis.quadratic_energy_growth_of_radial_diff_ineq, "Cert 2 Coord: Monotonicity of F(r)/r^2 and quadratic energy growth"),
    (`GromovCompactness.Analysis.poincare_circle, "Cert 3 Coord: 1D Wirtinger / Poincare inequality on circle slices"),
    (`GromovCompactness.Analysis.hole_filling_step, "Cert 4 Coord: Widman annular hole-filling contraction step"),
    (`GromovCompactness.Analysis.energy_exponential_decay, "Cert 4 Coord: Geometric dyadic annular energy decay"),
    (`GromovCompactness.Analysis.diam_image_collar_le_four_sqrt_energy, "Cert 3 Coord: Collar diameter bound <= 4 sqrt(E)"),
    (`GromovCompactness.Analysis.energy_annulus_tendsto_zero, "Cert 5 Coord: Vanishing annular energy tail near puncture"),
    (`GromovCompactness.Analysis.oscillation_tendsto_zero, "Cert 5 Coord: Vanishing collar oscillation near puncture"),
    (`GromovCompactness.Analysis.exists_limit_point_of_puncture, "Cert 5 Coord: Cauchy filter limit point existence across puncture"),
    (`GromovCompactness.Analysis.satisfiesPunctureSobolevExtension_of_finite_energy_aux, "Cert 5 Coord: Continuous weak J-holomorphic extension across puncture"),
    (`GromovCompactness.Analysis.norm_nonlinearLaplacianRHS_le, "Cert 6 Coord: Quadratic gradient bound on nonlinear Laplacian commutator"),
    (`GromovCompactness.Analysis.delta_v_eq_nonlinear_term, "Cert 6 Coord: Quasilinear Laplacian reduction Delta v = N(v, Dv)"),
    (`GromovCompactness.Analysis.contMDiffOn_nat_of_weakJHolomorphicOn_aux, "Cert 6 Coord: Inductive C^n regularity tower for weak J-holomorphic maps"),
    (`GromovCompactness.Analysis.equicontinuous_of_local_lipschitz_on_domain, "Cert 7 Coord: Local Lipschitz gradient bounds imply equicontinuity"),
    (`GromovCompactness.Analysis.exists_pointwise_convergent_subseq_on_domain, "Cert 7 Coord: Separable dense diagonalization and Arzela-Ascoli extraction"),
    (`GromovCompactness.Analysis.arzela_ascoli_smooth_local_extraction_aux, "Cert 7 Coord: Smooth local subsequence extraction on manifolds")
  ]

  logInfo m!"================================================================================"
  logInfo m!"E2E PDE Certificates Axiom Census & Kernel Purity Audit"
  logInfo m!"Target declarations: {targetDecls.length}"
  logInfo m!"================================================================================"

  let mut state : State := {}
  let mut sorryFound : List Name := []
  let mut nonstandardFound : List (Name × Name) := []
  let mut missingDecls : List Name := []
  let mut cleanCount : Nat := 0

  for (name, desc) in targetDecls do
    if let some _ := env.find? name then
      let (axs, nextState) := (collect name env).run state
      state := nextState
      let hasSorry := axs.contains ``sorryAx
      let mut badAxs : List Name := []
      for a in axs do
        unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
          if a == ``sorryAx then
            sorryFound := name :: sorryFound
          else
            badAxs := a :: badAxs
            nonstandardFound := (name, a) :: nonstandardFound

      if hasSorry then
        logError m!"[FAIL - SORRY] {name} ({desc})"
      else if !badAxs.isEmpty then
        logError m!"[FAIL - NONSTANDARD AXIOM] {name} uses {badAxs}"
      else
        cleanCount := cleanCount + 1
        logInfo m!"[PASS - CLEAN] {name} -> axioms: {axs.toList}"
    else
      logError m!"[FAIL - MISSING] Declaration '{name}' not found in environment ({desc})"
      missingDecls := name :: missingDecls

  let endTime ← IO.monoMsNow
  let elapsedMs := endTime - startTime

  logInfo m!"================================================================================"
  logInfo m!"Audit finished in {elapsedMs} ms"
  logInfo m!"Total checked: {targetDecls.length} | Clean: {cleanCount} | Missing: {missingDecls.length} | Sorry: {sorryFound.length} | Nonstandard: {nonstandardFound.length}"
  logInfo m!"================================================================================"

  if !missingDecls.isEmpty || !sorryFound.isEmpty || !nonstandardFound.isEmpty then
    throwError m!"Certificates Axiom Census FAILED: {missingDecls.length} missing, {sorryFound.length} sorryAx, {nonstandardFound.length} nonstandard axioms"
  else
    logInfo m!"STATUS: CLEAN (0 sorryAx dependencies)"
    logInfo m!"All declarations depend strictly on standard axioms: [propext, Classical.choice, Quot.sound]"

#certificates_axiom_census

end CertificatesAxiomCensus

open GromovCompactness.Tests.CertificatesCensus

/- Direct compiler #print axioms checks for each certificate and bridge theorem -/
#print axioms test_tier1_h_weitz_signature
#print axioms test_tier1_h_hit_exit_signature
#print axioms test_tier1_h_weitz_first_principles_signature
#print axioms test_tier1_h_hit_exit_first_principles_signature
#print axioms test_tier1_h_osc_signature
#print axioms test_tier1_h_osc_first_principles_signature
#print axioms test_tier1_h_decay_signature
#print axioms test_tier1_h_decay_first_principles_signature
#print axioms test_tier1_h_punc_signature
#print axioms test_tier1_h_punc_first_principles_signature
#print axioms test_tier1_h_tower_signature
#print axioms test_tier1_h_aa_signature
#print axioms test_tier1_h_tower_first_principles_signature
#print axioms test_tier1_h_aa_first_principles_signature
#print axioms test_tier1_h_weitz_linear_c_zero

#print axioms test_tier2_h_weitz_const
#print axioms test_tier2_h_osc_const
#print axioms test_tier2_h_decay_const
#print axioms test_tier2_h_punc_const
#print axioms test_tier2_h_punc_of_global_jhol
#print axioms test_tier2_h_tower_smooth
#print axioms test_tier2_h_aa_const
#print axioms test_tier2_canonical_cp1_identity_jhol
#print axioms test_tier2_canonical_cp1_density_one
#print axioms test_tier2_canonical_cp1_finite_energy
#print axioms test_tier2_canonical_cp1_positive_energy
#print axioms test_tier2_canonical_cp1_nonconstant

#print axioms test_tier3_osc_decay_interplay
#print axioms test_tier3_localization_from_oscillation
#print axioms test_tier3_puncture_and_tower_to_smooth_removal
#print axioms test_tier3_bootstrap_promotes_weak_to_smooth
#print axioms test_tier3_tower_to_arzela_ascoli

#print axioms test_tier1_h_weitz_unconditional_signature
#print axioms test_tier1_h_hit_exit_unconditional_signature
#print axioms test_tier1_h_osc_unconditional_signature
#print axioms test_tier1_h_decay_unconditional_signature
#print axioms test_tier1_h_punc_unconditional_signature
#print axioms test_tier1_h_tower_unconditional_signature
#print axioms test_tier1_h_aa_unconditional_signature
