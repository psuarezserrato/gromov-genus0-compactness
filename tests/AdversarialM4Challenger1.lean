/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Milestone M4 Empirical Challenger 1)
-/
import Lean
import Lean.Elab.Command
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
import GromovCompactness.Analysis.Bochner
import GromovCompactness.Analysis.Monotonicity
import GromovCompactness.Analysis.EnergyGap
import GromovCompactness.Analysis.SingularityRemoval
import GromovCompactness.Analysis.EllipticBootstrap

open scoped Manifold ContDiff Topology Real ENNReal
open Metric Set MeasureTheory Filter Topology ENNReal GromovCompactness GromovCompactness.Analysis
open Lean Elab Command

namespace AdversarialM4Challenger1

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/- =============================================================================
   SHARED INFRASTRUCTURE: CONSTANT MAP LEMMAS & NORMAL CHART SHRINKING
   ============================================================================= -/

section GeneralTarget

universe u v

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
variable [tgt : ClosedTameTarget I M]

/-- Constant maps are unconditionally J-holomorphic on any subset of CP1. -/
theorem jHolomorphicOn_const (c : M) (s : Set CP1) :
    JHolomorphicOn (I := I) (I_dom := I_CP1) (fun _ => c) s := by
  refine ⟨contMDiffOn_const, fun z _hz v => ?_⟩
  simp only [mfderiv_const]
  exact ((ClosedTameTarget.J (I := I) c).map_zero).symm

/-- Construction of Shrunk UniformNormalChartFamily.
Any UniformNormalChartFamily can be restricted to a smaller uniform radius r' ≤ r_norm,
preserving all 15 geometric fields. -/
def uniformNormalChartFamily_shrink
    (fam : UniformNormalChartFamily I (M := M))
    (r' : ℝ) (hr' : 0 < r') (hle : r' ≤ fam.r_norm) :
    UniformNormalChartFamily I (M := M) where
  r_norm := r'
  r_norm_pos := hr'
  chartAt := fun p => CenteredNormalChart.shrink I (fam.chartAt p) hr' hle
  L_dist := fam.L_dist
  L_dist_ge := fam.L_dist_ge
  dist_le_chart := fun p y hy => fam.dist_le_chart p y (Metric.ball_subset_ball hle hy)
  chart_le_dist := fun p y hy => fam.chart_le_dist p y (Metric.ball_subset_ball hle hy)
  C_curv := fam.C_curv
  C_curv_nonneg := fam.C_curv_nonneg
  C_metric3 := fam.C_metric3
  C_J3 := fam.C_J3
  C_omega3 := fam.C_omega3
  metric_c3_uniform := fun p y hy v w hv hw =>
    fam.metric_c3_uniform p y (Metric.ball_subset_ball hle hy) v w hv hw
  J_c3_uniform := fun p y hy v hv =>
    fam.J_c3_uniform p y (Metric.ball_subset_ball hle hy) v hv
  omega_c3_uniform := fun p y hy v w hv hw =>
    fam.omega_c3_uniform p y (Metric.ball_subset_ball hle hy) v w hv hw

/-- Shrunk chart family certificates: Any valid certificates on `fam` remain valid
on the shrunk family because the curvature constants and manifold are unchanged. -/
theorem uniformNormalChartCertificates_shrink
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (r' : ℝ) (hr' : 0 < r') (hle : r' ≤ fam.r_norm) :
    UniformNormalChartCertificates I (uniformNormalChartFamily_shrink I fam r' hr' hle) where
  h_weitz_curv := certs.h_weitz_curv
  h_hit_exit_prop := certs.h_hit_exit_prop
  h_osc_prop := certs.h_osc_prop
  h_decay_prop := certs.h_decay_prop
  h_punc_prop := certs.h_punc_prop
  h_tower_prop := certs.h_tower_prop
  h_aa_prop := certs.h_aa_prop

/- =============================================================================
   SUITE 1: CALLING PATTERNS & CALLING CONVENTIONS FOR ALL 11 UNCONDITIONAL DECLARATIONS
   Tests explicit positional and named argument calling for every Section 6 theorem.
   ============================================================================= -/

/-- Test 1.1: Positional calling of discharge_h_weitz_unconditional. -/
theorem stress_call_weitz_positional
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

/-- Test 1.2: Named calling of discharge_h_weitz_unconditional. -/
theorem stress_call_weitz_named
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
  discharge_h_weitz_unconditional (fam := fam) (certs := certs) (I := I)

/-- Test 1.3: Positional calling of discharge_h_hit_exit_unconditional. -/
theorem stress_call_hit_exit_positional
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.HitExitProperty I M :=
  discharge_h_hit_exit_unconditional I fam certs

/-- Test 1.4: Named calling of discharge_h_hit_exit_unconditional. -/
theorem stress_call_hit_exit_named
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.HitExitProperty I M :=
  discharge_h_hit_exit_unconditional (fam := fam) (certs := certs) (I := I)

/-- Test 1.5: Positional calling of discharge_h_osc_unconditional. -/
theorem stress_call_osc_positional
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CollarOscillationProperty I M :=
  discharge_h_osc_unconditional I fam certs

/-- Test 1.6: Named calling of discharge_h_osc_unconditional. -/
theorem stress_call_osc_named
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CollarOscillationProperty I M :=
  discharge_h_osc_unconditional (fam := fam) (certs := certs) (I := I)

/-- Test 1.7: Positional calling of discharge_h_decay_unconditional. -/
theorem stress_call_decay_positional
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CylinderEnergyDecayProperty I M :=
  discharge_h_decay_unconditional I fam certs

/-- Test 1.8: Named calling of discharge_h_decay_unconditional. -/
theorem stress_call_decay_named
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CylinderEnergyDecayProperty I M :=
  discharge_h_decay_unconditional (fam := fam) (certs := certs) (I := I)

/-- Test 1.9: Positional calling of discharge_h_decay_unconditional (pow_nat alias). -/
theorem stress_call_decay_pow_nat_positional
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CylinderEnergyDecayProperty I M :=
  discharge_h_decay_unconditional I fam certs

/-- Test 1.10: Named calling of discharge_h_decay_unconditional (pow_nat alias). -/
theorem stress_call_decay_pow_nat_named
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CylinderEnergyDecayProperty I M :=
  discharge_h_decay_unconditional (fam := fam) (certs := certs) (I := I)

/-- Test 1.11: Positional calling of discharge_h_punc_unconditional. -/
theorem stress_call_punc_positional
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

/-- Test 1.12: Named calling of discharge_h_punc_unconditional. -/
theorem stress_call_punc_named
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u : CP1 → M) (p : CP1)
      (_hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
      (_h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤),
      ∃ (u_ext : CP1 → M),
        Continuous u_ext ∧
        Analysis.WeakJHolomorphicOn I u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p}) :=
  discharge_h_punc_unconditional (fam := fam) (certs := certs) (I := I)

/-- Test 1.13: Positional calling of discharge_removal_of_singularities_unconditional. -/
theorem stress_call_removal_positional [T2Space M]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  discharge_removal_of_singularities_unconditional I fam certs u p h_jhol h_energy

/-- Test 1.14: Named calling of discharge_removal_of_singularities_unconditional. -/
theorem stress_call_removal_named [T2Space M]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  discharge_removal_of_singularities_unconditional (fam := fam) (certs := certs) (I := I) u p h_jhol h_energy

/-- Test 1.15: Positional calling of discharge_h_tower_unconditional. -/
theorem stress_call_tower_positional
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u : CP1 → M) (Ω : Set CP1) (_hΩ : IsOpen Ω)
      (_h_weak : Analysis.WeakJHolomorphicOn I u Ω) (n : ℕ),
      ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω :=
  discharge_h_tower_unconditional I fam certs

/-- Test 1.16: Named calling of discharge_h_tower_unconditional. -/
theorem stress_call_tower_named
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u : CP1 → M) (Ω : Set CP1) (_hΩ : IsOpen Ω)
      (_h_weak : Analysis.WeakJHolomorphicOn I u Ω) (n : ℕ),
      ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω :=
  discharge_h_tower_unconditional (fam := fam) (certs := certs) (I := I)

/-- Test 1.17: Positional calling of discharge_nonlinear_elliptic_bootstrap_unconditional. -/
theorem stress_call_bootstrap_positional
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I ∞ u Ω :=
  discharge_nonlinear_elliptic_bootstrap_unconditional I fam certs u Ω hΩ h_weak

/-- Test 1.18: Named calling of discharge_nonlinear_elliptic_bootstrap_unconditional. -/
theorem stress_call_bootstrap_named
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I ∞ u Ω :=
  discharge_nonlinear_elliptic_bootstrap_unconditional (fam := fam) (certs := certs) (I := I) u Ω hΩ h_weak

/-- Test 1.19: Positional calling of discharge_h_aa_unconditional. -/
theorem stress_call_aa_positional
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (_h_open : IsOpen Ω)
      (_h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
      (_h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C),
      ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω :=
  discharge_h_aa_unconditional I fam certs

/-- Test 1.20: Named calling of discharge_h_aa_unconditional. -/
theorem stress_call_aa_named
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (_h_open : IsOpen Ω)
      (_h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
      (_h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C),
      ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω :=
  discharge_h_aa_unconditional (fam := fam) (certs := certs) (I := I)

/-- Test 1.21: Positional calling of discharge_local_smooth_compactness_of_arzela_ascoli_unconditional. -/
theorem stress_call_local_smooth_compactness_positional
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω :=
  discharge_local_smooth_compactness_of_arzela_ascoli_unconditional I fam certs u_seq Ω h_open h_jhol h_grad_bdd

/-- Test 1.22: Named calling of discharge_local_smooth_compactness_of_arzela_ascoli_unconditional. -/
theorem stress_call_local_smooth_compactness_named
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω :=
  discharge_local_smooth_compactness_of_arzela_ascoli_unconditional (fam := fam) (certs := certs) (I := I) u_seq Ω h_open h_jhol h_grad_bdd

/- =============================================================================
   SUITE 2: CURRIED FUNCTIONAL PATTERNS & BRIDGE EVALUATION
   Tests passing only (I fam) to obtain the first-class functional contract.
   ============================================================================= -/

/-- Test 2.1: Curried functional application of h_osc. -/
theorem stress_curried_osc
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CollarOscillationProperty I M :=
  (discharge_h_osc_unconditional I fam) certs

/-- Test 2.2: Curried functional application of h_decay. -/
theorem stress_curried_decay
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CylinderEnergyDecayProperty I M :=
  (discharge_h_decay_unconditional I fam) certs

/-- Test 2.3: Curried functional application of h_decay (pow_nat alias). -/
theorem stress_curried_decay_pow_nat
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CylinderEnergyDecayProperty I M :=
  (discharge_h_decay_unconditional I fam) certs

/-- Test 2.4: Curried functional application of h_punc. -/
theorem stress_curried_punc
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u : CP1 → M) (p : CP1)
      (_hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
      (_h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤),
      ∃ (u_ext : CP1 → M),
        Continuous u_ext ∧
        Analysis.WeakJHolomorphicOn I u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p}) :=
  (discharge_h_punc_unconditional I fam) certs

/-- Test 2.5: Curried functional application of h_tower. -/
theorem stress_curried_tower
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u : CP1 → M) (Ω : Set CP1) (_hΩ : IsOpen Ω)
      (_h_weak : Analysis.WeakJHolomorphicOn I u Ω) (n : ℕ),
      ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω :=
  (discharge_h_tower_unconditional I fam) certs

/-- Test 2.6: Curried functional application of h_aa. -/
theorem stress_curried_aa
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (_h_open : IsOpen Ω)
      (_h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
      (_h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C),
      ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω :=
  (discharge_h_aa_unconditional I fam) certs

/-- Test 2.7: Definitional evaluation of exists_uniform_normal_chart_family. -/
theorem stress_exists_bridge_tautology (fam : UniformNormalChartFamily I (M := M)) :
    exists_uniform_normal_chart_family (I := I) fam = ⟨fam⟩ :=
  rfl

/-- Test 2.8: Definitional proof-irrelevance equality between unconditional and first-principles weitz. -/
theorem stress_unconditional_weitz_proof_irrel
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    discharge_h_weitz_unconditional I fam certs = discharge_h_weitz_first_principles I fam certs :=
  rfl

/-- Test 2.9: Definitional proof-irrelevance equality between unconditional and first-principles hit_exit. -/
theorem stress_unconditional_hit_exit_proof_irrel
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    discharge_h_hit_exit_unconditional I fam certs = discharge_h_hit_exit_first_principles I fam certs :=
  rfl

/-- Test 2.10: Definitional proof-irrelevance equality between unconditional and first-principles osc. -/
theorem stress_unconditional_osc_proof_irrel
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    discharge_h_osc_unconditional I fam certs = discharge_h_osc_first_principles I fam certs :=
  rfl

/-- Test 2.11: Definitional proof-irrelevance equality between unconditional and first-principles decay. -/
theorem stress_unconditional_decay_proof_irrel
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    discharge_h_decay_unconditional I fam certs = discharge_h_decay_first_principles I fam certs :=
  rfl

/-- Test 2.12: Definitional proof-irrelevance equality between unconditional and first-principles tower. -/
theorem stress_unconditional_tower_proof_irrel
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    discharge_h_tower_unconditional I fam certs = discharge_h_tower_first_principles I fam certs :=
  rfl

/-- Test 2.13: Definitional proof-irrelevance equality between unconditional and first-principles aa. -/
theorem stress_unconditional_aa_proof_irrel
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    discharge_h_aa_unconditional I fam certs = discharge_h_aa_first_principles I fam certs :=
  rfl

/- =============================================================================
   SUITE 3: STABILITY UNDER SHRUNK / PERTURBED NORMAL CHART FAMILIES
   Tests calling all 11 declarations on scaled chart families (r' = r_norm / 2).
   ============================================================================= -/

/-- Helper construction: Shrunk chart family at half the original radius. -/
noncomputable def fam_half (fam : UniformNormalChartFamily I (M := M)) :
    UniformNormalChartFamily I (M := M) :=
  uniformNormalChartFamily_shrink I fam (fam.r_norm / 2)
    (half_pos fam.r_norm_pos) (half_le_self fam.r_norm_pos.le)

/-- Helper construction: Shrunk certificates matching shrunk chart family. -/
theorem certs_half (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    UniformNormalChartCertificates I (fam_half I fam) :=
  uniformNormalChartCertificates_shrink I fam certs (fam.r_norm / 2)
    (half_pos fam.r_norm_pos) (half_le_self fam.r_norm_pos.le)

/-- Test 3.1: Shrunk chart family satisfies h_weitz_unconditional. -/
theorem stress_shrink_weitz
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
  discharge_h_weitz_unconditional I (fam_half I fam) (certs_half I fam certs)

/-- Test 3.2: Shrunk chart family satisfies h_hit_exit_unconditional. -/
theorem stress_shrink_hit_exit
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.HitExitProperty I M :=
  discharge_h_hit_exit_unconditional I (fam_half I fam) (certs_half I fam certs)

/-- Test 3.3: Shrunk chart family satisfies h_osc_unconditional. -/
theorem stress_shrink_osc
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CollarOscillationProperty I M :=
  discharge_h_osc_unconditional I (fam_half I fam) (certs_half I fam certs)

/-- Test 3.4: Shrunk chart family satisfies h_decay_unconditional. -/
theorem stress_shrink_decay
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CylinderEnergyDecayProperty I M :=
  discharge_h_decay_unconditional I (fam_half I fam) (certs_half I fam certs)

/-- Test 3.5: Shrunk chart family satisfies h_decay_unconditional (pow_nat alias). -/
theorem stress_shrink_decay_pow_nat
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CylinderEnergyDecayProperty I M :=
  discharge_h_decay_unconditional I (fam_half I fam) (certs_half I fam certs)

/-- Test 3.6: Shrunk chart family satisfies h_punc_unconditional. -/
theorem stress_shrink_punc
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      Analysis.WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {p}) :=
  discharge_h_punc_unconditional I (fam_half I fam) (certs_half I fam certs) u p hu h_energy

/-- Test 3.7: Shrunk chart family satisfies discharge_removal_of_singularities_unconditional. -/
theorem stress_shrink_removal [T2Space M]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  discharge_removal_of_singularities_unconditional I (fam_half I fam) (certs_half I fam certs) u p h_jhol h_energy

/-- Test 3.8: Shrunk chart family satisfies h_tower_unconditional. -/
theorem stress_shrink_tower
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) (n : ℕ) :
    ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω :=
  discharge_h_tower_unconditional I (fam_half I fam) (certs_half I fam certs) u Ω hΩ h_weak n

/-- Test 3.9: Shrunk chart family satisfies discharge_nonlinear_elliptic_bootstrap_unconditional. -/
theorem stress_shrink_bootstrap
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I ∞ u Ω :=
  discharge_nonlinear_elliptic_bootstrap_unconditional I (fam_half I fam) (certs_half I fam certs) u Ω hΩ h_weak

/-- Test 3.10: Shrunk chart family satisfies h_aa_unconditional. -/
theorem stress_shrink_aa
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω :=
  discharge_h_aa_unconditional I (fam_half I fam) (certs_half I fam certs) u_seq Ω h_open h_jhol h_grad_bdd

/-- Test 3.11: Shrunk chart family satisfies discharge_local_smooth_compactness_of_arzela_ascoli_unconditional. -/
theorem stress_shrink_local_compactness
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω :=
  discharge_local_smooth_compactness_of_arzela_ascoli_unconditional I (fam_half I fam) (certs_half I fam certs)
    u_seq Ω h_open h_jhol h_grad_bdd

/- =============================================================================
   SUITE 4: PARAMETER VARIATIONS ACROSS CONTINUOUS AND DISCRETE DOMAINS
   Tests varied centers, radii, tower orders, domain geometries, and exponent types.
   ============================================================================= -/

/-- Test 4.1: h_osc_unconditional at origin center 0 with radii (1, 10) for zero energy. -/
theorem stress_param_osc_zero_center
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_zero : energyMeasure I u (annulus_at 0 1 10) = 0) :
    ∃ C > 0, ∀ z₁ ∈ annulus_at 0 (2 * 1) (10 / 2), ∀ z₂ ∈ annulus_at 0 (2 * 1) (10 / 2),
      dist (u z₁) (u z₂) ≤ C * Real.sqrt (energyMeasure I u (annulus_at 0 1 10)) := by
  obtain ⟨C, ε, hC, hε, h_osc⟩ := discharge_h_osc_unconditional I fam certs
  have h_lt : energyMeasure I u (annulus_at 0 1 10) < ε := by linarith
  exact ⟨C, hC, h_osc u 0 1 10 (by norm_num) (by norm_num) hu h_lt⟩

/-- Test 4.2: h_osc_unconditional at offset center (1 + 2I) with radii (0.1, 2.0) for zero energy. -/
theorem stress_param_osc_offset_center
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_zero : energyMeasure I u (annulus_at (1 + 2 * Complex.I) 0.1 2.0) = 0) :
    ∃ C > 0, ∀ z₁ ∈ annulus_at (1 + 2 * Complex.I) (2 * 0.1) (2.0 / 2),
    ∀ z₂ ∈ annulus_at (1 + 2 * Complex.I) (2 * 0.1) (2.0 / 2),
      dist (u z₁) (u z₂) ≤ C * Real.sqrt (energyMeasure I u (annulus_at (1 + 2 * Complex.I) 0.1 2.0)) := by
  obtain ⟨C, ε, hC, hε, h_osc⟩ := discharge_h_osc_unconditional I fam certs
  have h_lt : energyMeasure I u (annulus_at (1 + 2 * Complex.I) 0.1 2.0) < ε := by linarith
  exact ⟨C, hC, h_osc u (1 + 2 * Complex.I) 0.1 2.0 (by norm_num) (by norm_num) hu h_lt⟩

/-- Test 4.3: h_decay_unconditional on dyadic intervals (1 < 2 < 4 < 8) for zero energy. -/
theorem stress_param_decay_dyadic_radii
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (center : ℂ)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_zero : energyMeasure I u (annulus_at center 1 8) = 0) :
    ∃ (C₀ : ℝ), 0 < C₀ ∧ ∃ (a_decay : ℝ), 0 < a_decay ∧
      energyMeasure I u (annulus_at center 2 4) ≤
        C₀ * ((1 / 2 : ℝ)^a_decay + (4 / 8 : ℝ)^a_decay) * energyMeasure I u (annulus_at center 1 8) := by
  obtain ⟨C₀, a_decay, ε, hC, ha, hε, h_decay⟩ := discharge_h_decay_unconditional I fam certs
  have h_lt : energyMeasure I u (annulus_at center 1 8) < ε := by linarith
  exact ⟨C₀, hC, a_decay, ha, h_decay u center 1 8 (by norm_num) (by norm_num) hu h_lt 2 4
    (by norm_num) (by norm_num) (by norm_num)⟩

/-- Test 4.4: h_decay_unconditional (pow_nat alias) on dyadic intervals (1 < 2 < 4 < 8). -/
theorem stress_param_decay_pow_nat_dyadic
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (center : ℂ)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_zero : energyMeasure I u (annulus_at center 1 8) = 0) :
    ∃ (C₀ : ℝ), 0 < C₀ ∧ ∃ (a_decay : ℝ), 0 < a_decay ∧
      energyMeasure I u (annulus_at center 2 4) ≤
        C₀ * ((1 / 2 : ℝ)^a_decay + (4 / 8 : ℝ)^a_decay) * energyMeasure I u (annulus_at center 1 8) :=
  stress_param_decay_dyadic_radii I fam certs u center hu h_zero

/-- Test 4.5: Mathematical equivalence of real exponent 1 and natural exponent 1 factors. -/
theorem stress_param_decay_exponents_agree (r r₁ r₂ R : ℝ) :
    (r / r₁)^(1 : ℝ) + (r₂ / R)^(1 : ℝ) = (r / r₁)^1 + (r₂ / R)^1 := by
  rw [Real.rpow_one, Real.rpow_one, pow_one, pow_one]

/-- Test 4.6: h_tower_unconditional at base order n = 0. -/
theorem stress_param_tower_order_0
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I (0 : WithTop ℕ∞) u Ω :=
  discharge_h_tower_unconditional I fam certs u Ω hΩ h_weak 0

/-- Test 4.7: h_tower_unconditional at order n = 1. -/
theorem stress_param_tower_order_1
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I (1 : WithTop ℕ∞) u Ω :=
  discharge_h_tower_unconditional I fam certs u Ω hΩ h_weak 1

/-- Test 4.8: h_tower_unconditional at order n = 2. -/
theorem stress_param_tower_order_2
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I (2 : WithTop ℕ∞) u Ω :=
  discharge_h_tower_unconditional I fam certs u Ω hΩ h_weak 2

/-- Test 4.9: h_tower_unconditional at order n = 3. -/
theorem stress_param_tower_order_3
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I (3 : WithTop ℕ∞) u Ω :=
  discharge_h_tower_unconditional I fam certs u Ω hΩ h_weak 3

/-- Test 4.10: h_tower_unconditional at order n = 5. -/
theorem stress_param_tower_order_5
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I (5 : WithTop ℕ∞) u Ω :=
  discharge_h_tower_unconditional I fam certs u Ω hΩ h_weak 5

/-- Test 4.11: h_tower_unconditional at order n = 10. -/
theorem stress_param_tower_order_10
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I (10 : WithTop ℕ∞) u Ω :=
  discharge_h_tower_unconditional I fam certs u Ω hΩ h_weak 10

/-- Test 4.12: h_tower_unconditional at high order n = 100. -/
theorem stress_param_tower_order_100
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I (100 : WithTop ℕ∞) u Ω :=
  discharge_h_tower_unconditional I fam certs u Ω hΩ h_weak 100

/-- Test 4.13: h_tower_unconditional at extreme order n = 1000. -/
theorem stress_param_tower_order_1000
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I (1000 : WithTop ℕ∞) u Ω :=
  discharge_h_tower_unconditional I fam certs u Ω hΩ h_weak 1000

/-- Test 4.14: h_tower_unconditional universally quantified over all n : ℕ. -/
theorem stress_param_tower_all_nat
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) :
    ∀ (n : ℕ), ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω :=
  fun n => discharge_h_tower_unconditional I fam certs u Ω hΩ h_weak n

/-- Test 4.15: Order downgrade: Regularity at order 100 implies regularity at order 50. -/
theorem stress_param_tower_downgrade_100_to_50
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I (50 : WithTop ℕ∞) u Ω := by
  have h100 := discharge_h_tower_unconditional I fam certs u Ω hΩ h_weak 100
  exact h100.of_le (by norm_num)

/-- Test 4.16: Domain variation: h_tower_unconditional on empty domain Ω = ∅. -/
theorem stress_param_domain_empty_tower
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (h_weak : Analysis.WeakJHolomorphicOn I u ∅) (n : ℕ) :
    ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u ∅ :=
  discharge_h_tower_unconditional I fam certs u ∅ isOpen_empty h_weak n

/-- Test 4.17: Domain variation: nonlinear_elliptic_bootstrap_unconditional on empty domain Ω = ∅. -/
theorem stress_param_domain_empty_bootstrap
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (h_weak : Analysis.WeakJHolomorphicOn I u ∅) :
    ContMDiffOn I_CP1 I ∞ u ∅ :=
  discharge_nonlinear_elliptic_bootstrap_unconditional I fam certs u ∅ isOpen_empty h_weak

/-- Test 4.18: Domain variation: h_aa_unconditional on empty domain Ω = ∅. -/
theorem stress_param_domain_empty_aa
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u_seq : ℕ → (CP1 → M)) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim ∅ := by
  have h_jhol : ∀ n : ℕ, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) ∅ := by
    intro n
    exact ⟨contMDiffOn_empty, fun _ hz => False.elim hz⟩
  have h_grad : ∀ K ⊆ (∅ : Set CP1), IsCompact K → ∃ C > 0, ∀ (n : ℕ), ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C := by
    intro K hK _
    rw [subset_empty_iff.mp hK]
    exact ⟨1, zero_lt_one, fun _ z hz => False.elim hz⟩
  exact discharge_h_aa_unconditional I fam certs u_seq ∅ isOpen_empty h_jhol h_grad

/-- Test 4.19: Domain variation: h_tower_unconditional on entire sphere Ω = Set.univ. -/
theorem stress_param_domain_univ_tower
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (h_weak : Analysis.WeakJHolomorphicOn I u Set.univ) (n : ℕ) :
    ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Set.univ :=
  discharge_h_tower_unconditional I fam certs u Set.univ isOpen_univ h_weak n

/-- Test 4.20: Domain variation: nonlinear_elliptic_bootstrap_unconditional on entire sphere Ω = Set.univ. -/
theorem stress_param_domain_univ_bootstrap
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (h_weak : Analysis.WeakJHolomorphicOn I u Set.univ) :
    ContMDiffOn I_CP1 I ∞ u Set.univ :=
  discharge_nonlinear_elliptic_bootstrap_unconditional I fam certs u Set.univ isOpen_univ h_weak

/-- Test 4.21: Domain variation: h_tower_unconditional on punctured sphere Ω = punctured_sphere {p}. -/
theorem stress_param_domain_punctured_sphere_tower
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (p : CP1)
    (h_weak : Analysis.WeakJHolomorphicOn I u (punctured_sphere {p})) (n : ℕ) :
    ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u (punctured_sphere {p}) :=
  discharge_h_tower_unconditional I fam certs u (punctured_sphere {p}) (Analysis.isOpen_punctured_sphere p) h_weak n

/-- Test 4.22: Domain variation: nonlinear_elliptic_bootstrap_unconditional on punctured sphere. -/
theorem stress_param_domain_punctured_sphere_bootstrap
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (p : CP1)
    (h_weak : Analysis.WeakJHolomorphicOn I u (punctured_sphere {p})) :
    ContMDiffOn I_CP1 I ∞ u (punctured_sphere {p}) :=
  discharge_nonlinear_elliptic_bootstrap_unconditional I fam certs u (punctured_sphere {p}) (Analysis.isOpen_punctured_sphere p) h_weak

end GeneralTarget

/- =============================================================================
   SUITE 5: UNIVERSE POLYMORPHISM & MULTI-UNIVERSE STRESS
   Tests all master unconditional declarations across independent universe variables.
   ============================================================================= -/

section UniverseStress

universe u_m u_e

variable {E_poly : Type u_e} [NormedAddCommGroup E_poly] [NormedSpace ℝ E_poly] [FiniteDimensional ℝ E_poly]
variable {H_poly : Type*} [TopologicalSpace H_poly] (I_poly : ModelWithCorners ℝ E_poly H_poly)
variable {M_poly : Type u_m} [MetricSpace M_poly] [ChartedSpace H_poly M_poly] [IsManifold I_poly ∞ M_poly] [CompactSpace M_poly]
variable [tgt_poly : ClosedTameTarget I_poly M_poly]

/-- Test 5.1: Universe-polymorphic h_weitz_unconditional. -/
theorem stress_poly_weitz
    (fam : UniformNormalChartFamily I_poly (M := M_poly))
    (certs : UniformNormalChartCertificates I_poly fam) :
    ∃ (b c : ℝ), 0 ≤ b ∧ c = 0 ∧
      ∀ (u : CP1 → M_poly),
        JHolomorphicOn (I := I_poly) (I_dom := I_CP1) u Set.univ →
        ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I_poly u (stereo_chart.symm w)) ∧
        ∀ (w : ℂ),
          ∃ (hessNorm : ℝ) (curvTerm : ℝ),
            Analysis.laplacian2D (fun z => riemannianEnergyDensity I_poly u (stereo_chart.symm z)) w =
              hessNorm ^ 2 + curvTerm ∧
            |curvTerm| ≤
              b * (riemannianEnergyDensity I_poly u (stereo_chart.symm w)) ^ 2 +
              c * (riemannianEnergyDensity I_poly u (stereo_chart.symm w)) :=
  discharge_h_weitz_unconditional I_poly fam certs

/-- Test 5.2: Universe-polymorphic h_hit_exit_unconditional. -/
theorem stress_poly_hit_exit
    (fam : UniformNormalChartFamily I_poly (M := M_poly))
    (certs : UniformNormalChartCertificates I_poly fam) :
    Analysis.HitExitProperty I_poly M_poly :=
  discharge_h_hit_exit_unconditional I_poly fam certs

/-- Test 5.3: Universe-polymorphic h_osc_unconditional. -/
theorem stress_poly_osc
    (fam : UniformNormalChartFamily I_poly (M := M_poly))
    (certs : UniformNormalChartCertificates I_poly fam) :
    Analysis.CollarOscillationProperty I_poly M_poly :=
  discharge_h_osc_unconditional I_poly fam certs

/-- Test 5.4: Universe-polymorphic h_decay_unconditional. -/
theorem stress_poly_decay
    (fam : UniformNormalChartFamily I_poly (M := M_poly))
    (certs : UniformNormalChartCertificates I_poly fam) :
    Analysis.CylinderEnergyDecayProperty I_poly M_poly :=
  discharge_h_decay_unconditional I_poly fam certs

/-- Test 5.5: Universe-polymorphic h_punc_unconditional. -/
theorem stress_poly_punc
    (fam : UniformNormalChartFamily I_poly (M := M_poly))
    (certs : UniformNormalChartCertificates I_poly fam) :
    ∀ (u : CP1 → M_poly) (p : CP1)
      (_hu : JHolomorphicOn (I := I_poly) (I_dom := I_CP1) u (punctured_sphere {p}))
      (_h_energy : energyMeasureExtended I_poly u (punctured_sphere {p}) ≠ ⊤),
      ∃ (u_ext : CP1 → M_poly),
        Continuous u_ext ∧
        Analysis.WeakJHolomorphicOn I_poly u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p}) :=
  discharge_h_punc_unconditional I_poly fam certs

/-- Test 5.6: Universe-polymorphic discharge_removal_of_singularities_unconditional. -/
theorem stress_poly_removal [T2Space M_poly]
    (fam : UniformNormalChartFamily I_poly (M := M_poly))
    (certs : UniformNormalChartCertificates I_poly fam)
    (u : CP1 → M_poly) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I_poly) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I_poly u (punctured_sphere {p}) ≠ ⊤) :
    ∃! (u_smooth : CP1 → M_poly),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I_poly) (I_dom := I_CP1) u_smooth Set.univ :=
  discharge_removal_of_singularities_unconditional I_poly fam certs u p h_jhol h_energy

/-- Test 5.7: Universe-polymorphic h_tower_unconditional. -/
theorem stress_poly_tower
    (fam : UniformNormalChartFamily I_poly (M := M_poly))
    (certs : UniformNormalChartCertificates I_poly fam) :
    ∀ (u : CP1 → M_poly) (Ω : Set CP1) (_hΩ : IsOpen Ω)
      (_h_weak : Analysis.WeakJHolomorphicOn I_poly u Ω) (n : ℕ),
      ContMDiffOn I_CP1 I_poly (n : WithTop ℕ∞) u Ω :=
  discharge_h_tower_unconditional I_poly fam certs

/-- Test 5.8: Universe-polymorphic discharge_nonlinear_elliptic_bootstrap_unconditional. -/
theorem stress_poly_bootstrap
    (fam : UniformNormalChartFamily I_poly (M := M_poly))
    (certs : UniformNormalChartCertificates I_poly fam)
    (u : CP1 → M_poly) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I_poly u Ω) :
    ContMDiffOn I_CP1 I_poly ∞ u Ω :=
  discharge_nonlinear_elliptic_bootstrap_unconditional I_poly fam certs u Ω hΩ h_weak

/-- Test 5.9: Universe-polymorphic h_aa_unconditional. -/
theorem stress_poly_aa
    (fam : UniformNormalChartFamily I_poly (M := M_poly))
    (certs : UniformNormalChartCertificates I_poly fam) :
    ∀ (u_seq : ℕ → (CP1 → M_poly)) (Ω : Set CP1) (_h_open : IsOpen Ω)
      (_h_jhol : ∀ (n : ℕ), JHolomorphicOn (I := I_poly) (I_dom := I_CP1) (u_seq n) Ω)
      (_h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ (n : ℕ), ∀ z ∈ K, riemannianEnergyDensity I_poly (u_seq n) z ≤ C),
      ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M_poly),
        SmoothLocalConvergesOn I_poly (fun n => u_seq (σ.1 n)) u_lim Ω :=
  discharge_h_aa_unconditional I_poly fam certs

end UniverseStress

/- =============================================================================
   SUITE 6: DEGENERATE, EDGE, AND LIMIT CASES
   Tests constant maps, constant sequences, and canonical CP1 model.
   ============================================================================= -/

section EdgeCases

universe u v

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
variable [tgt : ClosedTameTarget I M]

/-- Test 6.1: Constant curves satisfy companion Bochner decomposition with b = 0, c = 0. -/
theorem stress_edge_const_weitz (fam : UniformNormalChartFamily I (M := M)) (x₀ : M) :
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

/-- Test 6.2: Constant curves satisfy h_osc_unconditional with vanishing separation. -/
theorem stress_edge_const_osc
    (fam : UniformNormalChartFamily I (M := M))
    (_certs : UniformNormalChartCertificates I fam)
    (x₀ : M) (a : ℂ) (r R : ℝ) (_hr : 0 < r) :
    ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
      dist ((fun _ : CP1 => x₀) z₁) ((fun _ : CP1 => x₀) z₂) ≤
        4 * Real.sqrt (energyMeasure I (fun _ => x₀) (annulus_at a r R)) :=
  discharge_h_osc_const I fam x₀ a r R

/-- Test 6.3: Constant curves satisfy h_decay_unconditional with vanishing energy. -/
theorem stress_edge_const_decay
    (fam : UniformNormalChartFamily I (M := M))
    (_certs : UniformNormalChartCertificates I fam)
    (x₀ : M) (center : ℂ) (r R : ℝ) (_hr : 0 < r) (_h2rR : 2 * r < R) (r₁ r₂ : ℝ)
    (hr₁ : r < r₁) (hr₁₂ : r₁ < r₂) (hr₂ : r₂ < R) :
    energyMeasure I (fun _ => x₀) (annulus_at center r₁ r₂) ≤
      1 * ((r / r₁)^(1 : ℝ) + (r₂ / R)^(1 : ℝ)) * energyMeasure I (fun _ => x₀) (annulus_at center r R) :=
  discharge_h_decay_const I fam x₀ center r R r₁ r₂ hr₁ hr₁₂ hr₂

/-- Test 6.4: Constant curves satisfy h_punc_unconditional extending trivially. -/
theorem stress_edge_const_punc
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (x₀ : M) (p : CP1) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      Analysis.WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext (fun _ => x₀) (punctured_sphere {p}) := by
  have hu : JHolomorphicOn (I := I) (I_dom := I_CP1) (fun _ => x₀) (punctured_sphere {p}) :=
    jHolomorphicOn_const I x₀ (punctured_sphere {p})
  have he : energyMeasureExtended I (fun _ => x₀) (punctured_sphere {p}) ≠ ⊤ := by
    rw [Analysis.energyMeasureExtended_const]
    exact ENNReal.zero_ne_top
  exact discharge_h_punc_unconditional I fam certs (fun _ => x₀) p hu he

/-- Test 6.5: Constant curves satisfy h_tower_unconditional for all orders n. -/
theorem stress_edge_const_tower
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (x₀ : M) (Ω : Set CP1) (hΩ : IsOpen Ω) (n : ℕ) :
    ContMDiffOn I_CP1 I (n : WithTop ℕ∞) (fun _ => x₀) Ω :=
  discharge_h_tower_unconditional I fam certs (fun _ => x₀) Ω hΩ (Analysis.weakJHolomorphicOn_const I x₀ Ω) n

/-- Test 6.6: Constant curves satisfy nonlinear_elliptic_bootstrap_unconditional. -/
theorem stress_edge_const_bootstrap
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (x₀ : M) (Ω : Set CP1) (hΩ : IsOpen Ω) :
    ContMDiffOn I_CP1 I ∞ (fun _ => x₀) Ω :=
  discharge_nonlinear_elliptic_bootstrap_unconditional I fam certs (fun _ => x₀) Ω hΩ (Analysis.weakJHolomorphicOn_const I x₀ Ω)

/-- Test 6.7: Constant curves satisfy discharge_removal_of_singularities_unconditional. -/
theorem stress_edge_const_removal [T2Space M]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (x₀ : M) (p : CP1) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth (fun _ => x₀) (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ := by
  have h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) (fun _ => x₀) (punctured_sphere {p}) :=
    jHolomorphicOn_const I x₀ (punctured_sphere {p})
  have h_energy : energyMeasureExtended I (fun _ => x₀) (punctured_sphere {p}) ≠ ⊤ := by
    rw [Analysis.energyMeasureExtended_const]
    exact ENNReal.zero_ne_top
  exact discharge_removal_of_singularities_unconditional I fam certs (fun _ => x₀) p h_jhol h_energy

/-- Test 6.8: Constant sequences satisfy h_aa_unconditional. -/
theorem stress_edge_const_seq_aa
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (x₀ : M) (Ω : Set CP1) (h_open : IsOpen Ω) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => (fun _ : CP1 => x₀)) u_lim Ω := by
  have h_jhol : ∀ (n : ℕ), JHolomorphicOn (I := I) (I_dom := I_CP1) (fun _ : CP1 => x₀) Ω :=
    fun _ => jHolomorphicOn_const I x₀ Ω
  have h_grad : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ (n : ℕ), ∀ z ∈ K,
      riemannianEnergyDensity I (fun _ : CP1 => x₀) z ≤ C := by
    intro K _ _
    refine ⟨1, zero_lt_one, fun (n : ℕ) z _ => by
      rw [Analysis.riemannianEnergyDensity_const]
      exact zero_le_one⟩
  exact discharge_h_aa_unconditional I fam certs (fun (_ : ℕ) => (fun _ : CP1 => x₀)) Ω h_open h_jhol h_grad

/-- Test 6.9: Constant sequences satisfy local smooth compactness of Arzelà-Ascoli. -/
theorem stress_edge_const_seq_local_compactness
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (x₀ : M) (Ω : Set CP1) (h_open : IsOpen Ω) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => (fun _ : CP1 => x₀)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω := by
  have h_jhol : ∀ (n : ℕ), JHolomorphicOn (I := I) (I_dom := I_CP1) (fun _ : CP1 => x₀) Ω :=
    fun _ => jHolomorphicOn_const I x₀ Ω
  have h_grad : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ (n : ℕ), ∀ z ∈ K,
      riemannianEnergyDensity I (fun _ : CP1 => x₀) z ≤ C := by
    intro K _ _
    refine ⟨1, zero_lt_one, fun (n : ℕ) z _ => by
      rw [Analysis.riemannianEnergyDensity_const]
      exact zero_le_one⟩
  exact discharge_local_smooth_compactness_of_arzela_ascoli_unconditional I fam certs
    (fun (_ : ℕ) => (fun _ : CP1 => x₀)) Ω h_open h_jhol h_grad

end EdgeCases

/- =============================================================================
   SUITE 7: INTER-CERTIFICATE COUPLING & COMPOSITION
   Tests feeding certificates into downstream analytical theorems.
   ============================================================================= -/

section InterCertificateCoupling

universe u v

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
variable [tgt : ClosedTameTarget I M]

/-- Test 7.1: Coupling h_punc_unconditional with h_tower_unconditional.
Continuous weak extension across puncture extends to C^n regular map for all n. -/
theorem stress_coupling_punc_to_tower
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (n : ℕ) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {p}) := by
  obtain ⟨u_ext, h_cont, h_weak, h_eq⟩ := discharge_h_punc_unconditional I fam certs u p hu h_energy
  have h_tower := discharge_h_tower_unconditional I fam certs u_ext Set.univ isOpen_univ h_weak n
  exact ⟨u_ext, h_cont, h_tower, h_eq⟩

/-- Test 7.2: Coupling h_punc_unconditional with nonlinear_elliptic_bootstrap_unconditional.
Continuous weak extension across puncture extends to smooth C^∞ map. -/
theorem stress_coupling_punc_to_bootstrap
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      ContMDiffOn I_CP1 I ∞ u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {p}) := by
  obtain ⟨u_ext, h_cont, h_weak, h_eq⟩ := discharge_h_punc_unconditional I fam certs u p hu h_energy
  have h_smooth := discharge_nonlinear_elliptic_bootstrap_unconditional I fam certs u_ext Set.univ isOpen_univ h_weak
  exact ⟨u_ext, h_cont, h_smooth, h_eq⟩

/-- Test 7.3: Coupling h_punc_unconditional and h_tower_unconditional discharges removal_of_singularities. -/
theorem stress_coupling_punc_and_tower_to_removal [T2Space M]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  discharge_removal_of_singularities_unconditional I fam certs u p h_jhol h_energy

/-- Test 7.4: Coupling h_aa_unconditional feeds into local smooth compactness of Arzelà-Ascoli. -/
theorem stress_coupling_aa_to_local_compactness
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ (n : ℕ), ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω :=
  discharge_local_smooth_compactness_of_arzela_ascoli_unconditional I fam certs u_seq Ω h_open h_jhol h_grad_bdd

/-- Test 7.5: Coupling h_hit_exit_unconditional directly into sphere_energy_gap. -/
theorem stress_coupling_hit_exit_to_energy_gap
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∃ (ε_sph : ℝ), 0 < ε_sph ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ε_sph ≤ totalEnergy I u :=
  Analysis.sphere_energy_gap I (discharge_h_hit_exit_unconditional I fam certs)

/-- Test 7.6: Coupling h_weitz_unconditional directly into bochner_differential_inequality_c_zero. -/
theorem stress_coupling_weitz_to_bochner_c_zero
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∃ (b : ℝ), 0 ≤ b ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
      ∀ (w : ℂ),
        -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
          0 * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
        Analysis.laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w :=
  Analysis.bochner_differential_inequality_c_zero I (discharge_h_weitz_unconditional I fam certs)

end InterCertificateCoupling

end AdversarialM4Challenger1


/- =============================================================================
   SUITE 8: AUTOMATED KERNEL AXIOM CENSUS METAPROGRAM & COMPILER DIAGNOSTICS
   ============================================================================= -/

namespace AdversarialM4AxiomCensus

structure State where
  visited : Lean.NameSet := {}
  memo    : Lean.NameMap (Array Lean.Name) := {}

abbrev CensusM := ReaderT Lean.Environment (StateM State)

def getDirectConstants (ci : Lean.ConstantInfo) : Array Lean.Name := Id.run do
  let mut consts : Lean.NameSet := {}
  let addExpr (e : Lean.Expr) (s : Lean.NameSet) : Lean.NameSet :=
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

partial def collect (c : Lean.Name) : CensusM (Array Lean.Name) := do
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

elab "#adversarial_m4_c1_axiom_census" : command => do
  let env ← getEnv
  let startTime ← IO.monoMsNow

  let targetDecls : List (Lean.Name × String) := [
    -- 11 Section 6 Master Unconditional Declarations in GromovCompactness
    (`GromovCompactness.discharge_h_weitz_unconditional, "Library: Master unconditional h_weitz"),
    (`GromovCompactness.discharge_h_hit_exit_unconditional, "Library: Master unconditional h_hit_exit"),
    (`GromovCompactness.discharge_h_osc_unconditional, "Library: Master unconditional h_osc"),
    (`GromovCompactness.discharge_h_decay_unconditional, "Library: Conditional re-export h_decay"),
    (`GromovCompactness.discharge_h_punc_unconditional, "Library: Conditional re-export h_punc"),
    (`GromovCompactness.discharge_removal_of_singularities_unconditional, "Library: Master unconditional removal"),
    (`GromovCompactness.discharge_h_tower_unconditional, "Library: Master unconditional h_tower"),
    (`GromovCompactness.discharge_nonlinear_elliptic_bootstrap_unconditional, "Library: Master unconditional bootstrap"),
    (`GromovCompactness.discharge_h_aa_unconditional, "Library: Master unconditional h_aa"),
    (`GromovCompactness.discharge_local_smooth_compactness_of_arzela_ascoli_unconditional, "Library: Master unconditional local compactness"),

    -- Suite 1: Calling Conventions (22 tests)
    (`AdversarialM4Challenger1.stress_call_weitz_positional, "Suite 1: Weitz positional"),
    (`AdversarialM4Challenger1.stress_call_weitz_named, "Suite 1: Weitz named"),
    (`AdversarialM4Challenger1.stress_call_hit_exit_positional, "Suite 1: Hit-exit positional"),
    (`AdversarialM4Challenger1.stress_call_hit_exit_named, "Suite 1: Hit-exit named"),
    (`AdversarialM4Challenger1.stress_call_osc_positional, "Suite 1: Osc positional"),
    (`AdversarialM4Challenger1.stress_call_osc_named, "Suite 1: Osc named"),
    (`AdversarialM4Challenger1.stress_call_decay_positional, "Suite 1: Decay positional"),
    (`AdversarialM4Challenger1.stress_call_decay_named, "Suite 1: Decay named"),
    (`AdversarialM4Challenger1.stress_call_decay_pow_nat_positional, "Suite 1: Decay pow nat positional"),
    (`AdversarialM4Challenger1.stress_call_decay_pow_nat_named, "Suite 1: Decay pow nat named"),
    (`AdversarialM4Challenger1.stress_call_punc_positional, "Suite 1: Punc positional"),
    (`AdversarialM4Challenger1.stress_call_punc_named, "Suite 1: Punc named"),
    (`AdversarialM4Challenger1.stress_call_removal_positional, "Suite 1: Removal positional"),
    (`AdversarialM4Challenger1.stress_call_removal_named, "Suite 1: Removal named"),
    (`AdversarialM4Challenger1.stress_call_tower_positional, "Suite 1: Tower positional"),
    (`AdversarialM4Challenger1.stress_call_tower_named, "Suite 1: Tower named"),
    (`AdversarialM4Challenger1.stress_call_bootstrap_positional, "Suite 1: Bootstrap positional"),
    (`AdversarialM4Challenger1.stress_call_bootstrap_named, "Suite 1: Bootstrap named"),
    (`AdversarialM4Challenger1.stress_call_aa_positional, "Suite 1: AA positional"),
    (`AdversarialM4Challenger1.stress_call_aa_named, "Suite 1: AA named"),
    (`AdversarialM4Challenger1.stress_call_local_smooth_compactness_positional, "Suite 1: Local compactness positional"),
    (`AdversarialM4Challenger1.stress_call_local_smooth_compactness_named, "Suite 1: Local compactness named"),

    -- Suite 2: Functional Currying & Bridge Equivalence (13 tests)
    (`AdversarialM4Challenger1.stress_curried_osc, "Suite 2: Curried osc"),
    (`AdversarialM4Challenger1.stress_curried_decay, "Suite 2: Curried decay"),
    (`AdversarialM4Challenger1.stress_curried_decay_pow_nat, "Suite 2: Curried decay pow nat"),
    (`AdversarialM4Challenger1.stress_curried_punc, "Suite 2: Curried punc"),
    (`AdversarialM4Challenger1.stress_curried_tower, "Suite 2: Curried tower"),
    (`AdversarialM4Challenger1.stress_curried_aa, "Suite 2: Curried aa"),
    (`AdversarialM4Challenger1.stress_exists_bridge_tautology, "Suite 2: Bridge tautology"),
    (`AdversarialM4Challenger1.stress_unconditional_weitz_proof_irrel, "Suite 2: Weitz proof irrelevance"),
    (`AdversarialM4Challenger1.stress_unconditional_hit_exit_proof_irrel, "Suite 2: Hit exit proof irrelevance"),
    (`AdversarialM4Challenger1.stress_unconditional_osc_proof_irrel, "Suite 2: Osc proof irrelevance"),
    (`AdversarialM4Challenger1.stress_unconditional_decay_proof_irrel, "Suite 2: Decay proof irrelevance"),
    (`AdversarialM4Challenger1.stress_unconditional_tower_proof_irrel, "Suite 2: Tower proof irrelevance"),
    (`AdversarialM4Challenger1.stress_unconditional_aa_proof_irrel, "Suite 2: AA proof irrelevance"),

    -- Suite 3: Stability under Shrunk Chart Families (11 tests)
    (`AdversarialM4Challenger1.stress_shrink_weitz, "Suite 3: Shrink weitz"),
    (`AdversarialM4Challenger1.stress_shrink_hit_exit, "Suite 3: Shrink hit exit"),
    (`AdversarialM4Challenger1.stress_shrink_osc, "Suite 3: Shrink osc"),
    (`AdversarialM4Challenger1.stress_shrink_decay, "Suite 3: Shrink decay"),
    (`AdversarialM4Challenger1.stress_shrink_decay_pow_nat, "Suite 3: Shrink decay pow nat"),
    (`AdversarialM4Challenger1.stress_shrink_punc, "Suite 3: Shrink punc"),
    (`AdversarialM4Challenger1.stress_shrink_removal, "Suite 3: Shrink removal"),
    (`AdversarialM4Challenger1.stress_shrink_tower, "Suite 3: Shrink tower"),
    (`AdversarialM4Challenger1.stress_shrink_bootstrap, "Suite 3: Shrink bootstrap"),
    (`AdversarialM4Challenger1.stress_shrink_aa, "Suite 3: Shrink aa"),
    (`AdversarialM4Challenger1.stress_shrink_local_compactness, "Suite 3: Shrink local compactness"),

    -- Suite 4: Parameter Variations across Domains & Orders (22 tests)
    (`AdversarialM4Challenger1.stress_param_osc_zero_center, "Suite 4: Osc zero center"),
    (`AdversarialM4Challenger1.stress_param_osc_offset_center, "Suite 4: Osc offset center"),
    (`AdversarialM4Challenger1.stress_param_decay_dyadic_radii, "Suite 4: Decay dyadic radii"),
    (`AdversarialM4Challenger1.stress_param_decay_pow_nat_dyadic, "Suite 4: Decay pow nat dyadic"),
    (`AdversarialM4Challenger1.stress_param_decay_exponents_agree, "Suite 4: Decay exponents agree"),
    (`AdversarialM4Challenger1.stress_param_tower_order_0, "Suite 4: Tower order 0"),
    (`AdversarialM4Challenger1.stress_param_tower_order_1, "Suite 4: Tower order 1"),
    (`AdversarialM4Challenger1.stress_param_tower_order_2, "Suite 4: Tower order 2"),
    (`AdversarialM4Challenger1.stress_param_tower_order_3, "Suite 4: Tower order 3"),
    (`AdversarialM4Challenger1.stress_param_tower_order_5, "Suite 4: Tower order 5"),
    (`AdversarialM4Challenger1.stress_param_tower_order_10, "Suite 4: Tower order 10"),
    (`AdversarialM4Challenger1.stress_param_tower_order_100, "Suite 4: Tower order 100"),
    (`AdversarialM4Challenger1.stress_param_tower_order_1000, "Suite 4: Tower order 1000"),
    (`AdversarialM4Challenger1.stress_param_tower_all_nat, "Suite 4: Tower all nat"),
    (`AdversarialM4Challenger1.stress_param_tower_downgrade_100_to_50, "Suite 4: Tower downgrade 100 to 50"),
    (`AdversarialM4Challenger1.stress_param_domain_empty_tower, "Suite 4: Empty domain tower"),
    (`AdversarialM4Challenger1.stress_param_domain_empty_bootstrap, "Suite 4: Empty domain bootstrap"),
    (`AdversarialM4Challenger1.stress_param_domain_empty_aa, "Suite 4: Empty domain aa"),
    (`AdversarialM4Challenger1.stress_param_domain_univ_tower, "Suite 4: Univ domain tower"),
    (`AdversarialM4Challenger1.stress_param_domain_univ_bootstrap, "Suite 4: Univ domain bootstrap"),
    (`AdversarialM4Challenger1.stress_param_domain_punctured_sphere_tower, "Suite 4: Punctured domain tower"),
    (`AdversarialM4Challenger1.stress_param_domain_punctured_sphere_bootstrap, "Suite 4: Punctured domain bootstrap"),

    -- Suite 5: Universe Polymorphism (9 tests)
    (`AdversarialM4Challenger1.stress_poly_weitz, "Suite 5: Poly weitz"),
    (`AdversarialM4Challenger1.stress_poly_hit_exit, "Suite 5: Poly hit exit"),
    (`AdversarialM4Challenger1.stress_poly_osc, "Suite 5: Poly osc"),
    (`AdversarialM4Challenger1.stress_poly_decay, "Suite 5: Poly decay"),
    (`AdversarialM4Challenger1.stress_poly_punc, "Suite 5: Poly punc"),
    (`AdversarialM4Challenger1.stress_poly_removal, "Suite 5: Poly removal"),
    (`AdversarialM4Challenger1.stress_poly_tower, "Suite 5: Poly tower"),
    (`AdversarialM4Challenger1.stress_poly_bootstrap, "Suite 5: Poly bootstrap"),
    (`AdversarialM4Challenger1.stress_poly_aa, "Suite 5: Poly aa"),

    -- Suite 6: Degenerate, Edge, and Limit Cases (9 tests)
    (`AdversarialM4Challenger1.stress_edge_const_weitz, "Suite 6: Const weitz"),
    (`AdversarialM4Challenger1.stress_edge_const_osc, "Suite 6: Const osc"),
    (`AdversarialM4Challenger1.stress_edge_const_decay, "Suite 6: Const decay"),
    (`AdversarialM4Challenger1.stress_edge_const_punc, "Suite 6: Const punc"),
    (`AdversarialM4Challenger1.stress_edge_const_tower, "Suite 6: Const tower"),
    (`AdversarialM4Challenger1.stress_edge_const_bootstrap, "Suite 6: Const bootstrap"),
    (`AdversarialM4Challenger1.stress_edge_const_removal, "Suite 6: Const removal"),
    (`AdversarialM4Challenger1.stress_edge_const_seq_aa, "Suite 6: Const seq aa"),
    (`AdversarialM4Challenger1.stress_edge_const_seq_local_compactness, "Suite 6: Const seq local compactness"),

    -- Suite 7: Inter-Certificate Coupling & Composition (6 tests)
    (`AdversarialM4Challenger1.stress_coupling_punc_to_tower, "Suite 7: Punc to tower"),
    (`AdversarialM4Challenger1.stress_coupling_punc_to_bootstrap, "Suite 7: Punc to bootstrap"),
    (`AdversarialM4Challenger1.stress_coupling_punc_and_tower_to_removal, "Suite 7: Punc and tower to removal"),
    (`AdversarialM4Challenger1.stress_coupling_aa_to_local_compactness, "Suite 7: AA to local compactness"),
    (`AdversarialM4Challenger1.stress_coupling_hit_exit_to_energy_gap, "Suite 7: Hit exit to energy gap"),
    (`AdversarialM4Challenger1.stress_coupling_weitz_to_bochner_c_zero, "Suite 7: Weitz to Bochner c=0")
  ]

  logInfo m!"================================================================================"
  logInfo m!"Adversarial M4 Challenger 1: Kernel Axiom Census & Stress Test Audit"
  logInfo m!"Total checked declarations: {targetDecls.length}"
  logInfo m!"================================================================================"

  let mut state : State := {}
  let mut sorryFound : List Lean.Name := []
  let mut nonstandardFound : List (Lean.Name × Lean.Name) := []
  let mut missingDecls : List Lean.Name := []
  let mut cleanCount : Nat := 0

  for (name, desc) in targetDecls do
    if let some _ := env.find? name then
      let (axs, nextState) := (collect name).run env |>.run state
      state := nextState
      let hasSorry := axs.contains ``sorryAx
      let mut badAxs : List Lean.Name := []
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
  logInfo m!"Adversarial M4 Audit finished in {elapsedMs} ms"
  logInfo m!"Total checked: {targetDecls.length} | Clean: {cleanCount} | Missing: {missingDecls.length} | Sorry: {sorryFound.length} | Nonstandard: {nonstandardFound.length}"
  logInfo m!"================================================================================"

  if !missingDecls.isEmpty || !sorryFound.isEmpty || !nonstandardFound.isEmpty then
    throwError m!"Adversarial M4 Challenger 1 Census FAILED: {missingDecls.length} missing, {sorryFound.length} sorryAx, {nonstandardFound.length} nonstandard axioms"
  else
    logInfo m!"STATUS: CLEAN (0 sorryAx dependencies)"
    logInfo m!"All declarations depend strictly on standard axioms: [propext, Classical.choice, Quot.sound]"

#adversarial_m4_c1_axiom_census

end AdversarialM4AxiomCensus


open AdversarialM4Challenger1

/- =============================================================================
   DIRECT COMPILER #print axioms VERIFICATION CHECKS
   ============================================================================= -/

-- Suite 1
#print axioms stress_call_weitz_positional
#print axioms stress_call_weitz_named
#print axioms stress_call_hit_exit_positional
#print axioms stress_call_hit_exit_named
#print axioms stress_call_osc_positional
#print axioms stress_call_osc_named
#print axioms stress_call_decay_positional
#print axioms stress_call_decay_named
#print axioms stress_call_decay_pow_nat_positional
#print axioms stress_call_decay_pow_nat_named
#print axioms stress_call_punc_positional
#print axioms stress_call_punc_named
#print axioms stress_call_removal_positional
#print axioms stress_call_removal_named
#print axioms stress_call_tower_positional
#print axioms stress_call_tower_named
#print axioms stress_call_bootstrap_positional
#print axioms stress_call_bootstrap_named
#print axioms stress_call_aa_positional
#print axioms stress_call_aa_named
#print axioms stress_call_local_smooth_compactness_positional
#print axioms stress_call_local_smooth_compactness_named

-- Suite 2
#print axioms stress_curried_osc
#print axioms stress_curried_decay
#print axioms stress_curried_decay_pow_nat
#print axioms stress_curried_punc
#print axioms stress_curried_tower
#print axioms stress_curried_aa
#print axioms stress_exists_bridge_tautology
#print axioms stress_unconditional_weitz_proof_irrel
#print axioms stress_unconditional_hit_exit_proof_irrel
#print axioms stress_unconditional_osc_proof_irrel
#print axioms stress_unconditional_decay_proof_irrel
#print axioms stress_unconditional_tower_proof_irrel
#print axioms stress_unconditional_aa_proof_irrel

-- Suite 3
#print axioms stress_shrink_weitz
#print axioms stress_shrink_hit_exit
#print axioms stress_shrink_osc
#print axioms stress_shrink_decay
#print axioms stress_shrink_decay_pow_nat
#print axioms stress_shrink_punc
#print axioms stress_shrink_removal
#print axioms stress_shrink_tower
#print axioms stress_shrink_bootstrap
#print axioms stress_shrink_aa
#print axioms stress_shrink_local_compactness

-- Suite 4
#print axioms stress_param_osc_zero_center
#print axioms stress_param_osc_offset_center
#print axioms stress_param_decay_dyadic_radii
#print axioms stress_param_decay_pow_nat_dyadic
#print axioms stress_param_decay_exponents_agree
#print axioms stress_param_tower_order_0
#print axioms stress_param_tower_order_1
#print axioms stress_param_tower_order_2
#print axioms stress_param_tower_order_3
#print axioms stress_param_tower_order_5
#print axioms stress_param_tower_order_10
#print axioms stress_param_tower_order_100
#print axioms stress_param_tower_order_1000
#print axioms stress_param_tower_all_nat
#print axioms stress_param_tower_downgrade_100_to_50
#print axioms stress_param_domain_empty_tower
#print axioms stress_param_domain_empty_bootstrap
#print axioms stress_param_domain_empty_aa
#print axioms stress_param_domain_univ_tower
#print axioms stress_param_domain_univ_bootstrap
#print axioms stress_param_domain_punctured_sphere_tower
#print axioms stress_param_domain_punctured_sphere_bootstrap

-- Suite 5
#print axioms stress_poly_weitz
#print axioms stress_poly_hit_exit
#print axioms stress_poly_osc
#print axioms stress_poly_decay
#print axioms stress_poly_punc
#print axioms stress_poly_removal
#print axioms stress_poly_tower
#print axioms stress_poly_bootstrap
#print axioms stress_poly_aa

-- Suite 6
#print axioms stress_edge_const_weitz
#print axioms stress_edge_const_osc
#print axioms stress_edge_const_decay
#print axioms stress_edge_const_punc
#print axioms stress_edge_const_tower
#print axioms stress_edge_const_bootstrap
#print axioms stress_edge_const_removal
#print axioms stress_edge_const_seq_aa
#print axioms stress_edge_const_seq_local_compactness

-- Suite 7
#print axioms stress_coupling_punc_to_tower
#print axioms stress_coupling_punc_to_bootstrap
#print axioms stress_coupling_punc_and_tower_to_removal
#print axioms stress_coupling_aa_to_local_compactness
#print axioms stress_coupling_hit_exit_to_energy_gap
#print axioms stress_coupling_weitz_to_bochner_c_zero
