/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Phase 5 Milestone 3 Test Suite)
-/
import GromovCompactness
import GromovCompactness.Analysis.EllipticBootstrap
import GromovCompactness.Analysis.SingularityRemoval
import GromovCompactness.Analysis.Monotonicity
import GromovCompactness.Analysis.Bochner
import GromovCompactness.Analysis.EpsilonRegularity
import GromovCompactness.Compactness.Measures
import GromovCompactness.Compactness.Concentration
import GromovCompactness.Bubbling.LocalTree
import GromovCompactness.Compactness.Assembly
import GromovCompactness.Compactness.Stabilize
import GromovCompactness.Compactness.GenusZero
import GromovCompactness.Extensions.ModuliSpace

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology Classical
open Metric Set MeasureTheory Filter GromovCompactness Classical
open GromovCompactness.Analysis GromovCompactness.Assembly GromovCompactness.Compactness
open GromovCompactness.Bubbling GromovCompactness.Extensions

namespace GromovCompactness.ChallengeMilestone3Phase5

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [ClosedTameTarget I M]

/-!
# Acceptance Test Suite: Phase 5 Milestone 3 (P0-4 through P0-11)

This comprehensive test suite is cleanly partitioned into two distinct sections
per COMPLETION_PLAN.md §0 and Forensic Audit guidelines:

## Section A: Strict Standard-Kernel-Axiom Tests (Unconditional)
All declarations in this section depend STRICTLY on standard Lean kernel axioms:
`[propext, Classical.choice, Quot.sound]`.
Zero `sorryAx` appears anywhere in their transitive dependency closure.

## Section B: Conditional Reduction Theorems (Documented Dependencies)
All declarations in this section represent genuine composite reduction theorems.
Each declaration has ZERO direct `sorry` in its proof body (and the invoked theorem
has ZERO direct `sorry` in its proof body).
Per COMPLETION_PLAN.md §0, they are explicitly documented as conditional reductions
that transitively inherit `sorryAx` from upstream leaf contracts (e.g., A01, A02, A04, A05, A11, B04, C01).
-/

-- ============================================================================
-- SECTION A: STRICT STANDARD-KERNEL-AXIOM TESTS (UNCONDITIONAL)
-- All tests below depend STRICTLY on [propext, Classical.choice, Quot.sound]
-- ============================================================================

--------------------------------------------------------------------------------
-- Probe A.1: Hölder Norm Foundations & Spherical Geometry (P0-10)
--------------------------------------------------------------------------------

/-- Test A.1.1: Hölder seminorm is nonnegative on any subset (Zero-sorry). -/
theorem test_holder_seminorm_nonneg (α : ℝ) (f : ℂ → ℂ) (s : Set ℂ) :
    0 ≤ holderSeminorm α f s :=
  holderSeminorm_nonneg α f s

/-- Test A.1.2: Full C^{k,α} norm is nonnegative (Zero-sorry). -/
theorem test_ck_holder_norm_nonneg (k : ℕ) (α : ℝ) (f : ℂ → ℂ) (s : Set ℂ) :
    0 ≤ ckHolderNorm k α f s :=
  ckHolderNorm_nonneg k α f s

/-- Test A.1.3: Shrinking radius sequence is strictly decreasing along induction steps (Zero-sorry). -/
theorem test_shrinking_radius_step (r : ℝ) (hr : 0 < r) :
    shrinkingRadius r (2 * r) 2 1 < shrinkingRadius r (2 * r) 2 0 :=
  shrinkingRadius_step r (2 * r) 2 0 (by linarith) (by norm_num) (by norm_num)

/-- Test A.1.4: Punctured CP1 is dense in CP1 (Zero-sorry). -/
theorem test_dense_punctured_sphere (p : CP1) :
    Dense (punctured_sphere {p}) :=
  dense_punctured_sphere p

/-- Test A.1.5: Inductive Schauder bootstrap reduction under explicit Cauchy-Riemann hypothesis (Zero-sorry). -/
theorem test_elliptic_bootstrap_holder_of_cauchy_riemann
    (h_cr : ∀ (k : ℕ) (α r R : ℝ) (_hr : 0 < r) (_hrR : r < R) (_hα0 : 0 < α) (_hα1 : α < 1),
      ∃ (C : ℝ), 0 < C ∧
      ∀ (f : ℂ → ℂ),
        ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
        ckHolderNorm (k + 1) α f (Metric.ball (0 : ℂ) r) ≤
          C * (ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
               supNormOn f (Metric.ball (0 : ℂ) R)))
    (k : ℕ) (α r R : ℝ) (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
      ckHolderNorm (k + 1) α f (Metric.ball (0 : ℂ) r) ≤
        C * (ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
             ckHolderNorm k α f (Metric.ball (0 : ℂ) R)) :=
  elliptic_bootstrap_holder_of_cauchy_riemann h_cr k α r R hr hrR hα0 hα1

--------------------------------------------------------------------------------
-- Probe A.2: Base-Case Stabilization & Singleton Assembly Foundations (P0-11)
--------------------------------------------------------------------------------

/-- Test A.2.1: stabilize_prestable_tree_of_stable_root forwards all 5 fields with zero sorry. -/
theorem test_stabilize_stable_root_zero_sorry
    (u_seq : ℕ → (CP1 → M)) (pdata : PrestableLimitData I u_seq)
    (h_root_stable : (∃ c : M, ∀ z : CP1, pdata.map pdata.root z = c) → 3 ≤ pdata.tree.adj.degree pdata.root) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v) =
        ∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ∧
      ∃ (σ : Bookkeeping.SubseqMap)
        (frames : (v : u_lim.tree.V) → ℕ → MoebiusFrame),
        (∀ (v : u_lim.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (u_lim.map v)
            (punctured_sphere { z | ∃ (w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w), z = u_lim.tree.node_point v w h })) ∧
        (∀ (v w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w),
          ∀ K ⊆ punctured_sphere {u_lim.tree.node_point w v (u_lim.tree.adj.symm h)}, IsCompact K →
            TendstoUniformlyOn
              (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (frames v n)) (frames w n)).toHomeo)
              (fun _ => u_lim.tree.node_point v w h) atTop K) ∧
        Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
          (𝓝 (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v))) :=
  stabilize_prestable_tree_of_stable_root I u_seq pdata h_root_stable

/-- Test A.2.2: prestable_limit_singleton_subseq constructs valid PrestableLimitData with zero sorry. -/
theorem test_prestable_limit_singleton_subseq_zero_sorry
    (u_seq : ℕ → (CP1 → M)) (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M)
    (h_jhol : JHolomorphicOn I I_CP1 u_lim Set.univ)
    (h_conv : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Set.univ)
    (h_energy : Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop (𝓝 (totalEnergy I u_lim))) :
    (prestable_limit_singleton_subseq I u_seq σ u_lim h_jhol h_conv h_energy).tree.V = Unit :=
  rfl

/-- Test A.2.3: energyMeasureExtended_le_ofReal preserves real energy bounds with zero sorry. -/
theorem test_energy_measure_le_zero_sorry
    (u : CP1 → M) (B : ℝ) (h_en : totalEnergy I u ≤ B)
    (h_fin : energyMeasureExtended I u Set.univ < ⊤) :
    energyMeasureExtended I u Set.univ ≤ ENNReal.ofReal B :=
  energyMeasureExtended_le_ofReal_of_totalEnergy_le I u B h_en h_fin

/-- Test A.2.4: weak_energy_measure_compactness_of_weak_measure_compactness has zero sorry under h_comp. -/
theorem test_weak_energy_measure_compactness_reduction
    (h_comp : ∀ (μ_seq : ℕ → Measure CP1) [∀ n, IsFiniteMeasure (μ_seq n)],
      (∃ B > 0, ∀ n, μ_seq n Set.univ ≤ ENNReal.ofReal B) →
      ∃ (σ : Bookkeeping.SubseqMap) (μ_lim : Measure CP1),
        IsFiniteMeasure μ_lim ∧
        WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (hB : 0 < B)
    (h_bdd : ∀ n, energyMeasureExtended I (u_seq n) Set.univ ≤ ENNReal.ofReal B) :
    ∃ (σ : Bookkeeping.SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim :=
  weak_energy_measure_compactness_of_weak_measure_compactness I h_comp u_seq B hB h_bdd

--------------------------------------------------------------------------------
-- Probe A.3: Tree Rescaling Data & Explicit Recursion (P0-7)
--------------------------------------------------------------------------------

/-- Test A.3.1: TreeRescalingData.singleton is well-typed and has zero sorry. -/
theorem test_tree_rescaling_singleton :
    TreeRescalingData.singleton.scale () 0 = 1 :=
  rfl

--------------------------------------------------------------------------------
-- Probe A.4: Moduli Space Genuine Topology (P0-8)
--------------------------------------------------------------------------------

/-- Test A.4.1: moduliSpaceTopology is a genuine topological space instance on ModuliSpace. -/
def test_moduli_space_topology_instance (k : ℕ) (B : ℝ) :
    TopologicalSpace (ModuliSpace I (M := M) k B) :=
  moduliSpaceTopologicalSpace I k B

/-- Test A.4.2: ModuliSpaceInClass is a genuine non-sorry topological space. -/
def test_moduli_space_in_class_topology (k : ℕ) (A : HomologyClass2 M) :
    TopologicalSpace (ModuliSpaceInClass I (M := M) k A) :=
  moduliSpaceInClassTopologicalSpace I k A


-- ============================================================================
-- SECTION B: CONDITIONAL REDUCTION THEOREMS (DOCUMENTED DEPENDENCIES)
-- Each test below has ZERO direct sorry in its body and calls a theorem with
-- ZERO direct sorry in its body, but transitively inherits sorryAx from leaf contracts.
-- ============================================================================

--------------------------------------------------------------------------------
-- Probe B.1: Hölder / Schauder Bootstrap & Singularity Removal (P0-10)
--------------------------------------------------------------------------------

/-- Test B.1.1: Singularity removal bootstrap bridge (Contract A11 → A05 → A12).
Proved with ZERO direct sorry in `singularity_removal_bootstrap_bridge`.
CONDITIONAL STATUS: Transitively depends on `sorryAx` via leaf contract A05
(`nonlinear_elliptic_bootstrap` in `EllipticBootstrap.lean:747`). -/
theorem test_singularity_removal_bootstrap_bridge
    (u_ext : CP1 → M) (h_weak : WeakJHolomorphicOn I u_ext Set.univ) :
    JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ :=
  singularity_removal_bootstrap_bridge I u_ext h_weak

/-- Test B.1.2: Smooth Removal of Singularities (Contract A12).
Proved with ZERO direct sorry in `removal_of_singularities`.
CONDITIONAL STATUS: Transitively depends on `sorryAx` via leaf contracts A11
(`puncture_sobolev_extension`) and A05 (`nonlinear_elliptic_bootstrap`). -/
theorem test_removal_of_singularities
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  removal_of_singularities I u p h_jhol h_energy

/-- Test B.1.3: Inductive Schauder bootstrap step (Contract A05).
Proved with ZERO direct sorry in `elliptic_bootstrap_holder` via reduction to A04.
CONDITIONAL STATUS: Transitively depends on `sorryAx` via leaf contract A04
(`interior_cauchy_riemann_estimate` in `EllipticBootstrap.lean:663`). -/
theorem test_elliptic_bootstrap_holder_signature (k : ℕ) (α r R : ℝ)
    (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
      ckHolderNorm (k + 1) α f (Metric.ball (0 : ℂ) r) ≤
        C * (ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
             ckHolderNorm k α f (Metric.ball (0 : ℂ) R)) :=
  elliptic_bootstrap_holder k α r R hr hrR hα0 hα1

--------------------------------------------------------------------------------
-- Probe B.2: PDE Differential Inequality & Mean Value Inequality (P0-4, P0-5)
--------------------------------------------------------------------------------

/-- Test B.2.1: scalar_mean_value_inequality default parameter alignment (c : ℝ := 0) (Contract A01).
Invokes Contract A01 with trailing default arguments (c : ℝ := 0) and (hc : 0 ≤ c := by norm_num).
CONDITIONAL STATUS: Transitively depends on `sorryAx` via leaf contract A01. -/
theorem test_scalar_mean_value_inequality_default_args (b : ℝ) (hb : 0 ≤ b) :
    ∃ (η C : ℝ), 0 < η ∧ 0 < C ∧
    ∀ (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ),
      (∀ z, 0 ≤ e z) →
      ContinuousOn e (Metric.closedBall 0 r) →
      ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r) →
      (∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 - 0 * (e z) ≤ laplacian2D e z) →
      (∫ w in Metric.ball (0 : ℂ) r, e w) < η →
      (∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2), e z ≤ C * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w)) :=
  scalar_mean_value_inequality b hb

/-- Test B.2.2: Bochner differential inequality produces real subharmonic bound (Contract A02).
Proved with ZERO direct sorry in `bochner_differential_inequality` via curvature decomposition.
CONDITIONAL STATUS: Transitively depends on `sorryAx` via leaf contract A02
(`bochner_curvature_term_bound` in `Bochner.lean:177`). -/
theorem test_bochner_differential_inequality_signature :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ),
        -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
          c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
        laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w :=
  bochner_differential_inequality (M := M) I

--------------------------------------------------------------------------------
-- Probe B.3: Core Call-Graph Wiring Composite Theorems (P0-11)
--------------------------------------------------------------------------------

/-- Test B.3.1: Master stabilization theorem (Contract G02).
Proved with ZERO direct sorry in `stabilize_prestable_tree` via well-founded induction.
CONDITIONAL STATUS: Transitively depends on `sorryAx` via unstable root pruning helpers
(`prune_degree_one_root`, `suppress_degree_two_root`). -/
theorem test_stabilize_prestable_tree_composite
    (u_seq : ℕ → (CP1 → M)) (pdata : PrestableLimitData I u_seq)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v) =
        ∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ∧
      ∃ (σ : Bookkeeping.SubseqMap)
        (frames : (v : u_lim.tree.V) → ℕ → MoebiusFrame),
        (∀ (v : u_lim.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (u_lim.map v)
            (punctured_sphere { z | ∃ (w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w), z = u_lim.tree.node_point v w h })) ∧
        (∀ (v w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w),
          ∀ K ⊆ punctured_sphere {u_lim.tree.node_point w v (u_lim.tree.adj.symm h)}, IsCompact K →
            TendstoUniformlyOn
              (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (frames v n)) (frames w n)).toHomeo)
              (fun _ => u_lim.tree.node_point v w h) atTop K) ∧
        Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
          (𝓝 (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v))) :=
  stabilize_prestable_tree I u_seq pdata h_nonconst

/-- Test B.3.2: Prestable limit global assembly (Contract G01).
Proved with ZERO direct sorry in `assemble_prestable_limit`.
CONDITIONAL STATUS: Transitively depends on `sorryAx` via concentration data (`C02`),
defect measure identity (`C03`), and defect tree resolution (`B07`). -/
theorem test_assemble_prestable_limit_composite
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit I th u_seq B h_jhol h_energy h_fin

/-- Test B.3.3: Single defect resolution into bubble tree (Contract B07).
Proved with ZERO direct sorry in `resolve_single_defect_tree` via energy rank induction.
CONDITIONAL STATUS: Transitively depends on `sorryAx` via child defect tree grafting helper. -/
theorem test_resolve_single_defect_tree_composite
    (thresh : Bubbling.TargetThresholds I M) (m_defect : ℝ) (hm : 0 < m_defect) (base_val : M) :
    Nonempty (Bubbling.LocalDefectTree I thresh m_defect base_val) :=
  Bubbling.resolve_single_defect_tree I thresh m_defect hm base_val

/-- Test B.3.4: Weak energy measure compactness (Contract C01).
Proved with ZERO direct sorry in `weak_energy_measure_compactness`.
CONDITIONAL STATUS: Transitively depends on `sorryAx` via leaf weak measure compactness (`weak_measure_compactness`). -/
theorem test_weak_energy_measure_compactness_composite
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (hB : 0 < B)
    (h_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤) :
    ∃ (σ : Bookkeeping.SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim :=
  weak_energy_measure_compactness I u_seq B hB h_bdd h_fin

/-- Test B.3.5: Core Genus 0 Gromov Compactness Theorem (Theorem 1 Core & Contract G03).
Proved with ZERO direct sorry in `gromov_compactness_core` by composing G01 and G02.
CONDITIONAL STATUS: Transitively depends on `sorryAx` via assembly and stabilization reductions. -/
theorem test_gromov_compactness_core_composite
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  gromov_compactness_core I th u_seq B h_nonconst h_jhol h_energy h_fin


-- ============================================================================
-- SECTION C: KERNEL AXIOM AUDIT BLOCKS
-- ============================================================================

--------------------------------------------------------------------------------
-- Section C.1: Unconditional Standard Kernel Axioms Census
-- Must print STRICTLY [propext, Classical.choice, Quot.sound] (Zero sorryAx).
--------------------------------------------------------------------------------

#print axioms test_holder_seminorm_nonneg
#print axioms test_ck_holder_norm_nonneg
#print axioms test_shrinking_radius_step
#print axioms test_dense_punctured_sphere
#print axioms test_elliptic_bootstrap_holder_of_cauchy_riemann
#print axioms test_stabilize_stable_root_zero_sorry
#print axioms test_prestable_limit_singleton_subseq_zero_sorry
#print axioms test_energy_measure_le_zero_sorry
#print axioms test_weak_energy_measure_compactness_reduction
#print axioms test_tree_rescaling_singleton
#print axioms test_moduli_space_topology_instance
#print axioms test_moduli_space_in_class_topology

--------------------------------------------------------------------------------
-- Section C.2: Conditional Reduction Axiom Attribution
-- Expected axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-- All proof bodies contain ZERO direct sorry. sorryAx is inherited transitively
-- from upstream leaf contracts (A01, A02, A04, A05, A11, B04, C01) per COMPLETION_PLAN.md §0.
--------------------------------------------------------------------------------

#print axioms test_singularity_removal_bootstrap_bridge
#print axioms test_removal_of_singularities
#print axioms test_elliptic_bootstrap_holder_signature
#print axioms test_scalar_mean_value_inequality_default_args
#print axioms test_bochner_differential_inequality_signature
#print axioms test_stabilize_prestable_tree_composite
#print axioms test_assemble_prestable_limit_composite
#print axioms test_resolve_single_defect_tree_composite
#print axioms test_weak_energy_measure_compactness_composite
#print axioms test_gromov_compactness_core_composite

end GromovCompactness.ChallengeMilestone3Phase5
