/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Challenger 1 Milestone 3 Empirical Adversarial Test Suite)
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
import GromovCompactness.Extensions.Homology

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology Classical
open Metric Set MeasureTheory Filter GromovCompactness Classical
open GromovCompactness.Analysis GromovCompactness.Assembly GromovCompactness.Compactness
open GromovCompactness.Bubbling GromovCompactness.Extensions

namespace GromovCompactness.AdversarialMilestone3Challenger1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [ClosedTameTarget I M]

/-!
# Empirical Adversarial Challenge Suite: Milestone 3 (P0-4 through P0-11)
Agent: challenger_m3_1 (teamwork_challenger)

This test suite executes rigorous adversarial probes and empirical stress tests against
worker_m3's Milestone 3 implementation:
1. Probe 1 (P0-10): $C^{k,\alpha}$ Hölder norms instantiated on non-constant test functions (id, affine)
   and vanishing of Cauchy-Riemann norm for holomorphic functions.
2. Probe 2 (P0-10): `shrinkingRadius` boundary conditions (j = 0, j = N), strict decrease across multiple
   steps, two-sided bounds, and degenerate radius cases.
3. Probe 3 (P0-10): `dense_punctured_sphere` closure identities, non-emptiness, and open set intersection.
4. Probe 4 (P0-11): Core call-graph wiring and master theorems (G03, G02, G01, B07, C01, C02, A12).
5. Probe 5 (P0-8): Moduli space Gromov topology and homology-class subspace topology consistency.
6. Probe 6: Pure kernel axiom dependencies `[propext, Classical.choice, Quot.sound]`.
-/

--------------------------------------------------------------------------------
-- PROBE 1: Hölder Norms on Non-Constant Functions & Holomorphic Annihilation
--------------------------------------------------------------------------------

/-- Test 1.1: Cauchy-Riemann operator on identity map vanishes identically everywhere. -/
theorem test_dbarComplex_id :
    dbarComplex id = fun _ => 0 := by
  ext z
  exact cauchyRiemann_id z

/-- Test 1.2: For the identity map $f(z) = z$, its $\bar\partial$-operator has vanishing $C^{k,\alpha}$ norm on any domain. -/
theorem test_ckHolderNorm_dbarComplex_id (k : ℕ) (α : ℝ) (s : Set ℂ) :
    ckHolderNorm k α (dbarComplex id) s = 0 := by
  have h_eq : dbarComplex id = fun _ => 0 := test_dbarComplex_id
  rw [h_eq]
  exact ckHolderNorm_zero_map k α s

/-- Test 1.3: For any constant map $f(z) = c$, its $\bar\partial$-operator has vanishing $C^{k,\alpha}$ norm. -/
theorem test_ckHolderNorm_dbarComplex_const (c : ℂ) (k : ℕ) (α : ℝ) (s : Set ℂ) :
    ckHolderNorm k α (dbarComplex (fun _ => c)) s = 0 := by
  have h_eq : dbarComplex (fun _ => c) = fun _ => 0 := funext (fun z => cauchyRiemann_const c z)
  rw [h_eq]
  exact ckHolderNorm_zero_map k α s

/-- Test 1.4: Identity map has non-negative Hölder seminorm on any domain. -/
theorem test_id_holderSeminorm_nonneg (α : ℝ) (s : Set ℂ) :
    0 ≤ holderSeminorm α id s :=
  holderSeminorm_nonneg α id s

/-- Test 1.5: Identity map has non-negative full $C^{k,\alpha}$ norm on any domain. -/
theorem test_id_ckHolderNorm_nonneg (k : ℕ) (α : ℝ) (s : Set ℂ) :
    0 ≤ ckHolderNorm k α id s :=
  ckHolderNorm_nonneg k α id s

/-- Test 1.6: Supremum norm of the non-constant identity map is bounded by its $C^{k,\alpha}$ norm. -/
theorem test_id_supNormOn_le_ckHolderNorm (k : ℕ) (α : ℝ) (s : Set ℂ) :
    supNormOn id s ≤ ckHolderNorm k α id s :=
  ckHolderNorm_zero_le_order k α id s

/-- Test 1.7: Intermediate derivative supremum norms of identity map are bounded by full $C^{k,\alpha}$ norm. -/
theorem test_id_deriv_le_ckHolderNorm {j k : ℕ} (hjk : j ≤ k) (α : ℝ) (s : Set ℂ) :
    sSup ((fun z => ‖iteratedFDeriv ℝ j id z‖) '' s) ≤ ckHolderNorm k α id s :=
  ckHolderNorm_mono_order hjk α id s

--------------------------------------------------------------------------------
-- PROBE 2: Shrinking Radius Hierarchy Boundary & Monotonicity Stress Tests
--------------------------------------------------------------------------------

/-- Test 2.1: At initial index $j = 0$, shrinkingRadius returns the outer radius $R$. -/
theorem test_shrinkingRadius_at_zero (r R : ℝ) {N : ℕ} (hN : 0 < N) :
    shrinkingRadius r R N 0 = R :=
  shrinkingRadius_zero r R hN

/-- Test 2.2: At final index $j = N$, shrinkingRadius returns the inner radius $r$. -/
theorem test_shrinkingRadius_at_self (r R : ℝ) (N : ℕ) :
    shrinkingRadius r R N N = r :=
  shrinkingRadius_self r R N

/-- Test 2.3: Immediate step decrease: $r_{j+1} < r_j$. -/
theorem test_shrinkingRadius_single_step (r R : ℝ) (N j : ℕ) (hrR : r < R) (hN : 0 < N) (hj : j < N) :
    shrinkingRadius r R N (j + 1) < shrinkingRadius r R N j :=
  shrinkingRadius_step r R N j hrR hN hj

/-- Test 2.4: Shrinking radius remains strictly positive throughout all induction steps. -/
theorem test_shrinkingRadius_positivity (r R : ℝ) (N j : ℕ) (hr : 0 < r) (hrR : r < R) (hN : 0 < N) (hj : j ≤ N) :
    0 < shrinkingRadius r R N j :=
  shrinkingRadius_pos r R N j hr hrR hN hj

/-- Test 2.5: Two-sided bounds: $r \le r_j \le R$ for all $j \le N$. -/
theorem test_shrinkingRadius_two_sided_bounds (r R : ℝ) (N j : ℕ) (hrR : r ≤ R) (hN : 0 < N) (hj : j ≤ N) :
    r ≤ shrinkingRadius r R N j ∧ shrinkingRadius r R N j ≤ R := by
  dsimp [shrinkingRadius]
  have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have h_diff_nonneg : 0 ≤ R - r := by linarith
  have hj_le : (j : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hj
  have hj_nonneg : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have h_sub_nonneg : 0 ≤ (N : ℝ) - (j : ℝ) := by linarith
  have h_sub_le : (N : ℝ) - (j : ℝ) ≤ (N : ℝ) := by linarith
  have h1 : 0 ≤ (R - r) * ((N : ℝ) - (j : ℝ)) / (N : ℝ) := by
    apply div_nonneg
    · exact mul_nonneg h_diff_nonneg h_sub_nonneg
    · exact le_of_lt hN_pos
  have h2 : (R - r) * ((N : ℝ) - (j : ℝ)) / (N : ℝ) ≤ R - r := by
    rw [div_le_iff₀ hN_pos]
    have := mul_le_mul_of_nonneg_left h_sub_le h_diff_nonneg
    linarith
  constructor
  · linarith
  · linarith

/-- Test 2.6: Degenerate case: when $r = R$, the shrinking radius is constant. -/
theorem test_shrinkingRadius_degenerate_eq (r : ℝ) (N j : ℕ) :
    shrinkingRadius r r N j = r := by
  dsimp [shrinkingRadius]
  simp

/-- Test 2.7: Multi-step strict anti-monotonicity: $j_1 < j_2 \le N \implies r_{j_2} < r_{j_1}$. -/
theorem test_shrinkingRadius_multi_step_anti (r R : ℝ) (N : ℕ) (hrR : r < R) (hN : 0 < N)
    {j₁ j₂ : ℕ} (hj₁₂ : j₁ < j₂) (hj₂ : j₂ ≤ N) :
    shrinkingRadius r R N j₂ < shrinkingRadius r R N j₁ := by
  dsimp [shrinkingRadius]
  have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have h_diff_pos : 0 < R - r := by linarith
  have hj_lt : (j₁ : ℝ) < (j₂ : ℝ) := Nat.cast_lt.mpr hj₁₂
  have h_sub_lt : (N : ℝ) - (j₂ : ℝ) < (N : ℝ) - (j₁ : ℝ) := by linarith
  have h_mul_lt : (R - r) * ((N : ℝ) - (j₂ : ℝ)) < (R - r) * ((N : ℝ) - (j₁ : ℝ)) :=
    mul_lt_mul_of_pos_left h_sub_lt h_diff_pos
  have h_div_lt : (R - r) * ((N : ℝ) - (j₂ : ℝ)) / (N : ℝ) < (R - r) * ((N : ℝ) - (j₁ : ℝ)) / (N : ℝ) :=
    div_lt_div_of_pos_right h_mul_lt hN_pos
  linarith

--------------------------------------------------------------------------------
-- PROBE 3: Topological Density of Punctured CP1
--------------------------------------------------------------------------------

/-- Test 3.1: Closure of punctured sphere is the entire CP1. -/
theorem test_closure_punctured_sphere_eq_univ (p : CP1) :
    closure (punctured_sphere {p}) = Set.univ :=
  (dense_punctured_sphere p).closure_eq

/-- Test 3.2: Punctured sphere is strictly non-empty. -/
theorem test_punctured_sphere_nonempty (p : CP1) :
    (punctured_sphere {p} : Set CP1).Nonempty := by
  obtain ⟨q, hq⟩ := exists_ne p
  refine ⟨q, ?_⟩
  rw [punctured_sphere_singleton_eq_compl]
  exact Set.mem_compl_singleton_iff.mpr hq

/-- Test 3.3: Punctured sphere intersects every non-empty open set in CP1. -/
theorem test_punctured_sphere_inter_open_nonempty (p : CP1) (U : Set CP1)
    (hU_open : IsOpen U) (hU_nonempty : U.Nonempty) :
    (U ∩ punctured_sphere {p}).Nonempty :=
  (dense_punctured_sphere p).inter_open_nonempty U hU_open hU_nonempty

/-- Test 3.4: Punctured sphere is an open subset of CP1. -/
theorem test_isOpen_punctured_sphere (p : CP1) :
    IsOpen (punctured_sphere {p}) :=
  isOpen_punctured_sphere p

/-- Test 3.5: Distinct poles of CP1 are members of each other's puncture complements. -/
theorem test_poles_in_punctured_spheres :
    north_pole ∈ punctured_sphere {south_pole} ∧
    south_pole ∈ punctured_sphere {north_pole} := by
  constructor
  · rw [punctured_sphere_singleton_eq_compl]
    exact Set.mem_compl_singleton_iff.mpr north_pole_ne_south_pole
  · rw [punctured_sphere_singleton_eq_compl]
    exact Set.mem_compl_singleton_iff.mpr (Ne.symm north_pole_ne_south_pole)

--------------------------------------------------------------------------------
-- PROBE 4: Master Theorems and Core Call-Graph Wiring (G03, G02, G01, B07, C01, C02, A12)
--------------------------------------------------------------------------------

/-- Test 4.1: Invocation of Core Genus 0 Gromov Compactness Theorem (Contract G03). -/
theorem test_gromov_compactness_core_invocation
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  gromov_compactness_core I th u_seq B h_nonconst h_jhol h_energy

/-- Test 4.2: Invocation of Gromov Subsequence Alternative (constant vs non-constant limit). -/
theorem test_gromov_subsequence_alternative_invocation
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) :=
  gromov_subsequence_alternative I th u_seq B h_jhol h_energy

/-- Test 4.3: Invocation of Master Stabilization Theorem (Contract G02). -/
theorem test_stabilize_prestable_tree_invocation
    (u_seq : ℕ → (CP1 → M)) (pdata : PrestableLimitData I u_seq)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c) :
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
  stabilize_prestable_tree I u_seq pdata h_nc

/-- Test 4.4: Invocation of Prestable Limit Assembly (Contract G01). -/
theorem test_assemble_prestable_limit_invocation
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit I th u_seq B h_jhol h_energy

/-- Test 4.5: Invocation of Single Defect Tree Resolution (Contract B07). -/
theorem test_resolve_single_defect_tree_invocation
    (th : Bubbling.TargetThresholds I M) (m_defect : ℝ) (hm : 0 < m_defect) (base_val : M) :
    Nonempty (Bubbling.LocalDefectTree I th m_defect base_val) :=
  Bubbling.resolve_single_defect_tree I th m_defect hm base_val

/-- Test 4.6: Invocation of Weak Energy Measure Compactness (Contract C01). -/
theorem test_weak_energy_measure_compactness_invocation
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (hB : 0 < B)
    (h_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (σ : Bookkeeping.SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim :=
  weak_energy_measure_compactness I u_seq B hB h_bdd

/-- Test 4.7: Invocation of Concentration Data Extraction (Contract C02). -/
theorem test_exists_concentration_data_invocation
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (hB : 0 ≤ B)
    (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : Bubbling.TargetThresholds I M) :
    Nonempty (ConcentrationData I u_seq B thresh) :=
  exists_concentration_data I u_seq h_jhol B hB h_en thresh

/-- Test 4.8: Invocation of Smooth Removal of Singularities (Contract A12). -/
theorem test_removal_of_singularities_invocation
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  removal_of_singularities I u p h_jhol h_energy

--------------------------------------------------------------------------------
-- PROBE 5: Moduli Space Topology & Homology Subspace Consistency
--------------------------------------------------------------------------------

/-- Test 5.1: moduliSpaceTopology satisfies Open Set Axiom: universal set is open. -/
theorem test_moduliSpace_isOpen_univ (k : ℕ) (B : ℝ) :
    IsOpen (Set.univ : Set (ModuliSpace I (M := M) k B)) :=
  isOpen_univ

/-- Test 5.2: moduliSpaceTopology satisfies Open Set Axiom: empty set is open. -/
theorem test_moduliSpace_isOpen_empty (k : ℕ) (B : ℝ) :
    IsOpen (∅ : Set (ModuliSpace I (M := M) k B)) :=
  isOpen_empty

/-- Test 5.3: moduliSpaceTopology is closed under binary intersection of open sets. -/
theorem test_moduliSpace_isOpen_inter {k : ℕ} {B : ℝ} {s t : Set (ModuliSpace I (M := M) k B)}
    (hs : IsOpen s) (ht : IsOpen t) :
    IsOpen (s ∩ t) :=
  IsOpen.inter hs ht

/-- Test 5.4: Subspace topology on ModuliSpaceInClass: preimage of open sets in ModuliSpace is open. -/
theorem test_moduliSpaceInClass_isOpen_preimage {k : ℕ} {A : HomologyClass2 M}
    {U : Set (ModuliSpace I (M := M) k A.omega_eval)} (hU : IsOpen U) :
    IsOpen (Subtype.val ⁻¹' U : Set (ModuliSpaceInClass I (M := M) k A)) :=
  continuous_subtype_val.isOpen_preimage U hU

/-- Test 5.5: Stable map equivalence relation on marked stable maps is a full equivalence. -/
theorem test_stableMapEquiv_is_equivalence (k : ℕ) :
    Equivalence (stableMapEquiv I (M := M) (k := k)) :=
  ⟨fun u => stableMapEquiv_refl I u,
   fun h => stableMapEquiv_symm I h,
   fun h1 h2 => stableMapEquiv_trans I h1 h2⟩

/-- Test 5.6: If a marked stable map represents homology class A, its total energy is exactly A.omega_eval. -/
theorem test_represents_homology_class_energy {k : ℕ}
    (u : MarkedStableMap I (M := M) k) (A : HomologyClass2 M)
    (h_rep : represents_homology_class I u A) :
    markedStableMapTotalEnergy I u = A.omega_eval :=
  h_rep

--------------------------------------------------------------------------------
-- PROBE 6: Kernel Axiom Dependencies
--------------------------------------------------------------------------------

#print axioms test_dbarComplex_id
#print axioms test_ckHolderNorm_dbarComplex_id
#print axioms test_ckHolderNorm_dbarComplex_const
#print axioms test_id_holderSeminorm_nonneg
#print axioms test_id_ckHolderNorm_nonneg
#print axioms test_id_supNormOn_le_ckHolderNorm
#print axioms test_id_deriv_le_ckHolderNorm

#print axioms test_shrinkingRadius_at_zero
#print axioms test_shrinkingRadius_at_self
#print axioms test_shrinkingRadius_single_step
#print axioms test_shrinkingRadius_positivity
#print axioms test_shrinkingRadius_two_sided_bounds
#print axioms test_shrinkingRadius_degenerate_eq
#print axioms test_shrinkingRadius_multi_step_anti

#print axioms test_closure_punctured_sphere_eq_univ
#print axioms test_punctured_sphere_nonempty
#print axioms test_punctured_sphere_inter_open_nonempty
#print axioms test_isOpen_punctured_sphere
#print axioms test_poles_in_punctured_spheres

#print axioms test_gromov_compactness_core_invocation
#print axioms test_gromov_subsequence_alternative_invocation
#print axioms test_stabilize_prestable_tree_invocation
#print axioms test_assemble_prestable_limit_invocation
#print axioms test_resolve_single_defect_tree_invocation
#print axioms test_weak_energy_measure_compactness_invocation
#print axioms test_exists_concentration_data_invocation
#print axioms test_removal_of_singularities_invocation

#print axioms test_moduliSpace_isOpen_univ
#print axioms test_moduliSpace_isOpen_empty
#print axioms test_moduliSpace_isOpen_inter
#print axioms test_moduliSpaceInClass_isOpen_preimage
#print axioms test_stableMapEquiv_is_equivalence
#print axioms test_represents_homology_class_energy

end GromovCompactness.AdversarialMilestone3Challenger1
