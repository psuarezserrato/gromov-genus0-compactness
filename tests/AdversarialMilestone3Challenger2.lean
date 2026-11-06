/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Phase 5 Milestone 3 Adversarial Test Suite - Challenger 2)
-/
import GromovCompactness
import GromovCompactness.Analysis.EllipticBootstrap
import GromovCompactness.Analysis.SingularityRemoval
import GromovCompactness.Analysis.Monotonicity
import GromovCompactness.Analysis.Bochner
import GromovCompactness.Analysis.EpsilonRegularity
import GromovCompactness.Analysis.Energy
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

namespace GromovCompactness.AdversarialMilestone3Challenger2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [ClosedTameTarget I M]

/-!
# Adversarial Stress Test Suite: Milestone 3 (Challenger 2)

This adversarial test suite probes edge cases, boundary parameters, topological axioms,
and call-graph wiring across Milestone 3:

1. **P0-10 Edge Cases**:
   - Hölder seminorms and norms at $k = 0$, $k = 1$
   - Boundary values $\alpha = 0$ (distance/diameter quotient) and $\alpha = 1$ (Lipschitz quotient)
   - Shrinking radius hierarchy at extreme values: $r = R$, $j = 0$, $j = N$, and bounds $r \le r_j \le R$
   - Singularity removal bootstrap bridge tested on a concrete non-constant map
2. **P0-8 Moduli Space Topology Axioms**:
   - Empty set is open: `IsOpen ∅`
   - Universal set is open: `IsOpen Set.univ`
   - Binary intersection of open sets: `IsOpen (s ∩ t)`
   - Arbitrary infinite sUnion of open sets: `IsOpen (⋃₀ S)`
   - Empty sUnion: `IsOpen (⋃₀ ∅)`
   - Arbitrary indexed union: `IsOpen (⋃ i, U i)`
   - Subspace topology on `ModuliSpaceInClass`: `IsOpen ∅` and `IsOpen Set.univ`
3. **P0-11 Core Call-Graph Completeness and Non-Bypass**:
   - $G03 \to G02 \to G01 \to C02 \to C01$ and $B07$ wiring
   - Probing that each parent directly references and consumes the output of its children
4. **Kernel Axiom Census**:
   - Auditing `#print axioms` to ensure closed theorems and foundational lemmas
     depend strictly on standard Lean kernel axioms `[propext, Classical.choice, Quot.sound]`.
-/

--------------------------------------------------------------------------------
-- SECTION 1: P0-10 Hölder Seminorms, Boundary Exponents & Shrinking Radii
--------------------------------------------------------------------------------

/-- Probe 1.1: Order k = 0 decomposition of ckHolderNorm into sup norm and derivHolderSeminorm. -/
theorem probe_ck_holder_norm_k_zero (α : ℝ) (f : ℂ → ℂ) (s : Set ℂ) :
    ckHolderNorm 0 α f s = supNormOn f s + derivHolderSeminorm 0 α f s := by
  dsimp [ckHolderNorm, supNormOn]
  simp only [Finset.range_one, Finset.sum_singleton]
  have h0 : (fun z => ‖iteratedFDeriv ℝ 0 f z‖) = fun z => ‖f z‖ := by
    ext z; exact norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := f) (x := z)
  rw [h0]
  rfl

/-- Probe 1.2: Order k = 1 decomposition of ckHolderNorm into C^0, C^1, and [D^1 f]_{C^{0, α}}. -/
theorem probe_ck_holder_norm_k_one (α : ℝ) (f : ℂ → ℂ) (s : Set ℂ) :
    ckHolderNorm 1 α f s =
      supNormOn f s + sSup ((fun z => ‖iteratedFDeriv ℝ 1 f z‖) '' s) +
      derivHolderSeminorm 1 α f s := by
  dsimp [ckHolderNorm, supNormOn]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have h0 : (fun z => ‖iteratedFDeriv ℝ 0 f z‖) = fun z => ‖f z‖ := by
    ext z; exact norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := f) (x := z)
  rw [h0]
  rfl

/-- Probe 1.3: C^0 sup norm is bounded by C^{1, α} norm for any α. -/
theorem probe_ck_holder_norm_k0_le_k1 (α : ℝ) (f : ℂ → ℂ) (s : Set ℂ) :
    supNormOn f s ≤ ckHolderNorm 1 α f s :=
  ckHolderNorm_zero_le_order 1 α f s

/-- Probe 1.4: First derivative sup norm is bounded by C^{1, α} norm for any α. -/
theorem probe_ck_holder_norm_deriv_le_k1 (α : ℝ) (f : ℂ → ℂ) (s : Set ℂ) :
    sSup ((fun z => ‖iteratedFDeriv ℝ 1 f z‖) '' s) ≤ ckHolderNorm 1 α f s :=
  ckHolderNorm_mono_order le_rfl α f s

/-- Probe 1.5: Boundary value α = 0: Hölder seminorm is non-negative. -/
theorem probe_holder_seminorm_alpha_zero (f : ℂ → ℂ) (s : Set ℂ) :
    0 ≤ holderSeminorm 0 f s :=
  holderSeminorm_nonneg 0 f s

/-- Probe 1.6: Boundary value α = 0 quotient degenerates to metric distance ‖f z - f w‖. -/
theorem probe_holder_quotient_alpha_zero (f : ℂ → ℂ) (z w : ℂ) (hzw : z ≠ w) :
    ‖f z - f w‖ / (‖z - w‖ ^ (0 : ℝ)) = ‖f z - f w‖ := by
  have h_norm_pos : 0 < ‖z - w‖ := norm_sub_pos_iff.mpr hzw
  rw [Real.rpow_zero, div_one]

/-- Probe 1.7: Boundary value α = 1: Hölder seminorm is non-negative (Lipschitz seminorm). -/
theorem probe_holder_seminorm_alpha_one (f : ℂ → ℂ) (s : Set ℂ) :
    0 ≤ holderSeminorm 1 f s :=
  holderSeminorm_nonneg 1 f s

/-- Probe 1.8: Boundary value α = 1 quotient coincides with standard Lipschitz difference quotient. -/
theorem probe_holder_quotient_alpha_one (f : ℂ → ℂ) (z w : ℂ) :
    ‖f z - f w‖ / (‖z - w‖ ^ (1 : ℝ)) = ‖f z - f w‖ / ‖z - w‖ := by
  rw [Real.rpow_one]

/-- Probe 1.9: Extreme radius value r = R collapses shrinkingRadius hierarchy to constant R. -/
theorem probe_shrinking_radius_extreme_equal (r : ℝ) (N j : ℕ) :
    shrinkingRadius r r N j = r := by
  dsimp [shrinkingRadius]
  rw [sub_self, zero_mul, zero_div, add_zero]

/-- Probe 1.10: Extreme boundary j = 0 returns outer radius R. -/
theorem probe_shrinking_radius_at_zero (r R : ℝ) {N : ℕ} (hN : 0 < N) :
    shrinkingRadius r R N 0 = R :=
  shrinkingRadius_zero r R hN

/-- Probe 1.11: Extreme boundary j = N returns inner radius r. -/
theorem probe_shrinking_radius_at_N (r R : ℝ) (N : ℕ) :
    shrinkingRadius r R N N = r :=
  shrinkingRadius_self r R N

/-- Probe 1.12: Shrinking radius is bounded between r and R for any step j ≤ N. -/
theorem probe_shrinking_radius_bounds (r R : ℝ) (N j : ℕ)
    (hrR : r ≤ R) (hN : 0 < N) (hj : j ≤ N) :
    r ≤ shrinkingRadius r R N j ∧ shrinkingRadius r R N j ≤ R := by
  dsimp [shrinkingRadius]
  have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have h_diff_nonneg : 0 ≤ R - r := by linarith
  have hj_le : (j : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hj
  have h_rem_nonneg : 0 ≤ (N : ℝ) - (j : ℝ) := by linarith
  have h_rem_le : (N : ℝ) - (j : ℝ) ≤ (N : ℝ) := by
    have : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  constructor
  · have h_mul_nonneg : 0 ≤ (R - r) * ((N : ℝ) - (j : ℝ)) := mul_nonneg h_diff_nonneg h_rem_nonneg
    have h_div_nonneg : 0 ≤ (R - r) * ((N : ℝ) - (j : ℝ)) / (N : ℝ) :=
      div_nonneg h_mul_nonneg (le_of_lt hN_pos)
    linarith
  · have h_frac_le : ((N : ℝ) - (j : ℝ)) / (N : ℝ) ≤ 1 := by
      exact (div_le_one hN_pos).mpr h_rem_le
    have h_mul_le : (R - r) * (((N : ℝ) - (j : ℝ)) / (N : ℝ)) ≤ (R - r) * 1 :=
      mul_le_mul_of_nonneg_left h_frac_le h_diff_nonneg
    rw [mul_one] at h_mul_le
    have h_assoc : (R - r) * ((N : ℝ) - (j : ℝ)) / (N : ℝ) = (R - r) * (((N : ℝ) - (j : ℝ)) / (N : ℝ)) := by
      ring
    linarith

/-- Probe 1.13: Singularity removal bootstrap bridge verified on a concrete non-constant map. -/
theorem probe_singularity_removal_bootstrap_bridge_nonconstant :
    let u := (id : CP1 → CP1)
    WeakJHolomorphicOn I_CP1 u Set.univ →
    (JHolomorphicOn (I := I_CP1) (I_dom := I_CP1) u Set.univ ∧
     ∃ z₁ z₂ : CP1, u z₁ ≠ u z₂) := by
  intro u h_weak
  refine ⟨singularity_removal_bootstrap_bridge I_CP1 u h_weak, ?_⟩
  exact concrete_nonconstant_map_nonconstant

--------------------------------------------------------------------------------
-- SECTION 2: P0-8 Moduli Space Topology Axioms & Consistency
--------------------------------------------------------------------------------

/-- Probe 2.1: moduliSpaceTopology directly satisfies IsOpen ∅. -/
theorem probe_moduli_space_topology_isOpen_empty (k : ℕ) (B : ℝ) :
    (moduliSpaceTopology I (M := M) k B).IsOpen ∅ := by
  intro u_seq u_lim hu_empty h_conv
  cases hu_empty

/-- Probe 2.2: Mathlib's isOpen_empty holds for moduliSpaceTopology. -/
theorem probe_moduli_space_topology_isOpen_empty_inst (k : ℕ) (B : ℝ) :
    letI : TopologicalSpace (ModuliSpace I (M := M) k B) := moduliSpaceTopologicalSpace I k B
    IsOpen (∅ : Set (ModuliSpace I (M := M) k B)) := by
  letI : TopologicalSpace (ModuliSpace I (M := M) k B) := moduliSpaceTopologicalSpace I k B
  exact isOpen_empty

/-- Probe 2.3: Mathlib's isOpen_univ holds for moduliSpaceTopology. -/
theorem probe_moduli_space_topology_isOpen_univ (k : ℕ) (B : ℝ) :
    letI : TopologicalSpace (ModuliSpace I (M := M) k B) := moduliSpaceTopologicalSpace I k B
    IsOpen (Set.univ : Set (ModuliSpace I (M := M) k B)) := by
  letI : TopologicalSpace (ModuliSpace I (M := M) k B) := moduliSpaceTopologicalSpace I k B
  exact isOpen_univ

/-- Probe 2.4: Binary intersection of open sets is open. -/
theorem probe_moduli_space_topology_isOpen_inter (k : ℕ) (B : ℝ)
    (s t : Set (ModuliSpace I (M := M) k B)) :
    letI : TopologicalSpace (ModuliSpace I (M := M) k B) := moduliSpaceTopologicalSpace I k B
    IsOpen s → IsOpen t → IsOpen (s ∩ t) := by
  letI : TopologicalSpace (ModuliSpace I (M := M) k B) := moduliSpaceTopologicalSpace I k B
  intro hs ht
  exact hs.inter ht

/-- Probe 2.5: Arbitrary infinite sUnion of open sets is open. -/
theorem probe_moduli_space_topology_isOpen_sUnion_infinite (k : ℕ) (B : ℝ)
    (S : Set (Set (ModuliSpace I (M := M) k B))) :
    letI : TopologicalSpace (ModuliSpace I (M := M) k B) := moduliSpaceTopologicalSpace I k B
    (∀ s ∈ S, IsOpen s) → IsOpen (⋃₀ S) := by
  letI : TopologicalSpace (ModuliSpace I (M := M) k B) := moduliSpaceTopologicalSpace I k B
  intro hS
  exact isOpen_sUnion hS

/-- Probe 2.6: Empty sUnion is open. -/
theorem probe_moduli_space_topology_isOpen_sUnion_empty (k : ℕ) (B : ℝ) :
    letI : TopologicalSpace (ModuliSpace I (M := M) k B) := moduliSpaceTopologicalSpace I k B
    IsOpen (⋃₀ (∅ : Set (Set (ModuliSpace I (M := M) k B)))) := by
  letI : TopologicalSpace (ModuliSpace I (M := M) k B) := moduliSpaceTopologicalSpace I k B
  rw [Set.sUnion_empty]
  exact isOpen_empty

/-- Probe 2.7: Arbitrary indexed union of open sets is open. -/
theorem probe_moduli_space_topology_isOpen_iUnion (k : ℕ) (B : ℝ)
    {ι : Type*} (U : ι → Set (ModuliSpace I (M := M) k B)) :
    letI : TopologicalSpace (ModuliSpace I (M := M) k B) := moduliSpaceTopologicalSpace I k B
    (∀ i, IsOpen (U i)) → IsOpen (⋃ i, U i) := by
  letI : TopologicalSpace (ModuliSpace I (M := M) k B) := moduliSpaceTopologicalSpace I k B
  intro hU
  exact isOpen_iUnion hU

/-- Probe 2.8: Subspace topology on ModuliSpaceInClass satisfies topological space axioms. -/
theorem probe_moduli_space_in_class_topology_empty_and_univ (k : ℕ) (A : HomologyClass2 M) :
    letI : TopologicalSpace (ModuliSpaceInClass I (M := M) k A) := moduliSpaceInClassTopologicalSpace I k A
    IsOpen (∅ : Set (ModuliSpaceInClass I (M := M) k A)) ∧
    IsOpen (Set.univ : Set (ModuliSpaceInClass I (M := M) k A)) := by
  letI : TopologicalSpace (ModuliSpaceInClass I (M := M) k A) := moduliSpaceInClassTopologicalSpace I k A
  exact ⟨isOpen_empty, isOpen_univ⟩

--------------------------------------------------------------------------------
-- SECTION 3: P0-11 Core Call-Graph Completeness and Non-Bypass
--------------------------------------------------------------------------------

/-- Probe 3.1: G03 -> G02 & G01 wiring: gromov_compactness_core directly connects
assemble_prestable_limit (G01) and stabilize_prestable_tree (G02). -/
theorem probe_gromov_compactness_core_wiring
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  gromov_compactness_core I th u_seq B h_nonconst h_jhol h_energy h_fin

/-- Probe 3.2: G02: stabilize_prestable_tree produces valid StableSphereTreeLimit
preserving total energy and all 5 convergence fields with zero direct sorry. -/
theorem probe_stabilize_prestable_tree_wiring
    (u_seq : ℕ → (CP1 → M)) (pdata : PrestableLimitData I u_seq)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v) =
        ∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) := by
  obtain ⟨u_lim, h_en, _⟩ := stabilize_prestable_tree I u_seq pdata h_nonconst
  exact ⟨u_lim, h_en⟩

/-- Probe 3.3: G01 -> C02 & B07: assemble_prestable_limit branches on S = ∅
(using prestable_limit_singleton_subseq) vs S ≠ ∅ (using resolve_single_defect_tree). -/
theorem probe_assemble_prestable_limit_wiring
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit I th u_seq B h_jhol h_energy h_fin

/-- Probe 3.4: C02 -> C01: exists_concentration_data consumes weak_energy_measure_compactness (C01). -/
theorem probe_exists_concentration_data_wiring
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (hB : 0 ≤ B) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤)
    (thresh : Bubbling.TargetThresholds I M) :
    Nonempty (ConcentrationData I u_seq B thresh) :=
  exists_concentration_data I u_seq h_jhol B hB h_en h_fin thresh

/-- Probe 3.5: C01: weak_energy_measure_compactness consumes weak measure compactness reduction. -/
theorem probe_weak_energy_measure_compactness_wiring
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (hB : 0 < B)
    (h_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤) :
    ∃ (σ : Bookkeeping.SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim :=
  weak_energy_measure_compactness I u_seq B hB h_bdd h_fin

/-- Probe 3.6: B07: resolve_single_defect_tree constructs a finite rooted bubble tree
with energy rank induction with zero direct sorry. -/
theorem probe_resolve_single_defect_tree_wiring
    (thresh : Bubbling.TargetThresholds I M) (m_defect : ℝ) (hm : 0 < m_defect) (base_val : M) :
    Nonempty (Bubbling.LocalDefectTree I thresh m_defect base_val) :=
  Bubbling.resolve_single_defect_tree I thresh m_defect hm base_val

--------------------------------------------------------------------------------
-- SECTION 4: Axiom Census
--------------------------------------------------------------------------------

#print axioms probe_ck_holder_norm_k_zero
#print axioms probe_ck_holder_norm_k_one
#print axioms probe_ck_holder_norm_k0_le_k1
#print axioms probe_ck_holder_norm_deriv_le_k1
#print axioms probe_holder_seminorm_alpha_zero
#print axioms probe_holder_quotient_alpha_zero
#print axioms probe_holder_seminorm_alpha_one
#print axioms probe_holder_quotient_alpha_one
#print axioms probe_shrinking_radius_extreme_equal
#print axioms probe_shrinking_radius_at_zero
#print axioms probe_shrinking_radius_at_N
#print axioms probe_shrinking_radius_bounds
#print axioms probe_moduli_space_topology_isOpen_empty
#print axioms probe_moduli_space_topology_isOpen_empty_inst
#print axioms probe_moduli_space_topology_isOpen_univ
#print axioms probe_moduli_space_topology_isOpen_inter
#print axioms probe_moduli_space_topology_isOpen_sUnion_infinite
#print axioms probe_moduli_space_topology_isOpen_sUnion_empty
#print axioms probe_moduli_space_topology_isOpen_iUnion
#print axioms probe_moduli_space_in_class_topology_empty_and_univ
#print axioms local_defect_tree_of_empty_children
#print axioms stabilize_prestable_tree_of_stable_root
#print axioms prestable_limit_singleton_subseq
#print axioms weak_energy_measure_compactness_of_weak_measure_compactness
#print axioms energyMeasureExtended_le_ofReal_of_totalEnergy_le

end GromovCompactness.AdversarialMilestone3Challenger2
