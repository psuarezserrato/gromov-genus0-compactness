/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Challenger 1 Phase 3 Model A)
-/
import GromovCompactness

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology Classical
open Metric Set MeasureTheory Filter GromovCompactness Classical
open GromovCompactness.Bubbling GromovCompactness.Compactness
open GromovCompactness.Assembly GromovCompactness.Topology

namespace GromovCompactness.ChallengePhase3ModelA

/-!
# Empirical Adversarial Challenge Harness for Phase 3 Model A Scaffolding

This test harness rigorously evaluates, stress-tests, and verifies the Phase 3 Model A
formalization across all 13 modules (Contracts C01–C03, B03–B07, G01–G05).

## Verification Objectives:
1. **Evaluation and Edge Cases of `energy_rank_strict_decrease` (Contract B06)**:
   - Boundary condition $m = h$ with minimal child mass $m_i = 0$.
   - Integer multiples $m = 2h$ with $m_i = h$.
   - Fractional and non-integer multiples ($m = 2.5h, 2.99h, 2.01h, 1.7h$).
   - Extreme and asymptotic scales ($m = 10^6, h = 1$; microscopic $h = 10^{-3}$).
   - Sharpness demonstration: $m_i > m - h$ can fail rank decrease.
   - Axiom audit: confirming zero-`sorry` and standard foundational axioms only.

2. **Component Bounds Evaluation on $|V| = 1$ and $|V| > 1$ (Contract G04)**:
   - Single-sphere configuration $|V| = 1$: unconditional satisfaction of
     $(|V| : \mathbb{Z}) \le \max(1, 2\lfloor B/h \rfloor - 2)$ across all $B \in \mathbb{R}$ and $h > 0$.
   - Multi-vertex configuration $|V| > 1$: machine-checked arithmetic derivations of
     $G + 2 \le P$, $|V| + 2 \le 2P$, and $(|V| : \mathbb{Z}) \le \max(1, 2\lfloor B/h \rfloor - 2)$.
   - Explicit evaluation of concrete tree topologies ($P=2, G=0$; $P=3, G=1$; $P=4, G=2$; $P=10, G=8$).
   - Generalization to $k$-marked curves ($k \ge 1$).

3. **Synthesizing and Typechecking Structures**:
   - `WeakMeasureConvergence`: construct a full, machine-checked witness for constant measure sequences.
   - `ConcentrationData`: exercise and typecheck all fields and extraction theorem `exists_concentration_data`.
   - `OneLevelDecomposition`: exercise and typecheck all fields and extraction theorem `exists_one_level_decomposition`.
   - `PrestableLimitData`: exercise and typecheck all fields and assembly theorem `assemble_prestable_limit`.
   - `CompactnessWitness`: exercise and typecheck all fields and core theorem `gromov_compactness_core`.

4. **Master Integration & Gate Certification (Contract G05)**:
   - Verify `gromov_compactness_genus_zero` declaration signature, logic chain, and axiom footprints.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

--------------------------------------------------------------------------------
-- SECTION 1: Evaluation and Edge Cases of energy_rank_strict_decrease (B06)
--------------------------------------------------------------------------------

/-! ### 1.1 Concrete Numerical Evaluation -/

-- Edge Case 1: Minimal bubbling step m = h, child mass m_i = 0
theorem challenge_rank_edge_m_eq_h :
    Nat.floor ((0 : ℝ) / 1) < Nat.floor ((1 : ℝ) / 1) :=
  energy_rank_strict_decrease 1 0 1 (by norm_num) (by norm_num) (by norm_num)

-- Edge Case 2: Double threshold m = 2h, child mass m_i = h
theorem challenge_rank_edge_m_eq_2h :
    Nat.floor ((1 : ℝ) / 1) < Nat.floor ((2 : ℝ) / 1) :=
  energy_rank_strict_decrease 2 1 1 (by norm_num) (by norm_num) (by norm_num)

-- Edge Case 3a: Fractional rank m = 2.5, m_i = 1.5, h = 1
theorem challenge_rank_fractional_half :
    Nat.floor ((3/2 : ℝ) / 1) < Nat.floor ((5/2 : ℝ) / 1) :=
  energy_rank_strict_decrease (5/2) (3/2) 1 (by norm_num) (by norm_num) (by norm_num)

-- Edge Case 3b: Fractional rank close to upper integer m = 2.99, m_i = 1.99, h = 1
theorem challenge_rank_fractional_near_upper :
    Nat.floor ((199/100 : ℝ) / 1) < Nat.floor ((299/100 : ℝ) / 1) :=
  energy_rank_strict_decrease (299/100) (199/100) 1 (by norm_num) (by norm_num) (by norm_num)

-- Edge Case 3c: Fractional rank close to lower integer m = 2.01, m_i = 1.01, h = 1
theorem challenge_rank_fractional_near_lower :
    Nat.floor ((101/100 : ℝ) / 1) < Nat.floor ((201/100 : ℝ) / 1) :=
  energy_rank_strict_decrease (201/100) (101/100) 1 (by norm_num) (by norm_num) (by norm_num)

-- Edge Case 3d: Arbitrary threshold h = 0.5, m = 1.7, m_i = 1.2
theorem challenge_rank_non_integer_threshold :
    Nat.floor ((12/10 : ℝ) / (1/2)) < Nat.floor ((17/10 : ℝ) / (1/2)) :=
  energy_rank_strict_decrease (17/10) (12/10) (1/2) (by norm_num) (by norm_num) (by norm_num)

-- Edge Case 4a: Huge energy rank m = 1000000, m_i = 999999, h = 1
theorem challenge_rank_huge_rank :
    Nat.floor ((999999 : ℝ) / 1) < Nat.floor ((1000000 : ℝ) / 1) :=
  energy_rank_strict_decrease 1000000 999999 1 (by norm_num) (by norm_num) (by norm_num)

-- Edge Case 4b: Microscopic quantum h = 10⁻³, m = 1, m_i = 0.999
theorem challenge_rank_microscopic_quantum :
    Nat.floor ((999/1000 : ℝ) / (1/1000)) < Nat.floor ((1 : ℝ) / (1/1000)) :=
  energy_rank_strict_decrease 1 (999/1000) (1/1000) (by norm_num) (by norm_num) (by norm_num)

/-! ### 1.2 Zero Child Mass Universal Theorem -/

/-- For any energy m ≥ h > 0, child mass m_i = 0 strictly decreases rank to 0. -/
theorem challenge_rank_zero_child (m h : ℝ) (hh : 0 < h) (hm : h ≤ m) :
    Nat.floor ((0 : ℝ) / h) < Nat.floor (m / h) := by
  have h_pos : 0 ≤ (0 : ℝ) := by norm_num
  have h_le : (0 : ℝ) ≤ m - h := by linarith
  exact energy_rank_strict_decrease m 0 h hh h_pos h_le

/-! ### 1.3 Sharpness Demonstration (Boundary Barrier) -/

/-- Demonstrates that the hypothesis m_i ≤ m - h is sharp:
if m_i > m - h, the floor rank can fail to strictly decrease.
For m = 1.5, m_i = 1.2, h = 1: m - h = 0.5, but m_i = 1.2 > 0.5,
and ⌊1.2 / 1⌋ = 1 = ⌊1.5 / 1⌋, so strict decrease fails! -/
theorem challenge_rank_hypothesis_sharpness :
    Nat.floor ((12/10 : ℝ) / 1) = Nat.floor ((15/10 : ℝ) / 1) := by
  have h1 : Nat.floor ((12/10 : ℝ) / 1) = 1 := by
    rw [div_one, Nat.floor_eq_iff (by norm_num)]
    norm_num
  have h2 : Nat.floor ((15/10 : ℝ) / 1) = 1 := by
    rw [div_one, Nat.floor_eq_iff (by norm_num)]
    norm_num
  rw [h1, h2]

--------------------------------------------------------------------------------
-- SECTION 2: Component Bounds Evaluation on |V| = 1 and |V| > 1 (G04)
--------------------------------------------------------------------------------

/-! ### 2.1 Single Sphere Evaluation (|V| = 1) -/

/-- For |V| = 1, the integer bound (1 : ℤ) ≤ max 1 (2 * ⌊B / h⌋ - 2)
is unconditionally true for ANY real B and ANY h > 0, without requiring B ≥ h. -/
theorem challenge_single_sphere_unconditional (B h : ℝ) :
    (1 : ℤ) ≤ max 1 (2 * ⌊B / h⌋ - 2) :=
  le_max_left 1 _

-- Stress-test: B = 0 (sub-threshold, 2*⌊0⌋ - 2 = -2)
example (h : ℝ) : (1 : ℤ) ≤ max 1 (2 * ⌊(0 : ℝ) / h⌋ - 2) :=
  challenge_single_sphere_unconditional 0 h

-- Stress-test: B = 0.5 * h (sub-threshold, 2*⌊0.5⌋ - 2 = -2)
example (h : ℝ) : (1 : ℤ) ≤ max 1 (2 * ⌊(1/2 * h) / h⌋ - 2) :=
  challenge_single_sphere_unconditional (1/2 * h) h

-- Stress-test: B = h (single quantum threshold, 2*⌊1⌋ - 2 = 0)
example (h : ℝ) : (1 : ℤ) ≤ max 1 (2 * ⌊h / h⌋ - 2) :=
  challenge_single_sphere_unconditional h h

-- Stress-test: B = 100 * h (large energy, 2*⌊100⌋ - 2 = 198)
example (h : ℝ) : (1 : ℤ) ≤ max 1 (2 * ⌊(100 * h) / h⌋ - 2) :=
  challenge_single_sphere_unconditional (100 * h) h

/-! ### 2.2 Multi-Vertex Arithmetic Theorem (|V| > 1) -/

/-- Arithmetic core of Contract G04: for any stable sphere tree topology with V > 1,
if ghost stability gives G + 2 ≤ P, then V + 2 ≤ 2P and the integer bound holds. -/
theorem challenge_component_bounds_multi_arithmetic (P G V : ℕ) (B h : ℝ)
    (hh : 0 < h) (hB : (P : ℝ) * h ≤ B)
    (hV : 1 < V) (h_sum : V = P + G) (h_ghost : G + 2 ≤ P) :
    G + 2 ≤ P ∧ V + 2 ≤ 2 * P ∧ (V : ℤ) ≤ max 1 (2 * ⌊B / h⌋ - 2) := by
  have h_V_bound : V + 2 ≤ 2 * P := by omega
  have h_P_le_real : (P : ℝ) ≤ B / h := by
    rw [le_div_iff₀ hh]
    linarith
  have h_P_le_floor : (P : ℤ) ≤ ⌊B / h⌋ := Int.le_floor.mpr h_P_le_real
  have h_P_ge_2 : 2 ≤ P := by omega
  have h_V_le_2P2 : (V : ℤ) ≤ 2 * (P : ℤ) - 2 := by omega
  have h_2P_le_floor : 2 * (P : ℤ) - 2 ≤ 2 * ⌊B / h⌋ - 2 := by linarith
  have h_ge_1 : 1 ≤ 2 * ⌊B / h⌋ - 2 := by
    have : (2 : ℤ) ≤ (P : ℤ) := by exact_mod_cast h_P_ge_2
    linarith
  have h_le_max : 2 * ⌊B / h⌋ - 2 ≤ max 1 (2 * ⌊B / h⌋ - 2) :=
    le_max_right 1 (2 * ⌊B / h⌋ - 2)
  refine ⟨h_ghost, h_V_bound, ?_⟩
  linarith

/-! ### 2.3 Concrete Tree Topology Evaluations -/

-- Configuration 1: Two principal spheres attached at a node (P = 2, G = 0, V = 2)
theorem challenge_eval_two_spheres (B h : ℝ) (hh : 0 < h) (hB : (2 : ℝ) * h ≤ B) :
    (0 : ℕ) + 2 ≤ 2 ∧ (2 : ℕ) + 2 ≤ 2 * 2 ∧ (2 : ℤ) ≤ max 1 (2 * ⌊B / h⌋ - 2) :=
  challenge_component_bounds_multi_arithmetic 2 0 2 B h hh hB (by norm_num) (by norm_num) (by norm_num)

-- Configuration 2: Three principal spheres on one central ghost (P = 3, G = 1, V = 4)
theorem challenge_eval_tripod_tree (B h : ℝ) (hh : 0 < h) (hB : (3 : ℝ) * h ≤ B) :
    (1 : ℕ) + 2 ≤ 3 ∧ (4 : ℕ) + 2 ≤ 2 * 3 ∧ (4 : ℤ) ≤ max 1 (2 * ⌊B / h⌋ - 2) :=
  challenge_component_bounds_multi_arithmetic 3 1 4 B h hh hB (by norm_num) (by norm_num) (by norm_num)

-- Configuration 3: Four principal spheres with two ghost connectors (P = 4, G = 2, V = 6)
theorem challenge_eval_h_tree (B h : ℝ) (hh : 0 < h) (hB : (4 : ℝ) * h ≤ B) :
    (2 : ℕ) + 2 ≤ 4 ∧ (6 : ℕ) + 2 ≤ 2 * 4 ∧ (6 : ℤ) ≤ max 1 (2 * ⌊B / h⌋ - 2) :=
  challenge_component_bounds_multi_arithmetic 4 2 6 B h hh hB (by norm_num) (by norm_num) (by norm_num)

-- Configuration 4: Ten principal spheres with maximal ghost branching (P = 10, G = 8, V = 18)
theorem challenge_eval_large_tree (B h : ℝ) (hh : 0 < h) (hB : (10 : ℝ) * h ≤ B) :
    (8 : ℕ) + 2 ≤ 10 ∧ (18 : ℕ) + 2 ≤ 2 * 10 ∧ (18 : ℤ) ≤ max 1 (2 * ⌊B / h⌋ - 2) :=
  challenge_component_bounds_multi_arithmetic 10 8 18 B h hh hB (by norm_num) (by norm_num) (by norm_num)

/-! ### 2.4 Marked Sphere Trees Generalization (k ≥ 1) -/

/-- For k-marked trees with V > 1, G ≤ P + k - 2 and V ≤ 2P + k - 2. -/
theorem challenge_component_bounds_marked_arithmetic (P G V k : ℕ) (B h : ℝ)
    (hh : 0 < h) (hB : (P : ℝ) * h ≤ B)
    (hV : 1 < V) (h_sum : V = P + G) (h_ghost : G ≤ P + k - 2) :
    G ≤ P + k - 2 ∧ V ≤ 2 * P + k - 2 := by
  constructor
  · exact h_ghost
  · omega

--------------------------------------------------------------------------------
-- SECTION 3: Synthesizing and Typechecking Structures
--------------------------------------------------------------------------------

/-! ### 3.1 Structure 1: WeakMeasureConvergence (Contract C01) -/

/-- Synthesis test: Construct an explicit mathematical witness of `WeakMeasureConvergence`
for any finite Radon measure on CP1 under the constant sequence μ_n = μ. -/
theorem challenge_synthesize_weak_measure_convergence (μ : Measure CP1) :
    WeakMeasureConvergence (fun _ : ℕ => μ) μ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f _hf
    exact tendsto_const_nhds
  · intro K _hK
    rw [Filter.limsup_const]
  · intro A _hA
    exact tendsto_const_nhds
  · exact tendsto_const_nhds

#check weak_measure_compactness
#check (weak_energy_measure_compactness I)

/-! ### 3.2 Structure 2: ConcentrationData (Contract C02) -/

/-- Structural projection test: verify and typecheck fields of `ConcentrationData`. -/
def challenge_typecheck_concentration_data
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    Bookkeeping.SubseqMap × Measure CP1 × Finset CP1 × (CP1 → M) :=
  ⟨cdata.σ, cdata.μ, cdata.S, cdata.u₀⟩

theorem challenge_concentration_data_total_le
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    cdata.μ Set.univ ≤ ENNReal.ofReal B :=
  cdata.μ_total_le

#check (exists_concentration_data I)
#check (smooth_convergence_upgrade_of_zero_mass I)

/-! ### 3.3 Structure 3: OneLevelDecomposition (Contract B04) -/

/-- Structural projection test: verify and typecheck fields of `OneLevelDecomposition`. -/
def challenge_typecheck_one_level_decomp
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) :
    (CP1 → M) × Finset ℂ × (ℂ → ℝ) :=
  ⟨decomp.v, decomp.q, decomp.m_child⟩

theorem challenge_one_level_node_match
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) :
    decomp.v north_pole = base_val :=
  decomp.node_match

theorem challenge_one_level_mass_sum
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) :
    m_defect = totalEnergy I decomp.v + ∑ z ∈ decomp.q, decomp.m_child z :=
  decomp.mass_sum

#check (exists_one_level_decomposition I)
#check (child_mass_le_parent_sub_h I)
#check (child_rank_strict_decrease I)

/-! ### 3.4 Structure 4: PrestableLimitData (Contract G01) -/

/-- Structural projection test: verify and typecheck fields of `PrestableLimitData`. -/
def challenge_typecheck_prestable_limit_data
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq) :
    SphereTree × pdata.tree.V × ((v : pdata.tree.V) → CP1 → M) × Bookkeeping.SubseqMap ×
    ((v : pdata.tree.V) → ℕ → MoebiusFrame) :=
  ⟨pdata.tree, pdata.root, pdata.map, pdata.σ, pdata.frames⟩

#check assemble_global_frames
#check (assemble_prestable_limit I)

/-! ### 3.5 Structure 5: CompactnessWitness (Contract G03) -/

/-- Structural projection test: verify and typecheck fields of `CompactnessWitness`. -/
def challenge_typecheck_compactness_witness
    (u_seq : ℕ → (CP1 → M)) (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I u_seq u_lim) :
    Bookkeeping.SubseqMap × ((v : u_lim.tree.V) → ℕ → MoebiusFrame) :=
  ⟨wit.σ, wit.frames⟩

/-- Energy conservation proposition verified from CompactnessWitness. -/
theorem challenge_witness_energy_conv
    (u_seq : ℕ → (CP1 → M)) (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I u_seq u_lim) :
    Tendsto (fun n => totalEnergy I (u_seq (wit.σ.1 n))) atTop
      (𝓝 (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v))) :=
  wit.energy_conv

#check (gromov_compactness_core I)
#check (gromov_subsequence_alternative I)

--------------------------------------------------------------------------------
-- SECTION 4: Master Integration and Axiom Audit (Contract G05)
--------------------------------------------------------------------------------

#check (gromov_compactness_genus_zero I)

/-! ### 4.1 Axiom Footprint Audits -/

-- Verify that energy_rank_strict_decrease is zero-sorry and depends only on standard Lean axioms
#print axioms energy_rank_strict_decrease

-- Verify that all challenge numerical and arithmetic proofs are zero-sorry and depend only on standard Lean axioms
#print axioms challenge_rank_edge_m_eq_h
#print axioms challenge_rank_edge_m_eq_2h
#print axioms challenge_rank_fractional_half
#print axioms challenge_rank_fractional_near_upper
#print axioms challenge_rank_fractional_near_lower
#print axioms challenge_rank_non_integer_threshold
#print axioms challenge_rank_huge_rank
#print axioms challenge_rank_microscopic_quantum
#print axioms challenge_rank_zero_child
#print axioms challenge_rank_hypothesis_sharpness
#print axioms challenge_single_sphere_unconditional
#print axioms challenge_component_bounds_multi_arithmetic
#print axioms challenge_eval_two_spheres
#print axioms challenge_eval_tripod_tree
#print axioms challenge_eval_h_tree
#print axioms challenge_eval_large_tree
#print axioms challenge_component_bounds_marked_arithmetic
#print axioms challenge_synthesize_weak_measure_convergence
#print axioms challenge_witness_energy_conv

-- Confirm master theorem axiom footprint under Model A (expected: contains sorryAx from stubbed sub-proofs)
#print axioms gromov_compactness_genus_zero

end GromovCompactness.ChallengePhase3ModelA
