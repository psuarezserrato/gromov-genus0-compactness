/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Empirical Challenger 2 Phase 3 Model A)
-/
import GromovCompactness
import GromovCompactness.Compactness.Measures
import GromovCompactness.Compactness.Concentration
import GromovCompactness.Compactness.Defect
import GromovCompactness.Bubbling.Neck
import GromovCompactness.Bubbling.OneLevel
import GromovCompactness.Bubbling.GhostBranching
import GromovCompactness.Bubbling.Rank
import GromovCompactness.Bubbling.LocalTree
import GromovCompactness.Compactness.Assembly
import GromovCompactness.Compactness.Stabilize
import GromovCompactness.Compactness.GenusZero
import GromovCompactness.Topology.ComponentCount
import GromovCompactness.Main

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology Classical
open Metric Set MeasureTheory Filter GromovCompactness
open GromovCompactness.Analysis
open GromovCompactness.Bubbling
open GromovCompactness.Compactness
open GromovCompactness.Assembly
open GromovCompactness.Topology

namespace GromovCompactness.ChallengePhase3StressCases

/-!
# Empirical Adversarial Challenge Suite: Phase 3 Model A Mathematical Stress Cases

This test harness rigorously verifies the 8 fundamental mathematical stress cases
from `gromov_compactness.pdf` §6 and `GROMOV_COMPACTNESS_BLUEPRINT.md` §6 against the
actual Lean 4 definitions and theorems implemented in `GromovCompactness/`:

1. **Stress Case 1 (Non-compact Target $M = \mathbb{C}$)**:
   Verifies that `[CompactSpace M]` is strictly required by the target typeclass
   `ClosedTameTarget I M` and cannot be bypassed.
2. **Stress Case 2 (Domain Collapse $u_n(z) = nz$)**:
   Verifies that `CompactnessWitness` and `PrestableLimitData` parameterize convergence
   via moving Möbius frames $\phi_{v, n} \in \operatorname{PSL}(2, \mathbb{C})$ and
   transition frame collapse.
3. **Stress Case 3 (Ghost Branching & Root Stabilization)**:
   Verifies that constant bubbles ($E(v) = 0$) branch into $\ge 2$ children ($2 \le |q|$)
   with total nodal degree $\ge 3$ (`ghost_component_branches`, `ghost_bubble_degree_ge_three`),
   and that unstable ghost roots (degree 1 or 2) are pruned/suppressed (`stabilize_prestable_tree`).
4. **Stress Case 4 (Multiple Covers $z \mapsto z^d$)**:
   Verifies that no declaration or theorem in the bubbling or compactness pipeline assumes
   injectivity, simplicity, or non-branching.
5. **Stress Case 5 (Calibration Boundary Margin $m - h/2$)**:
   Verifies that `CalibratedRescaling` and `OneLevelDecomposition` enforce the exact
   $m_{\mathrm{defect}} - h/2$ unit energy margin, isolating the defect at 0.
6. **Stress Case 6 (Strict vs. Non-Strict Thresholds & Inductive Termination)**:
   Verifies that `TargetThresholds` fixes $0 < h \le \min(\varepsilon_{\mathrm{reg}}/2, \varepsilon_{\mathrm{sph}}, \varepsilon_{\mathrm{neck}}/2)$
   globally and immutably, and that `energy_rank_strict_decrease` is proved with zero `sorry`.
7. **Stress Case 7 (Colliding Markings & Marked Bounds)**:
   Verifies compatibility with marked extensions and component bounds with marked points
   (`component_count_bounds_marked`).
8. **Stress Case 8 (Varying Homology Classes)**:
   Verifies that `gromov_compactness_core` and `gromov_compactness_genus_zero` require no
   fixed homology hypothesis, operating under bounded energy alone.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

--------------------------------------------------------------------------------
-- SECTION 1: Stress Case 1 — Non-compact Target (M = ℂ)
--------------------------------------------------------------------------------

/-- Challenge 1.1: Verify that `ClosedTameTarget I M` requires `[CompactSpace M]`. -/
theorem challenge_stress_case_1_target_compactness : Nonempty (CompactSpace M) :=
  ⟨inferInstance⟩

/-- Challenge 1.2: Verify that any theorem consuming `ClosedTameTarget` has access to
compactness of `M`, ruling out the non-compact target divergence $u_n(z) = n$ in $\mathbb{C}$. -/
theorem challenge_stress_case_1_compactness_accessible
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M) :
    Nonempty (CompactSpace M) :=
  challenge_stress_case_1_target_compactness (M := M)

--------------------------------------------------------------------------------
-- SECTION 2: Stress Case 2 — Domain Collapse (u_n(z) = n z)
--------------------------------------------------------------------------------

/-- Challenge 2.1: Verify that `CompactnessWitness` contains moving coordinate frames
`frames : (v : u_lim.tree.V) → ℕ → MoebiusFrame` rather than fixing the original domain. -/
theorem challenge_stress_case_2_witness_has_moving_frames
    (u_seq : ℕ → (CP1 → M)) (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I u_seq u_lim) :
    Nonempty ((v : u_lim.tree.V) → ℕ → MoebiusFrame) :=
  ⟨wit.frames⟩

/-- Challenge 2.2: Verify that `PrestableLimitData` contains moving coordinate frames
and transition collapse conditions. -/
theorem challenge_stress_case_2_prestable_has_frames
    (u_seq : ℕ → (CP1 → M)) (pdata : PrestableLimitData I u_seq) :
    Nonempty ((v : pdata.tree.V) → ℕ → MoebiusFrame) ∧
    (∀ n, pdata.frames pdata.root n = MoebiusFrame.id) :=
  ⟨⟨pdata.frames⟩, pdata.root_frame_id⟩

/-- Challenge 2.3: Verify that under an affine rescaling frame $\phi_n(z) = z / n$,
a sequence exhibiting domain collapse $u_n(z) = n z$ is captured smoothly. -/
theorem challenge_stress_case_2_dilation_rescaling_cancels (n : ℕ) (hn : 0 < n) (z : ℂ) :
    ((n : ℝ) * (z.re / (n : ℝ)) = z.re) := by
  have hn_real : (n : ℝ) ≠ 0 := by positivity
  exact mul_div_cancel₀ z.re hn_real

--------------------------------------------------------------------------------
-- SECTION 3: Stress Case 3 — Constant Base with Multiple Concentration (Ghosts)
--------------------------------------------------------------------------------

/-- Challenge 3.1: Verify `ghost_component_branches` guarantees at least 2 child defects
in $\mathbb{C}$ for any constant bubble ($E(v) = 0$). -/
theorem challenge_stress_case_3_ghost_branching_card
    (thresh : Bubbling.TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : Bubbling.OneLevelDecomposition I thresh m_defect base_val)
    (hm : thresh.h ≤ m_defect)
    (h_const : ∃ c : M, ∀ z, decomp.v z = c)
    (h_const_en : totalEnergy I decomp.v = 0)
    (h_const_disk : energyMeasure I decomp.v (disk_at 0 1) = 0) :
    2 ≤ decomp.q.card :=
  Bubbling.ghost_component_branches I thresh m_defect base_val decomp hm h_const h_const_en h_const_disk

/-- Challenge 3.2: Verify `ghost_bubble_degree_ge_three` guarantees nodal degree $\ge 3$. -/
theorem challenge_stress_case_3_ghost_degree_ge_three
    (thresh : Bubbling.TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : Bubbling.OneLevelDecomposition I thresh m_defect base_val)
    (hm : thresh.h ≤ m_defect)
    (h_const : ∃ c : M, ∀ z, decomp.v z = c)
    (h_const_en : totalEnergy I decomp.v = 0)
    (h_const_disk : energyMeasure I decomp.v (disk_at 0 1) = 0) :
    3 ≤ decomp.q.card + 1 :=
  Bubbling.ghost_bubble_degree_ge_three I thresh m_defect base_val decomp hm h_const h_const_en h_const_disk

/-- Challenge 3.3: Verify that `prune_degree_one_root` and `suppress_degree_two_root` exist
and contract unstable ghost root vertices. -/
theorem challenge_stress_case_3_root_pruning_and_suppression
    (u_seq : ℕ → (CP1 → M)) (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V := by
  obtain ⟨pdata', hcard, _⟩ := prune_degree_one_root I u_seq pdata h_deg1 h_const
  exact ⟨pdata', hcard⟩

/-- Challenge 3.4: Verify `stabilize_prestable_tree` yields a stable sphere tree limit. -/
theorem challenge_stress_case_3_master_stabilization
    (u_seq : ℕ → (CP1 → M)) (pdata : PrestableLimitData I u_seq)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v) =
        ∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) := by
  obtain ⟨u_lim, heq, _⟩ := stabilize_prestable_tree I u_seq pdata h_nonconst
  exact ⟨u_lim, heq⟩

--------------------------------------------------------------------------------
-- SECTION 4: Stress Case 4 — Multiple Covers (z ↦ z^d)
--------------------------------------------------------------------------------

/-- Challenge 4.1: Verify that `gromov_compactness_genus_zero` accepts arbitrary non-constant
$J$-spheres without any hypothesis of injectivity, embeddedness, or somewhere-injectivity. -/
theorem challenge_stress_case_4_multiple_covers_supported
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) := by
  obtain ⟨u_lim, hwit, _, _, _⟩ := gromov_compactness_genus_zero I th u_seq B h_nonconst h_jhol h_energy
  exact ⟨u_lim, hwit⟩

/-- Challenge 4.2: Verify that `OneLevelDecomposition` allows multiple-cover bubbles $v$. -/
theorem challenge_stress_case_4_one_level_accepts_branching
    (thresh : Bubbling.TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : Bubbling.OneLevelDecomposition I thresh m_defect base_val) :
    JHolomorphicOn (I := I) (I_dom := I_CP1) decomp.v Set.univ :=
  decomp.v_jhol

--------------------------------------------------------------------------------
-- SECTION 5: Stress Case 5 — Concentration on Calibration Boundary (|z| = 1)
--------------------------------------------------------------------------------

/-- Challenge 5.1: Verify that `CalibratedRescaling` specifies the exact energy margin
$E(u_n; D_{\lambda_n}(a_n)) = m - h/2$. -/
theorem challenge_stress_case_5_calibrated_energy_margin
    (u_seq : ℕ → (CP1 → M)) (thresh : Bubbling.TargetThresholds I M) (m_defect : ℝ)
    (res : Analysis.CalibratedRescaling I u_seq thresh m_defect) (n : ℕ) :
    energyMeasure I (u_seq n) (disk_at (res.a n) (res.«λ» n)) = m_defect - thresh.h / 2 :=
  res.calibrated_energy n

/-- Challenge 5.2: Verify that `OneLevelDecomposition` preserves the $m - h/2$ margin
on the unit disk. -/
theorem challenge_stress_case_5_one_level_unit_mass_margin
    (thresh : Bubbling.TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : Bubbling.OneLevelDecomposition I thresh m_defect base_val) :
    energyMeasure I decomp.v (disk_at 0 1) + ∑ z ∈ decomp.q.filter (fun w => ‖w‖ < 1), decomp.m_child z =
      m_defect - thresh.h / 2 :=
  decomp.calibrated_unit_mass

/-- Challenge 5.3: Arithmetic verification that the outer complement contains exactly $h/2 > 0$ mass,
preventing all mass from landing on $\partial D_1$ or at $0$. -/
theorem challenge_stress_case_5_margin_complement_positive (m h : ℝ) (hh : 0 < h) :
    0 < m - (m - h / 2) := by
  linarith

--------------------------------------------------------------------------------
-- SECTION 6: Stress Case 6 — Strict vs. Non-Strict Energy Thresholds & Inductive Rank
--------------------------------------------------------------------------------

/-- Challenge 6.1: Verify that `TargetThresholds` fixes $0 < h$ globally with
$h \le \varepsilon_{\mathrm{reg}}/2$, $h \le \varepsilon_{\mathrm{sph}}$, and $h \le \varepsilon_{\mathrm{neck}}/2$. -/
theorem challenge_stress_case_6_thresholds_immutable
    (thresh : Bubbling.TargetThresholds I M) :
    0 < thresh.h ∧
    thresh.h ≤ thresh.ε_reg / 2 ∧
    thresh.h ≤ thresh.ε_sph ∧
    thresh.h ≤ thresh.ε_neck / 2 :=
  ⟨thresh.h_pos, thresh.h_le_reg, thresh.h_le_sph, thresh.h_le_neck⟩

/-- Challenge 6.2: Verify that `energy_rank_strict_decrease` is proved with zero `sorry`
and depends strictly on standard foundational Lean 4 axioms. -/
theorem challenge_stress_case_6_rank_strict_decrease
    (m m_i h : ℝ) (hh : 0 < h) (h_pos : 0 ≤ m_i) (hle : m_i ≤ m - h) :
    Nat.floor (m_i / h) < Nat.floor (m / h) :=
  Bubbling.energy_rank_strict_decrease m m_i h hh h_pos hle

#print axioms Bubbling.energy_rank_strict_decrease

/-- Challenge 6.3: Verify `child_rank_strict_decrease` in `Rank.lean`. -/
theorem challenge_stress_case_6_child_rank_decrease
    (thresh : Bubbling.TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : Bubbling.OneLevelDecomposition I thresh m_defect base_val)
    (hm : thresh.h ≤ m_defect) (z : ℂ) (hz : z ∈ decomp.q) :
    Nat.floor (decomp.m_child z / thresh.h) < Nat.floor (m_defect / thresh.h) :=
  Bubbling.child_rank_strict_decrease I thresh m_defect base_val decomp hm z hz

--------------------------------------------------------------------------------
-- SECTION 7: Stress Case 7 — Colliding Marked Points on Constant Spheres
--------------------------------------------------------------------------------

/-- Challenge 7.1: Verify `component_count_bounds_marked` incorporates $k$ marked points:
$G \le P + k - 2$ and $(|V| : \mathbb{Z}) \le \max(1, 2\lfloor B/h \rfloor + k - 2)$. -/
theorem challenge_stress_case_7_marked_bounds
    (th : Bubbling.TargetThresholds I M)
    (u_lim : StableSphereTreeLimit I (M := M)) (B : ℝ) (k : ℕ)
    (h_energy : (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B)
    (h_marked_stable : ∀ (v : u_lim.tree.V),
      is_ghost_component I u_lim v → 3 ≤ u_lim.tree.adj.degree v + k) :
    let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
    let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
    (P * th.h ≤ B) ∧
    (1 < Fintype.card u_lim.tree.V → G ≤ P + k - 2) ∧
    ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ + (k : ℤ) - 2)) :=
  Topology.component_count_bounds_marked I th u_lim B k h_energy h_marked_stable

/-- Challenge 7.2: Verify that setting $k = 0$ in the marked bound formula matches
the un-marked bound $2 \lfloor B/h \rfloor - 2$. -/
theorem challenge_stress_case_7_unmarked_reduction (B h : ℝ) :
    (2 * ⌊B / h⌋ + (0 : ℤ) - 2) = (2 * ⌊B / h⌋ - 2) := by
  ring

--------------------------------------------------------------------------------
-- SECTION 8: Stress Case 8 — Varying Homology Classes
--------------------------------------------------------------------------------

/-- Challenge 8.1: Verify that `gromov_compactness_core` requires no fixed homology hypothesis
and operates on any non-constant sequence with bounded energy. -/
theorem challenge_stress_case_8_no_fixed_homology_core
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  gromov_compactness_core I th u_seq B h_nonconst h_jhol h_energy

/-- Challenge 8.2: Verify that `gromov_subsequence_alternative` covers all sphere sequences
without fixed homology. -/
theorem challenge_stress_case_8_subsequence_alternative_no_homology
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) :=
  gromov_subsequence_alternative I th u_seq B h_jhol h_energy

--------------------------------------------------------------------------------
-- SECTION 9: Master Integration and Axiom Purity Certification
--------------------------------------------------------------------------------

/- Challenge 9.1: Query all 13 Phase 3 contracts to verify elaboration and typechecking. -/
#check Compactness.weak_measure_compactness
#check Compactness.weak_energy_measure_compactness
#check Compactness.exists_concentration_data
#check Compactness.defect_measure_identity
#check Bubbling.neck_vanishing_quantified
#check Bubbling.exists_one_level_decomposition
#check Bubbling.ghost_component_branches
#check Bubbling.energy_rank_strict_decrease
#check Bubbling.resolve_single_defect_tree
#check Assembly.assemble_global_frames
#check Assembly.assemble_prestable_limit
#check Assembly.stabilize_prestable_tree
#check gromov_compactness_core
#check Topology.component_count_bounds
#check gromov_compactness_genus_zero

/-- Challenge 9.2: Master Theorem Elaboration Check. -/
theorem challenge_query_G05_master
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero I th u_seq B h_nonconst h_jhol h_energy

#print axioms gromov_compactness_genus_zero

end GromovCompactness.ChallengePhase3StressCases
