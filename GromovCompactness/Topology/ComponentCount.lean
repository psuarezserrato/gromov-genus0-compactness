/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.HoferRescaling
import GromovCompactness.Topology.SphereTree

open scoped Manifold ContDiff Topology Classical
open Metric Set Filter GromovCompactness Classical

namespace GromovCompactness.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-!
# Task G04: Component Counts and Universal Vertex Bounds

This module formalizes the numerical component bounds for stable genus 0 Gromov limits,
following `gromov_compactness.pdf` §2.2, §2.3, Theorem 1, and `GROMOV_COMPACTNESS_BLUEPRINT.md` §4.11 (Task `G04`).

## Key Theorems
- `principal_components_energy_bound`: $P \cdot h \le B$, hence $P \le \lfloor B / h \rfloor$.
- `component_count_bounds`: For multi-vertex trees ($|V| > 1$), $G \le P - 2$ and $|V| \le 2P - 2$.
  Universally across all trees (including single spheres $|V| = 1$), $(|V| : \mathbb{Z}) \le \max(1, 2\lfloor B/h \rfloor - 2)$.
- `component_count_bounds_marked`: Generalization to $k$-marked curves: $G \le P + k - 2$ and
  $(|V| : \mathbb{Z}) \le \max(1, 2\lfloor B/h \rfloor + k - 2)$.
-/

/-- Each principal (non-constant) component carries energy at least $h > 0$, hence $P \cdot h \le B$. -/
theorem principal_components_energy_bound
    (th : Bubbling.TargetThresholds I M)
    (u_lim : StableSphereTreeLimit I (M := M)) (B : ℝ)
    (h_energy : (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B) :
    let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
    P * th.h ≤ B := by
  intro P
  let s_prin := Finset.univ.filter (is_principal_component I u_lim)
  have hP : P = s_prin.card := by
    dsimp [P, s_prin]
    rw [Fintype.card_subtype]
  have h_each : ∀ v ∈ s_prin, th.h ≤ totalEnergy I (u_lim.map v) := by
    intro v hv
    have hv_prin : is_principal_component I u_lim v := (Finset.mem_filter.mp hv).2
    have hv_nonconst : ¬ ∃ c : M, ∀ z : CP1, u_lim.map v z = c := hv_prin
    have h_sph := th.h_sph (u_lim.map v) (u_lim.is_jhol v) hv_nonconst
    exact th.h_le_sph.trans h_sph
  have h_sum_le : ∑ v ∈ s_prin, th.h ≤ ∑ v ∈ s_prin, totalEnergy I (u_lim.map v) :=
    Finset.sum_le_sum h_each
  have h_const_sum : ∑ v ∈ s_prin, th.h = (P : ℝ) * th.h := by
    rw [Finset.sum_const, nsmul_eq_mul, hP]
  rw [h_const_sum] at h_sum_le
  have h_nonneg : ∀ v : u_lim.tree.V, 0 ≤ totalEnergy I (u_lim.map v) := by
    intro v
    exact energy_nonneg I (u_lim.map v) Set.univ
  have h_sub_le : ∑ v ∈ s_prin, totalEnergy I (u_lim.map v) ≤
      ∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v) := by
    apply Finset.sum_le_univ_sum_of_nonneg
    intro i
    exact h_nonneg i
  exact h_sum_le.trans (h_sub_le.trans h_energy)

/-- **Universal Component Count Bounds (Contract G04 & Theorem 1)**.
For any stable sphere tree limit of total energy $\le B$:
1. $P \cdot h \le B$, so $P \le \lfloor B / h \rfloor$.
2. If $|V| > 1$, then $G \le P - 2$ and $|V| \le 2P - 2$.
3. Universally across all configurations (including single curves $|V| = 1$), the safe integer bound
   $$(|V| : \mathbb{Z}) \le \max(1, 2\lfloor B / h \rfloor - 2)$$
   holds without natural subtraction truncation artifacts. -/
theorem component_count_bounds
    (th : Bubbling.TargetThresholds I M)
    (u_lim : StableSphereTreeLimit I (M := M)) (B : ℝ)
    (h_energy : (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B) :
    let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
    let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
    (P * th.h ≤ B) ∧
    (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
    ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) := by
  intro P G
  have h_energy_bound : (P : ℝ) * th.h ≤ B :=
    principal_components_energy_bound I th u_lim B h_energy
  refine ⟨h_energy_bound, ?_, ?_⟩
  · intro h_multi
    have h_bound := ghost_components_bound I u_lim P G h_multi rfl rfl
    constructor
    · omega
    · omega
  · by_cases h_multi : 1 < Fintype.card u_lim.tree.V
    · have h_bound := ghost_components_bound I u_lim P G h_multi rfl rfl
      have h_card_le : (Fintype.card u_lim.tree.V : ℤ) ≤ 2 * (P : ℤ) - 2 := by
        omega
      have h_P_le_div : (P : ℝ) ≤ B / th.h := by
        rwa [le_div_iff₀ th.h_pos]
      have h_P_le_floor : (P : ℤ) ≤ ⌊B / th.h⌋ := by
        rw [Int.le_floor]
        exact h_P_le_div
      have h_card_le_floor : (Fintype.card u_lim.tree.V : ℤ) ≤ 2 * ⌊B / th.h⌋ - 2 := by
        linarith
      exact h_card_le_floor.trans (le_max_right 1 (2 * ⌊B / th.h⌋ - 2))
    · have h_card1 : Fintype.card u_lim.tree.V = 1 := by
        have h_pos : 0 < Fintype.card u_lim.tree.V := Fintype.card_pos
        omega
      rw [h_card1]
      push_cast
      exact le_max_left 1 (2 * ⌊B / th.h⌋ - 2)

/-- Generalized component count bound for $k$-marked stable sphere trees ($k \ge 0$). -/
theorem component_count_bounds_marked
    (th : Bubbling.TargetThresholds I M)
    (u_lim : StableSphereTreeLimit I (M := M)) (B : ℝ) (k : ℕ)
    (h_energy : (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B)
    (_h_marked_stable : ∀ (v : u_lim.tree.V),
      is_ghost_component I u_lim v → 3 ≤ u_lim.tree.adj.degree v + k) :
    let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
    let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
    (P * th.h ≤ B) ∧
    (1 < Fintype.card u_lim.tree.V → G ≤ P + k - 2) ∧
    ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ + (k : ℤ) - 2)) := by
  intro P G
  have h_unmarked := component_count_bounds I th u_lim B h_energy
  refine ⟨h_unmarked.1, ?_, ?_⟩
  · intro h_multi
    have h_g := (h_unmarked.2.1 h_multi).1
    omega
  · by_cases h_multi : 1 < Fintype.card u_lim.tree.V
    · have h_bound := ghost_components_bound I u_lim P G h_multi rfl rfl
      have h_P_le_div : (P : ℝ) ≤ B / th.h := by
        have hP := h_unmarked.1
        rwa [le_div_iff₀ th.h_pos]
      have h_P_le_floor : (P : ℤ) ≤ ⌊B / th.h⌋ := by
        rw [Int.le_floor]
        exact h_P_le_div
      have h_card_le : (Fintype.card u_lim.tree.V : ℤ) ≤ 2 * ⌊B / th.h⌋ + (k : ℤ) - 2 := by
        have h1 : (Fintype.card u_lim.tree.V : ℤ) ≤ 2 * (P : ℤ) - 2 := by omega
        have h2 : 0 ≤ (k : ℤ) := Nat.cast_nonneg k
        linarith
      exact h_card_le.trans (le_max_right 1 (2 * ⌊B / th.h⌋ + (k : ℤ) - 2))
    · have h_card1 : Fintype.card u_lim.tree.V = 1 := by
        have h_pos : 0 < Fintype.card u_lim.tree.V := Fintype.card_pos
        omega
      rw [h_card1]
      push_cast
      exact le_max_left 1 (2 * ⌊B / th.h⌋ + (k : ℤ) - 2)

#print axioms principal_components_energy_bound
#print axioms component_count_bounds
#print axioms component_count_bounds_marked

end GromovCompactness.Topology
