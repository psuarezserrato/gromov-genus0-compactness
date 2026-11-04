/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.EnergyGap
import GromovCompactness.Topology.SmoothLocal
import GromovCompactness.Topology.SphereTree
import GromovCompactness.Compactness.Assembly

open scoped Manifold ContDiff Topology Classical
open Metric Set Filter GromovCompactness GromovCompactness.Assembly Classical

namespace GromovCompactness.Assembly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-!
# Task G02: Stabilize Without Weakening Convergence

This module formalizes root stabilization of prestable sphere tree limits, following
`gromov_compactness.pdf` §3.7 and `GROMOV_COMPACTNESS_BLUEPRINT.md` §4.10 (Task `G02`).

Only the original base root vertex can be unstable (constant of degree 1 or 2).
- If $\operatorname{deg}(v_0) = 1$, delete the root vertex and promote its unique child to root.
- If $\operatorname{deg}(v_0) = 2$, suppress the root vertex and join its two child edges with a bridge edge.
- If $\operatorname{deg}(v_0) \ge 3$ or $u_0$ is non-constant, the tree is already stable.
- By Contract C02 (no-atom upgrade), zero limiting defect mass at the forgotten node guarantees
  that convergence upgrades to smooth convergence across the join.
-/

/-- The total energy of a constant root component vanishes (Zero-sorry). -/
theorem totalEnergy_root_eq_zero_of_const
    (u_seq : ℕ → (CP1 → M)) (pdata : PrestableLimitData I u_seq)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
    totalEnergy I (pdata.map pdata.root) = 0 := by
  rcases h_const with ⟨c, hc⟩
  have hu : pdata.map pdata.root = fun _ => c := funext hc
  rw [hu]
  exact Analysis.totalEnergy_const I c

/-- Deleting a constant root vertex preserves the sum of component energies (Zero-sorry). -/
theorem sum_energy_erase_root
    (u_seq : ℕ → (CP1 → M)) (pdata : PrestableLimitData I u_seq)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
    (∑ v ∈ (Finset.univ.erase pdata.root), totalEnergy I (pdata.map v)) =
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) := by
  have h_zero := totalEnergy_root_eq_zero_of_const I u_seq pdata h_const
  have h_add := Finset.sum_erase_add (Finset.univ : Finset pdata.tree.V)
    (fun v => totalEnergy I (pdata.map v)) (Finset.mem_univ pdata.root)
  dsimp at h_add
  rw [h_zero, add_zero] at h_add
  exact h_add

/-- Extraction of the unique neighbor of a degree-1 root (Zero-sorry). -/
theorem root_degree_one_neighbor (tree : SphereTree) (root : tree.V)
    (h_deg1 : tree.adj.degree root = 1) :
    ∃! (w : tree.V), tree.adj.Adj root w := by
  have h_card : (tree.adj.neighborFinset root).card = 1 := h_deg1
  rcases Finset.card_eq_one.mp h_card with ⟨w, hw⟩
  refine ⟨w, ?_, ?_⟩
  · have hw_mem : w ∈ tree.adj.neighborFinset root := by rw [hw]; exact Finset.mem_singleton_self w
    exact (tree.adj.mem_neighborFinset root w).mp hw_mem
  · intro y hy
    have hy_mem : y ∈ tree.adj.neighborFinset root := (tree.adj.mem_neighborFinset root y).mpr hy
    rw [hw] at hy_mem
    exact Finset.mem_singleton.mp hy_mem

/-- Extraction of the two distinct neighbors of a degree-2 root (Zero-sorry). -/
theorem root_degree_two_neighbors (tree : SphereTree) (root : tree.V)
    (h_deg2 : tree.adj.degree root = 2) :
    ∃ (w₁ w₂ : tree.V), w₁ ≠ w₂ ∧ tree.adj.Adj root w₁ ∧ tree.adj.Adj root w₂ := by
  have h_card : (tree.adj.neighborFinset root).card = 2 := h_deg2
  rcases Finset.card_eq_two.mp h_card with ⟨w₁, w₂, hne, hw⟩
  refine ⟨w₁, w₂, hne, ?_, ?_⟩
  · have hw1 : w₁ ∈ tree.adj.neighborFinset root := by rw [hw]; exact Finset.mem_insert_self w₁ _
    exact (tree.adj.mem_neighborFinset root w₁).mp hw1
  · have hw2 : w₂ ∈ tree.adj.neighborFinset root := by rw [hw]; simp
    exact (tree.adj.mem_neighborFinset root w₂).mp hw2

/-- Prestable limit data with a stable root directly defines a stable sphere tree limit (Zero-sorry). -/
def stableSphereTreeLimit_of_prestable_of_stable_root
    (u_seq : ℕ → (CP1 → M)) (pdata : PrestableLimitData I u_seq)
    (h_root_stable : (∃ c : M, ∀ z : CP1, pdata.map pdata.root z = c) → 3 ≤ pdata.tree.adj.degree pdata.root) :
    StableSphereTreeLimit I (M := M) where
  tree := pdata.tree
  map := pdata.map
  is_jhol := pdata.is_jhol
  nodal_match := pdata.nodal_match
  stable := fun v hv => by
    by_cases h : v = pdata.root
    · subst h; exact h_root_stable hv
    · exact pdata.stable_off_root v h hv

/-- Stabilization of prestable tree limits when the root component is stable (Zero-sorry). -/
theorem stabilize_prestable_tree_of_stable_root
    (u_seq : ℕ → (CP1 → M)) (pdata : PrestableLimitData I u_seq)
    (h_root_stable : (∃ c : M, ∀ z : CP1, pdata.map pdata.root z = c) → 3 ≤ pdata.tree.adj.degree pdata.root) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v) =
        ∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ∧
      ∃ (frames : (v : u_lim.tree.V) → ℕ → MoebiusFrame),
        (∀ (v : u_lim.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (pdata.σ.1 n)) ∘ (frames v n).toHomeo)
            (u_lim.map v)
            (punctured_sphere { z | ∃ (w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w), z = u_lim.tree.node_point v w h })) := by
  let u_lim := stableSphereTreeLimit_of_prestable_of_stable_root I u_seq pdata h_root_stable
  refine ⟨u_lim, rfl, pdata.frames, ?_⟩
  intro v
  exact pdata.smooth_conv v

/-- Stabilization of prestable tree limits when the root component is non-constant (Zero-sorry). -/
theorem stabilize_prestable_tree_of_nonconst_root
    (u_seq : ℕ → (CP1 → M)) (pdata : PrestableLimitData I u_seq)
    (h_nonconst_root : ¬ ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v) =
        ∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ∧
      ∃ (frames : (v : u_lim.tree.V) → ℕ → MoebiusFrame),
        (∀ (v : u_lim.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (pdata.σ.1 n)) ∘ (frames v n).toHomeo)
            (u_lim.map v)
            (punctured_sphere { z | ∃ (w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w), z = u_lim.tree.node_point v w h })) := by
  have h_root_stable : (∃ c : M, ∀ z, pdata.map pdata.root z = c) → 3 ≤ pdata.tree.adj.degree pdata.root := by
    intro h_c; exact False.elim (h_nonconst_root h_c)
  exact stabilize_prestable_tree_of_stable_root I u_seq pdata h_root_stable

/-- Pruning operation: removing a degree-1 constant root vertex and promoting its child to root. -/
theorem prune_degree_one_root
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (_h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (_h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) := by
  sorry

/-- Suppression operation: suppressing a degree-2 constant root vertex and joining its two neighbors. -/
theorem suppress_degree_two_root
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (_h_deg2 : pdata.tree.adj.degree pdata.root = 2)
    (_h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) := by
  sorry

/-- Smooth convergence upgrade across a deleted node:
At an interior smooth point with zero limiting energy atom, convergence upgrades smoothly across the point. -/
theorem upgrade_convergence_across_deleted_node
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (p : CP1) (Ω : Set CP1)
    (_h_open : IsOpen Ω) (_hp : p ∈ Ω)
    (_h_conv_punct : SmoothLocalConvergesOn I u_seq u_lim (Ω \ {p}))
    (_h_no_atom : ∀ r > 0, ∃ N, ∀ n ≥ N, energyMeasure I (u_seq n) (disk_at (stereo_chart p) r) < r) :
    SmoothLocalConvergesOn I u_seq u_lim Ω := by
  sorry

/-- **Master Stabilization Theorem (Contract G02)**.
Contracting unstable ghost roots yields a fully stable sphere tree limit preserving all nodal matching,
energy conservation, and convergence conditions. -/
theorem stabilize_prestable_tree
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (_h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v) =
        ∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ∧
      ∃ (frames : (v : u_lim.tree.V) → ℕ → MoebiusFrame),
        (∀ (v : u_lim.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (pdata.σ.1 n)) ∘ (frames v n).toHomeo)
            (u_lim.map v)
            (punctured_sphere { z | ∃ (w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w), z = u_lim.tree.node_point v w h })) := by
  sorry

#print axioms totalEnergy_root_eq_zero_of_const
#print axioms sum_energy_erase_root
#print axioms root_degree_one_neighbor
#print axioms root_degree_two_neighbors
#print axioms stableSphereTreeLimit_of_prestable_of_stable_root
#print axioms stabilize_prestable_tree_of_stable_root
#print axioms stabilize_prestable_tree_of_nonconst_root

end GromovCompactness.Assembly
