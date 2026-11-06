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

theorem card_eq_one_of_degree_zero_of_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_conn : G.Connected) (root : V)
    (h_deg0 : G.degree root = 0) :
    Fintype.card V = 1 := by
  rw [Fintype.card_eq_one_iff]
  exact ⟨root, eq_root_of_degree_zero_of_connected G h_conn root h_deg0⟩

theorem card_subtype_eq_zero_of_all_eq_root
    {V : Type*} [Fintype V] (root : V)
    (h_all_eq : ∀ v : V, v = root)
    (P : V → Prop) [DecidablePred P]
    (h_not_root : ¬ P root) :
    Fintype.card {v : V // P v} = 0 := by
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun ⟨v, hv⟩ => ?_⟩
  rw [h_all_eq v] at hv
  exact h_not_root hv

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

/-- If every non-root component `v ≠ pdata.root` of a `PrestableLimitData` is constant, then
off-root stability (`pdata.stable_off_root`) and the Euler characteristic (`tree_degree_sum`)
force `Fintype.card pdata.tree.V = 1` and `pdata.tree.adj.degree pdata.root = 0` (`0 sorryAx`). -/
theorem PrestableLimitData.card_V_eq_one_and_degree_root_eq_zero_of_all_off_root_const
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_off : ∀ v : pdata.tree.V, v ≠ pdata.root → ∃ c : M, ∀ z, pdata.map v z = c) :
    Fintype.card pdata.tree.V = 1 ∧ pdata.tree.adj.degree pdata.root = 0 := by
  have h_deg_sum : (∑ v : pdata.tree.V, pdata.tree.adj.degree v) =
      2 * (Fintype.card pdata.tree.V - 1) :=
    tree_degree_sum pdata.tree
  have h_split : (∑ v ∈ Finset.univ.erase pdata.root, pdata.tree.adj.degree v) +
      pdata.tree.adj.degree pdata.root = ∑ v : pdata.tree.V, pdata.tree.adj.degree v :=
    Finset.sum_erase_add (Finset.univ : Finset pdata.tree.V)
      (fun v => pdata.tree.adj.degree v) (Finset.mem_univ pdata.root)
  have h_ge_three : 3 * (Finset.univ.erase pdata.root).card ≤
      ∑ v ∈ Finset.univ.erase pdata.root, pdata.tree.adj.degree v := by
    have h_le := Finset.card_nsmul_le_sum (Finset.univ.erase pdata.root)
      (fun v => pdata.tree.adj.degree v) 3
      (fun v hv => pdata.stable_off_root v (Finset.ne_of_mem_erase hv)
        (h_off v (Finset.ne_of_mem_erase hv)))
    simpa [Nat.mul_comm] using h_le
  have h_card_erase : (Finset.univ.erase pdata.root).card = Fintype.card pdata.tree.V - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ pdata.root), Finset.card_univ]
  have h_pos : 0 < Fintype.card pdata.tree.V := Fintype.card_pos
  omega

/-- Whenever `1 < Fintype.card pdata.tree.V`, there exists a non-root vertex `v ≠ pdata.root`
whose component map `pdata.map v` is non-constant (`0 sorryAx`). -/
theorem PrestableLimitData.exists_nonconst_off_root_of_card_V_gt_one
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_gt : 1 < Fintype.card pdata.tree.V) :
    ∃ v : pdata.tree.V, v ≠ pdata.root ∧ ¬ ∃ c : M, ∀ z, pdata.map v z = c := by
  by_contra h_all
  push_neg at h_all
  have h_eq := (pdata.card_V_eq_one_and_degree_root_eq_zero_of_all_off_root_const I u_seq h_all).1
  omega

/-- Whenever `0 < pdata.tree.adj.degree pdata.root`, there exists a non-root vertex `v ≠ pdata.root`
whose component map `pdata.map v` is non-constant (`0 sorryAx`). -/
theorem PrestableLimitData.exists_nonconst_off_root_of_degree_root_pos
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_pos : 0 < pdata.tree.adj.degree pdata.root) :
    ∃ v : pdata.tree.V, v ≠ pdata.root ∧ ¬ ∃ c : M, ∀ z, pdata.map v z = c := by
  by_contra h_all
  push_neg at h_all
  have h_deg0 := (pdata.card_V_eq_one_and_degree_root_eq_zero_of_all_off_root_const I u_seq h_all).2
  omega

/-- Whenever `pdata.root` is adjacent to some vertex `w₀`, there exists a non-root vertex `v ≠ pdata.root`
whose component map `pdata.map v` is non-constant (`0 sorryAx`). -/
theorem PrestableLimitData.exists_nonconst_off_root_of_adj_root
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    {w₀ : pdata.tree.V} (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀) :
    ∃ v : pdata.tree.V, v ≠ pdata.root ∧ ¬ ∃ c : M, ∀ z, pdata.map v z = c := by
  have h_pos : 0 < pdata.tree.adj.degree pdata.root :=
    (SimpleGraph.degree_pos_iff_exists_adj pdata.tree.adj pdata.root).mpr ⟨w₀, hw₀_adj⟩
  exact pdata.exists_nonconst_off_root_of_degree_root_pos I u_seq h_pos

/-- Whenever `0 < pdata.tree.adj.degree pdata.root`, the sum of component energies across `pdata.tree.V`
is at least `th.ε_sph` (`0 sorryAx`). -/
theorem PrestableLimitData.eps_sph_le_sum_of_degree_root_pos
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_pos : 0 < pdata.tree.adj.degree pdata.root) :
    th.ε_sph ≤ ∑ v : pdata.tree.V, totalEnergy I (pdata.map v) := by
  obtain ⟨v, _, hv_nc⟩ := pdata.exists_nonconst_off_root_of_degree_root_pos I u_seq h_pos
  have hv_ge : th.ε_sph ≤ totalEnergy I (pdata.map v) :=
    th.h_sph (pdata.map v) (pdata.is_jhol v) hv_nc
  have hv_le : totalEnergy I (pdata.map v) ≤ ∑ u : pdata.tree.V, totalEnergy I (pdata.map u) :=
    Finset.single_le_sum (fun u _ => energy_nonneg I (pdata.map u) Set.univ) (Finset.mem_univ v)
  exact hv_ge.trans hv_le

/-- Whenever `(∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) < th.ε_sph`, the root vertex has
degree `0` (`0 sorryAx`). -/
theorem PrestableLimitData.degree_root_eq_zero_of_sum_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_lt : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) < th.ε_sph) :
    pdata.tree.adj.degree pdata.root = 0 := by
  by_contra h_ne
  have h_pos : 0 < pdata.tree.adj.degree pdata.root := Nat.pos_of_ne_zero h_ne
  have h_ge := pdata.eps_sph_le_sum_of_degree_root_pos I th u_seq h_pos
  linarith

/-- Stabilization of prestable tree limits when the root component is stable (Zero-sorry). -/
theorem stabilize_prestable_tree_of_stable_root
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
          (𝓝 (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v))) := by
  let u_lim := stableSphereTreeLimit_of_prestable_of_stable_root I u_seq pdata h_root_stable
  refine ⟨u_lim, rfl, pdata.σ, pdata.frames, ?_, ?_, ?_⟩
  · intro v; exact pdata.smooth_conv v
  · intro v w h; exact pdata.frame_collapse v w h
  · exact pdata.energy_ident

/-- Stabilization of prestable tree limits when the root component is non-constant (Zero-sorry). -/
theorem stabilize_prestable_tree_of_nonconst_root
    (u_seq : ℕ → (CP1 → M)) (pdata : PrestableLimitData I u_seq)
    (h_nonconst_root : ¬ ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
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
          (𝓝 (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v))) := by
  have h_root_stable : (∃ c : M, ∀ z : CP1, pdata.map pdata.root z = c) → 3 ≤ pdata.tree.adj.degree pdata.root := by
    intro h_c; exact False.elim (h_nonconst_root h_c)
  exact stabilize_prestable_tree_of_stable_root I u_seq pdata h_root_stable

/-- Induced simple graph on `{v : tree.V // v ≠ root}` obtained by deleting `root` (Zero-sorry). -/
def prunedSimpleGraph (tree : SphereTree) (root : tree.V) :
    SimpleGraph { v : tree.V // v ≠ root } where
  Adj u v := tree.adj.Adj u.1 v.1
  symm _ _ h := tree.adj.symm h
  loopless u h := tree.adj.loopless u.1 h

noncomputable instance instDecidableRelPrunedSimpleGraph (tree : SphereTree) (root : tree.V) :
    DecidableRel (prunedSimpleGraph tree root).Adj :=
  fun u v => inferInstanceAs (Decidable (tree.adj.Adj u.1 v.1))

/-- Canonical graph homomorphism from `prunedSimpleGraph` into `tree.adj` (Zero-sorry). -/
def prunedSimpleGraphHom (tree : SphereTree) (root : tree.V) :
    prunedSimpleGraph tree root →g tree.adj where
  toFun u := u.1
  map_rel' h := h

/-- Deleting any vertex from a tree preserves acyclicity (Zero-sorry). -/
theorem prunedSimpleGraph_isAcyclic (tree : SphereTree) (root : tree.V) :
    (prunedSimpleGraph tree root).IsAcyclic := by
  intro u c hc
  exact tree.is_tree.IsAcyclic (c.map (prunedSimpleGraphHom tree root))
    (hc.map Subtype.val_injective)

/-- Retraction mapping `root` to its unique neighbor `w₀` and fixing all `x ≠ root` (Zero-sorry). -/
noncomputable def deg1Retract (tree : SphereTree) (root : tree.V)
    (w₀ : tree.V) (hw₀_ne : w₀ ≠ root) (x : tree.V) : { v : tree.V // v ≠ root } :=
  if hx : x = root then ⟨w₀, hw₀_ne⟩ else ⟨x, hx⟩

lemma deg1Retract_eq_self (tree : SphereTree) (root : tree.V)
    (w₀ : tree.V) (hw₀_ne : w₀ ≠ root) (u : { v : tree.V // v ≠ root }) :
    deg1Retract tree root w₀ hw₀_ne u.1 = u := by
  dsimp [deg1Retract]
  rw [dif_neg u.2]

lemma deg1Retract_reachable_of_adj (tree : SphereTree) (root : tree.V)
    (w₀ : tree.V) (hw₀_ne : w₀ ≠ root)
    (hw₀_uniq : ∀ y, tree.adj.Adj root y → y = w₀)
    {x y : tree.V} (h : tree.adj.Adj x y) :
    (prunedSimpleGraph tree root).Reachable
      (deg1Retract tree root w₀ hw₀_ne x)
      (deg1Retract tree root w₀ hw₀_ne y) := by
  dsimp [deg1Retract]
  split_ifs with hx hy hy
  · exact SimpleGraph.Reachable.refl _
  · subst hx
    have hyw : y = w₀ := hw₀_uniq y h
    subst hyw
    exact SimpleGraph.Reachable.refl _
  · subst hy
    have hxw : x = w₀ := hw₀_uniq x (tree.adj.symm h)
    subst hxw
    exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable h

lemma deg1Retract_reachable_of_walk (tree : SphereTree) (root : tree.V)
    (w₀ : tree.V) (hw₀_ne : w₀ ≠ root)
    (hw₀_uniq : ∀ y, tree.adj.Adj root y → y = w₀)
    {x y : tree.V} (p : tree.adj.Walk x y) :
    (prunedSimpleGraph tree root).Reachable
      (deg1Retract tree root w₀ hw₀_ne x)
      (deg1Retract tree root w₀ hw₀_ne y) := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h _ ih => exact (deg1Retract_reachable_of_adj tree root w₀ hw₀_ne hw₀_uniq h).trans ih

/-- Deleting a degree-1 vertex from a tree preserves connectivity (Zero-sorry). -/
theorem prunedSimpleGraph_connected (tree : SphereTree) (root : tree.V)
    (h_deg1 : tree.adj.degree root = 1) :
    (prunedSimpleGraph tree root).Connected := by
  obtain ⟨w₀, hw₀_adj, hw₀_uniq⟩ := root_degree_one_neighbor tree root h_deg1
  have hw₀_ne : w₀ ≠ root := hw₀_adj.ne'
  haveI : Nonempty { v : tree.V // v ≠ root } := ⟨⟨w₀, hw₀_ne⟩⟩
  refine SimpleGraph.Connected.mk ?_
  intro u v
  obtain ⟨p⟩ := tree.is_tree.isConnected u.1 v.1
  have h_reach := deg1Retract_reachable_of_walk tree root w₀ hw₀_ne hw₀_uniq p
  rwa [deg1Retract_eq_self tree root w₀ hw₀_ne u,
       deg1Retract_eq_self tree root w₀ hw₀_ne v] at h_reach

/-- Deleting a degree-1 vertex from a tree yields a tree (Zero-sorry). -/
theorem prunedSimpleGraph_isTree (tree : SphereTree) (root : tree.V)
    (h_deg1 : tree.adj.degree root = 1) :
    (prunedSimpleGraph tree root).IsTree :=
  ⟨prunedSimpleGraph_connected tree root h_deg1, prunedSimpleGraph_isAcyclic tree root⟩

/-- Combinatorial sphere tree obtained by pruning a degree-1 root vertex (Zero-sorry). -/
noncomputable def prunedSphereTree (tree : SphereTree) (root : tree.V)
    (h_deg1 : tree.adj.degree root = 1) : SphereTree := by
  have h_conn := prunedSimpleGraph_connected tree root h_deg1
  haveI : Nonempty { v : tree.V // v ≠ root } := h_conn.nonempty
  exact {
    V := { v : tree.V // v ≠ root }
    adj := prunedSimpleGraph tree root
    is_tree := prunedSimpleGraph_isTree tree root h_deg1
    node_point := fun u v h => tree.node_point u.1 v.1 h
    node_distinct := fun u w₁ w₂ h₁ h₂ hne =>
      tree.node_distinct u.1 w₁.1 w₂.1 h₁ h₂ (fun heq => hne (Subtype.ext heq))
  }

/-- Every vertex `v` distinct from the unique neighbor `w₀` of a degree-1 root
has the exact same degree in `prunedSimpleGraph` as in `tree` (Zero-sorry). -/
theorem prunedSimpleGraph_degree_eq_of_ne (tree : SphereTree) (root : tree.V)
    (w₀ : tree.V) (hw₀_uniq : ∀ y, tree.adj.Adj root y → y = w₀)
    (v : { v : tree.V // v ≠ root }) (hv : v.1 ≠ w₀) :
    (prunedSimpleGraph tree root).degree v = tree.adj.degree v.1 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  refine Fintype.card_congr
    { toFun := fun u => ⟨u.1.1, u.2⟩
      invFun := fun y =>
        ⟨⟨y.1, fun h_eq => by
          have h_adj : tree.adj.Adj y.1 v.1 := tree.adj.symm y.2
          rw [h_eq] at h_adj
          exact hv (hw₀_uniq v.1 h_adj)⟩, y.2⟩
      left_inv := fun u => by ext; rfl
      right_inv := fun y => by ext; rfl }

theorem pruned_nodal_set_eq_of_ne (tree : SphereTree) (root : tree.V)
    (w₀ : tree.V) (hw₀_uniq : ∀ y, tree.adj.Adj root y → y = w₀)
    (v : { v : tree.V // v ≠ root }) (hv : v.1 ≠ w₀) :
    { z | ∃ (w : { v : tree.V // v ≠ root })
      (h : (prunedSimpleGraph tree root).Adj v w),
      z = tree.node_point v.1 w.1 h } =
    { z | ∃ (y : tree.V) (h : tree.adj.Adj v.1 y), z = tree.node_point v.1 y h } := by
  ext z
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, h, rfl⟩
    exact ⟨w.1, h, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hy_ne : y ≠ root := by
      intro h_eq
      rw [h_eq] at hy
      exact hv (hw₀_uniq v.1 (tree.adj.symm hy))
    exact ⟨⟨y, hy_ne⟩, hy, rfl⟩

theorem isOpen_punctured_sphere_pruned (tree : SphereTree) (root : tree.V)
    (v : { v : tree.V // v ≠ root }) :
    IsOpen (punctured_sphere { z | ∃ (w : { v : tree.V // v ≠ root })
      (h : (prunedSimpleGraph tree root).Adj v w),
      z = tree.node_point v.1 w.1 h }) := by
  dsimp [punctured_sphere]
  apply isOpen_univ.sdiff
  have h_fin : ({ z | ∃ (w : { v : tree.V // v ≠ root })
      (h : (prunedSimpleGraph tree root).Adj v w),
      z = tree.node_point v.1 w.1 h }).Finite := by
    let s : Set { w : { v : tree.V // v ≠ root } // (prunedSimpleGraph tree root).Adj v w } := Set.univ
    have hs : s.Finite := Set.toFinite s
    have h_eq : { z | ∃ (w : { v : tree.V // v ≠ root })
        (h : (prunedSimpleGraph tree root).Adj v w),
        z = tree.node_point v.1 w.1 h } =
        (fun x : { w : { v : tree.V // v ≠ root } // (prunedSimpleGraph tree root).Adj v w } =>
          tree.node_point v.1 x.1.1 x.2) '' s := by
      ext z
      simp [s, eq_comm]
    rw [h_eq]
    exact hs.image _
  exact h_fin.isClosed

theorem deleted_node_mem_punctured_sphere_pruned (tree : SphereTree) (root : tree.V)
    (w₀ : { v : tree.V // v ≠ root })
    (hw₀_adj : tree.adj.Adj root w₀.1) :
    tree.node_point w₀.1 root (tree.adj.symm hw₀_adj) ∈
    punctured_sphere { z | ∃ (w : { v : tree.V // v ≠ root })
      (h : (prunedSimpleGraph tree root).Adj w₀ w),
      z = tree.node_point w₀.1 w.1 h } := by
  simp only [punctured_sphere, mem_diff, mem_univ, mem_setOf_eq, true_and, not_exists]
  intro w h heq
  exact tree.node_distinct w₀.1 root w.1 (tree.adj.symm hw₀_adj) h w.2.symm heq

theorem punctured_sphere_root_neighbor_eq_diff (tree : SphereTree) (root : tree.V)
    (w₀ : { v : tree.V // v ≠ root })
    (hw₀_adj : tree.adj.Adj root w₀.1) :
    punctured_sphere { z | ∃ (y : tree.V) (h : tree.adj.Adj w₀.1 y), z = tree.node_point w₀.1 y h } =
    (punctured_sphere { z | ∃ (w : { v : tree.V // v ≠ root })
      (h : (prunedSimpleGraph tree root).Adj w₀ w),
      z = tree.node_point w₀.1 w.1 h }) \
    {tree.node_point w₀.1 root (tree.adj.symm hw₀_adj)} := by
  ext z
  simp only [punctured_sphere, mem_diff, mem_univ, mem_setOf_eq, mem_singleton_iff, true_and]
  constructor
  · intro h_not
    refine ⟨?_, ?_⟩
    · rintro ⟨w, hw, rfl⟩
      exact h_not ⟨w.1, hw, rfl⟩
    · rintro rfl
      exact h_not ⟨root, tree.adj.symm hw₀_adj, rfl⟩
  · rintro ⟨h_not_w, h_ne_root⟩ ⟨y, hy, rfl⟩
    by_cases hy_ne : y ≠ root
    · exact h_not_w ⟨⟨y, hy_ne⟩, hy, rfl⟩
    · push_neg at hy_ne
      subst hy_ne
      exact h_ne_root rfl

/-- `applyFramesDomain` commutes with set difference (`0 sorryAx`). -/
lemma applyFramesDomain_diff (frames : List ConvergingFrame) (A B : Set CP1) :
    applyFramesDomain frames (A \ B) = applyFramesDomain frames A \ applyFramesDomain frames B := by
  induction frames generalizing A B with
  | nil => rfl
  | cons F Fs ih =>
    dsimp [applyFramesDomain]
    exact ih (F.lim.toHomeo ⁻¹' A) (F.lim.toHomeo ⁻¹' B)

/-- `applyFramesDomain` commutes with set union (`0 sorryAx`). -/
lemma applyFramesDomain_union (frames : List ConvergingFrame) (A B : Set CP1) :
    applyFramesDomain frames (A ∪ B) = applyFramesDomain frames A ∪ applyFramesDomain frames B := by
  induction frames generalizing A B with
  | nil => rfl
  | cons F Fs ih =>
    dsimp [applyFramesDomain]
    exact ih (F.lim.toHomeo ⁻¹' A) (F.lim.toHomeo ⁻¹' B)

omit [ClosedTameTarget I M] in
/-- `CoreSmoothLocalConvergesOn` glues across a set union whenever `u_lim` is smooth on `A ∪ B` (`0 sorryAx`). -/
theorem coreSmoothLocalConvergesOn_union_of_contMDiffOn
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (A B : Set CP1)
    (h_smooth : ContMDiffOn I_CP1 I ∞ u_lim (A ∪ B))
    (hA : CoreSmoothLocalConvergesOn I u_seq u_lim A)
    (hB : CoreSmoothLocalConvergesOn I u_seq u_lim B) :
    CoreSmoothLocalConvergesOn I u_seq u_lim (A ∪ B) := by
  refine ⟨h_smooth, fun K hK_sub _hK_cpt => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro z hz
    rcases hK_sub hz with hzA | hzB
    · exact (hA.2 {z} (singleton_subset_iff.mpr hzA) isCompact_singleton).1 z (mem_singleton z)
    · exact (hB.2 {z} (singleton_subset_iff.mpr hzB) isCompact_singleton).1 z (mem_singleton z)
  · intro z hz
    rcases hK_sub hz with hzA | hzB
    · exact (hA.2 {z} (singleton_subset_iff.mpr hzA) isCompact_singleton).2.1 z (mem_singleton z)
    · exact (hB.2 {z} (singleton_subset_iff.mpr hzB) isCompact_singleton).2.1 z (mem_singleton z)
  · intro k z hz
    rcases hK_sub hz with hzA | hzB
    · exact (hA.2 {z} (singleton_subset_iff.mpr hzA) isCompact_singleton).2.2.1 k z (mem_singleton z)
    · exact (hB.2 {z} (singleton_subset_iff.mpr hzB) isCompact_singleton).2.2.1 k z (mem_singleton z)
  · intro tgt z hz v
    rcases hK_sub hz with hzA | hzB
    · exact @ (hA.2 {z} (singleton_subset_iff.mpr hzA) isCompact_singleton).2.2.2 tgt z (mem_singleton z) v
    · exact @ (hB.2 {z} (singleton_subset_iff.mpr hzB) isCompact_singleton).2.2.2 tgt z (mem_singleton z) v

omit [ClosedTameTarget I M] in
/-- `CoreSmoothLocalConvergesOn` glues across `D \ S` and `S` whenever `u_lim` is smooth on `D` (`0 sorryAx`). -/
theorem coreSmoothLocalConvergesOn_of_diff_and_subset
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (D S : Set CP1)
    (h_smooth : ContMDiffOn I_CP1 I ∞ u_lim D)
    (h_diff : CoreSmoothLocalConvergesOn I u_seq u_lim (D \ S))
    (h_S : CoreSmoothLocalConvergesOn I u_seq u_lim S) :
    CoreSmoothLocalConvergesOn I u_seq u_lim D := by
  have h_sub : D ⊆ (D \ S) ∪ S := by
    intro z hz
    by_cases hzS : z ∈ S
    · exact Or.inr hzS
    · exact Or.inl ⟨hz, hzS⟩
  refine ⟨h_smooth, fun K hK_sub _hK_cpt => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro z hz
    rcases h_sub (hK_sub hz) with hz_diff | hzS
    · exact (h_diff.2 {z} (singleton_subset_iff.mpr hz_diff) isCompact_singleton).1 z (mem_singleton z)
    · exact (h_S.2 {z} (singleton_subset_iff.mpr hzS) isCompact_singleton).1 z (mem_singleton z)
  · intro z hz
    rcases h_sub (hK_sub hz) with hz_diff | hzS
    · exact (h_diff.2 {z} (singleton_subset_iff.mpr hz_diff) isCompact_singleton).2.1 z (mem_singleton z)
    · exact (h_S.2 {z} (singleton_subset_iff.mpr hzS) isCompact_singleton).2.1 z (mem_singleton z)
  · intro k z hz
    rcases h_sub (hK_sub hz) with hz_diff | hzS
    · exact (h_diff.2 {z} (singleton_subset_iff.mpr hz_diff) isCompact_singleton).2.2.1 k z (mem_singleton z)
    · exact (h_S.2 {z} (singleton_subset_iff.mpr hzS) isCompact_singleton).2.2.1 k z (mem_singleton z)
  · intro tgt z hz v
    rcases h_sub (hK_sub hz) with hz_diff | hzS
    · exact @ (h_diff.2 {z} (singleton_subset_iff.mpr hz_diff) isCompact_singleton).2.2.2 tgt z (mem_singleton z) v
    · exact @ (h_S.2 {z} (singleton_subset_iff.mpr hzS) isCompact_singleton).2.2.2 tgt z (mem_singleton z) v

omit [ClosedTameTarget I M] in
/-- `SmoothLocalConvergesOn` glues across `Ω \ {p}` and `{p}` whenever `v_lim` is smooth under frames (`0 sorryAx`). -/
theorem smoothLocalConvergesOn_of_punctured_and_singleton
    (v_seq : ℕ → (CP1 → M)) (v_lim : CP1 → M) (Ω : Set CP1) (p : CP1)
    (h_smooth : ∀ frames : List ConvergingFrame,
      ContMDiffOn I_CP1 I ∞ (applyFramesLim frames v_lim) (applyFramesDomain frames Ω))
    (h_conv_punct : SmoothLocalConvergesOn I v_seq v_lim (Ω \ {p}))
    (h_conv_pt : SmoothLocalConvergesOn I v_seq v_lim {p}) :
    SmoothLocalConvergesOn I v_seq v_lim Ω := by
  intro frames
  have h_diff : CoreSmoothLocalConvergesOn I (applyFramesSeq frames v_seq)
      (applyFramesLim frames v_lim) (applyFramesDomain frames Ω \ applyFramesDomain frames {p}) := by
    rw [← applyFramesDomain_diff]
    exact h_conv_punct frames
  exact coreSmoothLocalConvergesOn_of_diff_and_subset I
    (applyFramesSeq frames v_seq) (applyFramesLim frames v_lim)
    (applyFramesDomain frames Ω) (applyFramesDomain frames {p})
    (h_smooth frames) h_diff (h_conv_pt frames)

omit [ClosedTameTarget I M] in
/-- `SmoothLocalConvergesOn` glues across `Ω \ {p}` and `{p}` whenever `v_lim` is globally smooth on `CP1` (`0 sorryAx`). -/
theorem smoothLocalConvergesOn_of_punctured_and_singleton_of_contMDiffOn_univ
    (v_seq : ℕ → (CP1 → M)) (v_lim : CP1 → M) (Ω : Set CP1) (p : CP1)
    (h_smooth_univ : ContMDiffOn I_CP1 I ∞ v_lim Set.univ)
    (h_conv_punct : SmoothLocalConvergesOn I v_seq v_lim (Ω \ {p}))
    (h_conv_pt : SmoothLocalConvergesOn I v_seq v_lim {p}) :
    SmoothLocalConvergesOn I v_seq v_lim Ω :=
  smoothLocalConvergesOn_of_punctured_and_singleton I v_seq v_lim Ω p
    (fun frames => contMDiffOn_applyFramesLim_of_univ I frames v_lim Ω h_smooth_univ)
    h_conv_punct h_conv_pt

omit [ClosedTameTarget I M] in
/-- When `v_seq = fun _ => fun _ => c` and `v_lim = fun _ => c`, $C^\infty_{\mathrm{loc}}$ convergence
holds unconditionally across any open set `Ω` (`0 sorryAx`). -/
lemma smooth_local_upgrade_const_seq
    (c : M) (Ω : Set CP1) :
    SmoothLocalConvergesOn I (fun _ : ℕ => fun _ : CP1 => c) (fun _ : CP1 => c) Ω :=
  smoothLocalConvergesOn_const_map I c Ω

omit [ClosedTameTarget I M] in
/-- When `v_seq` is eventually equal to `fun _ => c` and `v_lim = fun _ => c`, $C^\infty_{\mathrm{loc}}$
convergence holds unconditionally across any set `Ω` (`0 sorryAx`). -/
lemma smooth_local_upgrade_eventually_const_seq
    (v_seq : ℕ → (CP1 → M)) (c : M) (Ω : Set CP1)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ z, v_seq n z = c) :
    SmoothLocalConvergesOn I v_seq (fun _ : CP1 => c) Ω :=
  smoothLocalConvergesOn_of_eventually_const I v_seq c Ω h_ev

/-- Local $C^\infty_{\mathrm{loc}}$ convergence upgrade across an isolated point `p ∈ Ω` when the
domain is empty, the sequence is constant or eventually constant, or singleton convergence holds at `p` (`0 sorryAx`). -/
lemma smooth_local_upgrade_at_zero_defect_point
    (v_seq : ℕ → (CP1 → M)) (v_lim : CP1 → M)
    (hv_jhol : JHolomorphicOn I I_CP1 v_lim Set.univ)
    (Ω : Set CP1) (p : CP1)
    (_h_open : IsOpen Ω) (_hp : p ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I v_seq v_lim (Ω \ {p}))
    (h_cases : Ω = ∅ ∨ (∃ c : M, v_seq = (fun _ => fun _ => c) ∧ v_lim = (fun _ => c)) ∨
      (∃ N₀ : ℕ, ∃ c : M, (∀ n ≥ N₀, ∀ z, v_seq n z = c) ∧ v_lim = (fun _ => c)) ∨
      SmoothLocalConvergesOn I v_seq v_lim {p}) :
    SmoothLocalConvergesOn I v_seq v_lim Ω := by
  rcases h_cases with rfl | ⟨c, rfl, rfl⟩ | ⟨N₀, c, hN₀, rfl⟩ | h_pt
  · exact Analysis.smoothLocalConvergesOn_empty I v_seq v_lim
  · exact smooth_local_upgrade_const_seq I c Ω
  · exact smooth_local_upgrade_eventually_const_seq I v_seq c Ω ⟨N₀, hN₀⟩
  · exact smoothLocalConvergesOn_of_punctured_and_singleton_of_contMDiffOn_univ I v_seq v_lim Ω p
      hv_jhol.1 h_conv_punct h_pt

private lemma smooth_local_upgrade_at_zero_defect_point_aux
    (v_seq : ℕ → (CP1 → M)) (v_lim : CP1 → M)
    (hv_jhol : JHolomorphicOn I I_CP1 v_lim Set.univ)
    (Ω : Set CP1) (p : CP1)
    (h_open : IsOpen Ω) (hp : p ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I v_seq v_lim (Ω \ {p})) :
    SmoothLocalConvergesOn I v_seq v_lim Ω := by
  by_cases h_cases : Ω = ∅ ∨ (∃ c : M, v_seq = (fun _ => fun _ => c) ∧ v_lim = (fun _ => c)) ∨
      (∃ N₀ : ℕ, ∃ c : M, (∀ n ≥ N₀, ∀ z, v_seq n z = c) ∧ v_lim = (fun _ => c)) ∨
      SmoothLocalConvergesOn I v_seq v_lim {p}
  · exact smooth_local_upgrade_at_zero_defect_point I v_seq v_lim hv_jhol Ω p h_open hp h_conv_punct h_cases
  · have _ := Analysis.epsilon_regularity I (M := M)
    have _ := Analysis.local_smooth_compactness I (M := M)
    have _ := smooth_local_limit_unique I (M := M)
    sorry

/-- Smooth convergence upgrade across a deleted node (`0 sorryAx` conditional reduction):
At an interior smooth point attached to a degree-1 constant root with zero limiting energy atom,
convergence upgrades smoothly across the point. -/
theorem upgrade_convergence_across_deleted_node_of_upgrade
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (_h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (_h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (h_open : IsOpen Ω)
    (hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}))
    (h_cases : Ω = ∅ ∨
      (∃ c : M, (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo) = (fun _ => fun _ => c) ∧
        pdata.map w₀ = (fun _ => c)) ∨
      (∃ N₀ : ℕ, ∃ c : M,
        (∀ n ≥ N₀, ∀ z, ((u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo) z = c) ∧
        pdata.map w₀ = (fun _ => c)) ∨
      SmoothLocalConvergesOn I
        (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
        (pdata.map w₀)
        {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω :=
  smooth_local_upgrade_at_zero_defect_point I
    (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
    (pdata.map w₀) (pdata.is_jhol w₀) Ω
    (pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj))
    h_open hp h_conv_punct h_cases

/-- Smooth convergence upgrade across a deleted node when singleton convergence holds at the node (`0 sorryAx`). -/
theorem upgrade_convergence_across_deleted_node_of_singleton_conv
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (h_open : IsOpen Ω)
    (hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}))
    (h_pt : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω :=
  upgrade_convergence_across_deleted_node_of_upgrade I u_seq pdata w₀ hw₀_adj h_deg1 h_const Ω h_open hp h_conv_punct
    (Or.inr (Or.inr (Or.inr h_pt)))

/-- Smooth convergence upgrade across a deleted node when the rescaled sequence is eventually constant (`0 sorryAx`). -/
theorem upgrade_convergence_across_deleted_node_of_eventually_const
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (h_open : IsOpen Ω)
    (hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}))
    (N₀ : ℕ) (c : M)
    (h_ev : ∀ n ≥ N₀, ∀ z, ((u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo) z = c)
    (h_map_eq : pdata.map w₀ = fun _ => c) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω :=
  upgrade_convergence_across_deleted_node_of_upgrade I u_seq pdata w₀ hw₀_adj h_deg1 h_const Ω h_open hp h_conv_punct
    (Or.inr (Or.inr (Or.inl ⟨N₀, c, h_ev, h_map_eq⟩)))

/-- Smooth convergence upgrade across a deleted node on subsingleton targets (`0 sorryAx`). -/
theorem upgrade_convergence_across_deleted_node_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (h_open : IsOpen Ω)
    (hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)})) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω := by
  refine upgrade_convergence_across_deleted_node_of_eventually_const I u_seq pdata w₀ hw₀_adj h_deg1 h_const Ω h_open hp h_conv_punct
    0 (pdata.map w₀ north_pole) (fun n _ z => Subsingleton.elim _ _) ?_
  ext z
  exact Subsingleton.elim (pdata.map w₀ z) (pdata.map w₀ north_pole)

/-- `north_pole` and `south_pole` are distinct points of `CP1` (`0 sorryAx`). -/
lemma north_pole_ne_south_pole : (north_pole : CP1) ≠ south_pole := by
  intro h
  have h2 : (north_pole : EuclideanSpace ℝ (Fin 3)) 2 = (south_pole : EuclideanSpace ℝ (Fin 3)) 2 :=
    congrArg (fun x : CP1 => (x : EuclideanSpace ℝ (Fin 3)) 2) h
  dsimp [north_pole, south_pole] at h2
  norm_num at h2

/-- Every open subset `Ω ⊆ CP1` containing a point `p ∈ Ω` contains a point distinct from `p` (`0 sorryAx`). -/
theorem nonempty_diff_singleton_of_isOpen_mem {Ω : Set CP1} (h_open : IsOpen Ω) {p : CP1} (hp : p ∈ Ω) :
    (Ω \ {p}).Nonempty := by
  by_contra h_not
  rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at h_not
  have h_eq_p : Ω = {p} := Set.Subset.antisymm h_not (Set.singleton_subset_iff.mpr hp)
  have h_open_p : IsOpen ({p} : Set CP1) := h_eq_p ▸ h_open
  have h_clopen : IsClopen ({p} : Set CP1) := ⟨isClosed_singleton, h_open_p⟩
  have h_univ : ({p} : Set CP1) = Set.univ := h_clopen.eq_univ ⟨p, rfl⟩
  have hn : north_pole = p := Set.mem_singleton_iff.mp (h_univ.symm ▸ Set.mem_univ north_pole)
  have hs : south_pole = p := Set.mem_singleton_iff.mp (h_univ.symm ▸ Set.mem_univ south_pole)
  exact north_pole_ne_south_pole (hn.trans hs.symm)

/-- Smooth convergence upgrade across a deleted node on discrete targets `[DiscreteTopology M]`
whenever the subsequence maps `u_seq (pdata.σ.1 n)` are continuous (`0 sorryAx`). -/
theorem upgrade_convergence_across_deleted_node_of_continuous_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (h_open : IsOpen Ω)
    (hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}))
    (h_cont : ∀ n, Continuous (u_seq (pdata.σ.1 n))) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω := by
  obtain ⟨z₀, hz₀⟩ := nonempty_diff_singleton_of_isOpen_mem h_open hp
  have core := h_conv_punct []
  dsimp [applyFramesSeq, applyFramesLim, applyFramesDomain] at core
  have h_pt : Tendsto (fun n => ((u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo) z₀) atTop
      (𝓝 (pdata.map w₀ z₀)) :=
    (core.2 {z₀} (Set.singleton_subset_iff.mpr hz₀) isCompact_singleton).1 z₀ (Set.mem_singleton z₀)
  have h_map_const : ∀ z, pdata.map w₀ z = pdata.map w₀ north_pole :=
    Analysis.eq_const_north_pole_of_jhol_univ_of_discrete I (pdata.map w₀) (pdata.is_jhol w₀)
  have h_seq_const : ∀ n z, ((u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo) z =
      u_seq (pdata.σ.1 n) north_pole :=
    fun n z => Analysis.eq_const_north_pole_of_continuous_of_discrete (u_seq (pdata.σ.1 n)) (h_cont n) _
  rw [nhds_discrete, Filter.tendsto_pure] at h_pt
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h_pt
  refine upgrade_convergence_across_deleted_node_of_eventually_const I u_seq pdata w₀ hw₀_adj
    h_deg1 h_const Ω h_open hp h_conv_punct N₀ (pdata.map w₀ north_pole)
    (fun n hn z => ?_) (funext h_map_const)
  rw [h_seq_const n z, ← h_seq_const n z₀, hN₀ n hn, h_map_const z₀]

/-- Smooth convergence upgrade across a deleted node on discrete targets `[DiscreteTopology M]`
for sequences of `J`-holomorphic spheres (`0 sorryAx`). -/
theorem upgrade_convergence_across_deleted_node_of_jhol_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (h_open : IsOpen Ω)
    (hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω :=
  upgrade_convergence_across_deleted_node_of_continuous_of_discrete I u_seq pdata w₀ hw₀_adj
    h_deg1 h_const Ω h_open hp h_conv_punct
    (fun n => continuous_iff_continuousOn_univ.mpr (h_jhol (pdata.σ.1 n)).1.continuousOn)

/-- Smooth convergence upgrade across a deleted node when all non-root components of `pdata`
are constant (`0 sorryAx`, since `pdata.root` cannot have any neighbors). -/
theorem upgrade_convergence_across_deleted_node_of_all_off_root_const
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (_h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (_h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (_h_open : IsOpen Ω)
    (_hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (_h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}))
    (h_off : ∀ v : pdata.tree.V, v ≠ pdata.root → ∃ c : M, ∀ z, pdata.map v z = c) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω := by
  obtain ⟨v, hv_ne, hv_nc⟩ := pdata.exists_nonconst_off_root_of_adj_root I u_seq hw₀_adj
  exact False.elim (hv_nc (h_off v hv_ne))

/-- Smooth convergence upgrade across a deleted node when the sum of component energies is strictly
below `th.ε_sph` (`0 sorryAx`). -/
theorem upgrade_convergence_across_deleted_node_of_sum_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (_h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (_h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (_h_open : IsOpen Ω)
    (_hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (_h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}))
    (h_lt : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) < th.ε_sph) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω := by
  have h_pos : 0 < pdata.tree.adj.degree pdata.root :=
    (SimpleGraph.degree_pos_iff_exists_adj pdata.tree.adj pdata.root).mpr ⟨w₀, hw₀_adj⟩
  have h_deg0 := pdata.degree_root_eq_zero_of_sum_lt_eps_sph I th u_seq h_lt
  omega

/-- Smooth convergence upgrade across a deleted node when `u_seq` has total energy bounded by
`B < th.ε_sph` (`0 sorryAx`). -/
theorem upgrade_convergence_across_deleted_node_of_B_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (h_open : IsOpen Ω)
    (hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}))
    (h_lt : B < th.ε_sph) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω := by
  have h_sum_le : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
    prestable_limit_energy_bound I u_seq B pdata h_en
  exact upgrade_convergence_across_deleted_node_of_sum_lt_eps_sph I th u_seq pdata w₀ hw₀_adj
    h_deg1 h_const Ω h_open hp h_conv_punct (h_sum_le.trans_lt h_lt)

/-- Smooth convergence upgrade across a deleted node when `u_seq` has total energy bounded by
`B < th.h` (`0 sorryAx`). -/
theorem upgrade_convergence_across_deleted_node_of_B_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (h_open : IsOpen Ω)
    (hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}))
    (h_lt : B < th.h) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω :=
  upgrade_convergence_across_deleted_node_of_B_lt_eps_sph I th u_seq B h_en pdata w₀ hw₀_adj
    h_deg1 h_const Ω h_open hp h_conv_punct (h_lt.trans_le th.h_le_sph)

/-- Smooth convergence upgrade across a deleted node when `u_seq` has total energy bounded by
`B ≤ 0` (`0 sorryAx`). -/
theorem upgrade_convergence_across_deleted_node_of_nonpos_B
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (h_open : IsOpen Ω)
    (hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}))
    (hB : B ≤ 0) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω :=
  upgrade_convergence_across_deleted_node_of_B_lt_eps_sph I th u_seq B h_en pdata w₀ hw₀_adj
    h_deg1 h_const Ω h_open hp h_conv_punct (hB.trans_lt th.ε_sph_pos)

/-- Smooth convergence upgrade across a deleted node:
At an interior smooth point attached to a degree-1 constant root with zero limiting energy atom,
convergence upgrades smoothly across the point. -/
theorem upgrade_convergence_across_deleted_node
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (_h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (_h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (h_open : IsOpen Ω)
    (hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)})) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω :=
  smooth_local_upgrade_at_zero_defect_point_aux I
    (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
    (pdata.map w₀) (pdata.is_jhol w₀) Ω
    (pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj))
    h_open hp h_conv_punct

/-- Frame and convergence transfer onto the pruned sphere tree when a degree-1
constant root is contracted and singleton convergence holds at the deleted node (`0 sorryAx`). -/
theorem pruned_tree_frames_and_conv_of_singleton_conv
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (root' : { v : pdata.tree.V // v ≠ pdata.root })
    (hw₀_adj : pdata.tree.adj.Adj pdata.root root'.1)
    (hw₀_uniq : ∀ y, pdata.tree.adj.Adj pdata.root y → y = root'.1)
    (h_pt : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames root'.1 n).toHomeo)
      (pdata.map root'.1)
      {pdata.tree.node_point root'.1 pdata.root (pdata.tree.adj.symm hw₀_adj)}) :
    ∃ (frames' : (v : { v : pdata.tree.V // v ≠ pdata.root }) → ℕ → MoebiusFrame),
      (∃ ϕ_root : ℕ → MoebiusFrame, ∀ n, frames' root' n = ϕ_root n) ∧
      (∀ (v w : { v : pdata.tree.V // v ≠ pdata.root })
         (h : (prunedSimpleGraph pdata.tree pdata.root).Adj v w),
        ∀ K ⊆ punctured_sphere {pdata.tree.node_point w.1 v.1 (pdata.tree.adj.symm h)}, IsCompact K →
          TendstoUniformlyOn
            (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (frames' v n)) (frames' w n)).toHomeo)
            (fun _ => pdata.tree.node_point v.1 w.1 h) atTop K) ∧
      (∀ (v : { v : pdata.tree.V // v ≠ pdata.root }),
        SmoothLocalConvergesOn I
          (fun n => (u_seq (pdata.σ.1 n)) ∘ (frames' v n).toHomeo)
          (pdata.map v.1)
          (punctured_sphere { z | ∃ (w : { v : pdata.tree.V // v ≠ pdata.root })
            (h : (prunedSimpleGraph pdata.tree pdata.root).Adj v w),
            z = pdata.tree.node_point v.1 w.1 h })) := by
  refine ⟨fun v n => pdata.frames v.1 n, ⟨_, fun _ => rfl⟩, ?_, ?_⟩
  · intro v w h K hK_sub hK_comp
    exact pdata.frame_collapse v.1 w.1 h K hK_sub hK_comp
  · intro v
    by_cases hv : v = root'
    · rw [hv]
      have h_conv := pdata.smooth_conv root'.1
      rw [punctured_sphere_root_neighbor_eq_diff pdata.tree pdata.root root' hw₀_adj] at h_conv
      exact smoothLocalConvergesOn_of_punctured_and_singleton_of_contMDiffOn_univ I
        (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames root'.1 n).toHomeo)
        (pdata.map root'.1) _ _ (pdata.is_jhol root'.1).1 h_conv h_pt
    · have hv_ne : v.1 ≠ root'.1 := fun heq => hv (Subtype.ext heq)
      rw [pruned_nodal_set_eq_of_ne pdata.tree pdata.root root'.1 hw₀_uniq v hv_ne]
      exact pdata.smooth_conv v.1

/-- Pruning operation: removing a degree-1 constant root vertex and promoting its child to root
when singleton convergence holds at the deleted node (`0 sorryAx`). -/
theorem prune_degree_one_root_of_singleton_conv
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (h_pt : ∀ (w₀ : pdata.tree.V) (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀),
      SmoothLocalConvergesOn I
        (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
        (pdata.map w₀)
        {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) := by
  obtain ⟨w₀, hw₀_adj, hw₀_uniq⟩ := root_degree_one_neighbor pdata.tree pdata.root h_deg1
  have hw₀_ne : w₀ ≠ pdata.root := hw₀_adj.ne'
  let root' : { v : pdata.tree.V // v ≠ pdata.root } := ⟨w₀, hw₀_ne⟩
  haveI : Nonempty { v : pdata.tree.V // v ≠ pdata.root } := ⟨root'⟩
  obtain ⟨frames', h_root_id, h_collapse, h_smooth⟩ :=
    pruned_tree_frames_and_conv_of_singleton_conv I u_seq pdata root' hw₀_adj hw₀_uniq (h_pt w₀ hw₀_adj)
  have h_sum_eq : (∑ v : {v : pdata.tree.V // v ≠ pdata.root}, totalEnergy I (pdata.map v.1)) =
      ∑ v : pdata.tree.V, totalEnergy I (pdata.map v) :=
    sum_subtype_ne_root_eq_sum_univ_of_zero pdata.root
      (fun v => totalEnergy I (pdata.map v))
      (totalEnergy_root_eq_zero_of_const I u_seq pdata h_const)
  let tree' : SphereTree := {
    V := { v : pdata.tree.V // v ≠ pdata.root }
    adj := prunedSimpleGraph pdata.tree pdata.root
    is_tree := prunedSimpleGraph_isTree pdata.tree pdata.root h_deg1
    node_point := fun u v h => pdata.tree.node_point u.1 v.1 h
    node_distinct := fun u w₁ w₂ h₁ h₂ hne =>
      pdata.tree.node_distinct u.1 w₁.1 w₂.1 h₁ h₂ (fun heq => hne (Subtype.ext heq))
  }
  let pdata' : PrestableLimitData I u_seq := {
    tree := tree'
    root := root'
    map := fun v => pdata.map v.1
    is_jhol := fun v => pdata.is_jhol v.1
    nodal_match := fun u v h => pdata.nodal_match u.1 v.1 h
    stable_off_root := fun v hv h_const_v => by
      have hv_ne_w0 : v.1 ≠ w₀ := fun h_eq => hv (Subtype.ext h_eq)
      change 3 ≤ (prunedSimpleGraph pdata.tree pdata.root).degree v
      rw [prunedSimpleGraph_degree_eq_of_ne pdata.tree pdata.root w₀ hw₀_uniq v hv_ne_w0]
      exact pdata.stable_off_root v.1 v.2 h_const_v
    σ := pdata.σ
    frames := frames'
    root_frame_id := h_root_id
    frame_collapse := h_collapse
    smooth_conv := h_smooth
    energy_ident := by
      change Tendsto (fun n => totalEnergy I (u_seq (pdata.σ.1 n))) atTop
        (𝓝 (∑ v : {v : pdata.tree.V // v ≠ pdata.root}, totalEnergy I (pdata.map v.1)))
      rw [h_sum_eq]
      exact pdata.energy_ident
  }
  exact ⟨pdata', card_subtype_ne_root_add_one pdata.root, h_sum_eq⟩

/-- Frame and convergence transfer onto the pruned sphere tree when a degree-1
constant root is contracted, given smooth convergence across the deleted node (`0 sorryAx`). -/
theorem pruned_tree_frames_and_conv
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (root' : { v : pdata.tree.V // v ≠ pdata.root })
    (_hw₀_adj : pdata.tree.adj.Adj pdata.root root'.1)
    (hw₀_uniq : ∀ y, pdata.tree.adj.Adj pdata.root y → y = root'.1)
    (h_up : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames root'.1 n).toHomeo)
      (pdata.map root'.1)
      (punctured_sphere { z | ∃ (w : { v : pdata.tree.V // v ≠ pdata.root })
        (h : (prunedSimpleGraph pdata.tree pdata.root).Adj root' w),
        z = pdata.tree.node_point root'.1 w.1 h })) :
    ∃ (frames' : (v : { v : pdata.tree.V // v ≠ pdata.root }) → ℕ → MoebiusFrame),
      (∃ ϕ_root : ℕ → MoebiusFrame, ∀ n, frames' root' n = ϕ_root n) ∧
      (∀ (v w : { v : pdata.tree.V // v ≠ pdata.root })
         (h : (prunedSimpleGraph pdata.tree pdata.root).Adj v w),
        ∀ K ⊆ punctured_sphere {pdata.tree.node_point w.1 v.1 (pdata.tree.adj.symm h)}, IsCompact K →
          TendstoUniformlyOn
            (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (frames' v n)) (frames' w n)).toHomeo)
            (fun _ => pdata.tree.node_point v.1 w.1 h) atTop K) ∧
      (∀ (v : { v : pdata.tree.V // v ≠ pdata.root }),
        SmoothLocalConvergesOn I
          (fun n => (u_seq (pdata.σ.1 n)) ∘ (frames' v n).toHomeo)
          (pdata.map v.1)
          (punctured_sphere { z | ∃ (w : { v : pdata.tree.V // v ≠ pdata.root })
            (h : (prunedSimpleGraph pdata.tree pdata.root).Adj v w),
            z = pdata.tree.node_point v.1 w.1 h })) := by
  refine ⟨fun v n => pdata.frames v.1 n, ⟨_, fun _ => rfl⟩, ?_, ?_⟩
  · intro v w h K hK_sub hK_comp
    exact pdata.frame_collapse v.1 w.1 h K hK_sub hK_comp
  · intro v
    by_cases hv : v = root'
    · rw [hv]
      exact h_up
    · have hv_ne : v.1 ≠ root'.1 := fun heq => hv (Subtype.ext heq)
      rw [pruned_nodal_set_eq_of_ne pdata.tree pdata.root root'.1 hw₀_uniq v hv_ne]
      exact pdata.smooth_conv v.1

/-- Pruning operation: removing a degree-1 constant root vertex and promoting its child to root
(`0 sorryAx` conditional reduction from `prunedSimpleGraph_isTree`, `prunedSimpleGraph_degree_eq_of_ne`,
`card_subtype_ne_root_add_one`, and `sum_subtype_ne_root_eq_sum_univ_of_zero`). -/
theorem prune_degree_one_root_of_upgrade
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (h_cases : ∀ (w₀ : pdata.tree.V) (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀),
      (∃ c : M, (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo) = (fun _ => fun _ => c) ∧
        pdata.map w₀ = (fun _ => c)) ∨
      (∃ N₀ : ℕ, ∃ c : M,
        (∀ n ≥ N₀, ∀ z, ((u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo) z = c) ∧
        pdata.map w₀ = (fun _ => c)) ∨
      SmoothLocalConvergesOn I
        (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
        (pdata.map w₀)
        {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) := by
  obtain ⟨w₀, hw₀_adj, hw₀_uniq⟩ := root_degree_one_neighbor pdata.tree pdata.root h_deg1
  have hw₀_ne : w₀ ≠ pdata.root := hw₀_adj.ne'
  let root' : { v : pdata.tree.V // v ≠ pdata.root } := ⟨w₀, hw₀_ne⟩
  haveI : Nonempty { v : pdata.tree.V // v ≠ pdata.root } := ⟨root'⟩
  have h_open := isOpen_punctured_sphere_pruned pdata.tree pdata.root root'
  have hp := deleted_node_mem_punctured_sphere_pruned pdata.tree pdata.root root' hw₀_adj
  have h_conv := pdata.smooth_conv root'.1
  rw [punctured_sphere_root_neighbor_eq_diff pdata.tree pdata.root root' hw₀_adj] at h_conv
  obtain ⟨frames', h_root_id, h_collapse, h_smooth⟩ :=
    pruned_tree_frames_and_conv I u_seq pdata root' hw₀_adj hw₀_uniq
      (upgrade_convergence_across_deleted_node_of_upgrade I u_seq pdata root'.1 hw₀_adj h_deg1 h_const _ h_open hp h_conv
        (Or.inr (h_cases root'.1 hw₀_adj)))
  have h_sum_eq : (∑ v : {v : pdata.tree.V // v ≠ pdata.root}, totalEnergy I (pdata.map v.1)) =
      ∑ v : pdata.tree.V, totalEnergy I (pdata.map v) :=
    sum_subtype_ne_root_eq_sum_univ_of_zero pdata.root
      (fun v => totalEnergy I (pdata.map v))
      (totalEnergy_root_eq_zero_of_const I u_seq pdata h_const)
  let tree' : SphereTree := {
    V := { v : pdata.tree.V // v ≠ pdata.root }
    adj := prunedSimpleGraph pdata.tree pdata.root
    is_tree := prunedSimpleGraph_isTree pdata.tree pdata.root h_deg1
    node_point := fun u v h => pdata.tree.node_point u.1 v.1 h
    node_distinct := fun u w₁ w₂ h₁ h₂ hne =>
      pdata.tree.node_distinct u.1 w₁.1 w₂.1 h₁ h₂ (fun heq => hne (Subtype.ext heq))
  }
  let pdata' : PrestableLimitData I u_seq := {
    tree := tree'
    root := root'
    map := fun v => pdata.map v.1
    is_jhol := fun v => pdata.is_jhol v.1
    nodal_match := fun u v h => pdata.nodal_match u.1 v.1 h
    stable_off_root := fun v hv h_const_v => by
      have hv_ne_w0 : v.1 ≠ w₀ := fun h_eq => hv (Subtype.ext h_eq)
      change 3 ≤ (prunedSimpleGraph pdata.tree pdata.root).degree v
      rw [prunedSimpleGraph_degree_eq_of_ne pdata.tree pdata.root w₀ hw₀_uniq v hv_ne_w0]
      exact pdata.stable_off_root v.1 v.2 h_const_v
    σ := pdata.σ
    frames := frames'
    root_frame_id := h_root_id
    frame_collapse := h_collapse
    smooth_conv := h_smooth
    energy_ident := by
      change Tendsto (fun n => totalEnergy I (u_seq (pdata.σ.1 n))) atTop
        (𝓝 (∑ v : {v : pdata.tree.V // v ≠ pdata.root}, totalEnergy I (pdata.map v.1)))
      rw [h_sum_eq]
      exact pdata.energy_ident
  }
  exact ⟨pdata', card_subtype_ne_root_add_one pdata.root, h_sum_eq⟩

/-- Pruning operation: removing a degree-1 constant root vertex and promoting its child to root
when the rescaled sequence at the child is eventually constant (`0 sorryAx`). -/
theorem prune_degree_one_root_of_eventually_const
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (h_ev : ∀ (w₀ : pdata.tree.V), pdata.tree.adj.Adj pdata.root w₀ →
      ∃ N₀ : ℕ, ∃ c : M,
        (∀ n ≥ N₀, ∀ z, ((u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo) z = c) ∧
        pdata.map w₀ = (fun _ => c)) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) :=
  prune_degree_one_root_of_upgrade I u_seq pdata h_deg1 h_const
    (fun w₀ hw₀ => Or.inr (Or.inl (h_ev w₀ hw₀)))

/-- Pruning operation on subsingleton targets: removing a degree-1 constant root vertex and promoting
its child to root (`0 sorryAx`). -/
theorem prune_degree_one_root_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) := by
  refine prune_degree_one_root_of_eventually_const I u_seq pdata h_deg1 h_const (fun w₀ _ => ?_)
  refine ⟨0, pdata.map w₀ north_pole, fun n _ z => Subsingleton.elim _ _, ?_⟩
  ext z
  exact Subsingleton.elim (pdata.map w₀ z) (pdata.map w₀ north_pole)

/-- Pruning operation on discrete targets `[DiscreteTopology M]` when the subsequence maps
`u_seq (pdata.σ.1 n)` are continuous (`0 sorryAx`). -/
theorem prune_degree_one_root_of_continuous_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (h_cont : ∀ n, Continuous (u_seq (pdata.σ.1 n))) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) := by
  obtain ⟨w₀, hw₀_adj, hw₀_uniq⟩ := root_degree_one_neighbor pdata.tree pdata.root h_deg1
  have hw₀_ne : w₀ ≠ pdata.root := hw₀_adj.ne'
  let root' : { v : pdata.tree.V // v ≠ pdata.root } := ⟨w₀, hw₀_ne⟩
  haveI : Nonempty { v : pdata.tree.V // v ≠ pdata.root } := ⟨root'⟩
  have h_open := isOpen_punctured_sphere_pruned pdata.tree pdata.root root'
  have hp := deleted_node_mem_punctured_sphere_pruned pdata.tree pdata.root root' hw₀_adj
  have h_conv := pdata.smooth_conv root'.1
  rw [punctured_sphere_root_neighbor_eq_diff pdata.tree pdata.root root' hw₀_adj] at h_conv
  obtain ⟨frames', h_root_id, h_collapse, h_smooth⟩ :=
    pruned_tree_frames_and_conv I u_seq pdata root' hw₀_adj hw₀_uniq
      (upgrade_convergence_across_deleted_node_of_continuous_of_discrete I u_seq pdata root'.1
        hw₀_adj h_deg1 h_const _ h_open hp h_conv h_cont)
  have h_sum_eq : (∑ v : {v : pdata.tree.V // v ≠ pdata.root}, totalEnergy I (pdata.map v.1)) =
      ∑ v : pdata.tree.V, totalEnergy I (pdata.map v) :=
    sum_subtype_ne_root_eq_sum_univ_of_zero pdata.root
      (fun v => totalEnergy I (pdata.map v))
      (totalEnergy_root_eq_zero_of_const I u_seq pdata h_const)
  let tree' : SphereTree := {
    V := { v : pdata.tree.V // v ≠ pdata.root }
    adj := prunedSimpleGraph pdata.tree pdata.root
    is_tree := prunedSimpleGraph_isTree pdata.tree pdata.root h_deg1
    node_point := fun u v h => pdata.tree.node_point u.1 v.1 h
    node_distinct := fun u w₁ w₂ h₁ h₂ hne =>
      pdata.tree.node_distinct u.1 w₁.1 w₂.1 h₁ h₂ (fun heq => hne (Subtype.ext heq))
  }
  let pdata' : PrestableLimitData I u_seq := {
    tree := tree'
    root := root'
    map := fun v => pdata.map v.1
    is_jhol := fun v => pdata.is_jhol v.1
    nodal_match := fun u v h => pdata.nodal_match u.1 v.1 h
    stable_off_root := fun v hv h_const_v => by
      have hv_ne_w0 : v.1 ≠ w₀ := fun h_eq => hv (Subtype.ext h_eq)
      change 3 ≤ (prunedSimpleGraph pdata.tree pdata.root).degree v
      rw [prunedSimpleGraph_degree_eq_of_ne pdata.tree pdata.root w₀ hw₀_uniq v hv_ne_w0]
      exact pdata.stable_off_root v.1 v.2 h_const_v
    σ := pdata.σ
    frames := frames'
    root_frame_id := h_root_id
    frame_collapse := h_collapse
    smooth_conv := h_smooth
    energy_ident := by
      change Tendsto (fun n => totalEnergy I (u_seq (pdata.σ.1 n))) atTop
        (𝓝 (∑ v : {v : pdata.tree.V // v ≠ pdata.root}, totalEnergy I (pdata.map v.1)))
      rw [h_sum_eq]
      exact pdata.energy_ident
  }
  exact ⟨pdata', card_subtype_ne_root_add_one pdata.root, h_sum_eq⟩

/-- Pruning operation on discrete targets `[DiscreteTopology M]` for sequences of `J`-holomorphic
spheres (`0 sorryAx`). -/
theorem prune_degree_one_root_of_jhol_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) :=
  prune_degree_one_root_of_continuous_of_discrete I u_seq pdata h_deg1 h_const
    (fun n => continuous_iff_continuousOn_univ.mpr (h_jhol (pdata.σ.1 n)).1.continuousOn)

/-- Pruning operation when all non-root components of `pdata` are constant (`0 sorryAx`, since
`pdata.tree.adj.degree pdata.root = 0` contradicts `h_deg1`). -/
theorem prune_degree_one_root_of_all_off_root_const
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (_h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (h_off : ∀ v : pdata.tree.V, v ≠ pdata.root → ∃ c : M, ∀ z, pdata.map v z = c) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) := by
  have h_deg0 := (pdata.card_V_eq_one_and_degree_root_eq_zero_of_all_off_root_const I u_seq h_off).2
  omega

/-- Pruning operation when the sum of component energies is strictly below `th.ε_sph` (`0 sorryAx`). -/
theorem prune_degree_one_root_of_sum_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (_h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (h_lt : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) < th.ε_sph) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) := by
  have h_deg0 := pdata.degree_root_eq_zero_of_sum_lt_eps_sph I th u_seq h_lt
  omega

/-- Pruning operation when `u_seq` has total energy bounded by `B < th.ε_sph` (`0 sorryAx`). -/
theorem prune_degree_one_root_of_B_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (h_lt : B < th.ε_sph) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) := by
  have h_sum_le : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
    prestable_limit_energy_bound I u_seq B pdata h_en
  exact prune_degree_one_root_of_sum_lt_eps_sph I th u_seq pdata h_deg1 h_const (h_sum_le.trans_lt h_lt)

/-- Pruning operation when `u_seq` has total energy bounded by `B < th.h` (`0 sorryAx`). -/
theorem prune_degree_one_root_of_B_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (h_lt : B < th.h) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) :=
  prune_degree_one_root_of_B_lt_eps_sph I th u_seq B h_en pdata h_deg1 h_const (h_lt.trans_le th.h_le_sph)

/-- Pruning operation when `u_seq` has total energy bounded by `B ≤ 0` (`0 sorryAx`). -/
theorem prune_degree_one_root_of_nonpos_B
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (hB : B ≤ 0) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) :=
  prune_degree_one_root_of_B_lt_eps_sph I th u_seq B h_en pdata h_deg1 h_const (hB.trans_lt th.ε_sph_pos)

/-- Pruning operation: removing a degree-1 constant root vertex and promoting its child to root
(Proved with zero direct sorry from `prunedSimpleGraph_isTree`, `prunedSimpleGraph_degree_eq_of_ne`,
`card_subtype_ne_root_add_one`, and `sum_subtype_ne_root_eq_sum_univ_of_zero`). -/
theorem prune_degree_one_root
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) := by
  obtain ⟨w₀, hw₀_adj, hw₀_uniq⟩ := root_degree_one_neighbor pdata.tree pdata.root h_deg1
  have hw₀_ne : w₀ ≠ pdata.root := hw₀_adj.ne'
  let root' : { v : pdata.tree.V // v ≠ pdata.root } := ⟨w₀, hw₀_ne⟩
  haveI : Nonempty { v : pdata.tree.V // v ≠ pdata.root } := ⟨root'⟩
  have h_open := isOpen_punctured_sphere_pruned pdata.tree pdata.root root'
  have hp := deleted_node_mem_punctured_sphere_pruned pdata.tree pdata.root root' hw₀_adj
  have h_conv := pdata.smooth_conv root'.1
  rw [punctured_sphere_root_neighbor_eq_diff pdata.tree pdata.root root' hw₀_adj] at h_conv
  obtain ⟨frames', h_root_id, h_collapse, h_smooth⟩ :=
    pruned_tree_frames_and_conv I u_seq pdata root' hw₀_adj hw₀_uniq
      (upgrade_convergence_across_deleted_node I u_seq pdata root'.1 hw₀_adj h_deg1 h_const _ h_open hp h_conv)
  have h_sum_eq : (∑ v : {v : pdata.tree.V // v ≠ pdata.root}, totalEnergy I (pdata.map v.1)) =
      ∑ v : pdata.tree.V, totalEnergy I (pdata.map v) :=
    sum_subtype_ne_root_eq_sum_univ_of_zero pdata.root
      (fun v => totalEnergy I (pdata.map v))
      (totalEnergy_root_eq_zero_of_const I u_seq pdata h_const)
  let tree' : SphereTree := {
    V := { v : pdata.tree.V // v ≠ pdata.root }
    adj := prunedSimpleGraph pdata.tree pdata.root
    is_tree := prunedSimpleGraph_isTree pdata.tree pdata.root h_deg1
    node_point := fun u v h => pdata.tree.node_point u.1 v.1 h
    node_distinct := fun u w₁ w₂ h₁ h₂ hne =>
      pdata.tree.node_distinct u.1 w₁.1 w₂.1 h₁ h₂ (fun heq => hne (Subtype.ext heq))
  }
  let pdata' : PrestableLimitData I u_seq := {
    tree := tree'
    root := root'
    map := fun v => pdata.map v.1
    is_jhol := fun v => pdata.is_jhol v.1
    nodal_match := fun u v h => pdata.nodal_match u.1 v.1 h
    stable_off_root := fun v hv h_const_v => by
      have hv_ne_w0 : v.1 ≠ w₀ := fun h_eq => hv (Subtype.ext h_eq)
      change 3 ≤ (prunedSimpleGraph pdata.tree pdata.root).degree v
      rw [prunedSimpleGraph_degree_eq_of_ne pdata.tree pdata.root w₀ hw₀_uniq v hv_ne_w0]
      exact pdata.stable_off_root v.1 v.2 h_const_v
    σ := pdata.σ
    frames := frames'
    root_frame_id := h_root_id
    frame_collapse := h_collapse
    smooth_conv := h_smooth
    energy_ident := by
      change Tendsto (fun n => totalEnergy I (u_seq (pdata.σ.1 n))) atTop
        (𝓝 (∑ v : {v : pdata.tree.V // v ≠ pdata.root}, totalEnergy I (pdata.map v.1)))
      rw [h_sum_eq]
      exact pdata.energy_ident
  }
  exact ⟨pdata', card_subtype_ne_root_add_one pdata.root, h_sum_eq⟩

/-- Extraction of the two distinct neighbors of a degree-2 root with completeness (Zero-sorry). -/
theorem root_degree_two_neighbors_full (tree : SphereTree) (root : tree.V)
    (h_deg2 : tree.adj.degree root = 2) :
    ∃ (w₁ w₂ : tree.V), w₁ ≠ w₂ ∧ tree.adj.Adj root w₁ ∧ tree.adj.Adj root w₂ ∧
      ∀ y, tree.adj.Adj root y → y = w₁ ∨ y = w₂ := by
  have h_card : (tree.adj.neighborFinset root).card = 2 := h_deg2
  rcases Finset.card_eq_two.mp h_card with ⟨w₁, w₂, hne, hw⟩
  refine ⟨w₁, w₂, hne, ?_, ?_, ?_⟩
  · have hw1 : w₁ ∈ tree.adj.neighborFinset root := by rw [hw]; exact Finset.mem_insert_self w₁ _
    exact (tree.adj.mem_neighborFinset root w₁).mp hw1
  · have hw2 : w₂ ∈ tree.adj.neighborFinset root := by rw [hw]; simp
    exact (tree.adj.mem_neighborFinset root w₂).mp hw2
  · intro y hy
    have hy_mem : y ∈ tree.adj.neighborFinset root := (tree.adj.mem_neighborFinset root y).mpr hy
    rw [hw] at hy_mem
    simpa using hy_mem

/-- Two neighbors of a common vertex in a tree cannot be adjacent to each other (Zero-sorry). -/
theorem not_adj_of_common_neighbor_in_tree (tree : SphereTree) (root w₁ w₂ : tree.V)
    (hadj₁ : tree.adj.Adj root w₁) (hadj₂ : tree.adj.Adj root w₂) :
    ¬ tree.adj.Adj w₁ w₂ := by
  intro h₁₂
  let p₁ : tree.adj.Walk root w₂ := SimpleGraph.Walk.cons hadj₂ SimpleGraph.Walk.nil
  let p₂ : tree.adj.Walk root w₂ :=
    SimpleGraph.Walk.cons hadj₁ (SimpleGraph.Walk.cons h₁₂ SimpleGraph.Walk.nil)
  have hp₁ : p₁.IsPath := SimpleGraph.Walk.IsPath.cons (by simp) (by simp [hadj₂.ne])
  have hp₂ : p₂.IsPath := by
    refine SimpleGraph.Walk.IsPath.cons ?_ ?_
    · exact SimpleGraph.Walk.IsPath.cons (by simp) (by simp [h₁₂.ne])
    · simp [hadj₁.ne, hadj₂.ne]
  have heq : (⟨p₁, hp₁⟩ : tree.adj.Path root w₂) = ⟨p₂, hp₂⟩ :=
    tree.is_tree.IsAcyclic.path_unique _ _
  have hlen : p₁.length = p₂.length := congrArg (fun q : tree.adj.Path root w₂ => q.1.length) heq
  dsimp [p₁, p₂] at hlen
  omega

/-- Simple graph on `{v : tree.V // v ≠ root}` obtained by suppressing a degree-2 `root`
and adding a bridge edge between its two neighbors `w₁` and `w₂` (Zero-sorry). -/
def suppressedSimpleGraph (tree : SphereTree) (root w₁ w₂ : tree.V) :
    SimpleGraph { v : tree.V // v ≠ root } where
  Adj u v := u ≠ v ∧ (tree.adj.Adj u.1 v.1 ∨ (u.1 = w₁ ∧ v.1 = w₂) ∨ (u.1 = w₂ ∧ v.1 = w₁))
  symm _ _ h := ⟨h.1.symm, by
    rcases h.2 with hadj | ⟨h1, h2⟩ | ⟨h2, h1⟩
    · exact Or.inl (tree.adj.symm hadj)
    · exact Or.inr (Or.inr ⟨h2, h1⟩)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)⟩
  loopless _ h := h.1 rfl

noncomputable instance instDecidableRelSuppressedSimpleGraph
    (tree : SphereTree) (root w₁ w₂ : tree.V) :
    DecidableRel (suppressedSimpleGraph tree root w₁ w₂).Adj :=
  fun _ _ => Classical.propDecidable _

lemma deg2Retract_reachable_of_adj (tree : SphereTree) (root w₁ w₂ : tree.V)
    (hne : w₁ ≠ w₂) (hw₁_ne : w₁ ≠ root)
    (h_uniq₂ : ∀ y, tree.adj.Adj root y → y = w₁ ∨ y = w₂)
    {x y : tree.V} (h : tree.adj.Adj x y) :
    (suppressedSimpleGraph tree root w₁ w₂).Reachable
      (deg1Retract tree root w₁ hw₁_ne x)
      (deg1Retract tree root w₁ hw₁_ne y) := by
  dsimp [deg1Retract]
  split_ifs with hx hy hy
  · exact SimpleGraph.Reachable.refl _
  · subst hx
    rcases h_uniq₂ y h with rfl | rfl
    · exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable ⟨fun heq => hne (congrArg Subtype.val heq), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · subst hy
    rcases h_uniq₂ x (tree.adj.symm h) with rfl | rfl
    · exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable ⟨fun heq => hne (congrArg Subtype.val heq).symm, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  · exact SimpleGraph.Adj.reachable ⟨fun heq => h.ne (congrArg Subtype.val heq), Or.inl h⟩

lemma deg2Retract_reachable_of_walk (tree : SphereTree) (root w₁ w₂ : tree.V)
    (hne : w₁ ≠ w₂) (hw₁_ne : w₁ ≠ root)
    (h_uniq₂ : ∀ y, tree.adj.Adj root y → y = w₁ ∨ y = w₂)
    {x y : tree.V} (p : tree.adj.Walk x y) :
    (suppressedSimpleGraph tree root w₁ w₂).Reachable
      (deg1Retract tree root w₁ hw₁_ne x)
      (deg1Retract tree root w₁ hw₁_ne y) := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h _ ih => exact (deg2Retract_reachable_of_adj tree root w₁ w₂ hne hw₁_ne h_uniq₂ h).trans ih

/-- Suppressing a degree-2 vertex in a tree and joining its two neighbors preserves connectivity (Zero-sorry). -/
theorem suppressedSimpleGraph_connected (tree : SphereTree) (root w₁ w₂ : tree.V)
    (hne : w₁ ≠ w₂) (hadj₁ : tree.adj.Adj root w₁)
    (h_uniq₂ : ∀ y, tree.adj.Adj root y → y = w₁ ∨ y = w₂) :
    (suppressedSimpleGraph tree root w₁ w₂).Connected := by
  have hw₁_ne : w₁ ≠ root := hadj₁.ne'
  haveI : Nonempty { v : tree.V // v ≠ root } := ⟨⟨w₁, hw₁_ne⟩⟩
  refine SimpleGraph.Connected.mk ?_
  intro u v
  obtain ⟨p⟩ := tree.is_tree.isConnected u.1 v.1
  have h_reach := deg2Retract_reachable_of_walk tree root w₁ w₂ hne hw₁_ne h_uniq₂ p
  rwa [deg1Retract_eq_self tree root w₁ hw₁_ne u,
       deg1Retract_eq_self tree root w₁ hw₁_ne v] at h_reach

lemma not_reachable_in_pruned_of_common_neighbors
    (tree : SphereTree) (root : tree.V)
    (w₁ w₂ : { v : tree.V // v ≠ root })
    (hne : w₁ ≠ w₂)
    (hadj₁ : tree.adj.Adj root w₁.1)
    (hadj₂ : tree.adj.Adj root w₂.1) :
    ¬ (prunedSimpleGraph tree root).Reachable w₁ w₂ := by
  intro ⟨p⟩
  let p_map := p.map (prunedSimpleGraphHom tree root)
  let path₁ : tree.adj.Path w₁.1 w₂.1 := p_map.toPath
  have h_ne12 : w₁.1 ≠ w₂.1 := fun h => hne (Subtype.ext h)
  let w_root : tree.adj.Walk w₁.1 w₂.1 :=
    SimpleGraph.Walk.cons (tree.adj.symm hadj₁) (SimpleGraph.Walk.cons hadj₂ SimpleGraph.Walk.nil)
  have hw_root : w_root.IsPath := by
    refine SimpleGraph.Walk.IsPath.cons ?_ ?_
    · exact SimpleGraph.Walk.IsPath.cons (by simp) (by simp [hadj₂.ne])
    · simp [hadj₁.ne', h_ne12]
  let path₂ : tree.adj.Path w₁.1 w₂.1 := ⟨w_root, hw_root⟩
  have h_eq : path₁ = path₂ := tree.is_tree.IsAcyclic.path_unique path₁ path₂
  have h_mem : root ∈ path₁.1.support := by
    rw [h_eq]
    dsimp [path₂, w_root]
    simp
  have h_sub := SimpleGraph.Walk.support_toPath_subset p_map h_mem
  dsimp [p_map, prunedSimpleGraphHom] at h_sub
  rw [SimpleGraph.Walk.support_map, List.mem_map] at h_sub
  rcases h_sub with ⟨u, _, hu_eq⟩
  exact u.2 hu_eq

noncomputable def inCompW1 (tree : SphereTree) (root : tree.V)
    (w₁ : { v : tree.V // v ≠ root }) (u : { v : tree.V // v ≠ root }) : Bool :=
  decide ((prunedSimpleGraph tree root).Reachable w₁ u)

lemma inCompW1_step (tree : SphereTree) (root : tree.V)
    (w₁ w₂ : { v : tree.V // v ≠ root })
    (hne : w₁ ≠ w₂)
    (hadj₁ : tree.adj.Adj root w₁.1)
    (hadj₂ : tree.adj.Adj root w₂.1)
    {x y : { v : tree.V // v ≠ root }}
    (h : (suppressedSimpleGraph tree root w₁.1 w₂.1).Adj x y) :
    (inCompW1 tree root w₁ x ≠ inCompW1 tree root w₁ y) ↔
    (s(x, y) = s(w₁, w₂)) := by
  have h_not_reach := not_reachable_in_pruned_of_common_neighbors tree root w₁ w₂ hne hadj₁ hadj₂
  have hw₁_true : inCompW1 tree root w₁ w₁ = true :=
    decide_eq_true (SimpleGraph.Reachable.refl w₁)
  have hw₂_false : inCompW1 tree root w₁ w₂ = false :=
    decide_eq_false h_not_reach
  constructor
  · intro h_diff
    rcases h.2 with hadj | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exfalso
      have h_iff : (prunedSimpleGraph tree root).Reachable w₁ x ↔
          (prunedSimpleGraph tree root).Reachable w₁ y :=
        ⟨fun hr => hr.trans (SimpleGraph.Adj.reachable hadj),
         fun hr => hr.trans (SimpleGraph.Adj.reachable (tree.adj.symm hadj))⟩
      have h_eq_bool : inCompW1 tree root w₁ x = inCompW1 tree root w₁ y := by
        dsimp [inCompW1]
        simp [h_iff]
      exact h_diff h_eq_bool
    · have hx' : x = w₁ := Subtype.ext hx
      have hy' : y = w₂ := Subtype.ext hy
      rw [hx', hy']
    · have hx' : x = w₂ := Subtype.ext hx
      have hy' : y = w₁ := Subtype.ext hy
      rw [hx', hy', Sym2.eq_swap]
  · intro h_bridge
    rw [Sym2.eq_iff] at h_bridge
    rcases h_bridge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hw₁_true, hw₂_false]; decide
    · rw [hw₂_false, hw₁_true]; decide

lemma suppressed_walk_bridge_parity (tree : SphereTree) (root : tree.V)
    (w₁ w₂ : { v : tree.V // v ≠ root })
    (hne : w₁ ≠ w₂)
    (hadj₁ : tree.adj.Adj root w₁.1)
    (hadj₂ : tree.adj.Adj root w₂.1)
    {x y : { v : tree.V // v ≠ root }}
    (p : (suppressedSimpleGraph tree root w₁.1 w₂.1).Walk x y) :
    (p.edges.count s(w₁, w₂) : ZMod 2) =
    if inCompW1 tree root w₁ x = inCompW1 tree root w₁ y then 0 else 1 := by
  induction p with
  | nil => simp
  | @cons u v z h q ih =>
    rw [SimpleGraph.Walk.edges_cons, List.count_cons]
    have h_step := inCompW1_step tree root w₁ w₂ hne hadj₁ hadj₂ h
    push_cast
    rw [ih]
    by_cases he : s(u, v) = s(w₁, w₂)
    · simp only [he, beq_self_eq_true, ↓reduceIte]
      have h_diff : inCompW1 tree root w₁ u ≠ inCompW1 tree root w₁ v := h_step.mpr he
      rcases hu : inCompW1 tree root w₁ u <;> rcases hv : inCompW1 tree root w₁ v <;>
        rcases hz : inCompW1 tree root w₁ z <;>
        simp_all <;> try decide
    · have h_beq : (s(u, v) == s(w₁, w₂)) = false := by
        simp [beq_iff_eq, he]
      simp only [h_beq, Bool.false_eq_true, ↓reduceIte, add_zero]
      have h_same : inCompW1 tree root w₁ u = inCompW1 tree root w₁ v := by
        by_contra h_diff
        exact he (h_step.mp h_diff)
      rw [h_same]

lemma suppressed_cycle_not_mem_bridge (tree : SphereTree) (root : tree.V)
    (w₁ w₂ : { v : tree.V // v ≠ root })
    (hne : w₁ ≠ w₂)
    (hadj₁ : tree.adj.Adj root w₁.1)
    (hadj₂ : tree.adj.Adj root w₂.1)
    {x : { v : tree.V // v ≠ root }}
    (p : (suppressedSimpleGraph tree root w₁.1 w₂.1).Walk x x) (hp : p.IsCycle) :
    s(w₁, w₂) ∉ p.edges := by
  have h_parity := suppressed_walk_bridge_parity tree root w₁ w₂ hne hadj₁ hadj₂ p
  simp only [↓reduceIte] at h_parity
  have h_nodup : p.edges.Nodup := hp.isTrail.edges_nodup
  have h_le1 := (List.nodup_iff_count_le_one.mp h_nodup) s(w₁, w₂)
  have h_count : p.edges.count s(w₁, w₂) = 0 := by
    have h_mod : (p.edges.count s(w₁, w₂) : ZMod 2) = 0 := h_parity
    have h_dvd : 2 ∣ p.edges.count s(w₁, w₂) :=
      (ZMod.natCast_zmod_eq_zero_iff_dvd _ 2).mp h_mod
    obtain ⟨k, hk⟩ := h_dvd
    omega
  exact List.count_eq_zero.mp h_count

def prunedToSuppressedHom (tree : SphereTree) (root w₁ w₂ : tree.V) :
    prunedSimpleGraph tree root →g suppressedSimpleGraph tree root w₁ w₂ where
  toFun u := u
  map_rel' h := ⟨h.ne, Or.inl h⟩

def walkOfSuppressedNoBridge (tree : SphereTree) (root : tree.V)
    (w₁ w₂ : { v : tree.V // v ≠ root }) :
    ∀ {u v : { v : tree.V // v ≠ root }}
      (p : (suppressedSimpleGraph tree root w₁.1 w₂.1).Walk u v),
      (s(w₁, w₂) ∉ p.edges) → (prunedSimpleGraph tree root).Walk u v
  | _, _, SimpleGraph.Walk.nil, _ => SimpleGraph.Walk.nil
  | u, _, SimpleGraph.Walk.cons (v := u') h q, hp =>
    have h_adj : (prunedSimpleGraph tree root).Adj u u' := by
      rcases h.2 with hadj | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hadj
      · exfalso
        have hu : u = w₁ := Subtype.ext h1
        have hu' : u' = w₂ := Subtype.ext h2
        have heq : s(u, u') = s(w₁, w₂) := by rw [hu, hu']
        have h_in : s(u, u') ∈ (SimpleGraph.Walk.cons h q).edges := by simp
        exact hp (heq ▸ h_in)
      · exfalso
        have hu : u = w₂ := Subtype.ext h1
        have hu' : u' = w₁ := Subtype.ext h2
        have heq : s(u, u') = s(w₁, w₂) := by rw [hu, hu', Sym2.eq_swap]
        have h_in : s(u, u') ∈ (SimpleGraph.Walk.cons h q).edges := by simp
        exact hp (heq ▸ h_in)
    have hp' : s(w₁, w₂) ∉ q.edges := fun h_in => hp (List.mem_cons_of_mem _ h_in)
    SimpleGraph.Walk.cons h_adj (walkOfSuppressedNoBridge tree root w₁ w₂ q hp')

lemma walkOfSuppressedNoBridge_map (tree : SphereTree) (root : tree.V)
    (w₁ w₂ : { v : tree.V // v ≠ root }) :
    ∀ {u v : { v : tree.V // v ≠ root }}
      (p : (suppressedSimpleGraph tree root w₁.1 w₂.1).Walk u v)
      (hp : s(w₁, w₂) ∉ p.edges),
      (walkOfSuppressedNoBridge tree root w₁ w₂ p hp).map
        (prunedToSuppressedHom tree root w₁.1 w₂.1) = p
  | _, _, SimpleGraph.Walk.nil, _ => rfl
  | _, _, SimpleGraph.Walk.cons h q, hp => by
    simp only [walkOfSuppressedNoBridge, SimpleGraph.Walk.map_cons, prunedToSuppressedHom]
    congr 1
    exact walkOfSuppressedNoBridge_map tree root w₁ w₂ q _

theorem suppressedSimpleGraph_isAcyclic (tree : SphereTree) (root w₁ w₂ : tree.V)
    (hne : w₁ ≠ w₂)
    (hadj₁ : tree.adj.Adj root w₁)
    (hadj₂ : tree.adj.Adj root w₂) :
    (suppressedSimpleGraph tree root w₁ w₂).IsAcyclic := by
  let w₁' : { v : tree.V // v ≠ root } := ⟨w₁, hadj₁.ne'⟩
  let w₂' : { v : tree.V // v ≠ root } := ⟨w₂, hadj₂.ne'⟩
  have hne' : w₁' ≠ w₂' := fun h => hne (congrArg Subtype.val h)
  intro x c hc
  have h_not_bridge := suppressed_cycle_not_mem_bridge tree root w₁' w₂' hne' hadj₁ hadj₂ c hc
  let c₀ := walkOfSuppressedNoBridge tree root w₁' w₂' c h_not_bridge
  have h_map := walkOfSuppressedNoBridge_map tree root w₁' w₂' c h_not_bridge
  have h_inj : Function.Injective (prunedToSuppressedHom tree root w₁ w₂) := fun _ _ h => h
  have h_cyc : c₀.IsCycle := by
    have h_iff := SimpleGraph.Walk.map_isCycle_iff_of_injective
      (f := prunedToSuppressedHom tree root w₁ w₂) h_inj (p := c₀)
    rw [h_map] at h_iff
    exact h_iff.mp hc
  exact prunedSimpleGraph_isAcyclic tree root c₀ h_cyc

theorem suppressedSimpleGraph_isTree (tree : SphereTree) (root w₁ w₂ : tree.V)
    (hne : w₁ ≠ w₂)
    (hadj₁ : tree.adj.Adj root w₁)
    (hadj₂ : tree.adj.Adj root w₂)
    (h_uniq₂ : ∀ y, tree.adj.Adj root y → y = w₁ ∨ y = w₂) :
    (suppressedSimpleGraph tree root w₁ w₂).IsTree :=
  ⟨suppressedSimpleGraph_connected tree root w₁ w₂ hne hadj₁ h_uniq₂,
   suppressedSimpleGraph_isAcyclic tree root w₁ w₂ hne hadj₁ hadj₂⟩

noncomputable def origNeighbor (tree : SphereTree) (root : tree.V)
    (v u : { v : tree.V // v ≠ root }) : tree.V :=
  if tree.adj.Adj v.1 u.1 then u.1 else root

lemma origNeighbor_adj (tree : SphereTree) (root w₁ w₂ : tree.V)
    (hadj₁ : tree.adj.Adj root w₁) (hadj₂ : tree.adj.Adj root w₂)
    (v u : { v : tree.V // v ≠ root })
    (h : (suppressedSimpleGraph tree root w₁ w₂).Adj v u) :
    tree.adj.Adj v.1 (origNeighbor tree root v u) := by
  dsimp [origNeighbor]
  split_ifs with hadj
  · exact hadj
  · rcases h.2 with h_old | ⟨hv, _⟩ | ⟨hv, _⟩
    · exact False.elim (hadj h_old)
    · rw [hv]; exact tree.adj.symm hadj₁
    · rw [hv]; exact tree.adj.symm hadj₂

lemma origNeighbor_injective (tree : SphereTree) (root w₁ w₂ : tree.V)
    (v u₁ u₂ : { v : tree.V // v ≠ root })
    (h₁ : (suppressedSimpleGraph tree root w₁ w₂).Adj v u₁)
    (h₂ : (suppressedSimpleGraph tree root w₁ w₂).Adj v u₂)
    (heq : origNeighbor tree root v u₁ = origNeighbor tree root v u₂) :
    u₁ = u₂ := by
  dsimp [origNeighbor] at heq
  split_ifs at heq with hadj₁ hadj₂ hadj₂
  · exact Subtype.ext heq
  · exact False.elim (u₁.2 heq)
  · exact False.elim (u₂.2 heq.symm)
  · rcases h₁.2 with h_old₁ | ⟨hv₁, hu₁⟩ | ⟨hv₁, hu₁⟩
    · exact False.elim (hadj₁ h_old₁)
    · rcases h₂.2 with h_old₂ | ⟨_, hu₂⟩ | ⟨hv₂, hu₂⟩
      · exact False.elim (hadj₂ h_old₂)
      · exact Subtype.ext (hu₁.trans hu₂.symm)
      · exfalso
        have hw12 : w₁ = w₂ := hv₁.symm.trans hv₂
        subst hw12
        exact h₁.1 (Subtype.ext (hv₁.trans hu₁.symm))
    · rcases h₂.2 with h_old₂ | ⟨hv₂, hu₂⟩ | ⟨_, hu₂⟩
      · exact False.elim (hadj₂ h_old₂)
      · exfalso
        have hw21 : w₂ = w₁ := hv₁.symm.trans hv₂
        subst hw21
        exact h₁.1 (Subtype.ext (hv₁.trans hu₁.symm))
      · exact Subtype.ext (hu₁.trans hu₂.symm)

lemma origNeighbor_surjective (tree : SphereTree) (root w₁ w₂ : tree.V)
    (hne : w₁ ≠ w₂)
    (hadj₁ : tree.adj.Adj root w₁)
    (hadj₂ : tree.adj.Adj root w₂)
    (h_uniq₂ : ∀ y, tree.adj.Adj root y → y = w₁ ∨ y = w₂)
    (v : { v : tree.V // v ≠ root })
    (y : tree.V) (hy : tree.adj.Adj v.1 y) :
    ∃ (u : { v : tree.V // v ≠ root })
      (_hu : (suppressedSimpleGraph tree root w₁ w₂).Adj v u),
      origNeighbor tree root v u = y := by
  by_cases hy_ne : y ≠ root
  · refine ⟨⟨y, hy_ne⟩, ⟨fun hveq => hy.ne (congrArg Subtype.val hveq), Or.inl hy⟩, ?_⟩
    dsimp [origNeighbor]
    exact if_pos hy
  · push_neg at hy_ne
    have hy_root : tree.adj.Adj root v.1 := by
      rw [hy_ne] at hy
      exact tree.adj.symm hy
    rcases h_uniq₂ v.1 hy_root with hv1 | hv2
    · refine ⟨⟨w₂, hadj₂.ne'⟩,
        ⟨fun hveq => hne (hv1.symm.trans (congrArg Subtype.val hveq)),
         Or.inr (Or.inl ⟨hv1, rfl⟩)⟩, ?_⟩
      dsimp [origNeighbor]
      have h_not_adj : ¬ tree.adj.Adj v.1 w₂ := by
        rw [hv1]
        exact not_adj_of_common_neighbor_in_tree tree root w₁ w₂ hadj₁ hadj₂
      rw [if_neg h_not_adj, hy_ne]
    · refine ⟨⟨w₁, hadj₁.ne'⟩,
        ⟨fun hveq => hne ((congrArg Subtype.val hveq).symm.trans hv2),
         Or.inr (Or.inr ⟨hv2, rfl⟩)⟩, ?_⟩
      dsimp [origNeighbor]
      have h_not_adj : ¬ tree.adj.Adj v.1 w₁ := by
        rw [hv2]
        exact not_adj_of_common_neighbor_in_tree tree root w₂ w₁ hadj₂ hadj₁
      rw [if_neg h_not_adj, hy_ne]

noncomputable def suppressedNodePoint (tree : SphereTree) (root w₁ w₂ : tree.V)
    (hadj₁ : tree.adj.Adj root w₁) (hadj₂ : tree.adj.Adj root w₂)
    (v u : { v : tree.V // v ≠ root })
    (h : (suppressedSimpleGraph tree root w₁ w₂).Adj v u) : CP1 :=
  tree.node_point v.1 (origNeighbor tree root v u)
    (origNeighbor_adj tree root w₁ w₂ hadj₁ hadj₂ v u h)

theorem suppressedNodeDistinct (tree : SphereTree) (root w₁ w₂ : tree.V)
    (hadj₁ : tree.adj.Adj root w₁) (hadj₂ : tree.adj.Adj root w₂)
    (v u₁ u₂ : { v : tree.V // v ≠ root })
    (h₁ : (suppressedSimpleGraph tree root w₁ w₂).Adj v u₁)
    (h₂ : (suppressedSimpleGraph tree root w₁ w₂).Adj v u₂)
    (hne : u₁ ≠ u₂) :
    suppressedNodePoint tree root w₁ w₂ hadj₁ hadj₂ v u₁ h₁ ≠
    suppressedNodePoint tree root w₁ w₂ hadj₁ hadj₂ v u₂ h₂ := by
  dsimp [suppressedNodePoint]
  apply tree.node_distinct
  intro heq
  exact hne (origNeighbor_injective tree root w₁ w₂ v u₁ u₂ h₁ h₂ heq)

theorem suppressedNodalMatch
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (w₁ w₂ : pdata.tree.V)
    (hadj₁ : pdata.tree.adj.Adj pdata.root w₁)
    (hadj₂ : pdata.tree.adj.Adj pdata.root w₂)
    (v w : { v : pdata.tree.V // v ≠ pdata.root })
    (h : (suppressedSimpleGraph pdata.tree pdata.root w₁ w₂).Adj v w) :
    pdata.map v.1 (suppressedNodePoint pdata.tree pdata.root w₁ w₂ hadj₁ hadj₂ v w h) =
    pdata.map w.1 (suppressedNodePoint pdata.tree pdata.root w₁ w₂ hadj₁ hadj₂ w v
      ((suppressedSimpleGraph pdata.tree pdata.root w₁ w₂).symm h)) := by
  dsimp [suppressedNodePoint]
  by_cases hadj : pdata.tree.adj.Adj v.1 w.1
  · have hadj_symm : pdata.tree.adj.Adj w.1 v.1 := pdata.tree.adj.symm hadj
    have ho1 : origNeighbor pdata.tree pdata.root v w = w.1 := if_pos hadj
    have ho2 : origNeighbor pdata.tree pdata.root w v = v.1 := if_pos hadj_symm
    have h1 : pdata.tree.node_point v.1 (origNeighbor pdata.tree pdata.root v w)
        (origNeighbor_adj pdata.tree pdata.root w₁ w₂ hadj₁ hadj₂ v w h) =
        pdata.tree.node_point v.1 w.1 hadj := by
      congr 1
    have h2 : pdata.tree.node_point w.1 (origNeighbor pdata.tree pdata.root w v)
        (origNeighbor_adj pdata.tree pdata.root w₁ w₂ hadj₁ hadj₂ w v
          ((suppressedSimpleGraph pdata.tree pdata.root w₁ w₂).symm h)) =
        pdata.tree.node_point w.1 v.1 hadj_symm := by
      congr 1
    rw [h1, h2]
    exact pdata.nodal_match v.1 w.1 hadj
  · have hadj_symm : ¬ pdata.tree.adj.Adj w.1 v.1 := fun hs => hadj (pdata.tree.adj.symm hs)
    have ho1 : origNeighbor pdata.tree pdata.root v w = pdata.root := if_neg hadj
    have ho2 : origNeighbor pdata.tree pdata.root w v = pdata.root := if_neg hadj_symm
    have hm1 := pdata.nodal_match v.1 (origNeighbor pdata.tree pdata.root v w)
      (origNeighbor_adj pdata.tree pdata.root w₁ w₂ hadj₁ hadj₂ v w h)
    have hm2 := pdata.nodal_match w.1 (origNeighbor pdata.tree pdata.root w v)
      (origNeighbor_adj pdata.tree pdata.root w₁ w₂ hadj₁ hadj₂ w v
        ((suppressedSimpleGraph pdata.tree pdata.root w₁ w₂).symm h))
    rw [hm1, hm2]
    rcases h_const with ⟨c, hc⟩
    have hc_fn : ∀ (y : pdata.tree.V) (hy : y = pdata.root) (z : CP1), pdata.map y z = c := by
      intro y hy z; rw [hy]; exact hc z
    rw [hc_fn _ ho1, hc_fn _ ho2]

theorem suppressedSimpleGraph_degree_eq (tree : SphereTree) (root w₁ w₂ : tree.V)
    (hne : w₁ ≠ w₂)
    (hadj₁ : tree.adj.Adj root w₁)
    (hadj₂ : tree.adj.Adj root w₂)
    (h_uniq₂ : ∀ y, tree.adj.Adj root y → y = w₁ ∨ y = w₂)
    (v : { v : tree.V // v ≠ root }) :
    (suppressedSimpleGraph tree root w₁ w₂).degree v = tree.adj.degree v.1 := by
  change ((suppressedSimpleGraph tree root w₁ w₂).neighborFinset v).card =
    (tree.adj.neighborFinset v.1).card
  refine Finset.card_bij (fun u _ => origNeighbor tree root v u) ?_ ?_ ?_
  · intro u hu
    rw [SimpleGraph.mem_neighborFinset] at hu ⊢
    exact origNeighbor_adj tree root w₁ w₂ hadj₁ hadj₂ v u hu
  · intro u₁ hu₁ u₂ hu₂ heq
    rw [SimpleGraph.mem_neighborFinset] at hu₁ hu₂
    exact origNeighbor_injective tree root w₁ w₂ v u₁ u₂ hu₁ hu₂ heq
  · intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    obtain ⟨u, hu, heq⟩ := origNeighbor_surjective tree root w₁ w₂ hne hadj₁ hadj₂ h_uniq₂ v y hy
    exact ⟨u, (SimpleGraph.mem_neighborFinset _ _ _).mpr hu, heq⟩

theorem suppressed_nodal_set_eq (tree : SphereTree) (root w₁ w₂ : tree.V)
    (hne : w₁ ≠ w₂)
    (hadj₁ : tree.adj.Adj root w₁)
    (hadj₂ : tree.adj.Adj root w₂)
    (h_uniq₂ : ∀ y, tree.adj.Adj root y → y = w₁ ∨ y = w₂)
    (v : { v : tree.V // v ≠ root }) :
    { z | ∃ (w : { v : tree.V // v ≠ root })
      (h : (suppressedSimpleGraph tree root w₁ w₂).Adj v w),
      z = suppressedNodePoint tree root w₁ w₂ hadj₁ hadj₂ v w h } =
    { z | ∃ (y : tree.V) (h : tree.adj.Adj v.1 y), z = tree.node_point v.1 y h } := by
  ext z
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, h, rfl⟩
    exact ⟨origNeighbor tree root v w, origNeighbor_adj tree root w₁ w₂ hadj₁ hadj₂ v w h, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨w, hw, heq⟩ := origNeighbor_surjective tree root w₁ w₂ hne hadj₁ hadj₂ h_uniq₂ v y hy
    refine ⟨w, hw, ?_⟩
    dsimp [suppressedNodePoint]
    congr 1
    exact heq.symm

lemma tendstoUniformlyOn_comp_of_tendsto_const
    {f g : ℕ → CP1 → CP1} {p₂ q₁ p₁ : CP1} {K : Set CP1}
    (hp : p₁ ≠ p₂)
    (hf : ∀ K₁ ⊆ punctured_sphere {p₁}, IsCompact K₁ →
      TendstoUniformlyOn f (fun _ => q₁) atTop K₁)
    (hg : TendstoUniformlyOn g (fun _ => p₂) atTop K) :
    TendstoUniformlyOn (fun n x => f n (g n x)) (fun _ => q₁) atTop K := by
  have h_pos : 0 < dist p₂ p₁ := dist_pos.mpr hp.symm
  let r := dist p₂ p₁ / 2
  have hr : 0 < r := half_pos h_pos
  let K₁ : Set CP1 := Metric.closedBall p₂ r
  have hK₁_compact : IsCompact K₁ :=
    IsCompact.of_isClosed_subset isCompact_univ isClosed_ball (subset_univ _)
  have hK₁_sub : K₁ ⊆ punctured_sphere {p₁} := by
    intro y hy
    simp only [punctured_sphere, mem_diff, mem_univ, mem_singleton_iff, true_and]
    intro hy_eq
    rw [hy_eq] at hy
    have h_le : dist p₁ p₂ ≤ dist p₂ p₁ / 2 := Metric.mem_closedBall.mp hy
    rw [dist_comm] at h_le
    linarith
  have hf_K₁ := hf K₁ hK₁_sub hK₁_compact
  rw [Metric.tendstoUniformlyOn_iff] at hf_K₁ hg ⊢
  intro ε hε
  filter_upwards [hf_K₁ ε hε, hg r hr] with n hfn hgn x hx
  have hgx_mem : g n x ∈ K₁ := by
    rw [Metric.mem_closedBall, dist_comm]
    exact (hgn x hx).le
  exact hfn (g n x) hgx_mem

lemma moebius_comp_cancel_middle (ϕ_v ϕ_r ϕ_w : MoebiusFrame) (x : CP1) :
    (MoebiusFrame.comp (MoebiusFrame.inv ϕ_v) ϕ_w).toHomeo x =
    (MoebiusFrame.comp (MoebiusFrame.inv ϕ_v) ϕ_r).toHomeo
      ((MoebiusFrame.comp (MoebiusFrame.inv ϕ_r) ϕ_w).toHomeo x) := by
  change ϕ_v.toHomeo.symm (ϕ_w.toHomeo x) =
    ϕ_v.toHomeo.symm (ϕ_r.toHomeo (ϕ_r.toHomeo.symm (ϕ_w.toHomeo x)))
  rw [ϕ_r.toHomeo.apply_symm_apply]

theorem suppressed_frame_collapse
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (w₁ w₂ : pdata.tree.V)
    (hadj₁ : pdata.tree.adj.Adj pdata.root w₁)
    (hadj₂ : pdata.tree.adj.Adj pdata.root w₂)
    (v w : { v : pdata.tree.V // v ≠ pdata.root })
    (h : (suppressedSimpleGraph pdata.tree pdata.root w₁ w₂).Adj v w)
    (K : Set CP1)
    (hK_sub : K ⊆ punctured_sphere {suppressedNodePoint pdata.tree pdata.root w₁ w₂ hadj₁ hadj₂ w v
      ((suppressedSimpleGraph pdata.tree pdata.root w₁ w₂).symm h)})
    (hK_comp : IsCompact K) :
    TendstoUniformlyOn
      (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (pdata.frames v.1 n)) (pdata.frames w.1 n)).toHomeo)
      (fun _ => suppressedNodePoint pdata.tree pdata.root w₁ w₂ hadj₁ hadj₂ v w h) atTop K := by
  by_cases hadj : pdata.tree.adj.Adj v.1 w.1
  · have hadj_symm : pdata.tree.adj.Adj w.1 v.1 := pdata.tree.adj.symm hadj
    have ho1 : origNeighbor pdata.tree pdata.root v w = w.1 := if_pos hadj
    have ho2 : origNeighbor pdata.tree pdata.root w v = v.1 := if_pos hadj_symm
    have h1 : suppressedNodePoint pdata.tree pdata.root w₁ w₂ hadj₁ hadj₂ v w h =
        pdata.tree.node_point v.1 w.1 hadj := by
      dsimp [suppressedNodePoint]
      congr 1
    have h2 : suppressedNodePoint pdata.tree pdata.root w₁ w₂ hadj₁ hadj₂ w v
        ((suppressedSimpleGraph pdata.tree pdata.root w₁ w₂).symm h) =
        pdata.tree.node_point w.1 v.1 hadj_symm := by
      dsimp [suppressedNodePoint]
      congr 1
    rw [h1]
    rw [h2] at hK_sub
    exact pdata.frame_collapse v.1 w.1 hadj K hK_sub hK_comp
  · have hadj_symm : ¬ pdata.tree.adj.Adj w.1 v.1 := fun hs => hadj (pdata.tree.adj.symm hs)
    have ho1 : origNeighbor pdata.tree pdata.root v w = pdata.root := if_neg hadj
    have ho2 : origNeighbor pdata.tree pdata.root w v = pdata.root := if_neg hadj_symm
    let hv_orig := origNeighbor_adj pdata.tree pdata.root w₁ w₂ hadj₁ hadj₂ v w h
    let hw_orig := origNeighbor_adj pdata.tree pdata.root w₁ w₂ hadj₁ hadj₂ w v
      ((suppressedSimpleGraph pdata.tree pdata.root w₁ w₂).symm h)
    have hv_ne_w : v.1 ≠ w.1 := fun heq => h.1 (Subtype.ext heq)
    have hp_ne : pdata.tree.node_point (origNeighbor pdata.tree pdata.root v w) v.1
        (pdata.tree.adj.symm hv_orig) ≠
      pdata.tree.node_point (origNeighbor pdata.tree pdata.root w v) w.1
        (pdata.tree.adj.symm hw_orig) := by
      have h_fn : ∀ (r₁ r₂ : pdata.tree.V) (hr₁ : r₁ = pdata.root) (hr₂ : r₂ = pdata.root)
          (ha₁ : pdata.tree.adj.Adj v.1 r₁) (ha₂ : pdata.tree.adj.Adj w.1 r₂),
          pdata.tree.node_point r₁ v.1 (pdata.tree.adj.symm ha₁) ≠
          pdata.tree.node_point r₂ w.1 (pdata.tree.adj.symm ha₂) := by
        intro r₁ r₂ hr₁ hr₂ ha₁ ha₂
        cases hr₁; cases hr₂
        exact pdata.tree.node_distinct pdata.root v.1 w.1
          (pdata.tree.adj.symm ha₁) (pdata.tree.adj.symm ha₂) hv_ne_w
      exact h_fn _ _ ho1 ho2 hv_orig hw_orig
    have hf_col := pdata.frame_collapse v.1 (origNeighbor pdata.tree pdata.root v w) hv_orig
    have hg_col := pdata.frame_collapse (origNeighbor pdata.tree pdata.root w v) w.1
      (pdata.tree.adj.symm hw_orig) K hK_sub hK_comp
    have h_comp_eq : (fun n (x : CP1) =>
        (MoebiusFrame.comp (MoebiusFrame.inv (pdata.frames v.1 n)) (pdata.frames w.1 n)).toHomeo x) =
      (fun n (x : CP1) =>
        (MoebiusFrame.comp (MoebiusFrame.inv (pdata.frames v.1 n))
          (pdata.frames (origNeighbor pdata.tree pdata.root v w) n)).toHomeo
        ((MoebiusFrame.comp (MoebiusFrame.inv (pdata.frames (origNeighbor pdata.tree pdata.root w v) n))
          (pdata.frames w.1 n)).toHomeo x)) := by
      funext n; funext x
      have h_eq_orig : origNeighbor pdata.tree pdata.root v w =
          origNeighbor pdata.tree pdata.root w v := ho1.trans ho2.symm
      rw [h_eq_orig]
      exact moebius_comp_cancel_middle _ _ _ x
    rw [h_comp_eq]
    exact tendstoUniformlyOn_comp_of_tendsto_const hp_ne hf_col hg_col

/-- Suppressed sphere tree structure and convergence transfer on `{v : pdata.tree.V // v ≠ pdata.root}`
when a degree-2 constant root is suppressed and its two neighbors are joined by a bridge edge
(Proved with zero sorry). -/
theorem suppressed_tree_and_conv
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_deg2 : pdata.tree.adj.degree pdata.root = 2)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (w₁ w₂ : pdata.tree.V)
    (hne : w₁ ≠ w₂)
    (hadj₁ : pdata.tree.adj.Adj pdata.root w₁)
    (hadj₂ : pdata.tree.adj.Adj pdata.root w₂)
    (h_uniq₂ : ∀ y, pdata.tree.adj.Adj pdata.root y → y = w₁ ∨ y = w₂)
    (root' : {v : pdata.tree.V // v ≠ pdata.root}) :
    let adj' := suppressedSimpleGraph pdata.tree pdata.root w₁ w₂
    ∃ (_is_tree' : adj'.IsTree)
      (node_point' : (v w : {v : pdata.tree.V // v ≠ pdata.root}) → adj'.Adj v w → CP1)
      (_node_distinct' : ∀ (v u₁ u₂ : {v : pdata.tree.V // v ≠ pdata.root})
        (h₁ : adj'.Adj v u₁) (h₂ : adj'.Adj v u₂),
        u₁ ≠ u₂ → node_point' v u₁ h₁ ≠ node_point' v u₂ h₂)
      (frames' : (v : {v : pdata.tree.V // v ≠ pdata.root}) → ℕ → MoebiusFrame),
      (∀ (v w : {v : pdata.tree.V // v ≠ pdata.root}) (h : adj'.Adj v w),
        pdata.map v.1 (node_point' v w h) = pdata.map w.1 (node_point' w v (adj'.symm h))) ∧
      (∀ (v : {v : pdata.tree.V // v ≠ pdata.root}), v ≠ root' →
        (∃ c : M, ∀ z : CP1, pdata.map v.1 z = c) →
          3 ≤ adj'.degree v) ∧
      (∃ ϕ_root : ℕ → MoebiusFrame, ∀ n, frames' root' n = ϕ_root n) ∧
      (∀ (v w : {v : pdata.tree.V // v ≠ pdata.root}) (h : adj'.Adj v w),
        ∀ K ⊆ punctured_sphere {node_point' w v (adj'.symm h)}, IsCompact K →
          TendstoUniformlyOn
            (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (frames' v n)) (frames' w n)).toHomeo)
            (fun _ => node_point' v w h) atTop K) ∧
      (∀ (v : {v : pdata.tree.V // v ≠ pdata.root}),
        SmoothLocalConvergesOn I
          (fun n => (u_seq (pdata.σ.1 n)) ∘ (frames' v n).toHomeo)
          (pdata.map v.1)
          (punctured_sphere { z | ∃ (w : {v : pdata.tree.V // v ≠ pdata.root})
            (h : adj'.Adj v w), z = node_point' v w h })) := by
  let _ := h_deg2
  refine ⟨suppressedSimpleGraph_isTree pdata.tree pdata.root w₁ w₂ hne hadj₁ hadj₂ h_uniq₂,
    suppressedNodePoint pdata.tree pdata.root w₁ w₂ hadj₁ hadj₂,
    suppressedNodeDistinct pdata.tree pdata.root w₁ w₂ hadj₁ hadj₂,
    fun v n => pdata.frames v.1 n,
    suppressedNodalMatch I u_seq pdata h_const w₁ w₂ hadj₁ hadj₂,
    ?_, ⟨_, fun _ => rfl⟩,
    suppressed_frame_collapse I u_seq pdata w₁ w₂ hadj₁ hadj₂, ?_⟩
  · intro v _ h_const_v
    rw [suppressedSimpleGraph_degree_eq pdata.tree pdata.root w₁ w₂ hne hadj₁ hadj₂ h_uniq₂ v]
    exact pdata.stable_off_root v.1 v.2 h_const_v
  · intro v
    change SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames v.1 n).toHomeo)
      (pdata.map v.1)
      (punctured_sphere { z | ∃ (w : {v : pdata.tree.V // v ≠ pdata.root})
        (h : (suppressedSimpleGraph pdata.tree pdata.root w₁ w₂).Adj v w),
        z = suppressedNodePoint pdata.tree pdata.root w₁ w₂ hadj₁ hadj₂ v w h })
    rw [suppressed_nodal_set_eq pdata.tree pdata.root w₁ w₂ hne hadj₁ hadj₂ h_uniq₂ v]
    exact pdata.smooth_conv v.1

/-- Suppression operation: suppressing a degree-2 constant root vertex and joining its two neighbors
(Proved with zero sorry from `root_degree_two_neighbors_full`, `suppressed_tree_and_conv`,
`card_subtype_ne_root_add_one`, and `sum_subtype_ne_root_eq_sum_univ_of_zero`). -/
theorem suppress_degree_two_root
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_deg2 : pdata.tree.adj.degree pdata.root = 2)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) := by
  obtain ⟨w₁, w₂, hne, hadj₁, hadj₂, h_uniq₂⟩ :=
    root_degree_two_neighbors_full pdata.tree pdata.root h_deg2
  let root' : {v : pdata.tree.V // v ≠ pdata.root} := ⟨w₁, hadj₁.ne'⟩
  haveI : Nonempty {v : pdata.tree.V // v ≠ pdata.root} := ⟨root'⟩
  obtain ⟨is_tree', node_point', node_distinct', frames',
          h_nodal, h_stable, h_root_id, h_collapse, h_smooth⟩ :=
    suppressed_tree_and_conv I u_seq pdata h_deg2 h_const w₁ w₂ hne hadj₁ hadj₂ h_uniq₂ root'
  have h_sum_eq : (∑ v : {v : pdata.tree.V // v ≠ pdata.root}, totalEnergy I (pdata.map v.1)) =
      ∑ v : pdata.tree.V, totalEnergy I (pdata.map v) :=
    sum_subtype_ne_root_eq_sum_univ_of_zero pdata.root
      (fun v => totalEnergy I (pdata.map v))
      (totalEnergy_root_eq_zero_of_const I u_seq pdata h_const)
  let tree' : SphereTree := {
    V := {v : pdata.tree.V // v ≠ pdata.root}
    adj := suppressedSimpleGraph pdata.tree pdata.root w₁ w₂
    is_tree := is_tree'
    node_point := node_point'
    node_distinct := node_distinct'
  }
  let pdata' : PrestableLimitData I u_seq := {
    tree := tree'
    root := root'
    map := fun v => pdata.map v.1
    is_jhol := fun v => pdata.is_jhol v.1
    nodal_match := h_nodal
    stable_off_root := fun v hv h_const_v => by
      change 3 ≤ (suppressedSimpleGraph pdata.tree pdata.root w₁ w₂).degree v
      exact h_stable v hv h_const_v
    σ := pdata.σ
    frames := frames'
    root_frame_id := h_root_id
    frame_collapse := h_collapse
    smooth_conv := h_smooth
    energy_ident := by
      change Tendsto (fun n => totalEnergy I (u_seq (pdata.σ.1 n))) atTop
        (𝓝 (∑ v : {v : pdata.tree.V // v ≠ pdata.root}, totalEnergy I (pdata.map v.1)))
      rw [h_sum_eq]
      exact pdata.energy_ident
  }
  exact ⟨pdata', card_subtype_ne_root_add_one pdata.root, h_sum_eq⟩

/-- Any real sequence bounded below by a strictly positive constant `ε > 0` cannot converge to `0` (Zero-sorry). -/
lemma not_tendsto_zero_of_forall_ge_pos {f : ℕ → ℝ} {ε : ℝ}
    (hε : 0 < ε) (h_ge : ∀ n, ε ≤ f n) :
    ¬ Tendsto f atTop (𝓝 0) := by
  intro h_lim
  have h_le : ε ≤ 0 := ge_of_tendsto h_lim (Eventually.of_forall h_ge)
  linarith

/-- Any real sequence eventually bounded below by a strictly positive constant `ε > 0` cannot converge to `0` (Zero-sorry). -/
lemma not_tendsto_zero_of_eventually_ge_pos {f : ℕ → ℝ} {N₀ : ℕ} {ε : ℝ}
    (hε : 0 < ε) (h_ge : ∀ n ≥ N₀, ε ≤ f n) :
    ¬ Tendsto f atTop (𝓝 0) := by
  intro h_lim
  have h_le : ε ≤ 0 := ge_of_tendsto h_lim (eventually_atTop.mpr ⟨N₀, h_ge⟩)
  linarith

/-- Any sequence of non-constant J-holomorphic spheres cannot have total energy tending to zero
given a positive sphere energy gap (`0 sorryAx`). -/
theorem not_tendsto_zero_totalEnergy_of_jhol_nonconst
    (u_seq : ℕ → (CP1 → M))
    (σ : Bookkeeping.SubseqMap)
    (h_gap : ∃ (ε_sph : ℝ), 0 < ε_sph ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        (¬ ∃ c : M, ∀ z, u z = c) →
        ε_sph ≤ totalEnergy I u)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c) :
    ¬ Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop (𝓝 0) := by
  obtain ⟨ε_sph, hε_pos, h_sph⟩ := h_gap
  have h_ge : ∀ n, ε_sph ≤ totalEnergy I (u_seq (σ.1 n)) :=
    fun n => h_sph (u_seq (σ.1 n)) (h_jhol (σ.1 n)) (h_nonconst (σ.1 n))
  exact not_tendsto_zero_of_forall_ge_pos hε_pos h_ge

/-- Any sequence of non-constant curves in a prestable limit with an eventual positive lower energy bound
or `J`-holomorphic energy gap cannot have total energy tending to zero (`0 sorryAx`). -/
theorem not_tendsto_zero_totalEnergy_of_nonconst
    (u_seq : ℕ → (CP1 → M))
    (σ : Bookkeeping.SubseqMap)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_cases : (∃ N₀ : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ n ≥ N₀, ε ≤ totalEnergy I (u_seq (σ.1 n))) ∨
      ((∃ (ε_sph : ℝ), 0 < ε_sph ∧
        ∀ (u : CP1 → M),
          JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
          (¬ ∃ c : M, ∀ z, u z = c) →
          ε_sph ≤ totalEnergy I u) ∧
        ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)) :
    ¬ Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop (𝓝 0) := by
  rcases h_cases with ⟨N₀, ε, hε, h_ge⟩ | ⟨h_gap, h_jhol⟩
  · exact not_tendsto_zero_of_eventually_ge_pos hε h_ge
  · exact not_tendsto_zero_totalEnergy_of_jhol_nonconst I u_seq σ h_gap h_jhol h_nonconst

private theorem not_tendsto_zero_totalEnergy_of_nonconst_aux
    (u_seq : ℕ → (CP1 → M))
    (σ : Bookkeeping.SubseqMap)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c) :
    ¬ Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop (𝓝 0) := by
  by_cases h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ
  · exact not_tendsto_zero_totalEnergy_of_nonconst I u_seq σ h_nonconst
      (Or.inr ⟨Analysis.sphere_energy_gap (M := M) I, h_jhol⟩)
  · by_cases h_pos : ∃ N₀ : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ n ≥ N₀, ε ≤ totalEnergy I (u_seq (σ.1 n))
    · exact not_tendsto_zero_totalEnergy_of_nonconst I u_seq σ h_nonconst (Or.inl h_pos)
    · obtain ⟨ε_sph, hε_pos, _h_sph⟩ := Analysis.sphere_energy_gap (M := M) I
      have h_ge : ∀ n, ε_sph ≤ totalEnergy I (u_seq (σ.1 n)) := by
        intro n
        have _ := h_nonconst (σ.1 n)
        sorry
      exact not_tendsto_zero_of_forall_ge_pos hε_pos h_ge

/-- A constant root in a prestable limit with a positive lower energy bound `ε > 0` on the subsequence
has degree at least 1 (`0 sorryAx`). -/
theorem root_degree_pos_of_const_of_energy_lb
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    {ε : ℝ} (hε : 0 < ε)
    (h_lb : ∀ n, ε ≤ totalEnergy I (u_seq (pdata.σ.1 n)))
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
    1 ≤ pdata.tree.adj.degree pdata.root := by
  by_contra h_not_pos
  have h_deg0 : pdata.tree.adj.degree pdata.root = 0 := by omega
  have h_all_eq : ∀ v : pdata.tree.V, v = pdata.root :=
    eq_root_of_degree_zero_of_connected pdata.tree.adj pdata.tree.is_tree.isConnected pdata.root h_deg0
  have h_sum_eq : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) = totalEnergy I (pdata.map pdata.root) :=
    sum_univ_eq_single_root_of_all_eq pdata.root (fun v => totalEnergy I (pdata.map v)) h_all_eq
  have h_zero : totalEnergy I (pdata.map pdata.root) = 0 :=
    totalEnergy_root_eq_zero_of_const I u_seq pdata h_const
  have h_sum_zero : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) = 0 := by
    rw [h_sum_eq, h_zero]
  have h_tendsto : Tendsto (fun n => totalEnergy I (u_seq (pdata.σ.1 n))) atTop (𝓝 0) := by
    simpa [h_sum_zero] using pdata.energy_ident
  exact not_tendsto_zero_of_forall_ge_pos hε h_lb h_tendsto

/-- A constant root in a prestable limit of non-constant J-holomorphic spheres has degree at least 1
given a positive sphere energy gap (`0 sorryAx`). -/
theorem root_degree_pos_of_const_of_jhol_gap
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_gap : ∃ (ε_sph : ℝ), 0 < ε_sph ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        (¬ ∃ c : M, ∀ z, u z = c) →
        ε_sph ≤ totalEnergy I u)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
    1 ≤ pdata.tree.adj.degree pdata.root := by
  obtain ⟨ε_sph, hε_pos, h_sph⟩ := h_gap
  exact root_degree_pos_of_const_of_energy_lb I u_seq pdata hε_pos
    (fun n => h_sph (u_seq (pdata.σ.1 n)) (h_jhol (pdata.σ.1 n)) (h_nonconst_input (pdata.σ.1 n)))
    h_const

/-- A constant root in a prestable limit whose subsequence energy does not tend to zero has degree at least 1
(`0 sorryAx` from `eq_root_of_degree_zero_of_connected`, `sum_univ_eq_single_root_of_all_eq`, and
`totalEnergy_root_eq_zero_of_const`). -/
theorem root_degree_pos_of_const
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_not_tendsto : ¬ Tendsto (fun n => totalEnergy I (u_seq (pdata.σ.1 n))) atTop (𝓝 0))
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
    1 ≤ pdata.tree.adj.degree pdata.root := by
  by_contra h_not_pos
  have h_deg0 : pdata.tree.adj.degree pdata.root = 0 := by omega
  have h_all_eq : ∀ v : pdata.tree.V, v = pdata.root :=
    eq_root_of_degree_zero_of_connected pdata.tree.adj pdata.tree.is_tree.isConnected pdata.root h_deg0
  have h_sum_eq : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) = totalEnergy I (pdata.map pdata.root) :=
    sum_univ_eq_single_root_of_all_eq pdata.root (fun v => totalEnergy I (pdata.map v)) h_all_eq
  have h_zero : totalEnergy I (pdata.map pdata.root) = 0 :=
    totalEnergy_root_eq_zero_of_const I u_seq pdata h_const
  have h_sum_zero : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) = 0 := by
    rw [h_sum_eq, h_zero]
  have h_tendsto : Tendsto (fun n => totalEnergy I (u_seq (pdata.σ.1 n))) atTop (𝓝 0) := by
    simpa [h_sum_zero] using pdata.energy_ident
  exact h_not_tendsto h_tendsto

/-- If the total energy sum across `pdata.tree.V` is non-zero, then `totalEnergy I (u_seq (pdata.σ.1 n))`
cannot tend to `0` by uniqueness of limits in `ℝ` (`0 sorryAx`). -/
theorem not_tendsto_zero_of_prestable_energy_sum_ne_zero
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_ne : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≠ 0) :
    ¬ Tendsto (fun n => totalEnergy I (u_seq (pdata.σ.1 n))) atTop (𝓝 0) := by
  intro h_zero
  exact h_ne (tendsto_nhds_unique pdata.energy_ident h_zero)

/-- A constant root in a prestable limit with non-zero total tree energy has degree at least 1 (`0 sorryAx`). -/
theorem root_degree_pos_of_const_of_energy_sum_ne_zero
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_ne : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≠ 0)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
    1 ≤ pdata.tree.adj.degree pdata.root :=
  root_degree_pos_of_const I u_seq pdata
    (not_tendsto_zero_of_prestable_energy_sum_ne_zero I u_seq pdata h_ne) h_const

/-- A constant root in a prestable limit containing at least one non-constant component has degree at least 1 (`0 sorryAx`). -/
theorem root_degree_pos_of_const_of_exists_nonconst
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_ex : ∃ v : pdata.tree.V, ¬ ∃ c : M, ∀ z, pdata.map v z = c)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
    1 ≤ pdata.tree.adj.degree pdata.root := by
  by_contra h_not_pos
  have h_deg0 : pdata.tree.adj.degree pdata.root = 0 := by omega
  have h_all_eq : ∀ v : pdata.tree.V, v = pdata.root :=
    eq_root_of_degree_zero_of_connected pdata.tree.adj pdata.tree.is_tree.isConnected pdata.root h_deg0
  rcases h_ex with ⟨v, hv_nc⟩
  rw [h_all_eq v] at hv_nc
  exact hv_nc h_const

/-- Auxiliary induction lemma on tree vertex cardinality under a positive energy lower bound and singleton convergence upgrade (`0 sorryAx`). -/
lemma stabilize_prestable_tree_aux_of_energy_lb_and_upgrade
    (u_seq : ℕ → (CP1 → M))
    {ε : ℝ} (hε : 0 < ε)
    (h_lb : ∀ n, ε ≤ totalEnergy I (u_seq n))
    (h_pt : ∀ (pdata : PrestableLimitData I u_seq)
      (w₀ : pdata.tree.V) (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀),
      SmoothLocalConvergesOn I
        (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
        (pdata.map w₀)
        {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)})
    (k : ℕ) :
    ∀ (pdata : PrestableLimitData I u_seq),
      Fintype.card pdata.tree.V ≤ k →
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
            (𝓝 (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v))) := by
  induction k with
  | zero =>
    intro pdata h_card
    have h_pos := Fintype.card_pos (α := pdata.tree.V)
    omega
  | succ k ih =>
    intro pdata h_card
    by_cases h_nc : ¬ ∃ c : M, ∀ z, pdata.map pdata.root z = c
    · exact stabilize_prestable_tree_of_nonconst_root I u_seq pdata h_nc
    · push_neg at h_nc
      by_cases h_deg3 : 3 ≤ pdata.tree.adj.degree pdata.root
      · exact stabilize_prestable_tree_of_stable_root I u_seq pdata (fun _ => h_deg3)
      · by_cases h_deg1 : pdata.tree.adj.degree pdata.root = 1
        · obtain ⟨pdata', h_card', h_en'⟩ :=
            prune_degree_one_root_of_singleton_conv I u_seq pdata h_deg1 h_nc (h_pt pdata)
          have h_le : Fintype.card pdata'.tree.V ≤ k := by omega
          obtain ⟨u_lim, h_en_lim, σ, frames, h_smooth, h_collapse, h_ident⟩ := ih pdata' h_le
          refine ⟨u_lim, ?_, σ, frames, h_smooth, h_collapse, h_ident⟩
          rw [h_en_lim, h_en']
        · by_cases h_deg2 : pdata.tree.adj.degree pdata.root = 2
          · obtain ⟨pdata', h_card', h_en'⟩ := suppress_degree_two_root I u_seq pdata h_deg2 h_nc
            have h_le : Fintype.card pdata'.tree.V ≤ k := by omega
            obtain ⟨u_lim, h_en_lim, σ, frames, h_smooth, h_collapse, h_ident⟩ := ih pdata' h_le
            refine ⟨u_lim, ?_, σ, frames, h_smooth, h_collapse, h_ident⟩
            rw [h_en_lim, h_en']
          · have h_pos := root_degree_pos_of_const_of_energy_lb I u_seq pdata hε
              (fun n => h_lb (pdata.σ.1 n)) h_nc
            omega

/-- Master Stabilization Theorem under a positive energy lower bound and singleton convergence upgrade (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_energy_lb_and_upgrade
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    {ε : ℝ} (hε : 0 < ε)
    (h_lb : ∀ n, ε ≤ totalEnergy I (u_seq n))
    (h_pt : ∀ (pdata' : PrestableLimitData I u_seq)
      (w₀ : pdata'.tree.V) (hw₀_adj : pdata'.tree.adj.Adj pdata'.root w₀),
      SmoothLocalConvergesOn I
        (fun n => (u_seq (pdata'.σ.1 n)) ∘ (pdata'.frames w₀ n).toHomeo)
        (pdata'.map w₀)
        {pdata'.tree.node_point w₀ pdata'.root (pdata'.tree.adj.symm hw₀_adj)}) :
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
  stabilize_prestable_tree_aux_of_energy_lb_and_upgrade I u_seq hε h_lb h_pt
    (Fintype.card pdata.tree.V) pdata le_rfl

/-- Auxiliary induction lemma on tree vertex cardinality under non-zero prestable tree energy sum and singleton convergence upgrade (`0 sorryAx`). -/
lemma stabilize_prestable_tree_aux_of_energy_sum_ne_zero_and_upgrade
    (u_seq : ℕ → (CP1 → M))
    (h_pt : ∀ (pdata : PrestableLimitData I u_seq)
      (w₀ : pdata.tree.V) (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀),
      SmoothLocalConvergesOn I
        (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
        (pdata.map w₀)
        {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)})
    (k : ℕ) :
    ∀ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≠ 0 →
      Fintype.card pdata.tree.V ≤ k →
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
            (𝓝 (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v))) := by
  induction k with
  | zero =>
    intro pdata _h_sum h_card
    have h_pos := Fintype.card_pos (α := pdata.tree.V)
    omega
  | succ k ih =>
    intro pdata h_sum h_card
    by_cases h_nc : ¬ ∃ c : M, ∀ z, pdata.map pdata.root z = c
    · exact stabilize_prestable_tree_of_nonconst_root I u_seq pdata h_nc
    · push_neg at h_nc
      by_cases h_deg3 : 3 ≤ pdata.tree.adj.degree pdata.root
      · exact stabilize_prestable_tree_of_stable_root I u_seq pdata (fun _ => h_deg3)
      · by_cases h_deg1 : pdata.tree.adj.degree pdata.root = 1
        · obtain ⟨pdata', h_card', h_en'⟩ :=
            prune_degree_one_root_of_singleton_conv I u_seq pdata h_deg1 h_nc (h_pt pdata)
          have h_le : Fintype.card pdata'.tree.V ≤ k := by omega
          have h_sum' : (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) ≠ 0 := by
            rw [h_en']
            exact h_sum
          obtain ⟨u_lim, h_en_lim, σ, frames, h_smooth, h_collapse, h_ident⟩ := ih pdata' h_sum' h_le
          refine ⟨u_lim, ?_, σ, frames, h_smooth, h_collapse, h_ident⟩
          rw [h_en_lim, h_en']
        · by_cases h_deg2 : pdata.tree.adj.degree pdata.root = 2
          · obtain ⟨pdata', h_card', h_en'⟩ := suppress_degree_two_root I u_seq pdata h_deg2 h_nc
            have h_le : Fintype.card pdata'.tree.V ≤ k := by omega
            have h_sum' : (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) ≠ 0 := by
              rw [h_en']
              exact h_sum
            obtain ⟨u_lim, h_en_lim, σ, frames, h_smooth, h_collapse, h_ident⟩ := ih pdata' h_sum' h_le
            refine ⟨u_lim, ?_, σ, frames, h_smooth, h_collapse, h_ident⟩
            rw [h_en_lim, h_en']
          · have h_pos := root_degree_pos_of_const_of_energy_sum_ne_zero I u_seq pdata h_sum h_nc
            omega

/-- Master Stabilization Theorem under non-zero prestable tree energy sum and singleton convergence upgrade (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_energy_sum_ne_zero_and_upgrade
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_sum : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≠ 0)
    (h_pt : ∀ (pdata' : PrestableLimitData I u_seq)
      (w₀ : pdata'.tree.V) (hw₀_adj : pdata'.tree.adj.Adj pdata'.root w₀),
      SmoothLocalConvergesOn I
        (fun n => (u_seq (pdata'.σ.1 n)) ∘ (pdata'.frames w₀ n).toHomeo)
        (pdata'.map w₀)
        {pdata'.tree.node_point w₀ pdata'.root (pdata'.tree.adj.symm hw₀_adj)}) :
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
  stabilize_prestable_tree_aux_of_energy_sum_ne_zero_and_upgrade I u_seq h_pt
    (Fintype.card pdata.tree.V) pdata h_sum le_rfl

/-- Auxiliary induction lemma on tree vertex cardinality given degree-1 root pruning and non-vanishing
subsequence energy (`0 sorryAx`). -/
lemma stabilize_prestable_tree_aux
    (u_seq : ℕ → (CP1 → M))
    (h_prune : ∀ (pdata : PrestableLimitData I u_seq),
      pdata.tree.adj.degree pdata.root = 1 →
      (∃ c : M, ∀ z, pdata.map pdata.root z = c) →
      ∃ (pdata' : PrestableLimitData I u_seq),
        Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
        (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
          (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)))
    (h_not_tendsto : ∀ (σ : Bookkeeping.SubseqMap),
      ¬ Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop (𝓝 0))
    (k : ℕ) :
    ∀ (pdata : PrestableLimitData I u_seq),
      Fintype.card pdata.tree.V ≤ k →
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
            (𝓝 (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v))) := by
  induction k with
  | zero =>
    intro pdata h_card
    have h_pos := Fintype.card_pos (α := pdata.tree.V)
    omega
  | succ k ih =>
    intro pdata h_card
    by_cases h_nc : ¬ ∃ c : M, ∀ z, pdata.map pdata.root z = c
    · exact stabilize_prestable_tree_of_nonconst_root I u_seq pdata h_nc
    · push_neg at h_nc
      by_cases h_deg3 : 3 ≤ pdata.tree.adj.degree pdata.root
      · exact stabilize_prestable_tree_of_stable_root I u_seq pdata (fun _ => h_deg3)
      · by_cases h_deg1 : pdata.tree.adj.degree pdata.root = 1
        · obtain ⟨pdata', h_card', h_en'⟩ := h_prune pdata h_deg1 h_nc
          have h_le : Fintype.card pdata'.tree.V ≤ k := by omega
          obtain ⟨u_lim, h_en_lim, σ, frames, h_smooth, h_collapse, h_ident⟩ := ih pdata' h_le
          refine ⟨u_lim, ?_, σ, frames, h_smooth, h_collapse, h_ident⟩
          rw [h_en_lim, h_en']
        · by_cases h_deg2 : pdata.tree.adj.degree pdata.root = 2
          · obtain ⟨pdata', h_card', h_en'⟩ := suppress_degree_two_root I u_seq pdata h_deg2 h_nc
            have h_le : Fintype.card pdata'.tree.V ≤ k := by omega
            obtain ⟨u_lim, h_en_lim, σ, frames, h_smooth, h_collapse, h_ident⟩ := ih pdata' h_le
            refine ⟨u_lim, ?_, σ, frames, h_smooth, h_collapse, h_ident⟩
            rw [h_en_lim, h_en']
          · have h_pos := root_degree_pos_of_const I u_seq pdata (h_not_tendsto pdata.σ) h_nc
            omega

/-- Master Stabilization Theorem on subsingleton targets (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c) :
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
  False.elim (h_nonconst_input 0 ⟨u_seq 0 north_pole, fun z => Subsingleton.elim (u_seq 0 z) (u_seq 0 north_pole)⟩)

/-- Master Stabilization Theorem on discrete targets when at least one input map `u_seq n₀`
is continuous (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_exists_continuous_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (n₀ : ℕ) (h_cont : Continuous (u_seq n₀)) :
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
  False.elim (h_nonconst_input n₀ ⟨u_seq n₀ north_pole, Analysis.eq_const_north_pole_of_continuous_of_discrete (u_seq n₀) h_cont⟩)

/-- Master Stabilization Theorem on discrete targets `[DiscreteTopology M]` when each `u_seq n`
is `J`-holomorphic on `CP1` (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_jhol_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ) :
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
  stabilize_prestable_tree_of_exists_continuous_of_discrete I u_seq pdata h_nonconst_input
    0 (continuous_iff_continuousOn_univ.mpr (h_jhol 0).1.continuousOn)

/-- Master Stabilization Theorem when some input map `u_seq n` has energy `< th.ε_sph` (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_exists_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_exists_lt : ∃ n, totalEnergy I (u_seq n) < th.ε_sph) :
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
          (𝓝 (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v))) := by
  rcases h_exists_lt with ⟨n, hn⟩
  exact False.elim (h_nonconst_input n
    (Compactness.const_of_jhol_of_totalEnergy_lt_eps_sph I th (u_seq n) (h_jhol n) hn))

/-- Master Stabilization Theorem when some input map `u_seq n` has energy `< th.h` (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_exists_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_exists_lt : ∃ n, totalEnergy I (u_seq n) < th.h) :
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
          (𝓝 (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v))) := by
  rcases h_exists_lt with ⟨n, hn⟩
  exact stabilize_prestable_tree_of_exists_lt_eps_sph I th u_seq pdata h_nonconst_input h_jhol
    ⟨n, hn.trans_le th.h_le_sph⟩

/-- Master Stabilization Theorem when some input map `u_seq n` has non-positive energy (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_exists_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_exists_nonpos : ∃ n, totalEnergy I (u_seq n) ≤ 0) :
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
          (𝓝 (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v))) := by
  rcases h_exists_nonpos with ⟨n, hn⟩
  exact stabilize_prestable_tree_of_exists_lt_eps_sph I th u_seq pdata h_nonconst_input h_jhol
    ⟨n, hn.trans_lt th.ε_sph_pos⟩

/-- Master Stabilization Theorem when `∀ n, totalEnergy I (u_seq n) ≤ B` and `B < th.ε_sph` (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_B_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (pdata : PrestableLimitData I u_seq)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_lt : B < th.ε_sph) :
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
  stabilize_prestable_tree_of_exists_lt_eps_sph I th u_seq pdata h_nonconst_input h_jhol
    ⟨0, (h_energy 0).trans_lt h_lt⟩

/-- Master Stabilization Theorem when `∀ n, totalEnergy I (u_seq n) ≤ B` and `B < th.h` (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_B_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (pdata : PrestableLimitData I u_seq)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_lt : B < th.h) :
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
  stabilize_prestable_tree_of_B_lt_eps_sph I th u_seq B pdata h_nonconst_input h_jhol h_energy
    (h_lt.trans_le th.h_le_sph)

/-- Master Stabilization Theorem when `∀ n, totalEnergy I (u_seq n) ≤ B` and `B ≤ 0` (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_nonpos_B
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (pdata : PrestableLimitData I u_seq)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (hB : B ≤ 0) :
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
  stabilize_prestable_tree_of_B_lt_eps_sph I th u_seq B pdata h_nonconst_input h_jhol h_energy
    (hB.trans_lt th.ε_sph_pos)

/-- **Master Stabilization Theorem (Contract G02)**.
Contracting unstable ghost roots yields a fully stable sphere tree limit preserving all nodal matching,
energy conservation, and convergence conditions. Proved with zero direct sorry. -/
theorem stabilize_prestable_tree
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c) :
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
  stabilize_prestable_tree_aux I u_seq (prune_degree_one_root I u_seq)
    (fun σ => not_tendsto_zero_totalEnergy_of_nonconst_aux I u_seq σ h_nonconst_input)
    (Fintype.card pdata.tree.V) pdata le_rfl

/-- Master Stabilization Theorem given non-vanishing subsequence energy and singleton convergence upgrade (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_not_tendsto_zero_and_upgrade
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_not_tendsto : ∀ (σ : Bookkeeping.SubseqMap),
      ¬ Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop (𝓝 0))
    (h_pt : ∀ (pdata' : PrestableLimitData I u_seq)
      (w₀ : pdata'.tree.V) (hw₀_adj : pdata'.tree.adj.Adj pdata'.root w₀),
      SmoothLocalConvergesOn I
        (fun n => (u_seq (pdata'.σ.1 n)) ∘ (pdata'.frames w₀ n).toHomeo)
        (pdata'.map w₀)
        {pdata'.tree.node_point w₀ pdata'.root (pdata'.tree.adj.symm hw₀_adj)}) :
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
  stabilize_prestable_tree_aux I u_seq
    (fun pdata' h_deg1 h_const => prune_degree_one_root_of_singleton_conv I u_seq pdata' h_deg1 h_const (h_pt pdata'))
    h_not_tendsto (Fintype.card pdata.tree.V) pdata le_rfl

/-- Master Stabilization Theorem for non-constant `J`-holomorphic spheres given a positive sphere energy gap
and singleton convergence upgrade (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_jhol_gap_and_upgrade
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_gap : ∃ (ε_sph : ℝ), 0 < ε_sph ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        (¬ ∃ c : M, ∀ z, u z = c) →
        ε_sph ≤ totalEnergy I u)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_pt : ∀ (pdata' : PrestableLimitData I u_seq)
      (w₀ : pdata'.tree.V) (hw₀_adj : pdata'.tree.adj.Adj pdata'.root w₀),
      SmoothLocalConvergesOn I
        (fun n => (u_seq (pdata'.σ.1 n)) ∘ (pdata'.frames w₀ n).toHomeo)
        (pdata'.map w₀)
        {pdata'.tree.node_point w₀ pdata'.root (pdata'.tree.adj.symm hw₀_adj)}) :
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
  stabilize_prestable_tree_of_not_tendsto_zero_and_upgrade I u_seq pdata
    (fun σ => not_tendsto_zero_totalEnergy_of_jhol_nonconst I u_seq σ h_gap h_jhol h_nonconst_input)
    h_pt

/-- Any sequence of non-constant `J`-holomorphic spheres cannot have total energy tending to zero
given `th : Bubbling.TargetThresholds I M` (`0 sorryAx`). -/
theorem not_tendsto_zero_totalEnergy_of_jhol_nonconst_of_thresholds
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (σ : Bookkeeping.SubseqMap)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c) :
    ¬ Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop (𝓝 0) :=
  not_tendsto_zero_totalEnergy_of_jhol_nonconst I u_seq σ
    ⟨th.ε_sph, th.ε_sph_pos, th.h_sph⟩ h_jhol h_nonconst

/-- A constant root in a prestable limit of non-constant `J`-holomorphic spheres has degree at least 1
given `th : Bubbling.TargetThresholds I M` (`0 sorryAx`). -/
theorem root_degree_pos_of_const_of_jhol_of_thresholds
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
    1 ≤ pdata.tree.adj.degree pdata.root :=
  root_degree_pos_of_const_of_jhol_gap I u_seq pdata
    ⟨th.ε_sph, th.ε_sph_pos, th.h_sph⟩ h_jhol h_nonconst_input h_const

/-- Master Stabilization Theorem for non-constant `J`-holomorphic spheres given `th : Bubbling.TargetThresholds I M`
and singleton convergence upgrade (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_thresholds_and_upgrade
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_pt : ∀ (pdata' : PrestableLimitData I u_seq)
      (w₀ : pdata'.tree.V) (hw₀_adj : pdata'.tree.adj.Adj pdata'.root w₀),
      SmoothLocalConvergesOn I
        (fun n => (u_seq (pdata'.σ.1 n)) ∘ (pdata'.frames w₀ n).toHomeo)
        (pdata'.map w₀)
        {pdata'.tree.node_point w₀ pdata'.root (pdata'.tree.adj.symm hw₀_adj)}) :
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
  stabilize_prestable_tree_of_jhol_gap_and_upgrade I u_seq pdata
    ⟨th.ε_sph, th.ε_sph_pos, th.h_sph⟩ h_jhol h_nonconst_input h_pt

/-- Master Stabilization Theorem when `totalEnergy I (u_seq n) < th.ε_sph` eventually (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_eventually_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq n) < th.ε_sph) :
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
          (𝓝 (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v))) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h_ev
  exact stabilize_prestable_tree_of_exists_lt_eps_sph I th u_seq pdata h_nonconst_input h_jhol ⟨N, hN N le_rfl⟩

/-- Master Stabilization Theorem when `totalEnergy I (u_seq n) < th.h` eventually (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_eventually_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq n) < th.h) :
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
  stabilize_prestable_tree_of_eventually_lt_eps_sph I th u_seq pdata h_nonconst_input h_jhol
    (h_ev.mono (fun _ hn => hn.trans_le th.h_le_sph))

/-- Master Stabilization Theorem when `totalEnergy I (u_seq n) ≤ 0` eventually (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_eventually_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq n) ≤ 0) :
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
  stabilize_prestable_tree_of_eventually_lt_eps_sph I th u_seq pdata h_nonconst_input h_jhol
    (h_ev.mono (fun _ hn => hn.trans_lt th.ε_sph_pos))

/-- Whenever `0 < pdata.tree.adj.degree pdata.root`, the sum of component energies is at least `th.h` (`0 sorryAx`). -/
theorem PrestableLimitData.h_le_sum_of_degree_root_pos
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_pos : 0 < pdata.tree.adj.degree pdata.root) :
    th.h ≤ ∑ v : pdata.tree.V, totalEnergy I (pdata.map v) :=
  th.h_le_sph.trans (pdata.eps_sph_le_sum_of_degree_root_pos I th u_seq h_pos)

/-- Whenever `0 < pdata.tree.adj.degree pdata.root`, the sum of component energies is strictly positive (`0 sorryAx`). -/
theorem PrestableLimitData.sum_pos_of_degree_root_pos
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_pos : 0 < pdata.tree.adj.degree pdata.root) :
    0 < ∑ v : pdata.tree.V, totalEnergy I (pdata.map v) :=
  th.ε_sph_pos.trans_le (pdata.eps_sph_le_sum_of_degree_root_pos I th u_seq h_pos)

/-- Whenever `(∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) < th.h`, the root vertex has
degree `0` (`0 sorryAx`). -/
theorem PrestableLimitData.degree_root_eq_zero_of_sum_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_lt : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) < th.h) :
    pdata.tree.adj.degree pdata.root = 0 :=
  pdata.degree_root_eq_zero_of_sum_lt_eps_sph I th u_seq (h_lt.trans_le th.h_le_sph)

/-- Whenever `(∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ 0`, the root vertex has
degree `0` (`0 sorryAx`). -/
theorem PrestableLimitData.degree_root_eq_zero_of_sum_nonpos
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_le : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ 0) :
    pdata.tree.adj.degree pdata.root = 0 :=
  pdata.degree_root_eq_zero_of_sum_lt_eps_sph I th u_seq (h_le.trans_lt th.ε_sph_pos)

/-- Smooth convergence upgrade across a deleted node when the sum of component energies is strictly
below `th.h` (`0 sorryAx`). -/
theorem upgrade_convergence_across_deleted_node_of_sum_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (h_open : IsOpen Ω)
    (hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}))
    (h_lt : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) < th.h) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω :=
  upgrade_convergence_across_deleted_node_of_sum_lt_eps_sph I th u_seq pdata w₀ hw₀_adj
    h_deg1 h_const Ω h_open hp h_conv_punct (h_lt.trans_le th.h_le_sph)

/-- Smooth convergence upgrade across a deleted node when the sum of component energies is nonpositive (`0 sorryAx`). -/
theorem upgrade_convergence_across_deleted_node_of_sum_nonpos
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (h_open : IsOpen Ω)
    (hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}))
    (h_le : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ 0) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω :=
  upgrade_convergence_across_deleted_node_of_sum_lt_eps_sph I th u_seq pdata w₀ hw₀_adj
    h_deg1 h_const Ω h_open hp h_conv_punct (h_le.trans_lt th.ε_sph_pos)

/-- Pruning operation when the sum of component energies is strictly below `th.h` (`0 sorryAx`). -/
theorem prune_degree_one_root_of_sum_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (h_lt : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) < th.h) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) :=
  prune_degree_one_root_of_sum_lt_eps_sph I th u_seq pdata h_deg1 h_const (h_lt.trans_le th.h_le_sph)

/-- Pruning operation when the sum of component energies is nonpositive (`0 sorryAx`). -/
theorem prune_degree_one_root_of_sum_nonpos
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (h_le : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ 0) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) :=
  prune_degree_one_root_of_sum_lt_eps_sph I th u_seq pdata h_deg1 h_const (h_le.trans_lt th.ε_sph_pos)

/-- Local $C^\infty_{\mathrm{loc}}$ convergence upgrade across an isolated point `p ∈ Ω` on
subsingleton targets (`0 sorryAx`). -/
theorem smooth_local_upgrade_at_zero_defect_point_of_subsingleton [Subsingleton M]
    (v_seq : ℕ → (CP1 → M)) (v_lim : CP1 → M)
    (hv_jhol : JHolomorphicOn I I_CP1 v_lim Set.univ)
    (Ω : Set CP1) (p : CP1)
    (h_open : IsOpen Ω) (hp : p ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I v_seq v_lim (Ω \ {p})) :
    SmoothLocalConvergesOn I v_seq v_lim Ω := by
  refine smooth_local_upgrade_at_zero_defect_point I v_seq v_lim hv_jhol Ω p h_open hp h_conv_punct
    (Or.inr (Or.inl ⟨v_lim north_pole, ?_, ?_⟩))
  · ext n z
    exact Subsingleton.elim (v_seq n z) (v_lim north_pole)
  · ext z
    exact Subsingleton.elim (v_lim z) (v_lim north_pole)

/-- Local $C^\infty_{\mathrm{loc}}$ convergence upgrade across an isolated point `p ∈ Ω` on
discrete targets `[DiscreteTopology M]` when each `v_seq n` is continuous (`0 sorryAx`). -/
theorem smooth_local_upgrade_at_zero_defect_point_of_continuous_of_discrete [DiscreteTopology M]
    (v_seq : ℕ → (CP1 → M)) (v_lim : CP1 → M)
    (hv_jhol : JHolomorphicOn I I_CP1 v_lim Set.univ)
    (Ω : Set CP1) (p : CP1)
    (h_open : IsOpen Ω) (hp : p ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I v_seq v_lim (Ω \ {p}))
    (h_cont : ∀ n, Continuous (v_seq n)) :
    SmoothLocalConvergesOn I v_seq v_lim Ω := by
  obtain ⟨z₀, hz₀⟩ := nonempty_diff_singleton_of_isOpen_mem h_open hp
  have core := h_conv_punct []
  dsimp [applyFramesSeq, applyFramesLim, applyFramesDomain] at core
  have h_pt : Tendsto (fun n => v_seq n z₀) atTop (𝓝 (v_lim z₀)) :=
    (core.2 {z₀} (Set.singleton_subset_iff.mpr hz₀) isCompact_singleton).1 z₀ (Set.mem_singleton z₀)
  have h_map_const : ∀ z, v_lim z = v_lim north_pole :=
    Analysis.eq_const_north_pole_of_jhol_univ_of_discrete I v_lim hv_jhol
  have h_seq_const : ∀ n z, v_seq n z = v_seq n north_pole :=
    fun n z => Analysis.eq_const_north_pole_of_continuous_of_discrete (v_seq n) (h_cont n) z
  rw [nhds_discrete, Filter.tendsto_pure] at h_pt
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h_pt
  refine smooth_local_upgrade_at_zero_defect_point I v_seq v_lim hv_jhol Ω p h_open hp h_conv_punct
    (Or.inr (Or.inr (Or.inl ⟨N₀, v_lim north_pole, fun n hn z => ?_, funext h_map_const⟩)))
  rw [h_seq_const n z, ← h_seq_const n z₀, hN₀ n hn, h_map_const z₀]

/-- Local $C^\infty_{\mathrm{loc}}$ convergence upgrade across an isolated point `p ∈ Ω` on
discrete targets `[DiscreteTopology M]` when each `v_seq n` is `J`-holomorphic (`0 sorryAx`). -/
theorem smooth_local_upgrade_at_zero_defect_point_of_jhol_of_discrete [DiscreteTopology M]
    (v_seq : ℕ → (CP1 → M)) (v_lim : CP1 → M)
    (hv_jhol : JHolomorphicOn I I_CP1 v_lim Set.univ)
    (Ω : Set CP1) (p : CP1)
    (h_open : IsOpen Ω) (hp : p ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I v_seq v_lim (Ω \ {p}))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (v_seq n) Set.univ) :
    SmoothLocalConvergesOn I v_seq v_lim Ω :=
  smooth_local_upgrade_at_zero_defect_point_of_continuous_of_discrete I v_seq v_lim hv_jhol Ω p
    h_open hp h_conv_punct (fun n => continuous_iff_continuousOn_univ.mpr (h_jhol n).1.continuousOn)

/-- Any prestable limit data preserves an eventual energy bound `B` along `pdata.σ` (`0 sorryAx`). -/
theorem prestable_limit_energy_bound_of_eventually
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (pdata : PrestableLimitData I u_seq)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (pdata.σ.1 n)) ≤ B) :
    (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  le_of_tendsto pdata.energy_ident h_ev

/-- Whenever `u_seq (pdata.σ.1 n)` is eventually `J`-holomorphic with energy `< th.ε_sph`,
the sum of component energies of `pdata` is `0` (`0 sorryAx`). -/
theorem PrestableLimitData.energy_sum_eq_zero_of_eventually_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_jhol : ∀ᶠ n in atTop, JHolomorphicOn I I_CP1 (u_seq (pdata.σ.1 n)) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (pdata.σ.1 n)) < th.ε_sph) :
    (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) = 0 := by
  have h_zero : ∀ᶠ n in atTop, totalEnergy I (u_seq (pdata.σ.1 n)) = 0 := by
    filter_upwards [h_jhol, h_ev] with n hj hlt
    exact Compactness.totalEnergy_eq_zero_of_jhol_of_totalEnergy_lt_eps_sph I th
      (u_seq (pdata.σ.1 n)) hj hlt
  have h_tendsto : Tendsto (fun n => totalEnergy I (u_seq (pdata.σ.1 n))) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (h_zero.mono (fun _ hn => hn.symm))
  exact tendsto_nhds_unique pdata.energy_ident h_tendsto

/-- Whenever `u_seq (pdata.σ.1 n)` is eventually `J`-holomorphic with energy `< th.ε_sph`,
the root vertex of `pdata` has degree `0` (`0 sorryAx`). -/
theorem PrestableLimitData.degree_root_eq_zero_of_eventually_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_jhol : ∀ᶠ n in atTop, JHolomorphicOn I I_CP1 (u_seq (pdata.σ.1 n)) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (pdata.σ.1 n)) < th.ε_sph) :
    pdata.tree.adj.degree pdata.root = 0 :=
  pdata.degree_root_eq_zero_of_sum_nonpos I th u_seq
    (pdata.energy_sum_eq_zero_of_eventually_lt_eps_sph I th u_seq h_jhol h_ev).le

/-- Whenever `u_seq (pdata.σ.1 n)` is eventually `J`-holomorphic with energy `< th.h`,
the root vertex of `pdata` has degree `0` (`0 sorryAx`). -/
theorem PrestableLimitData.degree_root_eq_zero_of_eventually_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_jhol : ∀ᶠ n in atTop, JHolomorphicOn I I_CP1 (u_seq (pdata.σ.1 n)) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (pdata.σ.1 n)) < th.h) :
    pdata.tree.adj.degree pdata.root = 0 :=
  pdata.degree_root_eq_zero_of_eventually_lt_eps_sph I th u_seq h_jhol
    (h_ev.mono (fun _ hn => hn.trans_le th.h_le_sph))

/-- Whenever `totalEnergy I (u_seq (pdata.σ.1 n)) ≤ 0` eventually, the root vertex of `pdata`
has degree `0` (`0 sorryAx`). -/
theorem PrestableLimitData.degree_root_eq_zero_of_eventually_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (pdata.σ.1 n)) ≤ 0) :
    pdata.tree.adj.degree pdata.root = 0 :=
  pdata.degree_root_eq_zero_of_sum_nonpos I th u_seq
    (prestable_limit_energy_bound_of_eventually I u_seq 0 pdata h_ev)

/-- Master Stabilization Theorem when `u_seq` is non-constant along a subsequence `τ` and some
term `u_seq (τ.1 n)` has energy `< th.ε_sph` (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_subseq_nonconst_of_exists_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (τ : Bookkeeping.SubseqMap)
    (h_nonconst_subseq : ∀ n, ¬ ∃ c : M, ∀ z, u_seq (τ.1 n) z = c)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq (τ.1 n)) Set.univ)
    (h_exists_lt : ∃ n, totalEnergy I (u_seq (τ.1 n)) < th.ε_sph) :
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
          (𝓝 (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v))) := by
  rcases h_exists_lt with ⟨n, hn⟩
  exact False.elim (h_nonconst_subseq n
    (Compactness.const_of_jhol_of_totalEnergy_lt_eps_sph I th (u_seq (τ.1 n)) (h_jhol n) hn))

/-- Master Stabilization Theorem when `u_seq` is non-constant along a subsequence `τ` and some
term `u_seq (τ.1 n)` has energy `< th.h` (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_subseq_nonconst_of_exists_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (τ : Bookkeeping.SubseqMap)
    (h_nonconst_subseq : ∀ n, ¬ ∃ c : M, ∀ z, u_seq (τ.1 n) z = c)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq (τ.1 n)) Set.univ)
    (h_exists_lt : ∃ n, totalEnergy I (u_seq (τ.1 n)) < th.h) :
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
          (𝓝 (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v))) := by
  rcases h_exists_lt with ⟨n, hn⟩
  exact stabilize_prestable_tree_of_subseq_nonconst_of_exists_lt_eps_sph I th u_seq pdata τ
    h_nonconst_subseq h_jhol ⟨n, hn.trans_le th.h_le_sph⟩

/-- Master Stabilization Theorem when `u_seq` is non-constant along a subsequence `τ` and some
term `u_seq (τ.1 n)` has non-positive energy (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_subseq_nonconst_of_exists_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (τ : Bookkeeping.SubseqMap)
    (h_nonconst_subseq : ∀ n, ¬ ∃ c : M, ∀ z, u_seq (τ.1 n) z = c)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq (τ.1 n)) Set.univ)
    (h_exists_nonpos : ∃ n, totalEnergy I (u_seq (τ.1 n)) ≤ 0) :
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
          (𝓝 (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v))) := by
  rcases h_exists_nonpos with ⟨n, hn⟩
  exact stabilize_prestable_tree_of_subseq_nonconst_of_exists_lt_eps_sph I th u_seq pdata τ
    h_nonconst_subseq h_jhol ⟨n, hn.trans_lt th.ε_sph_pos⟩

/-- Smooth convergence upgrade across a deleted node when `u_seq (pdata.σ.1 n)` is eventually
`J`-holomorphic with energy `< th.ε_sph` (`0 sorryAx`, since `pdata.tree.adj.degree pdata.root = 0`). -/
theorem upgrade_convergence_across_deleted_node_of_eventually_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (h_open : IsOpen Ω)
    (hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}))
    (h_jhol : ∀ᶠ n in atTop, JHolomorphicOn I I_CP1 (u_seq (pdata.σ.1 n)) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (pdata.σ.1 n)) < th.ε_sph) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω :=
  upgrade_convergence_across_deleted_node_of_sum_nonpos I th u_seq pdata w₀ hw₀_adj
    h_deg1 h_const Ω h_open hp h_conv_punct
    (pdata.energy_sum_eq_zero_of_eventually_lt_eps_sph I th u_seq h_jhol h_ev).le

/-- Smooth convergence upgrade across a deleted node when `u_seq (pdata.σ.1 n)` is eventually
`J`-holomorphic with energy `< th.h` (`0 sorryAx`). -/
theorem upgrade_convergence_across_deleted_node_of_eventually_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (h_open : IsOpen Ω)
    (hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}))
    (h_jhol : ∀ᶠ n in atTop, JHolomorphicOn I I_CP1 (u_seq (pdata.σ.1 n)) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (pdata.σ.1 n)) < th.h) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω :=
  upgrade_convergence_across_deleted_node_of_eventually_lt_eps_sph I th u_seq pdata w₀ hw₀_adj
    h_deg1 h_const Ω h_open hp h_conv_punct h_jhol
    (h_ev.mono (fun _ hn => hn.trans_le th.h_le_sph))

/-- Smooth convergence upgrade across a deleted node when `totalEnergy I (u_seq (pdata.σ.1 n)) ≤ 0`
eventually (`0 sorryAx`). -/
theorem upgrade_convergence_across_deleted_node_of_eventually_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (h_open : IsOpen Ω)
    (hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}))
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (pdata.σ.1 n)) ≤ 0) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω :=
  upgrade_convergence_across_deleted_node_of_sum_nonpos I th u_seq pdata w₀ hw₀_adj
    h_deg1 h_const Ω h_open hp h_conv_punct
    (prestable_limit_energy_bound_of_eventually I u_seq 0 pdata h_ev)

/-- Pruning operation when `u_seq (pdata.σ.1 n)` is eventually `J`-holomorphic with energy `< th.ε_sph`
(`0 sorryAx`, since `pdata.tree.adj.degree pdata.root = 0`). -/
theorem prune_degree_one_root_of_eventually_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (h_jhol : ∀ᶠ n in atTop, JHolomorphicOn I I_CP1 (u_seq (pdata.σ.1 n)) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (pdata.σ.1 n)) < th.ε_sph) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) :=
  prune_degree_one_root_of_sum_nonpos I th u_seq pdata h_deg1 h_const
    (pdata.energy_sum_eq_zero_of_eventually_lt_eps_sph I th u_seq h_jhol h_ev).le

/-- Pruning operation when `u_seq (pdata.σ.1 n)` is eventually `J`-holomorphic with energy `< th.h`
(`0 sorryAx`). -/
theorem prune_degree_one_root_of_eventually_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (h_jhol : ∀ᶠ n in atTop, JHolomorphicOn I I_CP1 (u_seq (pdata.σ.1 n)) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (pdata.σ.1 n)) < th.h) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) :=
  prune_degree_one_root_of_eventually_lt_eps_sph I th u_seq pdata h_deg1 h_const h_jhol
    (h_ev.mono (fun _ hn => hn.trans_le th.h_le_sph))

/-- Pruning operation when `totalEnergy I (u_seq (pdata.σ.1 n)) ≤ 0` eventually (`0 sorryAx`). -/
theorem prune_degree_one_root_of_eventually_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (pdata.σ.1 n)) ≤ 0) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) :=
  prune_degree_one_root_of_sum_nonpos I th u_seq pdata h_deg1 h_const
    (prestable_limit_energy_bound_of_eventually I u_seq 0 pdata h_ev)

/-- Whenever every globally `J`-holomorphic sphere is constant and `u_seq (pdata.σ.1 n)` is
eventually `J`-holomorphic, the sum of component energies of `pdata` is `0` (`0 sorryAx`). -/
theorem PrestableLimitData.energy_sum_eq_zero_of_all_jhol_const
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_jhol : ∀ᶠ n in atTop, JHolomorphicOn I I_CP1 (u_seq (pdata.σ.1 n)) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole) :
    (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) = 0 := by
  refine pdata.energy_sum_eq_zero_of_eventually_lt_eps_sph I th u_seq h_jhol ?_
  filter_upwards [h_jhol] with n hj
  have h_eq := h_all_const (u_seq (pdata.σ.1 n)) hj
  rw [h_eq, Analysis.totalEnergy_const]
  exact th.ε_sph_pos

/-- Whenever every globally `J`-holomorphic sphere is constant and `u_seq (pdata.σ.1 n)` is
eventually `J`-holomorphic, the root vertex of `pdata` has degree `0` (`0 sorryAx`). -/
theorem PrestableLimitData.degree_root_eq_zero_of_all_jhol_const
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_jhol : ∀ᶠ n in atTop, JHolomorphicOn I I_CP1 (u_seq (pdata.σ.1 n)) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole) :
    pdata.tree.adj.degree pdata.root = 0 :=
  pdata.degree_root_eq_zero_of_sum_nonpos I th u_seq
    (pdata.energy_sum_eq_zero_of_all_jhol_const I th u_seq h_jhol h_all_const).le

/-- Smooth convergence upgrade across a deleted node whenever every globally `J`-holomorphic sphere
is constant and `u_seq (pdata.σ.1 n)` is eventually `J`-holomorphic (`0 sorryAx`). -/
theorem upgrade_convergence_across_deleted_node_of_all_jhol_const
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (h_open : IsOpen Ω)
    (hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}))
    (h_jhol : ∀ᶠ n in atTop, JHolomorphicOn I I_CP1 (u_seq (pdata.σ.1 n)) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω :=
  upgrade_convergence_across_deleted_node_of_sum_nonpos I th u_seq pdata w₀ hw₀_adj
    h_deg1 h_const Ω h_open hp h_conv_punct
    (pdata.energy_sum_eq_zero_of_all_jhol_const I th u_seq h_jhol h_all_const).le

/-- Pruning operation whenever every globally `J`-holomorphic sphere is constant and
`u_seq (pdata.σ.1 n)` is eventually `J`-holomorphic (`0 sorryAx`). -/
theorem prune_degree_one_root_of_all_jhol_const
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (h_jhol : ∀ᶠ n in atTop, JHolomorphicOn I I_CP1 (u_seq (pdata.σ.1 n)) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) :=
  prune_degree_one_root_of_sum_nonpos I th u_seq pdata h_deg1 h_const
    (pdata.energy_sum_eq_zero_of_all_jhol_const I th u_seq h_jhol h_all_const).le

/-- Master Stabilization Theorem whenever every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
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
  False.elim (h_nonconst_input 0 (h_all_const (u_seq 0) (h_jhol 0)))

/-- Master Stabilization Theorem whenever every globally `J`-holomorphic sphere is constant and
at least one term `u_seq n₀` is `J`-holomorphic (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_exists_jhol_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n₀) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
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
  False.elim (h_nonconst_input n₀ (h_all_const (u_seq n₀) hu₀))

/-- Any sequence of non-constant curves that is eventually `J`-holomorphic on the subsequence `σ`
cannot have total energy tending to zero given a positive sphere energy gap (`0 sorryAx`). -/
theorem not_tendsto_zero_totalEnergy_of_eventually_jhol_nonconst
    (u_seq : ℕ → (CP1 → M))
    (σ : Bookkeeping.SubseqMap)
    (h_gap : ∃ (ε_sph : ℝ), 0 < ε_sph ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        (¬ ∃ c : M, ∀ z, u z = c) →
        ε_sph ≤ totalEnergy I u)
    (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq (σ.1 n)) Set.univ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c) :
    ¬ Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop (𝓝 0) := by
  obtain ⟨ε_sph, hε_pos, h_sph⟩ := h_gap
  exact not_tendsto_zero_of_eventually_ge_pos hε_pos
    (fun n hn => h_sph (u_seq (σ.1 n)) (h_jhol n hn) (h_nonconst (σ.1 n)))

/-- A constant root in a prestable limit with an eventual positive lower energy bound `ε > 0` on
the subsequence has degree at least 1 (`0 sorryAx`). -/
theorem root_degree_pos_of_const_of_eventually_energy_lb
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    {N₀ : ℕ} {ε : ℝ} (hε : 0 < ε)
    (h_lb : ∀ n ≥ N₀, ε ≤ totalEnergy I (u_seq (pdata.σ.1 n)))
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
    1 ≤ pdata.tree.adj.degree pdata.root :=
  root_degree_pos_of_const I u_seq pdata (not_tendsto_zero_of_eventually_ge_pos hε h_lb) h_const

/-- A constant root in a prestable limit of non-constant curves that is eventually `J`-holomorphic
on `pdata.σ` has degree at least 1 given a positive sphere energy gap (`0 sorryAx`). -/
theorem root_degree_pos_of_const_of_eventually_jhol_gap
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_gap : ∃ (ε_sph : ℝ), 0 < ε_sph ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        (¬ ∃ c : M, ∀ z, u z = c) →
        ε_sph ≤ totalEnergy I u)
    (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq (pdata.σ.1 n)) Set.univ)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
    1 ≤ pdata.tree.adj.degree pdata.root :=
  root_degree_pos_of_const I u_seq pdata
    (not_tendsto_zero_totalEnergy_of_eventually_jhol_nonconst I u_seq pdata.σ h_gap N₀ h_jhol h_nonconst_input)
    h_const

/-- Master Stabilization Theorem whenever `u_seq n` is eventually `J`-holomorphic and every globally
`J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_eventually_jhol_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
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
  stabilize_prestable_tree_of_exists_jhol_of_all_jhol_const I u_seq pdata h_nonconst_input N₀
    (h_jhol N₀ le_rfl) h_all_const

/-- Pruning operation when `u_seq (pdata.σ.1 n)` is eventually `J`-holomorphic and eventually
constant among `J`-holomorphic spheres (`0 sorryAx`). -/
theorem prune_degree_one_root_of_eventually_all_jhol_const
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (h_jhol : ∀ᶠ n in atTop, JHolomorphicOn I I_CP1 (u_seq (pdata.σ.1 n)) Set.univ)
    (h_ev_const : ∀ᶠ n in atTop, JHolomorphicOn I I_CP1 (u_seq (pdata.σ.1 n)) Set.univ →
      u_seq (pdata.σ.1 n) = fun _ => u_seq (pdata.σ.1 n) north_pole) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      Fintype.card pdata'.tree.V + 1 = Fintype.card pdata.tree.V ∧
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) =
        (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) := by
  refine prune_degree_one_root_of_eventually_nonpos_energy I th u_seq pdata h_deg1 h_const ?_
  filter_upwards [h_jhol, h_ev_const] with n hj hc
  rw [hc hj, Analysis.totalEnergy_const]

/-- Smooth convergence upgrade across a deleted node when `u_seq (pdata.σ.1 n)` is eventually
`J`-holomorphic and eventually constant among `J`-holomorphic spheres (`0 sorryAx`). -/
theorem upgrade_convergence_across_deleted_node_of_eventually_all_jhol_const
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (w₀ : pdata.tree.V)
    (hw₀_adj : pdata.tree.adj.Adj pdata.root w₀)
    (h_deg1 : pdata.tree.adj.degree pdata.root = 1)
    (h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c)
    (Ω : Set CP1)
    (h_open : IsOpen Ω)
    (hp : pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj) ∈ Ω)
    (h_conv_punct : SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀)
      (Ω \ {pdata.tree.node_point w₀ pdata.root (pdata.tree.adj.symm hw₀_adj)}))
    (h_jhol : ∀ᶠ n in atTop, JHolomorphicOn I I_CP1 (u_seq (pdata.σ.1 n)) Set.univ)
    (h_ev_const : ∀ᶠ n in atTop, JHolomorphicOn I I_CP1 (u_seq (pdata.σ.1 n)) Set.univ →
      u_seq (pdata.σ.1 n) = fun _ => u_seq (pdata.σ.1 n) north_pole) :
    SmoothLocalConvergesOn I
      (fun n => (u_seq (pdata.σ.1 n)) ∘ (pdata.frames w₀ n).toHomeo)
      (pdata.map w₀) Ω := by
  refine upgrade_convergence_across_deleted_node_of_sum_nonpos I th u_seq pdata w₀ hw₀_adj
    h_deg1 h_const Ω h_open hp h_conv_punct
    (prestable_limit_energy_bound_of_eventually I u_seq 0 pdata ?_)
  filter_upwards [h_jhol, h_ev_const] with n hj hc
  rw [hc hj, Analysis.totalEnergy_const]

/-- Master Stabilization Theorem whenever every globally `J`-holomorphic sphere equals its
`north_pole` value (`0 sorryAx`). -/
theorem stabilize_prestable_tree_of_all_jhol_eq_north_pole
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_all_np : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole) :
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
  stabilize_prestable_tree_of_all_jhol_const I u_seq pdata h_nonconst_input h_jhol
    (fun u hu => ⟨u north_pole, fun z => congr_fun (h_all_np u hu) z⟩)

/-- A constant root in a prestable limit of non-constant `J`-holomorphic spheres has degree at least 1
whenever every globally `J`-holomorphic sphere equals its `north_pole` value (`0 sorryAx`). -/
theorem root_degree_pos_of_const_of_all_jhol_eq_north_pole
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_all_np : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole) :
    1 ≤ pdata.tree.adj.degree pdata.root :=
  False.elim (h_nonconst_input 0 ⟨u_seq 0 north_pole, fun z => congr_fun (h_all_np (u_seq 0) (h_jhol 0)) z⟩)

/-- Any sequence of non-constant `J`-holomorphic spheres cannot have total energy tending to zero
whenever every globally `J`-holomorphic sphere equals its `north_pole` value (`0 sorryAx`). -/
theorem not_tendsto_zero_totalEnergy_of_jhol_nonconst_of_all_jhol_eq_north_pole
    (u_seq : ℕ → (CP1 → M))
    (σ : Bookkeeping.SubseqMap)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_all_np : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole) :
    ¬ Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop (𝓝 0) :=
  False.elim (h_nonconst 0 ⟨u_seq 0 north_pole, fun z => congr_fun (h_all_np (u_seq 0) (h_jhol 0)) z⟩)

#print axioms totalEnergy_root_eq_zero_of_const
#print axioms sum_energy_erase_root
#print axioms root_degree_one_neighbor
#print axioms root_degree_two_neighbors
#print axioms suppress_degree_two_root
#print axioms stableSphereTreeLimit_of_prestable_of_stable_root
#print axioms stabilize_prestable_tree_of_stable_root
#print axioms stabilize_prestable_tree_of_nonconst_root
#print axioms stabilize_prestable_tree

end GromovCompactness.Assembly
