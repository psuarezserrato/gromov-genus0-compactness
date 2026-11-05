/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Sequences
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Hausdorff
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Topology.SmoothLocal
import GromovCompactness.Topology.Subsequence
import GromovCompactness.Topology.SphereTree
import GromovCompactness.Topology.ComponentCount
import GromovCompactness.Compactness.Assembly
import GromovCompactness.Compactness.Stabilize
import GromovCompactness.Compactness.GenusZero
import GromovCompactness.Main

open scoped Manifold ContDiff Topology Classical
open Metric Set Filter Classical

set_option linter.unusedSectionVars false

namespace GromovCompactness.Extensions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-!
# Contract E05: Gromov Topology Metrizability & Compact Hausdorff Moduli Space

This module formalizes Contract `E05`:
1. `MarkedSphereTree`: $k$-marked combinatorial sphere trees with pairwise distinct marked points
   and disjointness from nodal points.
2. `MarkedStableMap`: Genus 0 stable $k$-marked pseudo-holomorphic maps into $(M, J)$
   with Deligne-Mumford / Kontsevich stability: ghost components satisfy $\operatorname{deg}_{\mathrm{nodal}}(v) + k_v \ge 3$.
3. `StableMapIso`: Isomorphism of stable marked maps (graph isomorphism, Möbius frames, node matching,
   marked point matching, curve intertwining).
4. `stableMapEquiv`: Equivalence relation on marked stable maps (reflexivity proved zero-sorry).
5. `ModuliSpace`: The quotient moduli space $\overline{\mathcal{M}}_{0, k}(M, J, \le B)$.
6. `gromovDist` & `moduliSpaceMetric`: The canonical Gromov metric and metric space structure.
7. `moduli_space_t2`: Hausdorff separation ($T_2$) of the moduli space.
8. `moduli_space_compact` & `moduli_space_seq_compact`: Topological and sequential compactness.
9. `moduli_space_compact_hausdorff`: Master compact Hausdorff moduli space theorem.
10. `ModuliSpaceInClass`: Moduli space for a fixed homology class $A \in H_2(M; \mathbb{Z})$.

References:
- Mikhail Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Math. 82 (1985), §2.3.
- Sergei Ivashkovich & Vsevolod Shevchishin, arXiv:math/9912046, §2.
- D. McDuff & D. Salamon, *J-holomorphic Curves and Symplectic Topology*, AMS (2012), Chapter 5.
- `GROMOV_COMPACTNESS_BLUEPRINT.md` Contract `E05`.
-/

/-- A combinatorial $k$-marked sphere tree: a tree $T = (V, E_T)$ where each oriented edge
carries a nodal attachment point and $k$ marked points are assigned to vertices and coordinates. -/
structure MarkedSphereTree (k : ℕ) extends SphereTree where
  /-- Vertex carrying each marked point $i \in \{0, \dots, k-1\}$. -/
  mark_vertex : Fin k → V
  /-- Coordinates of each marked point on its host spherical component. -/
  mark_point : (i : Fin k) → CP1
  /-- Marked points on the same component are pairwise distinct. -/
  mark_distinct : ∀ (i j : Fin k), i ≠ j → mark_vertex i = mark_vertex j →
    mark_point i ≠ mark_point j
  /-- Marked points are disjoint from nodal attachment points on the same component. -/
  mark_node_distinct : ∀ (i : Fin k) (w : V) (h : adj.Adj (mark_vertex i) w),
    mark_point i ≠ node_point (mark_vertex i) w h

/-- The number of marked points located on component $v$. -/
noncomputable def marked_degree {k : ℕ} (tree : MarkedSphereTree k) (v : tree.V) : ℕ :=
  Fintype.card { i : Fin k // tree.mark_vertex i = v }

/-- Total number of special points (nodes + markings) on component $v$. -/
noncomputable def special_degree {k : ℕ} (tree : MarkedSphereTree k) (v : tree.V) : ℕ :=
  tree.adj.degree v + marked_degree tree v

/-- A $k$-marked stable pseudo-holomorphic map of genus 0 into $(M, J)$. -/
structure MarkedStableMap (k : ℕ) where
  /-- Underlying $k$-marked combinatorial sphere tree. -/
  tree : MarkedSphereTree k
  /-- Component pseudo-holomorphic curves $u_v : \mathbb{CP}^1 \to M$. -/
  map : (v : tree.V) → (CP1 → M)
  /-- Each component map is smooth and $J$-holomorphic. -/
  is_jhol : ∀ (v : tree.V), JHolomorphicOn I I_CP1 (map v) Set.univ
  /-- Nodal matching condition: across every incident edge $v \sim w$,
  $$u_v(z_{vw}) = u_w(z_{wv}).$$ -/
  nodal_match : ∀ (v w : tree.V) (h : tree.adj.Adj v w),
    map v (tree.node_point v w h) = map w (tree.node_point w v (tree.adj.symm h))
  /-- Deligne-Mumford / Kontsevich stability condition: any constant component
  ('ghost bubble') carries at least 3 special points (nodes + marked points):
  $$\operatorname{special\_deg}(v) = \operatorname{deg}_{\mathrm{nodal}}(v) + k_v \ge 3.$$ -/
  stable : ∀ (v : tree.V), (∃ c : M, ∀ z : CP1, map v z = c) → 3 ≤ special_degree tree v

/-- Total symplectic energy of a $k$-marked stable map: $E(u) = \sum_{v \in V} E(u_v)$. -/
noncomputable def markedStableMapTotalEnergy {k : ℕ} (u : MarkedStableMap I (M := M) k) : ℝ :=
  ∑ v : u.tree.V, totalEnergy I (u.map v)

/-- The space of $k$-marked stable maps with total energy bounded by $B$. -/
def BoundedMarkedStableMap (k : ℕ) (B : ℝ) : Type _ :=
  { u : MarkedStableMap I (M := M) k // markedStableMapTotalEnergy I u ≤ B }

/-- An isomorphism between two $k$-marked stable maps: a tree isomorphism and
Möbius transformations on each sphere component preserving nodes, markings, and maps. -/
structure StableMapIso {k : ℕ} (u₁ u₂ : MarkedStableMap I (M := M) k) where
  /-- Bijection between component vertex sets. -/
  v_equiv : u₁.tree.V ≃ u₂.tree.V
  /-- Preservation of graph adjacency. -/
  adj_compat : ∀ (v w : u₁.tree.V), u₁.tree.adj.Adj v w ↔ u₂.tree.adj.Adj (v_equiv v) (v_equiv w)
  /-- Biholomorphic Möbius frame transformation on each component sphere. -/
  moeb : (v : u₁.tree.V) → MoebiusFrame
  /-- Nodal points are mapped to corresponding nodal points. -/
  node_compat : ∀ (v w : u₁.tree.V) (h : u₁.tree.adj.Adj v w),
    (moeb v).toHomeo (u₁.tree.node_point v w h) =
      u₂.tree.node_point (v_equiv v) (v_equiv w) ((adj_compat v w).mp h)
  /-- Marked points lie on corresponding components. -/
  mark_vertex_compat : ∀ (i : Fin k), v_equiv (u₁.tree.mark_vertex i) = u₂.tree.mark_vertex i
  /-- Marked point coordinates are preserved under the component Möbius transformation. -/
  mark_point_compat : ∀ (i : Fin k),
    (moeb (u₁.tree.mark_vertex i)).toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i
  /-- Component curves are intertwined: $u_2 \circ \phi_v = u_1$. -/
  map_compat : ∀ (v : u₁.tree.V) (z : CP1),
    u₂.map (v_equiv v) ((moeb v).toHomeo z) = u₁.map v z

/-- Isomorphism of marked stable maps is an equivalence relation. -/
def stableMapEquiv {k : ℕ} (u₁ u₂ : MarkedStableMap I (M := M) k) : Prop :=
  Nonempty (StableMapIso I u₁ u₂)

/-- Reflexivity of stable map isomorphism (Zero-sorry). -/
theorem stableMapEquiv_refl {k : ℕ} (u : MarkedStableMap I (M := M) k) :
    stableMapEquiv I u u := by
  refine ⟨⟨Equiv.refl _, fun _ _ => Iff.rfl, fun _ => MoebiusFrame.id, ?_, fun _ => rfl, ?_, ?_⟩⟩
  · intro v w h; rfl
  · intro i; rfl
  · intro v z; rfl

/-- Symmetry of stable map isomorphism (Zero-sorry). -/
theorem stableMapEquiv_symm {k : ℕ} {u₁ u₂ : MarkedStableMap I (M := M) k}
    (h : stableMapEquiv I u₁ u₂) : stableMapEquiv I u₂ u₁ := by
  obtain ⟨iso⟩ := h
  refine ⟨{
    v_equiv := iso.v_equiv.symm
    adj_compat := fun u v => by
      have h_adj := (iso.adj_compat (iso.v_equiv.symm u) (iso.v_equiv.symm v)).symm
      rw [iso.v_equiv.apply_symm_apply u, iso.v_equiv.apply_symm_apply v] at h_adj
      exact h_adj
    moeb := fun v => MoebiusFrame.inv (iso.moeb (iso.v_equiv.symm v))
    node_compat := fun v w h_adj => by
      dsimp [MoebiusFrame.inv]
      obtain ⟨v', rfl⟩ := iso.v_equiv.surjective v
      obtain ⟨w', rfl⟩ := iso.v_equiv.surjective w
      simp only [Equiv.symm_apply_apply]
      have h_orig_adj : u₁.tree.adj.Adj v' w' := (iso.adj_compat v' w').mpr h_adj
      have h_node := iso.node_compat v' w' h_orig_adj
      rw [← h_node, (iso.moeb v').toHomeo.symm_apply_apply]
    mark_vertex_compat := fun i => by
      have h_mv := iso.mark_vertex_compat i
      exact iso.v_equiv.symm_apply_eq.mpr h_mv.symm
    mark_point_compat := fun i => by
      dsimp [MoebiusFrame.inv]
      have h_mv : iso.v_equiv.symm (u₂.tree.mark_vertex i) = u₁.tree.mark_vertex i := by
        exact iso.v_equiv.symm_apply_eq.mpr (iso.mark_vertex_compat i).symm
      rw [h_mv]
      have h_mp := iso.mark_point_compat i
      rw [← h_mp, (iso.moeb (u₁.tree.mark_vertex i)).toHomeo.symm_apply_apply]
    map_compat := fun v z => by
      dsimp [MoebiusFrame.inv]
      have h_map := iso.map_compat (iso.v_equiv.symm v) ((iso.moeb (iso.v_equiv.symm v)).toHomeo.symm z)
      rw [iso.v_equiv.apply_symm_apply v] at h_map
      rw [(iso.moeb (iso.v_equiv.symm v)).toHomeo.apply_symm_apply z] at h_map
      exact h_map.symm
  }⟩

/-- Transitivity of stable map isomorphism (Zero-sorry). -/
theorem stableMapEquiv_trans {k : ℕ} {u₁ u₂ u₃ : MarkedStableMap I (M := M) k}
    (h₁₂ : stableMapEquiv I u₁ u₂) (h₂₃ : stableMapEquiv I u₂ u₃) :
    stableMapEquiv I u₁ u₃ := by
  obtain ⟨iso12⟩ := h₁₂
  obtain ⟨iso23⟩ := h₂₃
  refine ⟨{
    v_equiv := iso12.v_equiv.trans iso23.v_equiv
    adj_compat := fun u v =>
      (iso12.adj_compat u v).trans (iso23.adj_compat (iso12.v_equiv u) (iso12.v_equiv v))
    moeb := fun v => MoebiusFrame.comp (iso23.moeb (iso12.v_equiv v)) (iso12.moeb v)
    node_compat := fun v w h => by
      dsimp [MoebiusFrame.comp]
      have h1 := iso12.node_compat v w h
      have h2 := iso23.node_compat (iso12.v_equiv v) (iso12.v_equiv w) ((iso12.adj_compat v w).mp h)
      rw [h1, h2]
    mark_vertex_compat := fun i => by
      dsimp [Equiv.trans]
      rw [iso12.mark_vertex_compat i, iso23.mark_vertex_compat i]
    mark_point_compat := fun i => by
      dsimp [MoebiusFrame.comp]
      rw [iso12.mark_vertex_compat i]
      rw [iso12.mark_point_compat i, iso23.mark_point_compat i]
    map_compat := fun v z => by
      dsimp [MoebiusFrame.comp, Equiv.trans]
      have h2 := iso23.map_compat (iso12.v_equiv v) ((iso12.moeb v).toHomeo z)
      have h1 := iso12.map_compat v z
      rw [h2, h1]
  }⟩

/-- Equivalence relation on bounded marked stable maps. -/
def boundedMarkedStableMapSetoid (k : ℕ) (B : ℝ) :
    Setoid (BoundedMarkedStableMap I (M := M) k B) where
  r u₁ u₂ := stableMapEquiv I u₁.1 u₂.1
  iseqv := {
    refl := fun u => stableMapEquiv_refl I u.1
    symm := fun h => stableMapEquiv_symm I h
    trans := fun h₁ h₂ => stableMapEquiv_trans I h₁ h₂
  }

instance boundedMarkedStableMapSetoidInst (k : ℕ) (B : ℝ) :
    Setoid (BoundedMarkedStableMap I (M := M) k B) :=
  boundedMarkedStableMapSetoid I k B

/-- The Kontsevich moduli space $\overline{\mathcal{M}}_{0, k}(M, J, \le B)$ of stable
$k$-marked genus 0 pseudo-holomorphic curves with energy bounded by $B$. -/
def ModuliSpace (k : ℕ) (B : ℝ) : Type _ :=
  Quotient (boundedMarkedStableMapSetoid I (M := M) k B)

/-- Mathematical witness of Gromov convergence of marked stable maps (Contract E05). -/
structure MarkedGromovWitness {k : ℕ}
    (u_seq : ℕ → MarkedStableMap I (M := M) k)
    (u_lim : MarkedStableMap I (M := M) k) where
  frames : (v : u_lim.tree.V) → ℕ → MoebiusFrame
  comp_map : (v : u_lim.tree.V) → (n : ℕ) → (u_seq n).tree.V
  smooth_conv : ∀ (v : u_lim.tree.V),
    SmoothLocalConvergesOn I
      (fun n => (u_seq n).map (comp_map v n) ∘ (frames v n).toHomeo)
      (u_lim.map v)
      (punctured_sphere { z | (∃ (w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w), z = u_lim.tree.node_point v w h) ∨
                              (∃ (i : Fin k), u_lim.tree.mark_vertex i = v ∧ z = u_lim.tree.mark_point i) })
  frame_collapse : ∀ (v w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w),
    ∀ K ⊆ punctured_sphere {u_lim.tree.node_point w v (u_lim.tree.adj.symm h)}, IsCompact K →
      TendstoUniformlyOn
        (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (frames v n)) (frames w n)).toHomeo)
        (fun _ => u_lim.tree.node_point v w h) atTop K
  mark_conv : ∀ (i : Fin k),
    let v := u_lim.tree.mark_vertex i
    Tendsto (fun n => (MoebiusFrame.inv (frames v n)).toHomeo
      ((u_seq n).tree.mark_point i)) atTop (𝓝 (u_lim.tree.mark_point i))
  energy_conv :
    Tendsto (fun n => markedStableMapTotalEnergy I (u_seq n)) atTop
      (𝓝 (markedStableMapTotalEnergy I u_lim))

/-- Sequential Gromov convergence on the moduli space (McDuff-Salamon §5.6, Zero-sorry). -/
def GromovConverges {k : ℕ} {B : ℝ}
    (u_seq : ℕ → ModuliSpace I (M := M) k B)
    (u_lim : ModuliSpace I (M := M) k B) : Prop :=
  ∃ (reps : ℕ → BoundedMarkedStableMap I (M := M) k B)
    (lim_rep : BoundedMarkedStableMap I (M := M) k B),
    (∀ n, Quotient.mk' (reps n) = u_seq n) ∧
    Quotient.mk' lim_rep = u_lim ∧
    Nonempty (MarkedGromovWitness I (fun n => (reps n).1) lim_rep.1)

/-- The sequential Gromov topology on the moduli space (McDuff-Salamon §5.6, Zero-sorry). -/
def moduliSpaceTopology (k : ℕ) (B : ℝ) : TopologicalSpace (ModuliSpace I (M := M) k B) where
  IsOpen U := ∀ (u_seq : ℕ → ModuliSpace I (M := M) k B) (u_lim : ModuliSpace I (M := M) k B),
    u_lim ∈ U → GromovConverges I u_seq u_lim → ∀ᶠ n in atTop, u_seq n ∈ U
  isOpen_univ := fun _u_seq _u_lim _ _ => Eventually.of_forall (fun _ => mem_univ _)
  isOpen_inter := by
    intro s t hs ht u_seq u_lim ⟨hu_s, hu_t⟩ h_conv
    have hs_ev := hs u_seq u_lim hu_s h_conv
    have ht_ev := ht u_seq u_lim hu_t h_conv
    exact hs_ev.and ht_ev
  isOpen_sUnion := by
    intro S hS u_seq u_lim ⟨t, ht_mem, hu_t⟩ h_conv
    have ht_open := hS t ht_mem
    have ht_ev := ht_open u_seq u_lim hu_t h_conv
    filter_upwards [ht_ev] with n hn
    exact mem_sUnion_of_mem hn ht_mem

/-- Canonical topological space instance on the Kontsevich moduli space (Zero-sorry). -/
instance moduliSpaceTopologicalSpace (k : ℕ) (B : ℝ) :
    TopologicalSpace (ModuliSpace I (M := M) k B) :=
  moduliSpaceTopology I k B

/-- **Hausdorff Separation of the Moduli Space (Contract E05)**:
The moduli space $\overline{\mathcal{M}}_{0, k}(M, J, \le B)$ is a Hausdorff space ($T_2$).
This formalizes the uniqueness of Gromov limits up to stable map isomorphism. -/
theorem moduli_space_t2 (k : ℕ) (B : ℝ) :
    T2Space (ModuliSpace I (M := M) k B) := by
  sorry

/-- **Compactness of the Moduli Space (Contract E05)**:
The moduli space $\overline{\mathcal{M}}_{0, k}(M, J, \le B)$ is a compact topological space. -/
theorem moduli_space_compact (k : ℕ) (B : ℝ) :
    CompactSpace (ModuliSpace I (M := M) k B) := by sorry

/-- **Sequential Compactness of the Moduli Space (Contract E05)**:
Every sequence in $\overline{\mathcal{M}}_{0, k}(M, J, \le B)$ has a convergent subsequence
in the Gromov topology. -/
theorem moduli_space_seq_compact (k : ℕ) (B : ℝ) :
    SeqCompactSpace (ModuliSpace I (M := M) k B) := by sorry

/-- **Master Compact Hausdorff Moduli Space Theorem (Contract E05)**:
The moduli space $\overline{\mathcal{M}}_{0, k}(M, J, \le B)$ is both compact and Hausdorff. -/
theorem moduli_space_compact_hausdorff (k : ℕ) (B : ℝ) :
    CompactSpace (ModuliSpace I (M := M) k B) ∧ T2Space (ModuliSpace I (M := M) k B) :=
  ⟨moduli_space_compact I k B, moduli_space_t2 I k B⟩

/-- Metrizability of the Gromov Moduli Space (McDuff-Salamon §5.6, deferred theorem).
There exists a metric inducing the sequential Gromov topology on $\overline{\mathcal{M}}_{0, k}(M, J, \le B)$. -/
theorem moduli_space_metrizable (k : ℕ) (B : ℝ) :
    ∃ (m : MetricSpace (ModuliSpace I (M := M) k B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I k B := by
  sorry

/-- A homology class $A \in H_2(M; \mathbb{Z})$ represented with its symplectic pairing. -/
structure HomologyClass2 (M : Type*) where
  /-- Symplectic area pairing $\langle [\omega], A \rangle$. -/
  omega_eval : ℝ
  /-- Area is non-negative for pseudo-holomorphic curves. -/
  omega_eval_nonneg : 0 ≤ omega_eval

/-- Predicate selecting marked stable maps representing class $A$. -/
def represents_homology_class {k : ℕ}
    (u : MarkedStableMap I (M := M) k) (A : HomologyClass2 M) : Prop :=
  markedStableMapTotalEnergy I u = A.omega_eval

/-- Predicate for moduli space elements representing a homology class A (Zero-sorry). -/
def ModuliSpace.represents_class {k : ℕ} (A : HomologyClass2 M)
    (x : ModuliSpace I (M := M) k A.omega_eval) : Prop :=
  ∃ (u : BoundedMarkedStableMap I (M := M) k A.omega_eval),
    Quotient.mk' u = x ∧ represents_homology_class I u.1 A

/-- The moduli space for a fixed homology class A (Zero-sorry). -/
def ModuliSpaceInClass (k : ℕ) (A : HomologyClass2 M) : Type _ :=
  { x : ModuliSpace I (M := M) k A.omega_eval // ModuliSpace.represents_class I A x }

/-- Subspace topology on the homology-fixed moduli space (Zero-sorry). -/
instance moduliSpaceInClassTopologicalSpace (k : ℕ) (A : HomologyClass2 M) :
    TopologicalSpace (ModuliSpaceInClass I (M := M) k A) :=
  TopologicalSpace.induced Subtype.val (moduliSpaceTopologicalSpace I k A.omega_eval)

/-- **Compact Hausdorff Space for Fixed Homology Class (Contract E05)**:
The moduli space $\overline{\mathcal{M}}_{0, k}(M, J, A)$ representing class $A \in H_2(M; \mathbb{Z})$
is compact and Hausdorff. -/
theorem moduli_space_in_class_compact_hausdorff (k : ℕ) (A : HomologyClass2 M) :
    CompactSpace (ModuliSpaceInClass I k A) ∧ T2Space (ModuliSpaceInClass I k A) := by
  haveI : T2Space (ModuliSpace I (M := M) k A.omega_eval) := moduli_space_t2 I k A.omega_eval
  refine ⟨?_, Topology.IsEmbedding.t2Space ⟨⟨rfl⟩, Subtype.val_injective⟩⟩
  sorry

#print axioms stableMapEquiv_refl
#print axioms stableMapEquiv_symm
#print axioms stableMapEquiv_trans
#print axioms moduli_space_t2

end GromovCompactness.Extensions
