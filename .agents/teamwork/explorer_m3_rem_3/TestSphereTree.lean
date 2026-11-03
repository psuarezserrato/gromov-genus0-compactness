import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere

open scoped Manifold ContDiff Topology
open Metric Set

namespace RemediatedSphereTree

open GromovCompactness

noncomputable def northPole : CP1 :=
  ⟨EuclideanSpace.single (2 : Fin 3) 1, by
    rw [mem_sphere_zero_iff_norm]
    simp [EuclideanSpace.norm_single]⟩

instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable def stereoNorth : PartialHomeomorph CP1 ℂ :=
  (stereographic' 2 northPole).transHomeomorph c_equiv_e2.toHomeomorph.symm

noncomputable instance : MeasurableSpace CP1 := borel CP1
instance : BorelSpace CP1 := ⟨rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

structure SphereTree where
  V : Type
  [fintypeV : Fintype V]
  [nonemptyV : Nonempty V]
  adj : SimpleGraph V
  is_tree : adj.IsTree
  node_point : (v : V) → (w : V) → adj.Adj v w → CP1
  node_distinct : ∀ (v : V) (w₁ w₂ : V) (h₁ : adj.Adj v w₁) (h₂ : adj.Adj v w₂),
    w₁ ≠ w₂ → node_point v w₁ h₁ ≠ node_point v w₂ h₂

structure StableSphereTreeLimit where
  tree : SphereTree
  map : (v : tree.V) → (CP1 → M)
  is_jhol : ∀ (v : tree.V), JHolomorphicOn I I_CP1 (map v) Set.univ
  nodal_match : ∀ (v w : tree.V) (h : tree.adj.Adj v w),
    map v (tree.node_point v w h) = map w (tree.node_point w v (tree.adj.symm h))
  stable : ∀ (v : tree.V), (∃ c : M, ∀ z : CP1, map v z = c) → 3 ≤ tree.adj.degree v

def is_ghost_component (lim : StableSphereTreeLimit I M) (v : lim.tree.V) : Prop :=
  ∃ c : M, ∀ z : CP1, lim.map v z = c

def is_principal_component (lim : StableSphereTreeLimit I M) (v : lim.tree.V) : Prop :=
  ¬ is_ghost_component I M lim v

theorem tree_degree_sum (tree : SphereTree) :
    let _ := tree.fintypeV
    ∑ v : tree.V, tree.adj.degree v = 2 * (Fintype.card tree.V - 1) := by
  sorry

theorem ghost_components_bound
    (lim : StableSphereTreeLimit I M)
    (P G : ℕ)
    (let _ := lim.tree.fintypeV;
     h_multivertex : 1 < Fintype.card lim.tree.V)
    (h_P : P = Fintype.card { v : lim.tree.V // is_principal_component I M lim v })
    (h_G : G = Fintype.card { v : lim.tree.V // is_ghost_component I M lim v }) :
    G ≤ P - 2 ∧ (let _ := lim.tree.fintypeV; Fintype.card lim.tree.V ≤ 2 * P - 2) := by
  sorry

noncomputable def totalEnergy (I : ModelWithCorners ℝ E H) (u : CP1 → M) : ℝ :=
  (sorry : ℝ)

noncomputable def sphereTreeTotalEnergy (lim : StableSphereTreeLimit I M) : ℝ :=
  let _ := lim.tree.fintypeV
  ∑ v : lim.tree.V, totalEnergy I (lim.map v)

def graft_trees (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V)
    (p₁ : CP1) (p₂ : CP1) : SphereTree := by
  sorry

end RemediatedSphereTree
