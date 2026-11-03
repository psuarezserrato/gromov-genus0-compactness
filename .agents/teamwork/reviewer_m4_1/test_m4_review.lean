import GromovCompactness.Analysis.Energy
import GromovCompactness.Topology.SphereTree

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness Classical

namespace GromovCompactness

-- Test 1: Verify all axioms of Energy.lean and SphereTree.lean
#print axioms riemannianEnergyDensity_nonneg
#print axioms energy_density_eq_omega
#print axioms energy_nonneg
#print axioms energy_eq_pullback_omega
#print axioms energy_additive
#print axioms energy_point_null
#print axioms energy_circle_null
#print axioms energy_conformal_invariant
#print axioms continuous_volume_ball
#print axioms tree_degree_sum
#print axioms ghost_components_bound
#print axioms graft_trees
#print axioms sphereTreeTotalEnergy

-- Test 2: Algebraic sharpness of the ghost component bound
example (P G : ℕ) (hP : 2 ≤ P) (hG : G ≤ P - 2) :
    P + G ≤ 2 * P - 2 := by
  omega

-- Test 3: Impossibility of ghost leaf in stable tree
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

example (lim : StableSphereTreeLimit I (M := M))
    (v : lim.tree.V) (h_ghost : is_ghost_component I lim v) :
    3 ≤ lim.tree.adj.degree v :=
  lim.stable v h_ghost

-- Test 4: Degree sum in 1-vertex tree is 0
example (T : SphereTree) (h1 : Fintype.card T.V = 1) :
    ∑ v : T.V, T.adj.degree v = 0 := by
  have h := tree_degree_sum T
  rw [h1] at h
  exact h

end GromovCompactness
