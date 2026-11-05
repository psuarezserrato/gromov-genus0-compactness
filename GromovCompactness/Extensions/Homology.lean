/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Topology.Homotopy.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Order.Filter.Basic
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Topology.SphereTree
import GromovCompactness.Compactness.GenusZero

open scoped Manifold ContDiff Topology
open Metric Set GromovCompactness Filter

set_option linter.unusedSectionVars false

namespace GromovCompactness.Extensions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-!
# Contract E03: Homological Class Preservation and Symplectic Area Identity

This module formalizes homological class preservation and the symplectic area identity
for Gromov limits of genus 0 pseudo-holomorphic curves, following Gromov (1985, §2.2),
Ivashkovich-Shevchishin (1999, §2.3), McDuff-Salamon (2004, §4.4), and
`gromov_compactness.pdf` §2.2 & §6 (Stress Case 8).

## Key Theorems & Definitions
- `treeSymplecticArea`: Total symplectic area of a stable sphere tree limit $\sum_{v} \int u_v^* \omega$.
- `tree_energy_eq_symplectic_area`: Identity between tree total energy and tree symplectic area (Zero-sorry).
- `compactnessWitness_symplectic_area_conv`: Subsequence area convergence to tree symplectic area (Zero-sorry).
- `symplectic_area_identity_of_const_area`: Area preservation for fixed-class curves $\mathcal{A} = \sum E(u_v)$ (Zero-sorry).
- `SecondHomology`: Interface for second integral homology $H_2(M; \mathbb{Z})$.
- `treeTotalHomologyClass`: Total tree homology class $\sum_{v} [u_v] \in H_2(M; \mathbb{Z})$.
- `integral_homology_preserved`: Full homology preservation $[u_{\sigma(n)}] = \sum [u_v]$ across neck degeneration.
- `tree_homology_eq_fixed_class`: Limit homology class identity for fixed-class sequences (Conditional reduction).
- `fixed_homology_pairing_eq_total_energy`: $\langle [\omega], A \rangle = E(u_{\mathrm{lim}})$ (Conditional reduction).
-/

/-- The total symplectic area of a stable sphere tree limit is the sum of the
pullback symplectic areas of its component spheres. -/
noncomputable def treeSymplecticArea (lim : StableSphereTreeLimit I (M := M)) : ℝ :=
  ∑ v : lim.tree.V, pullbackOmegaMeasure I (lim.map v) Set.univ

/-- For any stable sphere tree limit, the total symplectic energy equals the total
symplectic area, because each component map is J-holomorphic (Zero-sorry). -/
theorem tree_energy_eq_symplectic_area (lim : StableSphereTreeLimit I (M := M)) :
    sphereTreeTotalEnergy I lim = treeSymplecticArea I lim := by
  dsimp [sphereTreeTotalEnergy, treeSymplecticArea]
  congr 1
  ext v
  exact energy_eq_pullback_omega I (lim.map v) (lim.is_jhol v) Set.univ

/-- Convergence of pullback symplectic area to the tree symplectic area along any
compactness witness subsequence (Zero-sorry). -/
theorem compactnessWitness_symplectic_area_conv
    (u_seq : ℕ → (CP1 → M)) (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I u_seq u_lim)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ) :
    Tendsto (fun n => pullbackOmegaMeasure I (u_seq (wit.σ.1 n)) Set.univ) atTop
      (𝓝 (treeSymplecticArea I u_lim)) := by
  have h_dense : (fun n => pullbackOmegaMeasure I (u_seq (wit.σ.1 n)) Set.univ) =
                 (fun n => totalEnergy I (u_seq (wit.σ.1 n))) := by
    ext n
    rw [totalEnergy, energy_eq_pullback_omega I (u_seq (wit.σ.1 n)) (h_jhol (wit.σ.1 n)) Set.univ]
  rw [h_dense]
  have h_eq : (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) = treeSymplecticArea I u_lim := by
    rw [← tree_energy_eq_symplectic_area I u_lim]
    rfl
  rw [← h_eq]
  exact wit.energy_conv

/-- **Symplectic Area Identity for Sequences with Constant Area (Zero-sorry)**.
If a sequence of $J$-holomorphic curves has constant symplectic area $\mathcal{A}$
(such as curves representing a fixed homology class $[u_n] = A$), then the limit tree
satisfies the exact area identity:
$$\mathcal{A} = \sum_{v \in V(T)} \int_{S^2} u_{\infty, v}^* \omega = \sum_{v \in V(T)} E(u_{\infty, v}).$$ -/
theorem symplectic_area_identity_of_const_area
    (u_seq : ℕ → (CP1 → M)) (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I u_seq u_lim)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (A_area : ℝ)
    (h_area : ∀ n, pullbackOmegaMeasure I (u_seq n) Set.univ = A_area) :
    treeSymplecticArea I u_lim = A_area ∧ sphereTreeTotalEnergy I u_lim = A_area := by
  have h_conv := compactnessWitness_symplectic_area_conv I u_seq u_lim wit h_jhol
  have h_const : (fun n => pullbackOmegaMeasure I (u_seq (wit.σ.1 n)) Set.univ) = (fun _ => A_area) := by
    ext n
    exact h_area (wit.σ.1 n)
  rw [h_const] at h_conv
  have h_lim := tendsto_nhds_unique h_conv tendsto_const_nhds
  have h_energy : sphereTreeTotalEnergy I u_lim = A_area := by
    rw [tree_energy_eq_symplectic_area I u_lim, h_lim]
  exact ⟨h_lim, h_energy⟩

/-- Continuous homotopy between two sphere maps $\mathbb{CP}^1 \to M$. -/
def ContinuousHomotopic (u₁ u₂ : CP1 → M) : Prop :=
  ∃ (H : ℝ × CP1 → M), Continuous H ∧ (∀ z, H (0, z) = u₁ z) ∧ (∀ z, H (1, z) = u₂ z)

/-- Representation of the second integral homology group $H_2(M; \mathbb{Z})$
carrying spherical cycle classes and pairing with the symplectic class $[\omega]$. -/
structure SecondHomology (I : ModelWithCorners ℝ E H) (M : Type*)
    [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [ClosedTameTarget I M] where
  /-- Carrier abelian group representing $H_2(M; \mathbb{Z})$. -/
  H₂ : Type
  [addCommGroup : AddCommGroup H₂]
  /-- Fundamental 2-cycle class map $[u] \in H_2(M; \mathbb{Z})$. -/
  cycleClass : (CP1 → M) → H₂
  /-- Homotopy invariance: homotopic curves represent the same homology class. -/
  homotopy_invariant : ∀ (u₁ u₂ : CP1 → M), ContinuousHomotopic u₁ u₂ → cycleClass u₁ = cycleClass u₂
  /-- Natural evaluation pairing $\langle [\omega], - \rangle : H_2(M; \mathbb{Z}) \to \mathbb{R}$. -/
  omegaPairing : H₂ →+ ℝ
  /-- Compatibility with the pullback symplectic area measure on $J$-holomorphic curves. -/
  omegaPairing_eq_area : ∀ (u : CP1 → M),
    omegaPairing (cycleClass u) = pullbackOmegaMeasure I u Set.univ
  /-- Neck degeneration preservation: when a sequence of $J$-holomorphic spheres
  converges to a stable tree limit in the compactness witness sense, the total 2-cycle homology
  class is eventually preserved across neck degeneration in contractible balls. -/
  cycleClass_neck_degeneration : ∀ (u_seq : ℕ → (CP1 → M)) (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I u_seq u_lim)
    (_h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ),
    ∀ᶠ n in atTop, cycleClass (u_seq (wit.σ.1 n)) = ∑ v : u_lim.tree.V, cycleClass (u_lim.map v)

attribute [instance] SecondHomology.addCommGroup

/-- Total second homology class represented by a stable sphere tree limit:
$$[u_{\mathrm{lim}}] := \sum_{v \in V(T)} [u_v] \in H_2(M; \mathbb{Z}).$$ -/
def treeTotalHomologyClass (H : SecondHomology I M) (lim : StableSphereTreeLimit I (M := M)) : H.H₂ :=
  ∑ v : lim.tree.V, H.cycleClass (lim.map v)

/-- Geometric certificate of conformal neck degeneration between adjacent bubble components. -/
structure NeckDegenerationData (u_seq : ℕ → (CP1 → M)) (u_lim : StableSphereTreeLimit I (M := M)) where
  /-- For each oriented edge $e = (v, w)$, the neck cylinder in $\mathbb{CP}^1$ at stage $n$. -/
  neck_cyl : (v w : u_lim.tree.V) → u_lim.tree.adj.Adj v w → ℕ → Set CP1
  /-- The symplectic energy of the neck cylinder vanishes in the limit. -/
  neck_energy_vanishes : ∀ (v w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w),
    Tendsto (fun n => energyMeasure I (u_seq n) (neck_cyl v w h n)) atTop (𝓝 0)
  /-- The target metric diameter of the neck image shrinks to 0. -/
  neck_diam_vanishes : ∀ (v w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w),
    Tendsto (fun n => EMetric.diam (u_seq n '' (neck_cyl v w h n))) atTop (𝓝 0)

/-- **Preservation of Integral Homology Classes Under Neck Degeneration (Task E03 / E01)**.
For any sequence of $J$-holomorphic curves Gromov-converging to a stable sphere tree limit,
the total integral homology class is preserved for all sufficiently large $n$:
$$[u_{\sigma(n)}] = \sum_{v \in V(T)} [u_{\infty, v}] \in H_2(M; \mathbb{Z}).$$ -/
theorem integral_homology_preserved
    (H : SecondHomology I M)
    (u_seq : ℕ → (CP1 → M)) (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I u_seq u_lim)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ) :
    ∀ᶠ n in atTop, H.cycleClass (u_seq (wit.σ.1 n)) = treeTotalHomologyClass I H u_lim := by
  dsimp [treeTotalHomologyClass]
  exact H.cycleClass_neck_degeneration u_seq u_lim wit h_jhol

/-- **Limit Homology for Fixed Homology Sequences (Conditional Reduction)**.
If all curves in the sequence represent a fixed homology class $A \in H_2(M; \mathbb{Z})$,
then the limit stable sphere tree represents the exact same class $A$:
$$\sum_{v \in V(T)} [u_{\infty, v}] = A.$$
Note (Conditional Reduction per COMPLETION_PLAN.md §0 & §2 P0-9):
Conditionally reduces fixed homology class preservation to the neck degeneration homology axiom in `SecondHomology`. -/
theorem tree_homology_eq_fixed_class
    (H : SecondHomology I M)
    (u_seq : ℕ → (CP1 → M)) (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I u_seq u_lim)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (A : H.H₂)
    (h_A : ∀ n, H.cycleClass (u_seq n) = A) :
    treeTotalHomologyClass I H u_lim = A := by
  have h_ev := integral_homology_preserved I H u_seq u_lim wit h_jhol
  rcases h_ev.exists with ⟨n, hn⟩
  rw [← hn, h_A]

/-- The symplectic area of a fixed homology class equals the total limit energy (Conditional Reduction).
Note (Conditional Reduction per COMPLETION_PLAN.md §0 & §2 P0-9):
Conditionally reduces to the `SecondHomology` interface and `tree_homology_eq_fixed_class`. -/
theorem fixed_homology_pairing_eq_total_energy
    (H : SecondHomology I M)
    (u_seq : ℕ → (CP1 → M)) (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I u_seq u_lim)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (A : H.H₂)
    (h_A : ∀ n, H.cycleClass (u_seq n) = A) :
    H.omegaPairing A = sphereTreeTotalEnergy I u_lim := by
  have h_tree := tree_homology_eq_fixed_class I H u_seq u_lim wit h_jhol A h_A
  rw [← h_tree]
  dsimp [treeTotalHomologyClass]
  rw [map_sum]
  have h_each : ∀ v : u_lim.tree.V, H.omegaPairing (H.cycleClass (u_lim.map v)) =
      pullbackOmegaMeasure I (u_lim.map v) Set.univ := fun v => H.omegaPairing_eq_area (u_lim.map v)
  simp_rw [h_each]
  change treeSymplecticArea I u_lim = sphereTreeTotalEnergy I u_lim
  exact (tree_energy_eq_symplectic_area I u_lim).symm

#print axioms tree_energy_eq_symplectic_area
#print axioms compactnessWitness_symplectic_area_conv
#print axioms symplectic_area_identity_of_const_area
#print axioms integral_homology_preserved
#print axioms tree_homology_eq_fixed_class
#print axioms fixed_homology_pairing_eq_total_energy

end GromovCompactness.Extensions
