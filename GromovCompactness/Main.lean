/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.HoferRescaling
import GromovCompactness.Topology.SmoothLocal
import GromovCompactness.Topology.Subsequence
import GromovCompactness.Topology.SphereTree
import GromovCompactness.Topology.ComponentCount
import GromovCompactness.Compactness.Assembly
import GromovCompactness.Compactness.Stabilize
import GromovCompactness.Compactness.GenusZero

open scoped Manifold ContDiff Topology Classical
open Metric Set Filter GromovCompactness Classical

namespace GromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-!
# Task G05: Master Core Integration and Axiom Audit

This module serves as the master integration gate for the core Genus 0 Gromov Compactness
formalization in Lean 4, following `GROMOV_COMPACTNESS_BLUEPRINT.md` §4.11 & §5 (Task `G05`)
and `gromov_compactness.pdf` Theorem 1.

## Main Result
- `gromov_compactness_genus_zero`: The complete master theorem combining subsequence convergence,
  energy conservation, vanishing neck diameters, and universal component bounds.
- `#print axioms gromov_compactness_genus_zero`: Audits that only standard Lean 4 axioms
  (`propext`, `Quot.sound`, `Classical.choice`) are present, with no `sorryAx` or artificial axioms.
-/

/-- **Master Theorem: Genus 0 Gromov Compactness in Lean 4 (Theorem 1)**.
Let $M$ be a compact, boundaryless manifold equipped with a smooth closed symplectic form $\omega$
and a tame almost complex structure $J$. Let $u_n : \mathbb{CP}^1 \to M$ be a sequence of
non-constant $J$-holomorphic spheres with uniformly bounded energy $E(u_n) \le B < \infty$.

Then there exists a strictly increasing subsequence $u_{\sigma(n)}$ converging to a stable
pseudo-holomorphic sphere tree limit curve $u_{\mathrm{lim}} = (T, \{u_v\}, \{z_{vw}\})$ in the
compactness witness sense, satisfying:
1. $C^\infty_{\mathrm{loc}}$ convergence on each spherical component away from incident nodes under
   moving Möbius coordinate frames $\phi_{v, n} \in \operatorname{PSL}(2, \mathbb{C})$.
2. Transition collapse of neighboring coordinate frames towards the nodal attachment points.
3. Total energy conservation: $\lim_{n \to \infty} E(u_{\sigma(n)}) = \sum_{v \in V} E(u_v)$.
4. Vanishing neck image diameters across all edges.
5. Linear component bounds: $P \cdot h \le B$, and for $|V| > 1$, $G \le P - 2$ and $|V| \le 2P - 2$.
6. Universal integer vertex bound: $(|V| : \mathbb{Z}) \le \max(1, 2\lfloor B / h \rfloor - 2)$. -/
theorem gromov_compactness_genus_zero
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
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) := by
  obtain ⟨u_lim, ⟨wit⟩⟩ := gromov_compactness_core I th u_seq B h_nonconst h_jhol h_energy
  refine ⟨u_lim, ⟨wit⟩, ?_⟩
  have h_lim_energy : (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B := by
    have h_conv := wit.energy_conv
    have h_le_B : ∀ n, totalEnergy I (u_seq (wit.σ.1 n)) ≤ B := fun n => h_energy (wit.σ.1 n)
    exact le_of_tendsto h_conv (Eventually.of_forall h_le_B)
  exact Topology.component_count_bounds I th u_lim B h_lim_energy

#print axioms gromov_compactness_genus_zero

end GromovCompactness
