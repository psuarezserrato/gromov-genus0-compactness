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
- `gromov_compactness_genus_zero`: Master reduction theorem combining subsequence convergence,
  energy conservation, vanishing neck diameters, and universal component bounds.
  Note (Conditional Reduction per COMPLETION_PLAN.md §0 & §2 P0-9):
  This master theorem conditionally reduces genus 0 Gromov compactness to the core contract stack
  (`gromov_compactness_core` + `component_count_bounds`). It takes open analytical statements
  transitively and will become unconditionally sorryAx-free upon proof of the leaf contracts.
- `#print axioms gromov_compactness_genus_zero`: Tracks the transitive axiom dependency closure.
-/

/-- Zero-sorry conditional reduction of `gromov_compactness_genus_zero` from `gromov_compactness_core` (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_core
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_core : ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim)) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) := by
  obtain ⟨u_lim, ⟨wit⟩⟩ := h_core
  refine ⟨u_lim, ⟨wit⟩, ?_⟩
  have h_lim_energy : (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B := by
    have h_conv := wit.energy_conv
    have h_le_B : ∀ n, totalEnergy I (u_seq (wit.σ.1 n)) ≤ B := fun n => h_energy (wit.σ.1 n)
    exact le_of_tendsto h_conv (Eventually.of_forall h_le_B)
  exact Topology.component_count_bounds I th u_lim B h_lim_energy

/-- **Master Theorem: Genus 0 Gromov Compactness in Lean 4 (Theorem 1, Conditional Reduction)**.
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
6. Universal integer vertex bound: $(|V| : \mathbb{Z}) \le \max(1, 2\lfloor B / h \rfloor - 2)$.

Note (Conditional Reduction per COMPLETION_PLAN.md §0 & §2 P0-9):
This theorem reduces the master compactness result to the core compactness theorem `gromov_compactness_core`
and component bounds `component_count_bounds`. It takes open statements transitively and does not count
as closing the master theorem unconditionally until the underlying analytical leaf contracts are proved. -/
theorem gromov_compactness_genus_zero
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core I th u_seq B h_nonconst h_jhol h_energy h_fin)

/-- Zero-sorry Genus 0 Gromov Compactness when a subsequence converges smoothly on `CP1` to a
non-constant map with energy conservation (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_global_conv_nonconst
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M)
    (h_nonconst_lim : ¬ ∃ c : M, ∀ z, u_lim z = c)
    (h_conv : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Set.univ)
    (h_tendsto : Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop (𝓝 (totalEnergy I u_lim))) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_global_conv_nonconst I u_seq h_jhol σ u_lim h_nonconst_lim h_conv h_tendsto)

/-- Zero-sorry Genus 0 Gromov Compactness from a prestable limit with non-zero energy sum and
singleton nodal convergence upgrade (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_prestable_energy_sum_ne_zero_and_upgrade
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (pdata : Assembly.PrestableLimitData I u_seq)
    (h_sum : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≠ 0)
    (h_pt : ∀ (pdata' : Assembly.PrestableLimitData I u_seq)
      (w₀ : pdata'.tree.V) (hw₀_adj : pdata'.tree.adj.Adj pdata'.root w₀),
      SmoothLocalConvergesOn I
        (fun n => (u_seq (pdata'.σ.1 n)) ∘ (pdata'.frames w₀ n).toHomeo)
        (pdata'.map w₀)
        {pdata'.tree.node_point w₀ pdata'.root (pdata'.tree.adj.adj_symm hw₀_adj)}) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_prestable_energy_sum_ne_zero_and_upgrade I u_seq pdata h_sum h_pt)

/-- Zero-sorry Genus 0 Gromov Compactness from a prestable limit when the sequence is non-constant
$J$-holomorphic, the sphere energy gap holds, and singleton nodal convergence holds (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_prestable_jhol_gap_and_upgrade
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (pdata : Assembly.PrestableLimitData I u_seq)
    (h_gap : ∃ h_s > 0, ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z : CP1, u z = c) →
      totalEnergy I u ≥ h_s)
    (h_pt : ∀ (pdata' : Assembly.PrestableLimitData I u_seq)
      (w₀ : pdata'.tree.V) (hw₀_adj : pdata'.tree.adj.Adj pdata'.root w₀),
      SmoothLocalConvergesOn I
        (fun n => (u_seq (pdata'.σ.1 n)) ∘ (pdata'.frames w₀ n).toHomeo)
        (pdata'.map w₀)
        {pdata'.tree.node_point w₀ pdata'.root (pdata'.tree.adj.adj_symm hw₀_adj)}) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_prestable_jhol_gap_and_upgrade I u_seq pdata h_jhol h_nonconst h_gap h_pt)

/-- Zero-sorry Genus 0 Gromov Compactness when concentration data `cdata` has
`cdata.μ = energyMeasureExtended I cdata.u₀` and non-constant background curve `cdata.u₀` (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_cdata_mu_eq_energyMeasureExtended
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_eq : cdata.μ = energyMeasureExtended I cdata.u₀)
    (h_nonconst_u0 : ¬ ∃ c : M, ∀ z, cdata.u₀ z = c) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_cdata_mu_eq_energyMeasureExtended I th u_seq B h_jhol cdata h_eq h_nonconst_u0)

/-- Unconditional Genus 0 Gromov Compactness on subsingleton targets (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_subsingleton [Subsingleton M]
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_subsingleton I u_seq h_nonconst)

/-- Unconditional Genus 0 Gromov Compactness when `B < th.ε_sph` (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_lt : B < th.ε_sph) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_lt_eps_sph I th u_seq B h_nonconst h_jhol h_energy h_lt)

/-- Unconditional Genus 0 Gromov Compactness when `B < th.h` (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_lt : B < th.h) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_lt_eps_sph I th u_seq B h_nonconst h_jhol h_energy
    (h_lt.trans_le th.h_le_sph)

/-- Unconditional Genus 0 Gromov Compactness when `B ≤ 0` (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_nonpos_B
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (hB : B ≤ 0) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_lt_eps_sph I th u_seq B h_nonconst h_jhol h_energy
    (hB.trans_lt th.ε_sph_pos)

/-- Unconditional Genus 0 Gromov Compactness on `[DiscreteTopology M]` targets (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_discrete [DiscreteTopology M]
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_discrete I th u_seq h_nonconst h_jhol)

/-- Unconditional threshold-free Genus 0 Gromov Compactness on `[DiscreteTopology M]` targets (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_univ_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (th : Bubbling.TargetThresholds I M)
      (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) := by
  obtain ⟨th⟩ := Bubbling.exists_target_thresholds_of_discrete I (M := M)
  obtain ⟨u_stable, h⟩ := gromov_compactness_genus_zero_of_discrete I th u_seq B h_nonconst h_jhol h_energy
  exact ⟨th, u_stable, h⟩

/-- Unconditional threshold-free Genus 0 Gromov Compactness on `[Subsingleton M]` targets (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_univ_of_subsingleton [h_sub : Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (th : Bubbling.TargetThresholds I M)
      (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) := by
  obtain ⟨th⟩ := Bubbling.exists_target_thresholds_of_subsingleton I h_sub
  obtain ⟨u_stable, h⟩ := gromov_compactness_genus_zero_of_subsingleton I th u_seq B h_nonconst h_energy
  exact ⟨th, u_stable, h⟩

/-- Unconditional Genus 0 Gromov Compactness when at least one curve `u_seq n` has
`totalEnergy < th.ε_sph` (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_exists_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_exists : ∃ n, totalEnergy I (u_seq n) < th.ε_sph) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_exists_lt_eps_sph I th u_seq h_nonconst h_jhol h_exists)

/-- Unconditional Genus 0 Gromov Compactness when at least one curve `u_seq n` has
`totalEnergy < th.h` (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_exists_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_exists : ∃ n, totalEnergy I (u_seq n) < th.h) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_exists_lt_h I th u_seq h_nonconst h_jhol h_exists)

/-- Unconditional Genus 0 Gromov Compactness when at least one curve `u_seq n` has
`totalEnergy ≤ 0` (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_exists_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_exists : ∃ n, totalEnergy I (u_seq n) ≤ 0) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_exists_nonpos_energy I th u_seq h_nonconst h_jhol h_exists)

/-- Zero-sorry Genus 0 Gromov Compactness from any `CompactnessWitness` (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_witness
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I u_seq u_lim) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy ⟨u_lim, ⟨wit⟩⟩

/-- Zero-sorry Genus 0 Gromov Compactness from a `CompactnessWitness` along a subsequence `σ` (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_subseq_witness
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_subseq_witness I u_seq σ u_lim wit)

/-- Unconditional Genus 0 Gromov Compactness when `totalEnergy I (u_seq n) < th.ε_sph` eventually (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_eventually_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq n) < th.ε_sph) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_eventually_lt_eps_sph I th u_seq h_nonconst h_jhol h_ev)

/-- Unconditional Genus 0 Gromov Compactness when `totalEnergy I (u_seq n) < th.h` eventually (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_eventually_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq n) < th.h) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_eventually_lt_h I th u_seq h_nonconst h_jhol h_ev)

/-- Unconditional Genus 0 Gromov Compactness when `totalEnergy I (u_seq n) ≤ 0` eventually (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_eventually_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq n) ≤ 0) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_eventually_nonpos_energy I th u_seq h_nonconst h_jhol h_ev)

/-- Unconditional Genus 0 Gromov Compactness when a subsequence `σ` consists of non-constant maps
and some term on `σ` has `totalEnergy < th.ε_sph` (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_subseq_nonconst_of_exists_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, u_seq (σ.1 n) z = c)
    (h_exists : ∃ n, totalEnergy I (u_seq (σ.1 n)) < th.ε_sph) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_subseq_nonconst_of_exists_lt_eps_sph I th u_seq h_jhol σ h_nc h_exists)

/-- Unconditional Genus 0 Gromov Compactness when a subsequence `σ` consists of non-constant maps
and some term on `σ` has `totalEnergy < th.h` (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_subseq_nonconst_of_exists_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, u_seq (σ.1 n) z = c)
    (h_exists : ∃ n, totalEnergy I (u_seq (σ.1 n)) < th.h) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_subseq_nonconst_of_exists_lt_h I th u_seq h_jhol σ h_nc h_exists)

/-- Unconditional Genus 0 Gromov Compactness when a subsequence `σ` consists of non-constant maps
and some term on `σ` has `totalEnergy ≤ 0` (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_subseq_nonconst_of_exists_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, u_seq (σ.1 n) z = c)
    (h_exists : ∃ n, totalEnergy I (u_seq (σ.1 n)) ≤ 0) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_subseq_nonconst_of_exists_nonpos_energy I th u_seq h_jhol σ h_nc h_exists)

/-- Unconditional Genus 0 Gromov Compactness when a subsequence `σ` consists of non-constant maps
and `totalEnergy I (u_seq (σ.1 n)) < th.ε_sph` eventually (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_subseq_nonconst_of_eventually_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, u_seq (σ.1 n) z = c)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (σ.1 n)) < th.ε_sph) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_subseq_nonconst_of_eventually_lt_eps_sph I th u_seq h_jhol σ h_nc h_ev)

/-- Unconditional Genus 0 Gromov Compactness when a subsequence `σ` consists of non-constant maps
and `totalEnergy I (u_seq (σ.1 n)) < th.h` eventually (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_subseq_nonconst_of_eventually_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, u_seq (σ.1 n) z = c)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (σ.1 n)) < th.h) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_subseq_nonconst_of_eventually_lt_h I th u_seq h_jhol σ h_nc h_ev)

/-- Unconditional Genus 0 Gromov Compactness when a subsequence `σ` consists of non-constant maps
and `totalEnergy I (u_seq (σ.1 n)) ≤ 0` eventually (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_subseq_nonconst_of_eventually_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, u_seq (σ.1 n) z = c)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (σ.1 n)) ≤ 0) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_subseq_nonconst_of_eventually_nonpos_energy I th u_seq h_jhol σ h_nc h_ev)

/-- Unconditional Genus 0 Gromov Compactness when every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_all_jhol_const
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_all_jhol_const I u_seq h_nonconst h_jhol h_all_const)

/-- Unconditional threshold-free Genus 0 Gromov Compactness when every globally `J`-holomorphic
sphere is constant (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_univ_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
    ∃ (th : Bubbling.TargetThresholds I M)
      (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) := by
  obtain ⟨th⟩ := Bubbling.exists_target_thresholds_of_all_jhol_const I h_all_const
  obtain ⟨u_stable, h⟩ := gromov_compactness_genus_zero_of_all_jhol_const I th u_seq B
    h_nonconst h_jhol h_energy h_all_const
  exact ⟨th, u_stable, h⟩

/-- Unconditional Genus 0 Gromov Compactness when at least one map `u_seq n` is non-constant and
every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_exists_nonconst_of_all_jhol_const
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_exists_nc : ∃ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_exists_nonconst_of_all_jhol_const I u_seq h_jhol h_exists_nc h_all_const)

/-- Unconditional Genus 0 Gromov Compactness when `u_seq` is eventually `J`-holomorphic and
non-constant and every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_eventually_all_jhol_const
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (N₀ : ℕ)
    (h_nonconst : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_eventually_all_jhol_const I u_seq N₀ h_nonconst h_jhol h_all_const)

/-- Unconditional threshold-free Genus 0 Gromov Compactness when `u_seq` is eventually `J`-holomorphic
and non-constant and every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_univ_of_eventually_all_jhol_const
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (N₀ : ℕ)
    (h_nonconst : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
    ∃ (th : Bubbling.TargetThresholds I M)
      (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) := by
  obtain ⟨th⟩ := Bubbling.exists_target_thresholds_of_all_jhol_const I h_all_const
  obtain ⟨u_stable, h⟩ := gromov_compactness_genus_zero_of_eventually_all_jhol_const I th u_seq B N₀
    h_nonconst h_jhol h_energy h_all_const
  exact ⟨th, u_stable, h⟩

/-- Unconditional Genus 0 Gromov Compactness when a subsequence `σ` is eventually `J`-holomorphic
and non-constant and every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_subseq_nonconst_of_eventually_all_jhol_const
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (σ : Bookkeeping.SubseqMap) (N₀ : ℕ)
    (h_nc : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, u_seq (σ.1 n) z = c)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq (σ.1 n)) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_subseq_nonconst_of_eventually_all_jhol_const I u_seq σ N₀ h_nc h_jhol h_all_const)

/-- Unconditional Genus 0 Gromov Compactness when `u_seq n` is eventually non-constant and
eventually has `totalEnergy I (u_seq n) < th.ε_sph` (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_eventually_nonconst_and_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (N₀ : ℕ)
    (h_nc : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_lt : ∀ n ≥ N₀, totalEnergy I (u_seq n) < th.ε_sph) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_eventually_nonconst_and_lt_eps_sph I th u_seq N₀ h_nc h_jhol h_lt)

/-- Unconditional Genus 0 Gromov Compactness when `u_seq n` is eventually non-constant and
eventually has `totalEnergy I (u_seq n) < th.h` (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_eventually_nonconst_and_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (N₀ : ℕ)
    (h_nc : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_lt : ∀ n ≥ N₀, totalEnergy I (u_seq n) < th.h) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_eventually_nonconst_and_lt_h I th u_seq N₀ h_nc h_jhol h_lt)

/-- Unconditional Genus 0 Gromov Compactness when `u_seq n` is eventually non-constant and
eventually has `totalEnergy I (u_seq n) ≤ 0` (`0 sorryAx`). -/
theorem gromov_compactness_genus_zero_of_eventually_nonconst_and_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (N₀ : ℕ)
    (h_nc : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_nonpos : ∀ n ≥ N₀, totalEnergy I (u_seq n) ≤ 0) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) ∧
      let P := Fintype.card { v : u_stable.tree.V // is_principal_component I u_stable v }
      let G := Fintype.card { v : u_stable.tree.V // is_ghost_component I u_stable v }
      (P * th.h ≤ B) ∧
      (1 < Fintype.card u_stable.tree.V → G + 2 ≤ P ∧ Fintype.card u_stable.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_stable.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  gromov_compactness_genus_zero_of_core I th u_seq B h_energy
    (gromov_compactness_core_of_eventually_nonconst_and_nonpos_energy I th u_seq N₀ h_nc h_jhol h_nonpos)

/-- **Universal Component and Vertex Bounds for the Master Limit** (Zero-sorry integration). -/
theorem gromov_compactness_component_bounds
    (th : Bubbling.TargetThresholds I M)
    (u_lim : StableSphereTreeLimit I (M := M)) (B : ℝ)
    (h_energy : (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B) :
    let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
    let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
    (P * th.h ≤ B) ∧
    (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
    ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) :=
  Topology.component_count_bounds I th u_lim B h_energy

#print axioms gromov_compactness_component_bounds
#print axioms gromov_compactness_genus_zero

end GromovCompactness
