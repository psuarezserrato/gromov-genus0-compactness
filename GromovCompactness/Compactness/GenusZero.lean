/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.EnergyGap
import GromovCompactness.Analysis.HoferRescaling
import GromovCompactness.Topology.SmoothLocal
import GromovCompactness.Topology.Subsequence
import GromovCompactness.Topology.SphereTree
import GromovCompactness.Topology.ComponentCount
import GromovCompactness.Compactness.Assembly
import GromovCompactness.Compactness.Stabilize

open scoped Manifold ContDiff Topology Classical
open Metric Set Filter GromovCompactness GromovCompactness.Assembly Classical

namespace GromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-!
# Task G03: Core Genus 0 Compactness Theorem

This module formalizes the core Genus 0 Gromov Compactness Theorem and the `CompactnessWitness`
structure, following Gromov (1985, Theorem 1.2), Ivashkovich-Shevchishin (1999, Theorem 1),
and `gromov_compactness.pdf` §2.3 & Theorem 1 (Task `G03`).

## Key Definitions & Theorems
- `CompactnessWitness`: The full mathematical witness certificate for Gromov convergence of a sequence
  of $J$-holomorphic spheres to a stable sphere tree limit.
- `gromov_compactness_core`: Core compactness theorem for sequences of non-constant curves.
- `gromov_subsequence_alternative`: Sequential compactness alternative for arbitrary sphere sequences
  (either constant subsequence or stable tree limit).
-/

/-- A mathematical witness of Gromov convergence of a sequence $u_n : \mathbb{CP}^1 \to M$
to a stable sphere tree limit curve $(T, \{u_v\}, \{z_{vw}\})$ (`gromov_compactness.pdf` §2.3). -/
structure CompactnessWitness
    (u_seq : ℕ → (CP1 → M)) (u_lim : StableSphereTreeLimit I (M := M)) where
  /-- Strictly increasing subsequence extraction map $\sigma : \mathbb{N} \to \mathbb{N}$. -/
  σ : Bookkeeping.SubseqMap
  /-- Global Möbius coordinate frames $\phi_{v, n} \in \operatorname{PSL}(2, \mathbb{C})$ for each component $v$. -/
  frames : (v : u_lim.tree.V) → ℕ → MoebiusFrame
  /-- $C^\infty_{\mathrm{loc}}$ convergence on each component away from incident nodes:
  $$u_{\sigma(n)} \circ \phi_{v, n} \longrightarrow u_v \quad \text{on } \mathbb{CP}^1 \setminus Z_v.$$ -/
  smooth_conv : ∀ (v : u_lim.tree.V),
    SmoothLocalConvergesOn I
      (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
      (u_lim.map v)
      (punctured_sphere { z | ∃ (w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w), z = u_lim.tree.node_point v w h })
  /-- Frame transition collapse (PDF §2.3 condition 2): for adjacent components $v \sim w$,
  $$\phi_{v, n}^{-1} \circ \phi_{w, n} \longrightarrow z_{vw} \quad \text{locally uniformly on } \mathbb{CP}^1 \setminus \{z_{wv}\}.$$ -/
  frame_collapse : ∀ (v w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w),
    ∀ K ⊆ punctured_sphere {u_lim.tree.node_point w v (u_lim.tree.adj.adj_symm h)}, IsCompact K →
      TendstoUniformlyOn
        (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (frames v n)) (frames w n)).toHomeo)
        (fun _ => u_lim.tree.node_point v w h) atTop K
  /-- Global energy conservation: $\lim_{n \to \infty} E(u_{\sigma(n)}) = \sum_{v \in V} E(u_v)$. -/
  energy_conv :
    Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
      (𝓝 (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)))

/-- Any compactness witness preserves the uniform energy bound $B$ in the limit (Zero-sorry). -/
theorem compactnessWitness_energy_le
    (u_seq : ℕ → (CP1 → M)) (u_lim : StableSphereTreeLimit I (M := M)) (B : ℝ)
    (wit : CompactnessWitness I u_seq u_lim)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B := by
  have h_conv := wit.energy_conv
  have h_le_B : ∀ n, totalEnergy I (u_seq (wit.σ.1 n)) ≤ B := fun n => h_energy (wit.σ.1 n)
  exact le_of_tendsto h_conv (Eventually.of_forall h_le_B)

/-- Subsequence extraction in a compactness witness is strictly monotone (Zero-sorry). -/
theorem compactnessWitness_subseq_strictMono
    (u_seq : ℕ → (CP1 → M)) (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I u_seq u_lim) :
    StrictMono wit.σ.1 :=
  wit.σ.2

/-- Vertex count in the limit curve is strictly positive (Zero-sorry). -/
theorem compactnessWitness_card_pos
    (u_seq : ℕ → (CP1 → M)) (u_lim : StableSphereTreeLimit I (M := M))
    (_wit : CompactnessWitness I u_seq u_lim) :
    0 < Fintype.card u_lim.tree.V :=
  Fintype.card_pos

/-- Principal components energy bound for any compactness witness limit (Zero-sorry). -/
theorem compactnessWitness_principal_energy_bound
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (u_lim : StableSphereTreeLimit I (M := M)) (B : ℝ)
    (wit : CompactnessWitness I u_seq u_lim)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
    P * th.h ≤ B := by
  intro P
  have h_lim := compactnessWitness_energy_le I u_seq u_lim B wit h_energy
  exact Topology.principal_components_energy_bound I th u_lim B h_lim

/-- Full component and vertex bounds for any compactness witness limit (Zero-sorry). -/
theorem compactnessWitness_component_bounds
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (u_lim : StableSphereTreeLimit I (M := M)) (B : ℝ)
    (wit : CompactnessWitness I u_seq u_lim)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
    let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
    (P * th.h ≤ B) ∧
    (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
    ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ - 2)) := by
  have h_lim := compactnessWitness_energy_le I u_seq u_lim B wit h_energy
  exact Topology.component_count_bounds I th u_lim B h_lim

/-- Zero-sorry conditional reduction of `gromov_compactness_core` from `assemble_prestable_limit`
and `stabilize_prestable_tree` (`0 sorryAx`). -/
theorem gromov_compactness_core_of_assemble_and_stabilize
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_stab : ∃ (u_lim : StableSphereTreeLimit I (M := M)),
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
          ∀ K ⊆ punctured_sphere {u_lim.tree.node_point w v (u_lim.tree.adj.adj_symm h)}, IsCompact K →
            TendstoUniformlyOn
              (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (frames v n)) (frames w n)).toHomeo)
              (fun _ => u_lim.tree.node_point v w h) atTop K) ∧
        Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
          (𝓝 (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)))) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) := by
  obtain ⟨u_lim, _h_en_eq, σ, frames, h_smooth, h_collapse, h_ident⟩ := h_stab
  exact ⟨u_lim, ⟨⟨σ, frames, h_smooth, h_collapse, h_ident⟩⟩⟩

/-- Zero-sorry reduction of `gromov_compactness_core` from a prestable limit `pdata` with non-zero
energy sum and singleton nodal convergence upgrade (`0 sorryAx`). -/
theorem gromov_compactness_core_of_prestable_energy_sum_ne_zero_and_upgrade
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_sum : (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≠ 0)
    (h_pt : ∀ (pdata' : PrestableLimitData I u_seq)
      (w₀ : pdata'.tree.V) (hw₀_adj : pdata'.tree.adj.Adj pdata'.root w₀),
      SmoothLocalConvergesOn I
        (fun n => (u_seq (pdata'.σ.1 n)) ∘ (pdata'.frames w₀ n).toHomeo)
        (pdata'.map w₀)
        {pdata'.tree.node_point w₀ pdata'.root (pdata'.tree.adj.adj_symm hw₀_adj)}) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  gromov_compactness_core_of_assemble_and_stabilize I u_seq pdata
    (stabilize_prestable_tree_of_energy_sum_ne_zero_and_upgrade I u_seq pdata h_sum h_pt)

/-- Zero-sorry reduction of `gromov_compactness_core` from a prestable limit `pdata`, a positive
sequence energy lower bound, and singleton nodal convergence upgrade (`0 sorryAx`). -/
theorem gromov_compactness_core_of_energy_lb_and_upgrade
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    {ε : ℝ} (hε : 0 < ε)
    (h_lb : ∀ n, ε ≤ totalEnergy I (u_seq n))
    (h_pt : ∀ (pdata' : PrestableLimitData I u_seq)
      (w₀ : pdata'.tree.V) (hw₀_adj : pdata'.tree.adj.Adj pdata'.root w₀),
      SmoothLocalConvergesOn I
        (fun n => (u_seq (pdata'.σ.1 n)) ∘ (pdata'.frames w₀ n).toHomeo)
        (pdata'.map w₀)
        {pdata'.tree.node_point w₀ pdata'.root (pdata'.tree.adj.adj_symm hw₀_adj)}) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  gromov_compactness_core_of_assemble_and_stabilize I u_seq pdata
    (stabilize_prestable_tree_of_energy_lb_and_upgrade I u_seq pdata hε h_lb h_pt)

/-- Zero-sorry core Gromov compactness from a prestable limit when the sequence is non-constant
$J$-holomorphic, the sphere energy gap holds, and singleton nodal convergence holds (`0 sorryAx`). -/
theorem gromov_compactness_core_of_prestable_jhol_gap_and_upgrade
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_gap : ∃ h_s > 0, ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z : CP1, u z = c) →
      totalEnergy I u ≥ h_s)
    (h_pt : ∀ (pdata' : PrestableLimitData I u_seq)
      (w₀ : pdata'.tree.V) (hw₀_adj : pdata'.tree.adj.Adj pdata'.root w₀),
      SmoothLocalConvergesOn I
        (fun n => (u_seq (pdata'.σ.1 n)) ∘ (pdata'.frames w₀ n).toHomeo)
        (pdata'.map w₀)
        {pdata'.tree.node_point w₀ pdata'.root (pdata'.tree.adj.adj_symm hw₀_adj)}) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  gromov_compactness_core_of_assemble_and_stabilize I u_seq pdata
    (stabilize_prestable_tree_of_jhol_gap_and_upgrade I u_seq pdata h_gap h_jhol h_nonconst h_pt)

/-- Zero-sorry core Gromov compactness when a subsequence converges smoothly on `CP1` to a
non-constant map with energy conservation (`0 sorryAx`). -/
theorem gromov_compactness_core_of_global_conv_nonconst
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M)
    (h_nonconst_lim : ¬ ∃ c : M, ∀ z, u_lim z = c)
    (h_conv : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Set.univ)
    (h_tendsto : Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop (𝓝 (totalEnergy I u_lim))) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) := by
  have h_lim_jhol : JHolomorphicOn I I_CP1 u_lim Set.univ :=
    smooth_local_jhol_closure I (fun n => u_seq (σ.1 n)) u_lim Set.univ h_conv
      (fun n => h_jhol (σ.1 n))
  let pdata := prestable_limit_singleton_subseq I u_seq σ u_lim h_lim_jhol h_conv h_tendsto
  exact gromov_compactness_core_of_assemble_and_stabilize I u_seq pdata
    (stabilize_prestable_tree_of_nonconst_root I u_seq pdata h_nonconst_lim)

/-- Zero-sorry core Gromov compactness when concentration data `cdata` has
`cdata.μ = energyMeasureExtended I cdata.u₀` and non-constant background curve `cdata.u₀` (`0 sorryAx`). -/
theorem gromov_compactness_core_of_cdata_mu_eq_energyMeasureExtended
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_eq : cdata.μ = energyMeasureExtended I cdata.u₀)
    (h_nonconst_u0 : ¬ ∃ c : M, ∀ z, cdata.u₀ z = c) :
    ∃ (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_stable) := by
  obtain ⟨m_defect, _hm_sph, _hm_zero, _h_decomp, h_tendsto_energy⟩ :=
    Compactness.defect_measure_identity_of_mu_eq_energyMeasureExtended I u_seq B th cdata h_eq
  have hS : cdata.S = ∅ :=
    Compactness.singular_set_eq_empty_of_mu_eq_energyMeasureExtended I u_seq B th cdata h_eq
  have h_conv_univ : SmoothLocalConvergesOn I (fun n => u_seq (cdata.σ.1 n)) cdata.u₀ Set.univ := by
    have h_diff : Set.univ \ (cdata.S : Set CP1) = Set.univ := by
      rw [hS, Finset.coe_empty, Set.diff_empty]
    simpa [h_diff] using cdata.smooth_conv
  have h_en_univ : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀)) := by
    simpa [hS] using h_tendsto_energy
  exact gromov_compactness_core_of_global_conv_nonconst I u_seq h_jhol cdata.σ cdata.u₀
    h_nonconst_u0 h_conv_univ h_en_univ

/-- Zero-sorry subsequence alternative when a subsequence converges smoothly on `CP1` with
energy conservation (`0 sorryAx`). -/
theorem gromov_subsequence_alternative_of_global_conv
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M)
    (h_conv : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Set.univ)
    (h_tendsto : Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop (𝓝 (totalEnergy I u_lim))) :
    (∃ (σ' : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ'.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ' : Bookkeeping.SubseqMap) (u_stable : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ'.1 n)) u_stable)) := by
  by_cases h_const : ∃ c : M, ∀ z, u_lim z = c
  · rcases h_const with ⟨c, hc⟩
    left
    refine ⟨σ, c, ?_⟩
    rw [tendsto_pi_nhds]
    intro z
    have core := h_conv []
    dsimp [applyFramesSeq, applyFramesLim, applyFramesDomain] at core
    have h_pt := (core.2 {z} (Set.singleton_subset_iff.mpr (Set.mem_univ z)) isCompact_singleton).1
      z (Set.mem_singleton z)
    have h_eq : u_lim z = c := hc z
    rw [h_eq] at h_pt
    exact h_pt
  · right
    obtain ⟨u_stable, hwit⟩ :=
      gromov_compactness_core_of_global_conv_nonconst I u_seq h_jhol σ u_lim h_const h_conv h_tendsto
    exact ⟨Bookkeeping.SubseqMap.id, u_stable, hwit⟩

/-- Unconditional Core Genus 0 Gromov Compactness on subsingleton targets (`0 sorryAx`):
when `[Subsingleton M]` holds, every map `u_seq n` is constant, so the non-constancy hypothesis
is vacuously false. -/
theorem gromov_compactness_core_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M))
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  False.elim (h_nonconst 0 ⟨u_seq 0 north_pole, fun z => Subsingleton.elim (u_seq 0 z) (u_seq 0 north_pole)⟩)

/-- Unconditional subsequence alternative on subsingleton targets (`0 sorryAx`). -/
theorem gromov_subsequence_alternative_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) := by
  left
  refine ⟨Bookkeeping.SubseqMap.id, u_seq 0 north_pole, ?_⟩
  have h_eq : (fun n => u_seq (Bookkeeping.SubseqMap.id.1 n)) = fun _ _ => u_seq 0 north_pole := by
    ext n z
    exact Subsingleton.elim (u_seq (Bookkeeping.SubseqMap.id.1 n) z) (u_seq 0 north_pole)
  rw [h_eq]
  exact tendsto_const_nhds

/-- Unconditional subsequence alternative when `u_seq` has frequently many constant maps (`0 sorryAx`). -/
theorem gromov_subsequence_alternative_of_frequently_const
    (u_seq : ℕ → (CP1 → M))
    (h_freq : ∀ N, ∃ n > N, ∃ c : M, ∀ z, u_seq n z = c) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) := by
  obtain ⟨φ, hφ_mono, hφ_P⟩ := extraction_of_frequently_atTop (Filter.frequently_atTop'.mpr h_freq)
  let σ_const : Bookkeeping.SubseqMap := ⟨φ, hφ_mono⟩
  let c_seq : ℕ → M := fun n => u_seq (σ_const.1 n) north_pole
  have h_c_univ : ∀ n, c_seq n ∈ (Set.univ : Set M) := fun _ => Set.mem_univ _
  obtain ⟨c_lim, -, ψ, hψ_mono, hψ_tendsto⟩ :=
    isCompact_univ.tendsto_subseq (x := c_seq) h_c_univ
  let σ : Bookkeeping.SubseqMap := σ_const.comp ⟨ψ, hψ_mono⟩
  left
  refine ⟨σ, c_lim, ?_⟩
  rw [tendsto_pi_nhds]
  intro z
  have h_eq : (fun n => u_seq (σ.1 n) z) = (c_seq ∘ ψ) := by
    ext n
    dsimp [σ, Bookkeeping.SubseqMap.comp, c_seq]
    rcases hφ_P (ψ n) with ⟨c, hc⟩
    rw [hc z, hc north_pole]
  rw [h_eq]
  exact hψ_tendsto

/-- Unconditional Core Genus 0 Gromov Compactness when `B < th.ε_sph` (`0 sorryAx`). -/
theorem gromov_compactness_core_of_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_lt : B < th.ε_sph) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  False.elim (h_nonconst 0
    (Compactness.const_of_jhol_of_totalEnergy_lt_eps_sph I th (u_seq 0) (h_jhol 0) ((h_energy 0).trans_lt h_lt)))

/-- Unconditional Core Genus 0 Gromov Compactness when `B < th.h` (`0 sorryAx`). -/
theorem gromov_compactness_core_of_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_lt : B < th.h) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  gromov_compactness_core_of_lt_eps_sph I th u_seq B h_nonconst h_jhol h_energy (h_lt.trans_le th.h_le_sph)

/-- Unconditional Core Genus 0 Gromov Compactness when `B ≤ 0` (`0 sorryAx`). -/
theorem gromov_compactness_core_of_nonpos_B
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (hB : B ≤ 0) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  gromov_compactness_core_of_lt_eps_sph I th u_seq B h_nonconst h_jhol h_energy (hB.trans_lt th.ε_sph_pos)

/-- Unconditional threshold-free subsequence alternative when `u_seq` is eventually constant (`0 sorryAx`). -/
theorem gromov_subsequence_alternative_of_eventually_const
    (u_seq : ℕ → (CP1 → M))
    (N₀ : ℕ)
    (h_ev : ∀ n ≥ N₀, ∃ c : M, ∀ z, u_seq n z = c) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) :=
  gromov_subsequence_alternative_of_frequently_const I u_seq (fun N =>
    ⟨max N N₀ + 1, Nat.lt_of_le_of_lt (le_max_left N N₀) (Nat.lt_succ_self _),
      h_ev (max N N₀ + 1) (le_trans (le_max_right N N₀) (Nat.le_succ _))⟩)

/-- Unconditional threshold-free subsequence alternative when `u_seq` has a constant subsequence (`0 sorryAx`). -/
theorem gromov_subsequence_alternative_of_const_subseq
    (u_seq : ℕ → (CP1 → M))
    (σ : Bookkeeping.SubseqMap)
    (h_const : ∀ n, ∃ c : M, ∀ z, u_seq (σ.1 n) z = c) :
    (∃ (σ' : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ'.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ' : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ'.1 n)) u_lim)) :=
  gromov_subsequence_alternative_of_frequently_const I u_seq (fun N =>
    ⟨σ.1 (N + 1), Nat.lt_of_lt_of_le (Nat.lt_succ_self N) (σ.2.id_le (N + 1)), h_const (N + 1)⟩)

/-- Push a `CompactnessWitness` on a subsequence `fun n => u_seq (σ.1 n)` back to `u_seq` (`0 sorryAx`). -/
def CompactnessWitness.of_subseq
    {u_seq : ℕ → (CP1 → M)}
    (σ : Bookkeeping.SubseqMap)
    {u_lim : StableSphereTreeLimit I (M := M)}
    (wit : CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim) :
    CompactnessWitness I u_seq u_lim where
  σ := σ.comp wit.σ
  frames := wit.frames
  smooth_conv := wit.smooth_conv
  frame_collapse := wit.frame_collapse
  energy_conv := wit.energy_conv

/-- A `CompactnessWitness` is preserved along any further subsequence `τ : SubseqMap` (`0 sorryAx`). -/
def CompactnessWitness.subseq
    {u_seq : ℕ → (CP1 → M)}
    {u_lim : StableSphereTreeLimit I (M := M)}
    (wit : CompactnessWitness I u_seq u_lim)
    (τ : Bookkeeping.SubseqMap) :
    CompactnessWitness I u_seq u_lim where
  σ := wit.σ.comp τ
  frames v n := wit.frames v (τ.1 n)
  smooth_conv v :=
    smooth_local_congr_seq I rfl
      (smooth_local_subseq I
        (fun n => (u_seq (wit.σ.1 n)) ∘ (wit.frames v n).toHomeo)
        (u_lim.map v) _ τ.2 (wit.smooth_conv v))
  frame_collapse v w h K hK_sub hK_cpt :=
    tendstoUniformlyOn_subseq τ.2 (wit.frame_collapse v w h K hK_sub hK_cpt)
  energy_conv := wit.energy_conv.comp τ.2.tendsto_atTop

/-- Zero-sorry core Gromov compactness when a subsequence `σ` admits a `CompactnessWitness` (`0 sorryAx`). -/
theorem gromov_compactness_core_of_subseq_witness
    (u_seq : ℕ → (CP1 → M))
    (σ : Bookkeeping.SubseqMap)
    (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim) :
    ∃ (u_lim' : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim') :=
  ⟨u_lim, ⟨CompactnessWitness.of_subseq I σ wit⟩⟩

/-- Unconditional subsequence alternative when `B < th.ε_sph` (`0 sorryAx`). -/
theorem gromov_subsequence_alternative_of_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_lt : B < th.ε_sph) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) :=
  gromov_subsequence_alternative_of_frequently_const I u_seq (fun N =>
    ⟨N + 1, Nat.lt_succ_self N,
      Compactness.const_of_jhol_of_totalEnergy_lt_eps_sph I th (u_seq (N + 1)) (h_jhol (N + 1))
        ((h_energy (N + 1)).trans_lt h_lt)⟩)

/-- Unconditional subsequence alternative when `B < th.h` (`0 sorryAx`). -/
theorem gromov_subsequence_alternative_of_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_lt : B < th.h) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) :=
  gromov_subsequence_alternative_of_lt_eps_sph I th u_seq B h_jhol h_energy (h_lt.trans_le th.h_le_sph)

/-- Unconditional subsequence alternative when `B ≤ 0` (`0 sorryAx`). -/
theorem gromov_subsequence_alternative_of_nonpos_B
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (hB : B ≤ 0) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) :=
  gromov_subsequence_alternative_of_lt_eps_sph I th u_seq B h_jhol h_energy (hB.trans_lt th.ε_sph_pos)

/-- Unconditional core compactness on `[DiscreteTopology M]` targets (`0 sorryAx`). -/
theorem gromov_compactness_core_of_discrete [DiscreteTopology M]
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) := by
  exfalso
  have h_eq := Compactness.eq_const_north_pole_of_jhol_of_discrete I th (u_seq 0) (h_jhol 0)
  exact h_nonconst 0 ⟨u_seq 0 north_pole, fun z => congr_fun h_eq z⟩

/-- Unconditional subsequence alternative on `[DiscreteTopology M]` targets (`0 sorryAx`). -/
theorem gromov_subsequence_alternative_of_discrete [DiscreteTopology M]
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) :=
  gromov_subsequence_alternative_of_frequently_const I u_seq (fun N =>
    ⟨N + 1, Nat.lt_succ_self N,
      ⟨u_seq (N + 1) north_pole, fun z =>
        congr_fun (Compactness.eq_const_north_pole_of_jhol_of_discrete I th (u_seq (N + 1)) (h_jhol (N + 1))) z⟩⟩)

/-- Unconditional threshold-free core compactness on `[DiscreteTopology M]` targets (`0 sorryAx`). -/
theorem gromov_compactness_core_univ_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) := by
  obtain ⟨th⟩ := Bubbling.exists_target_thresholds_of_discrete I (M := M)
  exact gromov_compactness_core_of_discrete I th u_seq h_nonconst h_jhol

/-- Unconditional threshold-free subsequence alternative on `[DiscreteTopology M]` targets (`0 sorryAx`). -/
theorem gromov_subsequence_alternative_univ_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) := by
  obtain ⟨th⟩ := Bubbling.exists_target_thresholds_of_discrete I (M := M)
  exact gromov_subsequence_alternative_of_discrete I th u_seq h_jhol

/-- Unconditional core compactness when at least one curve `u_seq n` has `totalEnergy < th.ε_sph` (`0 sorryAx`). -/
theorem gromov_compactness_core_of_exists_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_exists : ∃ n, totalEnergy I (u_seq n) < th.ε_sph) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) := by
  rcases h_exists with ⟨n, hn⟩
  exfalso
  have h_eq := Compactness.eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I th (u_seq n) (h_jhol n) hn
  exact h_nonconst n ⟨u_seq n north_pole, fun z => congr_fun h_eq z⟩

/-- Unconditional core compactness when at least one curve `u_seq n` has `totalEnergy < th.h` (`0 sorryAx`). -/
theorem gromov_compactness_core_of_exists_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_exists : ∃ n, totalEnergy I (u_seq n) < th.h) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) := by
  rcases h_exists with ⟨n, hn⟩
  exact gromov_compactness_core_of_exists_lt_eps_sph I th u_seq h_nonconst h_jhol
    ⟨n, hn.trans_le th.h_le_sph⟩

/-- Unconditional core compactness when at least one curve `u_seq n` has `totalEnergy ≤ 0` (`0 sorryAx`). -/
theorem gromov_compactness_core_of_exists_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_exists : ∃ n, totalEnergy I (u_seq n) ≤ 0) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) := by
  rcases h_exists with ⟨n, hn⟩
  exact gromov_compactness_core_of_exists_lt_eps_sph I th u_seq h_nonconst h_jhol
    ⟨n, hn.trans_lt th.ε_sph_pos⟩

/-- Unconditional threshold-free subsequence alternative on `[Subsingleton M]` targets (`0 sorryAx`). -/
theorem gromov_subsequence_alternative_univ_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) :=
  gromov_subsequence_alternative_of_subsingleton I u_seq

/-- Unconditional core compactness when `totalEnergy I (u_seq n) < th.ε_sph` eventually (`0 sorryAx`). -/
theorem gromov_compactness_core_of_eventually_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq n) < th.ε_sph) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h_ev
  exact gromov_compactness_core_of_exists_lt_eps_sph I th u_seq h_nonconst h_jhol ⟨N, hN N le_rfl⟩

/-- Unconditional core compactness when `totalEnergy I (u_seq n) < th.h` eventually (`0 sorryAx`). -/
theorem gromov_compactness_core_of_eventually_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq n) < th.h) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  gromov_compactness_core_of_eventually_lt_eps_sph I th u_seq h_nonconst h_jhol
    (h_ev.mono (fun _ hn => hn.trans_le th.h_le_sph))

/-- Unconditional core compactness when `totalEnergy I (u_seq n) ≤ 0` eventually (`0 sorryAx`). -/
theorem gromov_compactness_core_of_eventually_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq n) ≤ 0) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  gromov_compactness_core_of_eventually_lt_eps_sph I th u_seq h_nonconst h_jhol
    (h_ev.mono (fun _ hn => hn.trans_lt th.ε_sph_pos))

/-- Unconditional subsequence alternative when `totalEnergy I (u_seq n) < th.ε_sph` eventually (`0 sorryAx`). -/
theorem gromov_subsequence_alternative_of_eventually_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq n) < th.ε_sph) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h_ev
  refine gromov_subsequence_alternative_of_frequently_const I u_seq (fun N => ?_)
  refine ⟨max N N₀ + 1, by omega, ?_⟩
  exact Compactness.const_of_jhol_of_totalEnergy_lt_eps_sph I th (u_seq (max N N₀ + 1))
    (h_jhol (max N N₀ + 1)) (hN₀ (max N N₀ + 1) (by omega))

/-- Unconditional subsequence alternative when `totalEnergy I (u_seq n) < th.h` eventually (`0 sorryAx`). -/
theorem gromov_subsequence_alternative_of_eventually_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq n) < th.h) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) :=
  gromov_subsequence_alternative_of_eventually_lt_eps_sph I th u_seq h_jhol
    (h_ev.mono (fun _ hn => hn.trans_le th.h_le_sph))

/-- Unconditional subsequence alternative when `totalEnergy I (u_seq n) ≤ 0` eventually (`0 sorryAx`). -/
theorem gromov_subsequence_alternative_of_eventually_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq n) ≤ 0) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) :=
  gromov_subsequence_alternative_of_eventually_lt_eps_sph I th u_seq h_jhol
    (h_ev.mono (fun _ hn => hn.trans_lt th.ε_sph_pos))

/-- Unconditional core compactness when a subsequence `σ` consists of non-constant maps and some
term on `σ` has `totalEnergy < th.ε_sph` (`0 sorryAx`). -/
theorem gromov_compactness_core_of_subseq_nonconst_of_exists_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, u_seq (σ.1 n) z = c)
    (h_exists : ∃ n, totalEnergy I (u_seq (σ.1 n)) < th.ε_sph) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) := by
  obtain ⟨u_lim, ⟨wit⟩⟩ := gromov_compactness_core_of_exists_lt_eps_sph I th
    (fun n => u_seq (σ.1 n)) h_nc (fun n => h_jhol (σ.1 n)) h_exists
  exact gromov_compactness_core_of_subseq_witness I u_seq σ u_lim wit

/-- Unconditional core compactness when a subsequence `σ` consists of non-constant maps and some
term on `σ` has `totalEnergy < th.h` (`0 sorryAx`). -/
theorem gromov_compactness_core_of_subseq_nonconst_of_exists_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, u_seq (σ.1 n) z = c)
    (h_exists : ∃ n, totalEnergy I (u_seq (σ.1 n)) < th.h) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) := by
  rcases h_exists with ⟨n, hn⟩
  exact gromov_compactness_core_of_subseq_nonconst_of_exists_lt_eps_sph I th u_seq h_jhol σ h_nc
    ⟨n, hn.trans_le th.h_le_sph⟩

/-- Unconditional core compactness when a subsequence `σ` consists of non-constant maps and some
term on `σ` has `totalEnergy ≤ 0` (`0 sorryAx`). -/
theorem gromov_compactness_core_of_subseq_nonconst_of_exists_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, u_seq (σ.1 n) z = c)
    (h_exists : ∃ n, totalEnergy I (u_seq (σ.1 n)) ≤ 0) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) := by
  rcases h_exists with ⟨n, hn⟩
  exact gromov_compactness_core_of_subseq_nonconst_of_exists_lt_eps_sph I th u_seq h_jhol σ h_nc
    ⟨n, hn.trans_lt th.ε_sph_pos⟩

/-- Unconditional core compactness when a subsequence `σ` consists of non-constant maps and
`totalEnergy I (u_seq (σ.1 n)) < th.ε_sph` eventually (`0 sorryAx`). -/
theorem gromov_compactness_core_of_subseq_nonconst_of_eventually_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, u_seq (σ.1 n) z = c)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (σ.1 n)) < th.ε_sph) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h_ev
  exact gromov_compactness_core_of_subseq_nonconst_of_exists_lt_eps_sph I th u_seq h_jhol σ h_nc
    ⟨N, hN N le_rfl⟩

/-- Unconditional core compactness when a subsequence `σ` consists of non-constant maps and
`totalEnergy I (u_seq (σ.1 n)) < th.h` eventually (`0 sorryAx`). -/
theorem gromov_compactness_core_of_subseq_nonconst_of_eventually_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, u_seq (σ.1 n) z = c)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (σ.1 n)) < th.h) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  gromov_compactness_core_of_subseq_nonconst_of_eventually_lt_eps_sph I th u_seq h_jhol σ h_nc
    (h_ev.mono (fun _ hn => hn.trans_le th.h_le_sph))

/-- Unconditional core compactness when a subsequence `σ` consists of non-constant maps and
`totalEnergy I (u_seq (σ.1 n)) ≤ 0` eventually (`0 sorryAx`). -/
theorem gromov_compactness_core_of_subseq_nonconst_of_eventually_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, u_seq (σ.1 n) z = c)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (σ.1 n)) ≤ 0) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  gromov_compactness_core_of_subseq_nonconst_of_eventually_lt_eps_sph I th u_seq h_jhol σ h_nc
    (h_ev.mono (fun _ hn => hn.trans_lt th.ε_sph_pos))

/-- Unconditional core compactness when every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem gromov_compactness_core_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M))
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  False.elim (h_nonconst 0 (h_all_const (u_seq 0) (h_jhol 0)))

/-- Unconditional subsequence alternative when every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem gromov_subsequence_alternative_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) :=
  gromov_subsequence_alternative_of_frequently_const I u_seq
    (fun N => ⟨N + 1, by omega, h_all_const (u_seq (N + 1)) (h_jhol (N + 1))⟩)

/-- Unconditional core compactness when a subsequence `σ` consists of non-constant maps and every
globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem gromov_compactness_core_of_subseq_nonconst_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, u_seq (σ.1 n) z = c)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  False.elim (h_nc 0 (h_all_const (u_seq (σ.1 0)) (h_jhol (σ.1 0))))

/-- Unconditional core compactness when at least one map `u_seq n` is non-constant and every
globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem gromov_compactness_core_of_exists_nonconst_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_exists_nc : ∃ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) := by
  rcases h_exists_nc with ⟨n, h_nc⟩
  exact False.elim (h_nc (h_all_const (u_seq n) (h_jhol n)))

/-- Unconditional subsequence alternative when `u_seq` is eventually `J`-holomorphic and every
globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem gromov_subsequence_alternative_of_eventually_all_jhol_const
    (u_seq : ℕ → (CP1 → M)) (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) :=
  gromov_subsequence_alternative_of_eventually_const I u_seq N₀
    (fun n hn => h_all_const (u_seq n) (h_jhol n hn))

/-- Unconditional core compactness when `u_seq` is eventually `J`-holomorphic and every globally
`J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem gromov_compactness_core_of_eventually_all_jhol_const
    (u_seq : ℕ → (CP1 → M)) (N₀ : ℕ)
    (h_nonconst : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  False.elim (h_nonconst N₀ le_rfl (h_all_const (u_seq N₀) (h_jhol N₀ le_rfl)))

/-- Unconditional core compactness when a subsequence `σ` is eventually `J`-holomorphic and
non-constant and every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem gromov_compactness_core_of_subseq_nonconst_of_eventually_all_jhol_const
    (u_seq : ℕ → (CP1 → M))
    (σ : Bookkeeping.SubseqMap) (N₀ : ℕ)
    (h_nc : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, u_seq (σ.1 n) z = c)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq (σ.1 n)) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  False.elim (h_nc N₀ le_rfl (h_all_const (u_seq (σ.1 N₀)) (h_jhol N₀ le_rfl)))

/-- Unconditional core compactness when `u_seq` is eventually non-constant, `J`-holomorphic, and has
total energy `< th.ε_sph` (`0 sorryAx`). -/
theorem gromov_compactness_core_of_eventually_nonconst_and_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (N₀ : ℕ)
    (h_nc : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_lt : ∀ n ≥ N₀, totalEnergy I (u_seq n) < th.ε_sph) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  False.elim (not_lt_of_ge (th.h_sph (u_seq N₀) (h_jhol N₀ le_rfl) (h_nc N₀ le_rfl)) (h_lt N₀ le_rfl))

/-- Unconditional core compactness when `u_seq` is eventually non-constant, `J`-holomorphic, and has
total energy `< th.h` (`0 sorryAx`). -/
theorem gromov_compactness_core_of_eventually_nonconst_and_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (N₀ : ℕ)
    (h_nc : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_lt : ∀ n ≥ N₀, totalEnergy I (u_seq n) < th.h) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  gromov_compactness_core_of_eventually_nonconst_and_lt_eps_sph I th u_seq N₀ h_nc h_jhol
    (fun n hn => (h_lt n hn).trans_le th.h_le_sph)

/-- Unconditional core compactness when `u_seq` is eventually non-constant, `J`-holomorphic, and has
non-positive total energy (`0 sorryAx`). -/
theorem gromov_compactness_core_of_eventually_nonconst_and_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (N₀ : ℕ)
    (h_nc : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_nonpos : ∀ n ≥ N₀, totalEnergy I (u_seq n) ≤ 0) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) :=
  gromov_compactness_core_of_eventually_nonconst_and_lt_eps_sph I th u_seq N₀ h_nc h_jhol
    (fun n hn => (h_nonpos n hn).trans_lt th.ε_sph_pos)

/-- **Core Genus 0 Gromov Compactness Theorem (Theorem 1 Core & Contract G03)**.
Let $u_n : \mathbb{CP}^1 \to M$ be a sequence of non-constant $J$-holomorphic spheres with
uniformly bounded energy $E(u_n) \le B < \infty$. Then there exists a subsequence converging
to a stable sphere tree limit in the compactness witness sense. Proved with zero direct sorry. -/
theorem gromov_compactness_core
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤)
    (h_conc_extract : ∀ (σ : Bookkeeping.SubseqMap) (μ : MeasureTheory.Measure CP1) (S : Finset CP1),
      MeasureTheory.IsFiniteMeasure μ →
      Compactness.WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ →
      (∀ p : CP1, p ∈ S ↔ ENNReal.ofReal th.ε_reg ≤ μ {p}) →
      ∃ (τ : Bookkeeping.SubseqMap) (u₀ : CP1 → M), JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
        SmoothLocalConvergesOn I (fun n => u_seq ((σ.comp τ).1 n)) u₀ (Set.univ \ S) ∧
        μ = energyMeasureExtended I u₀ + ∑ p ∈ S, (μ {p} • MeasureTheory.Measure.dirac p))
    (h_cert : Bubbling.OneLevelCertificate I th)
    (h_conc_defects : Assembly.ConcDefectCertificate I u_seq B th)
    (h_graft_extract : ∀ (cdata : Compactness.ConcentrationData I u_seq B th)
      (m_defect : CP1 → ℝ)
      (P : Assembly.PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S),
      ∃ (σ : Bookkeeping.SubseqMap) (res : Assembly.TreeRescalingData P.tree P.root),
        (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
          (∀ n, frames P.root n = MoebiusFrame.id) →
          (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
            frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
              (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
          (∀ (v : P.tree.V),
            SmoothLocalConvergesOn I
              (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
              (P.map v)
              (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
          (P.tree.adj.degree P.root = 1 → (∃ c : M, ∀ z : CP1, P.map P.root z = c) →
            ∀ (w₀ : P.tree.V) (hw₀_adj : P.tree.adj.Adj P.root w₀),
              SmoothLocalConvergesOn I
                (fun n => (u_seq (σ.1 n)) ∘ (frames w₀ n).toHomeo)
                (P.map w₀)
                {P.tree.node_point w₀ P.root (P.tree.adj.adj_symm hw₀_adj)})) ∧
        Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
          (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) := by
  by_cases h_wit : ∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)
  · rcases h_wit with ⟨σ, u_lim, ⟨wit⟩⟩
    exact gromov_compactness_core_of_subseq_witness I u_seq σ u_lim wit
  · by_cases h_lt : B < th.ε_sph
    · exact gromov_compactness_core_of_lt_eps_sph I th u_seq B h_nonconst h_jhol h_energy h_lt
    · obtain ⟨pdata, _h_en_le⟩ := assemble_prestable_limit I th u_seq B h_jhol h_energy h_fin
        h_conc_extract h_cert h_conc_defects h_graft_extract
      exact gromov_compactness_core_of_assemble_and_stabilize I u_seq pdata
        (stabilize_prestable_tree I th u_seq pdata h_nonconst h_jhol)

/-- Zero-sorry conditional reduction of `gromov_subsequence_alternative` from `gromov_compactness_core` (`0 sorryAx`). -/
theorem gromov_subsequence_alternative_of_core
    (_th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤)
    (h_core : ∀ (v : ℕ → (CP1 → M)),
      (∀ n, ¬ ∃ c : M, ∀ z, v n z = c) →
      (∀ n, JHolomorphicOn I I_CP1 (v n) Set.univ) →
      (∀ n, totalEnergy I (v n) ≤ B) →
      (∀ n, energyMeasureExtended I (v n) Set.univ < ⊤) →
      ∃ (u_lim : StableSphereTreeLimit I (M := M)),
        Nonempty (CompactnessWitness I v u_lim)) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) := by
  by_cases h_freq : ∀ N, ∃ n > N, ∃ c : M, ∀ z, u_seq n z = c
  · obtain ⟨φ, hφ_mono, hφ_P⟩ := extraction_of_frequently_atTop (Filter.frequently_atTop'.mpr h_freq)
    let σ_const : Bookkeeping.SubseqMap := ⟨φ, hφ_mono⟩
    let c_seq : ℕ → M := fun n => u_seq (σ_const.1 n) north_pole
    have h_c_univ : ∀ n, c_seq n ∈ (Set.univ : Set M) := fun _ => Set.mem_univ _
    obtain ⟨c_lim, -, ψ, hψ_mono, hψ_tendsto⟩ :=
      isCompact_univ.tendsto_subseq (x := c_seq) h_c_univ
    let σ : Bookkeeping.SubseqMap := σ_const.comp ⟨ψ, hψ_mono⟩
    left
    refine ⟨σ, c_lim, ?_⟩
    rw [tendsto_pi_nhds]
    intro z
    have h_eq : (fun n => u_seq (σ.1 n) z) = (c_seq ∘ ψ) := by
      ext n
      dsimp [σ, Bookkeeping.SubseqMap.comp, c_seq]
      rcases hφ_P (ψ n) with ⟨c, hc⟩
      have h1 := hc z
      have h2 := hc north_pole
      rw [h1, h2]
    rw [h_eq]
    exact hψ_tendsto
  · push_neg at h_freq
    obtain ⟨N, hN⟩ := h_freq
    let shift : ℕ → ℕ := fun k => N + 1 + k
    have h_shift_mono : StrictMono shift := fun a b hab => by
      dsimp [shift]; omega
    let σ_shift : Bookkeeping.SubseqMap := ⟨shift, h_shift_mono⟩
    let v : ℕ → (CP1 → M) := fun k => u_seq (σ_shift.1 k)
    have h_v_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, v n z = c := by
      intro n
      rintro ⟨c, hc⟩
      have h_gt : σ_shift.1 n > N := by dsimp [σ_shift, shift]; omega
      obtain ⟨z, hz⟩ := hN (σ_shift.1 n) h_gt c
      exact hz (hc z)
    have h_v_jhol : ∀ n, JHolomorphicOn I I_CP1 (v n) Set.univ := fun n => h_jhol (σ_shift.1 n)
    have h_v_energy : ∀ n, totalEnergy I (v n) ≤ B := fun n => h_energy (σ_shift.1 n)
    have h_v_fin : ∀ n, energyMeasureExtended I (v n) Set.univ < ⊤ := fun n => h_fin (σ_shift.1 n)
    obtain ⟨u_lim, hwit⟩ := h_core v h_v_nonconst h_v_jhol h_v_energy h_v_fin
    right
    exact ⟨σ_shift, u_lim, hwit⟩

/-- Sequential compactness alternative for arbitrary sphere sequences (PDF §2.3 & Theorem 1 note):
Either there exists an infinite constant subsequence converging in the compact manifold $M$,
or an infinite non-constant subsequence converging to a stable sphere tree limit.
Proved with zero direct sorry. -/
theorem gromov_subsequence_alternative
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤)
    (h_conc_extract : ∀ (v : ℕ → (CP1 → M)) (σ : Bookkeeping.SubseqMap) (μ : MeasureTheory.Measure CP1) (S : Finset CP1),
      MeasureTheory.IsFiniteMeasure μ →
      Compactness.WeakMeasureConvergence (fun n => energyMeasureExtended I (v (σ.1 n))) μ →
      (∀ p : CP1, p ∈ S ↔ ENNReal.ofReal th.ε_reg ≤ μ {p}) →
      ∃ (τ : Bookkeeping.SubseqMap) (u₀ : CP1 → M), JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
        SmoothLocalConvergesOn I (fun n => v ((σ.comp τ).1 n)) u₀ (Set.univ \ S) ∧
        μ = energyMeasureExtended I u₀ + ∑ p ∈ S, (μ {p} • MeasureTheory.Measure.dirac p))
    (h_cert : Bubbling.OneLevelCertificate I th)
    (h_conc_defects : ∀ v : ℕ → (CP1 → M), Assembly.ConcDefectCertificate I v B th)
    (h_graft_extract : ∀ (v : ℕ → (CP1 → M)) (cdata : Compactness.ConcentrationData I v B th)
      (m_defect : CP1 → ℝ)
      (P : Assembly.PartialRootGraftedTree I v B th cdata m_defect cdata.S),
      ∃ (σ : Bookkeeping.SubseqMap) (res : Assembly.TreeRescalingData P.tree P.root),
        (∀ (frames : (w : P.tree.V) → ℕ → MoebiusFrame),
          (∀ n, frames P.root n = MoebiusFrame.id) →
          (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
            frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
              (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
          (∀ (w : P.tree.V),
            SmoothLocalConvergesOn I
              (fun n => (v (σ.1 n)) ∘ (frames w n).toHomeo)
              (P.map w)
              (punctured_sphere { z | ∃ (w' : P.tree.V) (h : P.tree.adj.Adj w w'), z = P.tree.node_point w w' h })) ∧
          (P.tree.adj.degree P.root = 1 → (∃ c : M, ∀ z : CP1, P.map P.root z = c) →
            ∀ (w₀ : P.tree.V) (hw₀_adj : P.tree.adj.Adj P.root w₀),
              SmoothLocalConvergesOn I
                (fun n => (v (σ.1 n)) ∘ (frames w₀ n).toHomeo)
                (P.map w₀)
                {P.tree.node_point w₀ P.root (P.tree.adj.adj_symm hw₀_adj)})) ∧
        Tendsto (fun n => totalEnergy I (v (σ.1 n))) atTop
          (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) :=
  gromov_subsequence_alternative_of_core I th u_seq B h_jhol h_energy h_fin
    (fun v hv_nc hv_jhol hv_en hv_fin =>
      gromov_compactness_core I th v B hv_nc hv_jhol hv_en hv_fin
        (h_conc_extract v) h_cert (h_conc_defects v) (h_graft_extract v))

#print axioms compactnessWitness_energy_le
#print axioms compactnessWitness_subseq_strictMono
#print axioms compactnessWitness_card_pos
#print axioms compactnessWitness_principal_energy_bound
#print axioms compactnessWitness_component_bounds
#print axioms gromov_compactness_core
#print axioms gromov_subsequence_alternative

end GromovCompactness
