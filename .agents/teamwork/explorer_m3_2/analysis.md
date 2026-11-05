# Technical Analysis: P0-11 Core Call-Graph Wiring Components 1–4 (Task G03-W)

**Author:** `explorer_m3_2` (Teamwork Explorer)  
**Date:** 2026-11-05  
**Scope:** Components 1–4 of `core_wiring_plan.md` / Task `G03-W` for Milestone 3

---

## 1. Executive Summary

This report establishes kernel-verified Lean 4 blueprints for the complete wiring of the core Genus 0 Gromov Compactness call graph (Task P0-11 / G03-W, Components 1–4). Prior to this task, the top-level theorem `gromov_compactness_core` was an isolated `sorry` stub disconnected from the underlying bubbling, assembly, and measure-theoretic foundations.

The formal architecture developed and verified herein establishes the call graph:

```mermaid
flowchart TD
    G03[gromov_compactness_core G03] --> G01[assemble_prestable_limit G01]
    G03 --> G02[stabilize_prestable_tree G02]
    G03Alt[gromov_subsequence_alternative G03] --> G03
    G03Alt --> CompactM[CompactSpace M extraction]

    G02 --> Prune1[prune_degree_one_root deg=1]
    G02 --> Suppress2[suppress_degree_two_root deg=2]
    G02 --> StableRoot[stabilize_prestable_tree_of_stable_root deg≥3]

    G01 --> C02[exists_concentration_data C02]
    G01 --> C03[defect_measure_identity C03]
    G01 --> Singl[prestable_limit_singleton_subseq S=∅]
    G01 --> B07[resolve_single_defect_tree B07]
    G01 --> GraftRoot[graft_defect_trees_to_root]

    B07 --> RankInd[energy_rank_induction]
    B07 --> B04[exists_one_level_decomp B04]
    B07 --> B07Empty[local_defect_tree_of_empty_children q=∅]
    B07 --> B06[child_rank_strict_decrease B06]
    B07 --> GraftChild[graft_child_defect_trees q≠∅]

    C02 --> C01[weak_energy_measure_compactness C01]
    C01 --> WeakMeas[weak_measure_compactness]
    C02 --> C02Props[concentration_singular_set_properties]
    C02 --> A06A12[extract_smooth_limit_off_singular_set A06+A12]
```

Every top-level declaration in scope:
1. `gromov_compactness_core` (`G03`)
2. `gromov_subsequence_alternative` (`G03`)
3. `stabilize_prestable_tree` (`G02`)
4. `stabilize_prestable_tree_of_stable_root` (`G02`)
5. `stabilize_prestable_tree_of_nonconst_root` (`G02`)
6. `assemble_prestable_limit` (`G01`)
7. `resolve_single_defect_tree` (`B07`)
8. `weak_energy_measure_compactness` (`C01`)
9. `exists_concentration_data` (`C02`)

is proved with **ZERO DIRECT `sorry`**, reducing all remaining obligations exclusively to well-scoped, named leaf lemmas.

---

## 2. Component 1: `Stabilize.lean` (G02) & `GenusZero.lean` (G03)

### 2.1 Problem Analysis
In `Stabilize.lean`, `stabilize_prestable_tree` had a `sorry` body and only claimed the existence of `frames` and `smooth_conv`. It dropped:
- `σ : SubseqMap`
- `frame_collapse : ∀ (v w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w), ...`
- `energy_conv : Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop (𝓝 (∑ v, totalEnergy I (u_lim.map v)))`

These three fields are essential fields of `CompactnessWitness` in `GenusZero.lean`. Because `PrestableLimitData` already contains `σ`, `frames`, `smooth_conv`, `frame_collapse`, and `energy_ident`, the base stabilization case where the root is stable (`stabilize_prestable_tree_of_stable_root`) can forward all 5 fields directly with zero `sorry`.

### 2.2 Machine-Checked Lean 4 Implementation for `Stabilize.lean`

```lean
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

/-- A constant root in a prestable limit of non-constant curves has degree at least 1. -/
theorem root_degree_pos_of_const
    (u_seq : ℕ → (CP1 → M))
    (pdata : PrestableLimitData I u_seq)
    (_h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (_h_const : ∃ c : M, ∀ z, pdata.map pdata.root z = c) :
    1 ≤ pdata.tree.adj.degree pdata.root := by
  sorry

/-- Auxiliary induction lemma on tree vertex cardinality. -/
lemma stabilize_prestable_tree_aux
    (u_seq : ℕ → (CP1 → M))
    (h_nonconst_input : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
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
        · obtain ⟨pdata', h_card', h_en'⟩ := prune_degree_one_root I u_seq pdata h_deg1 h_nc
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
          · have h_pos := root_degree_pos_of_const I u_seq pdata h_nonconst_input h_nc
            omega

/-- Master Stabilization Theorem (Contract G02). Proved with zero direct sorry. -/
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
  stabilize_prestable_tree_aux I u_seq h_nonconst_input (Fintype.card pdata.tree.V) pdata le_rfl
```

### 2.3 Machine-Checked Lean 4 Implementation for `GenusZero.lean`

```lean
/-- Core Genus 0 Gromov Compactness Theorem (Theorem 1 Core & Contract G03). Proved with zero direct sorry. -/
theorem gromov_compactness_core
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) := by
  obtain ⟨pdata, _h_en_le⟩ := assemble_prestable_limit I th u_seq B h_jhol h_energy
  obtain ⟨u_lim, _h_en_eq, σ, frames, h_smooth, h_collapse, h_ident⟩ :=
    stabilize_prestable_tree I u_seq pdata h_nonconst
  refine ⟨u_lim, ⟨⟨σ, frames, h_smooth, h_collapse, h_ident⟩⟩⟩

/-- Sequential compactness alternative for arbitrary sphere sequences. Proved with zero direct sorry. -/
theorem gromov_subsequence_alternative
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) := by
  by_cases h_freq : ∀ N, ∃ n > N, ∃ c : M, ∀ z, u_seq n z = c
  · obtain ⟨φ, hφ_mono, hφ_P⟩ := extraction_of_frequently_atTop' h_freq
    let σ_const : SubseqMap := ⟨φ, hφ_mono⟩
    let c_seq : ℕ → M := fun n => u_seq (σ_const.1 n) north_pole
    have h_c_univ : ∀ n, c_seq n ∈ (Set.univ : Set M) := fun _ => Set.mem_univ _
    obtain ⟨c_lim, -, ψ, hψ_mono, hψ_tendsto⟩ :=
      isCompact_univ.tendsto_subseq (x := c_seq) h_c_univ
    let σ : SubseqMap := σ_const.comp ⟨ψ, hψ_mono⟩
    left
    refine ⟨σ, c_lim, ?_⟩
    rw [tendsto_pi_nhds]
    intro z
    have h_eq : (fun n => u_seq (σ.1 n) z) = (c_seq ∘ ψ) := by
      ext n
      dsimp [σ, SubseqMap.comp, c_seq]
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
    let σ_shift : SubseqMap := ⟨shift, h_shift_mono⟩
    let v : ℕ → (CP1 → M) := fun k => u_seq (σ_shift.1 k)
    have h_v_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, v n z = c := by
      intro n
      rintro ⟨c, hc⟩
      have h_gt : σ_shift.1 n > N := by dsimp [σ_shift, shift]; omega
      obtain ⟨z, hz⟩ := hN (σ_shift.1 n) h_gt c
      exact hz (hc z)
    have h_v_jhol : ∀ n, JHolomorphicOn I I_CP1 (v n) Set.univ := fun n => h_jhol (σ_shift.1 n)
    have h_v_energy : ∀ n, totalEnergy I (v n) ≤ B := fun n => h_energy (σ_shift.1 n)
    obtain ⟨u_lim, hwit⟩ := gromov_compactness_core I th v B h_v_nonconst h_v_jhol h_v_energy
    right
    exact ⟨σ_shift, u_lim, hwit⟩
```

---

## 3. Component 2: `Assembly.lean` (G01 ↔ C02 + C03 + B07)

### 3.1 Problem Analysis
In `Assembly.lean`, `assemble_prestable_limit` previously had a bare `sorry` body that did not invoke:
- `exists_concentration_data` (Contract `C02`)
- `defect_measure_identity` (Contract `C03`)
- `prestable_limit_singleton_subseq` ($S = \emptyset$)
- `resolve_single_defect_tree` (Contract `B07`, $S \ne \emptyset$)

### 3.2 Machine-Checked Wiring in `Assembly.lean`

```lean
/-- Construction of a prestable limit for a single non-bubbling curve sequence along a subsequence. -/
def prestable_limit_singleton_subseq
    (u_seq : ℕ → (CP1 → M)) (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M)
    (h_jhol : JHolomorphicOn I I_CP1 u_lim Set.univ)
    (h_conv : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Set.univ)
    (h_energy : Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop (𝓝 (totalEnergy I u_lim))) :
    PrestableLimitData I u_seq where
  tree := Bubbling.singletonSphereTree
  root := ()
  map := fun _ => u_lim
  is_jhol := fun _ => h_jhol
  nodal_match := fun _ _ h => False.elim h
  stable_off_root := fun (v : Unit) h_ne => by
    cases v; exact False.elim (h_ne rfl)
  σ := σ
  frames := fun _ _ => MoebiusFrame.id
  root_frame_id := fun _ => rfl
  frame_collapse := fun _ _ h => False.elim h
  smooth_conv := fun (v : Unit) => by
    have h_empty : (punctured_sphere { z : CP1 | ∃ (w : Bubbling.singletonSphereTree.V) (h : Bubbling.singletonSphereTree.adj.Adj v w),
        z = Bubbling.singletonSphereTree.node_point v w h }) = Set.univ := by
      dsimp [punctured_sphere]
      have h_none : { z : CP1 | ∃ (w : Bubbling.singletonSphereTree.V) (h : Bubbling.singletonSphereTree.adj.Adj v w),
          z = Bubbling.singletonSphereTree.node_point v w h } = ∅ := by
        ext z
        simp only [mem_setOf_eq, not_exists, mem_empty_iff_false, iff_false]
        intro w h; exact False.elim h
      rw [h_none, diff_empty]
    rw [h_empty]
    have h_seq : (fun n => (u_seq (σ.1 n)) ∘ ((fun _ _ => MoebiusFrame.id) v n).toHomeo) = fun n => u_seq (σ.1 n) := by
      ext n x; rfl
    rw [h_seq]
    exact h_conv
  energy_ident := by
    have h_sum : (∑ v : Bubbling.singletonSphereTree.V, totalEnergy I ((fun _ => u_lim) v)) = totalEnergy I u_lim := by
      change (∑ _v : Unit, totalEnergy I u_lim) = totalEnergy I u_lim
      simp
    rw [h_sum]
    exact h_energy

/-- Grafting local defect trees at each concentration point p ∈ S onto the base curve u₀. -/
theorem graft_defect_trees_to_root
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (_hm_sph : ∀ p ∈ cdata.S, th.ε_sph ≤ m_defect p)
    (_h_energy : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)))
    (_defect_trees : (p : CP1) → p ∈ cdata.S →
      Bubbling.LocalDefectTree I th (m_defect p) (cdata.u₀ p)) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  sorry

/-- Assembles the base map u₀ and all defect trees from Contract B07 into a global prestable limit.
Proved with zero direct sorry. -/
theorem assemble_prestable_limit
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  have hB : 0 ≤ B := (energy_nonneg I (u_seq 0) Set.univ).trans (h_energy 0)
  obtain ⟨cdata⟩ := Compactness.exists_concentration_data I u_seq h_jhol B hB h_energy th
  obtain ⟨m_defect, hm_sph, _hm_zero, _h_decomp, h_tendsto_energy⟩ :=
    Compactness.defect_measure_identity I u_seq B th cdata
  by_cases hS : cdata.S = ∅
  · have h_smooth : SmoothLocalConvergesOn I (fun n => u_seq (cdata.σ.1 n)) cdata.u₀ Set.univ := by
      have h_sc := cdata.smooth_conv
      have h_diff : Set.univ \ (cdata.S : Set CP1) = Set.univ := by simp [hS]
      rwa [h_diff] at h_sc
    have h_en_lim : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop (𝓝 (totalEnergy I cdata.u₀)) := by
      have h_sum_zero : (∑ p ∈ cdata.S, m_defect p) = 0 := by simp [hS]
      rw [h_sum_zero, add_zero] at h_tendsto_energy
      exact h_tendsto_energy
    let pdata := prestable_limit_singleton_subseq I u_seq cdata.σ cdata.u₀ cdata.u₀_jhol h_smooth h_en_lim
    refine ⟨pdata, ?_⟩
    exact prestable_limit_energy_bound I u_seq B pdata h_energy
  · let defect_trees : (p : CP1) → p ∈ cdata.S → Bubbling.LocalDefectTree I th (m_defect p) (cdata.u₀ p) :=
      fun p hp =>
        have h_pos : 0 < m_defect p := th.ε_sph_pos.trans_le (hm_sph p hp)
        Classical.choice (Bubbling.resolve_single_defect_tree I th (m_defect p) h_pos (cdata.u₀ p))
    exact graft_defect_trees_to_root I u_seq B th cdata m_defect hm_sph h_tendsto_energy defect_trees
```

---

## 4. Component 3: `LocalTree.lean` (B07 ↔ B06 + B05 + B04)

### 4.1 Problem Analysis
`resolve_single_defect_tree` formalizes well-founded induction on the discrete energy rank $\lfloor m / h \rfloor \in \mathbb{N}$.
In the induction step for mass $m$:
- If $m \ge h$, we extract a `OneLevelDecomposition` via `exists_one_level_decomp` (`B04`).
- If $q = \emptyset$, we call `local_defect_tree_of_empty_children`, which is **already proved with zero sorry** in `LocalTree.lean`.
- If $q \ne \emptyset$, each child defect $z \in q$ satisfies $\lfloor m_{\text{child}} / h \rfloor < \lfloor m / h \rfloor$ by `child_rank_strict_decrease` (`B06`), allowing the induction hypothesis `ih` to produce a `LocalDefectTree` for each child.
- We then graft the child trees onto the bubble curve using `graft_child_defect_trees`.

### 4.2 Machine-Checked Lean 4 Implementation for `LocalTree.lean`

```lean
/-- One-level decomposition extraction for an isolated defect mass m ≥ h. -/
theorem exists_one_level_decomp
    (thresh : TargetThresholds I M) (m_defect : ℝ)
    (_hm : thresh.h ≤ m_defect) (base_val : M) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) := by
  sorry

/-- Grafting child defect trees onto the one-level bubble curve. -/
theorem graft_child_defect_trees
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (_hm : thresh.h ≤ m_defect)
    (_child_trees : (z : ℂ) → z ∈ decomp.q →
      LocalDefectTree I thresh (decomp.m_child z) (decomp.v (stereo_chart.symm z))) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) := by
  sorry

/-- Resolution of sub-threshold mass (below the minimal sphere energy h). -/
theorem local_defect_tree_of_subthreshold
    (thresh : TargetThresholds I M) (m_defect : ℝ)
    (_hm_pos : 0 < m_defect) (_hm_lt : m_defect < thresh.h) (base_val : M) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) := by
  sorry

/-- Resolution of a Single Defect into a Finite Rooted Bubble Tree (Contract B07).
Proved with zero direct sorry via energy_rank_induction and B04/B06. -/
theorem resolve_single_defect_tree
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : 0 < m_defect) (base_val : M) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) := by
  revert hm base_val
  refine energy_rank_induction thresh.h
    (fun m => 0 < m → ∀ (b : M), Nonempty (LocalDefectTree I thresh m b)) ?_ m_defect
  intro m ih hm_pos b
  by_cases h_ge : thresh.h ≤ m
  · obtain ⟨decomp⟩ := exists_one_level_decomp I thresh m h_ge b
    by_cases h_q : decomp.q = ∅
    · exact ⟨local_defect_tree_of_empty_children I thresh m b decomp h_ge h_q⟩
    · have h_children : ∀ (z : ℂ) (hz : z ∈ decomp.q),
          Nonempty (LocalDefectTree I thresh (decomp.m_child z) (decomp.v (stereo_chart.symm z))) := by
        intro z hz
        have h_rel : energy_rank_rel thresh.h (decomp.m_child z) m :=
          child_rank_strict_decrease I thresh m b decomp h_ge z hz
        have h_pos : 0 < decomp.m_child z :=
          thresh.h_pos.trans_le (decomp.m_child_pos z hz)
        exact ih (decomp.m_child z) h_rel h_pos (decomp.v (stereo_chart.symm z))
      let child_trees : (z : ℂ) → z ∈ decomp.q → LocalDefectTree I thresh (decomp.m_child z) (decomp.v (stereo_chart.symm z)) :=
        fun z hz => Classical.choice (h_children z hz)
      exact graft_child_defect_trees I thresh m b decomp h_ge child_trees
  · push_neg at h_ge
    exact local_defect_tree_of_subthreshold I thresh m hm_pos h_ge b
```

---

## 5. Component 4: `Measures.lean` (C01) and Wiring into `Concentration.lean` (C02)

### 5.1 Problem Analysis
In `Compactness/Measures.lean`:
- `weak_energy_measure_compactness_of_weak_measure_compactness` was already completely proved with zero sorry!
- We prove `energyMeasureExtended_le_ofReal_of_totalEnergy_le` with zero sorry via `ENNReal.ofReal_toReal` and `ENNReal.ofReal_le_ofReal`.
- `weak_energy_measure_compactness` is then proved with **zero direct `sorry`** by composing the reduction with `weak_measure_compactness`.
- In `Compactness/Concentration.lean`, `exists_concentration_data` is proved with **zero direct `sorry`** by consuming `weak_energy_measure_compactness`, `concentration_singular_set_properties` (zero-sorry), and `extract_smooth_limit_off_singular_set`.

### 5.2 Machine-Checked Lean 4 Implementation for `Measures.lean` & `Concentration.lean`

```lean
/-- Preservation of real energy upper bounds in extended ENNReal measures (Zero-sorry). -/
theorem energyMeasureExtended_le_ofReal_of_totalEnergy_le
    (u : CP1 → M) (B : ℝ) (h_en : totalEnergy I u ≤ B)
    (h_fin : energyMeasureExtended I u Set.univ < ⊤) :
    energyMeasureExtended I u Set.univ ≤ ENNReal.ofReal B := by
  have h_toReal : (energyMeasureExtended I u Set.univ).toReal = totalEnergy I u := rfl
  have h_eq : energyMeasureExtended I u Set.univ = ENNReal.ofReal (totalEnergy I u) := by
    rw [← h_toReal, ENNReal.ofReal_toReal h_fin.ne]
  rw [h_eq]
  exact ENNReal.ofReal_le_ofReal h_en

/-- Finiteness of extended energy measure for curves with bounded total energy. -/
theorem energyMeasureExtended_lt_top_of_totalEnergy_le
    (u : CP1 → M) (B : ℝ) (_hB : 0 < B) (_h : totalEnergy I u ≤ B) :
    energyMeasureExtended I u Set.univ < ⊤ := by
  sorry

/-- Weak Compactness of Energy Measures for sequences of J-holomorphic curves (Contract C01).
Proved with zero direct sorry. -/
theorem weak_energy_measure_compactness
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (hB : 0 < B)
    (h_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  have h_meas_bdd : ∀ n, energyMeasureExtended I (u_seq n) Set.univ ≤ ENNReal.ofReal B := by
    intro n
    have h_fin := energyMeasureExtended_lt_top_of_totalEnergy_le I (u_seq n) B hB (h_bdd n)
    exact energyMeasureExtended_le_ofReal_of_totalEnergy_le I (u_seq n) B (h_bdd n) h_fin
  exact weak_energy_measure_compactness_of_weak_measure_compactness I
    weak_measure_compactness u_seq B hB h_meas_bdd

/-- Smooth limit extraction off the singular set S combining local smooth compactness (A06)
and removal of singularities (A12). -/
theorem extract_smooth_limit_off_singular_set
    (u_seq : ℕ → (CP1 → M)) (σ : SubseqMap)
    (_h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (_S : Finset CP1) :
    ∃ (u₀ : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ _S) := by
  sorry

/-- Extraction of Concentration Data from bounded-energy J-spheres (Contract C02).
Proved with zero direct sorry. -/
theorem exists_concentration_data
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (hB : 0 ≤ B)
    (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : Bubbling.TargetThresholds I M) :
    Nonempty (ConcentrationData I u_seq B thresh) := by
  by_cases hB_pos : 0 < B
  · obtain ⟨σ, μ, _hμ_fin, h_weak⟩ :=
      weak_energy_measure_compactness I u_seq B hB_pos h_en
    have h_tot_le : ∀ n, energyMeasureExtended I (u_seq (σ.1 n)) Set.univ ≤ ENNReal.ofReal B := by
      intro n
      have h_fin := energyMeasureExtended_lt_top_of_totalEnergy_le I (u_seq (σ.1 n)) B hB_pos (h_en (σ.1 n))
      exact energyMeasureExtended_le_ofReal_of_totalEnergy_le I (u_seq (σ.1 n)) B (h_en (σ.1 n)) h_fin
    have h_tot : μ Set.univ ≤ ENNReal.ofReal B := h_weak.total_mass_le h_tot_le
    obtain ⟨S, hS_def, hS_mul, hS_le⟩ :=
      concentration_singular_set_properties I μ B hB thresh h_tot
    obtain ⟨u₀, hu₀_jhol, h_smooth⟩ :=
      extract_smooth_limit_off_singular_set I u_seq σ h_jhol S
    exact ⟨⟨σ, μ, h_tot, h_weak, S, hS_def, hS_mul, hS_le, u₀, hu₀_jhol, h_smooth⟩⟩
  · have hB0 : B = 0 := by linarith
    have hB1 : 0 < B + 1 := by linarith
    have h_en1 : ∀ n, totalEnergy I (u_seq n) ≤ B + 1 := fun n => (h_en n).trans (by linarith)
    obtain ⟨σ, μ, _hμ_fin, h_weak⟩ :=
      weak_energy_measure_compactness I u_seq (B + 1) hB1 h_en1
    have h_tot_le : ∀ n, energyMeasureExtended I (u_seq (σ.1 n)) Set.univ ≤ ENNReal.ofReal B := by
      intro n
      rw [hB0, ENNReal.ofReal_zero]
      have h_en0 : totalEnergy I (u_seq (σ.1 n)) ≤ 0 := by
        have := h_en (σ.1 n); linarith [hB0]
      have h_fin := energyMeasureExtended_lt_top_of_totalEnergy_le I (u_seq (σ.1 n)) (B + 1) hB1 (h_en1 (σ.1 n))
      have h_le_ofReal := energyMeasureExtended_le_ofReal_of_totalEnergy_le I (u_seq (σ.1 n)) 0 h_en0 h_fin
      rwa [ENNReal.ofReal_zero] at h_le_ofReal
    have h_tot : μ Set.univ ≤ ENNReal.ofReal B := h_weak.total_mass_le h_tot_le
    obtain ⟨S, hS_def, hS_mul, hS_le⟩ :=
      concentration_singular_set_properties I μ B hB thresh h_tot
    obtain ⟨u₀, hu₀_jhol, h_smooth⟩ :=
      extract_smooth_limit_off_singular_set I u_seq σ h_jhol S
    exact ⟨⟨σ, μ, h_tot, h_weak, S, hS_def, hS_mul, hS_le, u₀, hu₀_jhol, h_smooth⟩⟩
```

---

## 6. Verification and Axiomatic Audit

Every lemma and theorem in this design was compiled and verified via `lake env lean --stdin`.
The declarations:
1. `gromov_compactness_core`
2. `gromov_subsequence_alternative`
3. `stabilize_prestable_tree`
4. `stabilize_prestable_tree_of_stable_root`
5. `stabilize_prestable_tree_of_nonconst_root`
6. `assemble_prestable_limit`
7. `resolve_single_defect_tree`
8. `weak_energy_measure_compactness`
9. `exists_concentration_data`

contain **0 direct `sorry`**.
Their axiomatic closures depend strictly on standard Lean 4 / Mathlib axioms:
- `propext`
- `Classical.choice`
- `Quot.sound`
plus the declared leaf lemmas (which will be closed in Model B).

The call-graph wiring for P0-11 Components 1–4 is 100% complete.
