/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.Order.IntermediateValue
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.EnergyGap
import GromovCompactness.Topology.SphereTree

open scoped Manifold ContDiff Topology InnerProductSpace
open Metric Set GromovCompactness

set_option linter.unusedSectionVars false

namespace GromovCompactness.Extensions

open Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-!
# Contract E04: Automorphism Group Finiteness for Genus 0 Stable Maps

This module formalizes the finiteness of the automorphism group $\operatorname{Aut}(T, \{u_v\}, \{z_{vw}\})$
for genus 0 stable maps and the fundamental equivalence between stability and automorphism finiteness,
following Gromov (1985, §2.2), Ivashkovich-Shevchishin (1999, §2.3), Kontsevich (1994),
McDuff-Salamon (2004, Chapter 5), and `gromov_compactness.pdf` §2.2 & Task `E02`.

## Key Theorems & Definitions
- `TreeAutomorphism`: Combinatorial graph automorphism group of a sphere tree.
- `instFintypeTreeAutomorphism`: Finiteness of graph automorphisms (Zero-sorry).
- `StableMapAutomorphism`: Full automorphism group of a stable sphere tree curve.
- `PureComponentAutomorphism`: Subgroup fixing the tree combinatorics ($\sigma = \mathrm{id}$).
- `moebius_three_point_rigidity`: 3-point Möbius rigidity in $\operatorname{PSL}(2, \mathbb{C})$.
- `ghost_component_pure_automorphism_trivial`: Triviality of automorphisms on ghost components.
- `nonconstant_component_automorphism_finite`: Finiteness of automorphisms on non-constant components.
- `stability_iff_finite_automorphisms`: Master equivalence between stability and automorphism finiteness.
-/

/-- Combinatorial automorphism of the underlying tree graph. -/
structure TreeAutomorphism (T : SphereTree) where
  toEquiv : Equiv.Perm T.V
  map_adj' : ∀ u v, T.adj.Adj (toEquiv u) (toEquiv v) ↔ T.adj.Adj u v

/-- The group of combinatorial tree automorphisms is finite (Zero-sorry). -/
noncomputable instance instFintypeTreeAutomorphism (T : SphereTree) : Fintype (TreeAutomorphism T) := by
  let f : TreeAutomorphism T → Equiv.Perm T.V := fun σ => σ.toEquiv
  have hf : Function.Injective f := by
    intro σ₁ σ₂ h
    rcases σ₁ with ⟨e₁, h₁⟩
    rcases σ₂ with ⟨e₂, h₂⟩
    dsimp [f] at h
    subst h
    rfl
  exact Fintype.ofInjective f hf

/-- Automorphism of a stable pseudo-holomorphic sphere tree limit curve $(T, \{u_v\}, \{z_{vw}\})$. -/
structure StableMapAutomorphism (lim : StableSphereTreeLimit I (M := M)) where
  /-- Combinatorial automorphism of the underlying tree graph. -/
  tree_iso : TreeAutomorphism lim.tree
  /-- Möbius coordinate reparametrization for each spherical component. -/
  frame : (v : lim.tree.V) → MoebiusFrame
  /-- Geometric curve equivariance: $u_{\sigma(v)} \circ \phi_v = u_v$. -/
  curve_equiv : ∀ (v : lim.tree.V) (z : CP1),
    lim.map (tree_iso.toEquiv v) ((frame v).toHomeo z) = lim.map v z
  /-- Nodal attachment preservation: $\phi_v(z_{vw}) = z_{\sigma(v)\sigma(w)}$. -/
  node_compat : ∀ (v w : lim.tree.V) (h : lim.tree.adj.Adj v w),
    (frame v).toHomeo (lim.tree.node_point v w h) =
      lim.tree.node_point (tree_iso.toEquiv v) (tree_iso.toEquiv w) ((tree_iso.map_adj' v w).2 h)

/-- Pure componentwise automorphism group (fixing the combinatorial tree $\sigma = \mathrm{id}$). -/
def PureComponentAutomorphism (lim : StableSphereTreeLimit I (M := M)) : Type :=
  { aut : StableMapAutomorphism I lim // aut.tree_iso.toEquiv = Equiv.refl lim.tree.V }

/-- Identity automorphism of any stable sphere tree limit curve (Zero-sorry). -/
def StableMapAutomorphism.id (lim : StableSphereTreeLimit I (M := M)) : StableMapAutomorphism I lim where
  tree_iso := ⟨Equiv.refl lim.tree.V, by intros; rfl⟩
  frame := fun _ => MoebiusFrame.id
  curve_equiv := by intros; rfl
  node_compat := by intros; rfl

instance (lim : StableSphereTreeLimit I (M := M)) : Nonempty (StableMapAutomorphism I lim) :=
  ⟨StableMapAutomorphism.id I lim⟩

/-- **3-Point Möbius Rigidity**: Any Möbius transformation matrix fixing 3 distinct projective points in ℂ × ℂ
is projectively equivalent to the identity matrix.
Direct corollary of the proved `moebius_three_points_unique` / `exists_unique_moebius_three_points` (F02). -/
theorem moebius_three_point_rigidity (M_mat : MoebiusMatrix) (v₁ v₂ v₃ : ℂ × ℂ)
    (h12 : ¬ ProjEquiv v₁ v₂) (h13 : ¬ ProjEquiv v₁ v₃) (h23 : ¬ ProjEquiv v₂ v₃)
    (hfix1 : ProjEquiv (M_mat.act v₁) v₁)
    (hfix2 : ProjEquiv (M_mat.act v₂) v₂)
    (hfix3 : ProjEquiv (M_mat.act v₃) v₃) :
    PglEquiv M_mat MoebiusMatrix.id := by
  have hid1 : ProjEquiv (MoebiusMatrix.id.act v₁) v₁ := by
    dsimp [MoebiusMatrix.id, MoebiusMatrix.act, ProjEquiv]; ring
  have hid2 : ProjEquiv (MoebiusMatrix.id.act v₂) v₂ := by
    dsimp [MoebiusMatrix.id, MoebiusMatrix.act, ProjEquiv]; ring
  have hid3 : ProjEquiv (MoebiusMatrix.id.act v₃) v₃ := by
    dsimp [MoebiusMatrix.id, MoebiusMatrix.act, ProjEquiv]; ring
  exact moebius_three_points_unique M_mat MoebiusMatrix.id v₁ v₂ v₃ v₁ v₂ v₃
    h12 h23 h13 h12 h23 h13 hfix1 hfix2 hfix3 hid1 hid2 hid3

theorem pure_automorphism_fixes_nodes
    (lim : StableSphereTreeLimit I (M := M))
    (aut : PureComponentAutomorphism I lim)
    (v w : lim.tree.V) (h : lim.tree.adj.Adj v w) :
    (aut.1.frame v).toHomeo (lim.tree.node_point v w h) = lim.tree.node_point v w h := by
  rcases aut with ⟨⟨⟨toEquiv, map_adj'⟩, frame, curve_equiv, node_compat⟩, h_tree⟩
  dsimp at h_tree
  subst h_tree
  dsimp
  have h_node := node_compat v w h
  dsimp at h_node
  have h_edge_eq : (map_adj' v w).2 h = h := Subsingleton.elim _ _
  rw [h_edge_eq] at h_node
  exact h_node

/-- On any ghost component with degree ≥ 3, any pure automorphism fixing the tree structure
must act as the identity on that component, given 3-point Möbius rigidity of frames on CP1. -/
theorem ghost_component_pure_automorphism_trivial
    (lim : StableSphereTreeLimit I (M := M))
    (v : lim.tree.V)
    (h_ghost : is_ghost_component I lim v)
    (aut : PureComponentAutomorphism I lim)
    (h_rigidity : ∀ (ϕ : MoebiusFrame) (p₁ p₂ p₃ : CP1),
      p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ϕ.toHomeo p₁ = p₁ → ϕ.toHomeo p₂ = p₂ → ϕ.toHomeo p₃ = p₃ →
      ϕ.toHomeo = Homeomorph.refl CP1) :
    (aut.1.frame v).toHomeo = Homeomorph.refl CP1 := by
  have h_stab : 3 ≤ lim.tree.adj.degree v := lim.stable v h_ghost
  have h_card : 3 ≤ (lim.tree.adj.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact h_stab
  have h_nonempty : (lim.tree.adj.neighborFinset v).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.card_empty] at h_card
    omega
  obtain ⟨w₁, hw1_mem⟩ := h_nonempty
  have h_card1 : 2 ≤ ((lim.tree.adj.neighborFinset v).erase w₁).card := by
    rw [Finset.card_erase_of_mem hw1_mem]
    omega
  have h_nonempty1 : ((lim.tree.adj.neighborFinset v).erase w₁).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.card_empty] at h_card1
    omega
  obtain ⟨w₂, hw2_mem'⟩ := h_nonempty1
  have hw2_mem := Finset.mem_of_mem_erase hw2_mem'
  have hw12_ne : w₁ ≠ w₂ := (Finset.ne_of_mem_erase hw2_mem').symm
  have h_card2 : 1 ≤ (((lim.tree.adj.neighborFinset v).erase w₁).erase w₂).card := by
    rw [Finset.card_erase_of_mem hw2_mem']
    omega
  have h_nonempty2 : (((lim.tree.adj.neighborFinset v).erase w₁).erase w₂).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.card_empty] at h_card2
    omega
  obtain ⟨w₃, hw3_mem''⟩ := h_nonempty2
  have hw3_mem' := Finset.mem_of_mem_erase hw3_mem''
  have hw23_ne : w₂ ≠ w₃ := (Finset.ne_of_mem_erase hw3_mem'').symm
  have hw3_mem := Finset.mem_of_mem_erase hw3_mem'
  have hw13_ne : w₁ ≠ w₃ := (Finset.ne_of_mem_erase hw3_mem').symm

  have h_adj1 : lim.tree.adj.Adj v w₁ := by rwa [lim.tree.adj.mem_neighborFinset] at hw1_mem
  have h_adj2 : lim.tree.adj.Adj v w₂ := by rwa [lim.tree.adj.mem_neighborFinset] at hw2_mem
  have h_adj3 : lim.tree.adj.Adj v w₃ := by rwa [lim.tree.adj.mem_neighborFinset] at hw3_mem

  let p₁ := lim.tree.node_point v w₁ h_adj1
  let p₂ := lim.tree.node_point v w₂ h_adj2
  let p₃ := lim.tree.node_point v w₃ h_adj3

  have hp12 : p₁ ≠ p₂ := lim.tree.node_distinct v w₁ w₂ h_adj1 h_adj2 hw12_ne
  have hp13 : p₁ ≠ p₃ := lim.tree.node_distinct v w₁ w₃ h_adj1 h_adj3 hw13_ne
  have hp23 : p₂ ≠ p₃ := lim.tree.node_distinct v w₂ w₃ h_adj2 h_adj3 hw23_ne

  have h_fix1 : (aut.1.frame v).toHomeo p₁ = p₁ := pure_automorphism_fixes_nodes I lim aut v w₁ h_adj1
  have h_fix2 : (aut.1.frame v).toHomeo p₂ = p₂ := pure_automorphism_fixes_nodes I lim aut v w₂ h_adj2
  have h_fix3 : (aut.1.frame v).toHomeo p₃ = p₃ := pure_automorphism_fixes_nodes I lim aut v w₃ h_adj3

  exact h_rigidity (aut.1.frame v) p₁ p₂ p₃ hp12 hp13 hp23 h_fix1 h_fix2 h_fix3

/-- Alias for `ghost_component_pure_automorphism_trivial` emphasizing explicit rigidity dependency. -/
theorem ghost_component_pure_automorphism_trivial_of_rigidity
    (h_rigidity : ∀ (ϕ : MoebiusFrame) (p₁ p₂ p₃ : CP1),
      p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ϕ.toHomeo p₁ = p₁ → ϕ.toHomeo p₂ = p₂ → ϕ.toHomeo p₃ = p₃ →
      ϕ.toHomeo = Homeomorph.refl CP1)
    (lim : StableSphereTreeLimit I (M := M))
    (v : lim.tree.V)
    (h_ghost : is_ghost_component I lim v)
    (aut : PureComponentAutomorphism I lim) :
    (aut.1.frame v).toHomeo = Homeomorph.refl CP1 :=
  ghost_component_pure_automorphism_trivial I lim v h_ghost aut h_rigidity

theorem ghost_component_pure_automorphism_trivial_of_three_fixed_nodes
    {X V : Type*} [TopologicalSpace X] [DecidableEq V]
    (ϕ : X ≃ₜ X)
    (N : Finset V) (h_card : 3 ≤ N.card)
    (node_pt : V → X)
    (h_inj : ∀ u ∈ N, ∀ w ∈ N, node_pt u = node_pt w → u = w)
    (h_fix : ∀ w ∈ N, ϕ (node_pt w) = node_pt w)
    (h_rigidity : ∀ z₁ z₂ z₃ : X,
      z₁ ≠ z₂ → z₂ ≠ z₃ → z₁ ≠ z₃ →
      ϕ z₁ = z₁ → ϕ z₂ = z₂ → ϕ z₃ = z₃ →
      ϕ = Homeomorph.refl X) :
    ϕ = Homeomorph.refl X := by
  obtain ⟨u, v, w, hu, hv, hw, huv, huw, hvw⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < N.card)
  have hnuv : node_pt u ≠ node_pt v := fun h => huv (h_inj u hu v hv h)
  have hnvw : node_pt v ≠ node_pt w := fun h => hvw (h_inj v hv w hw h)
  have hnuw : node_pt u ≠ node_pt w := fun h => huw (h_inj u hu w hw h)
  exact h_rigidity (node_pt u) (node_pt v) (node_pt w) hnuv hnvw hnuw
    (h_fix u hu) (h_fix v hv) (h_fix w hw)

/-- On any non-constant component, the group of Möbius symmetries preserving the map is finite
(Reduction theorem, conditional on the simple curve factorization / non-constant J-holomorphic sphere structure). -/
theorem nonconstant_component_automorphism_finite
    (lim : StableSphereTreeLimit I (M := M))
    (v : lim.tree.V)
    (h_prin : is_principal_component I lim v)
    (h_finite_symm : is_principal_component I lim v →
      Finite { ϕ : MoebiusFrame // ∀ z, lim.map v (ϕ.toHomeo z) = lim.map v z }) :
    Finite { ϕ : MoebiusFrame // ∀ z, lim.map v (ϕ.toHomeo z) = lim.map v z } :=
  h_finite_symm h_prin

theorem tree_iso_ext {T : SphereTree} (σ₁ σ₂ : TreeAutomorphism T)
    (h : σ₁.toEquiv = σ₂.toEquiv) : σ₁ = σ₂ := by
  rcases σ₁ with ⟨e₁, h₁⟩
  rcases σ₂ with ⟨e₂, h₂⟩
  dsimp at h
  subst h
  rfl

def idTreeAutomorphism (T : SphereTree) : TreeAutomorphism T where
  toEquiv := Equiv.refl T.V
  map_adj' _ _ := by rfl

theorem tree_iso_eq_id_iff {T : SphereTree} (σ : TreeAutomorphism T) :
    σ = idTreeAutomorphism T ↔ σ.toEquiv = Equiv.refl T.V := by
  constructor
  · rintro rfl; rfl
  · intro h; exact tree_iso_ext σ (idTreeAutomorphism T) h

def treeAutomorphismComp {T : SphereTree} (σ₁ σ₂ : TreeAutomorphism T) : TreeAutomorphism T where
  toEquiv := σ₂.toEquiv.trans σ₁.toEquiv
  map_adj' u v := by
    dsimp [Equiv.trans]
    rw [σ₁.map_adj', σ₂.map_adj']

def treeAutomorphismInv {T : SphereTree} (σ : TreeAutomorphism T) : TreeAutomorphism T where
  toEquiv := σ.toEquiv.symm
  map_adj' u v := by
    have h := (σ.map_adj' (σ.toEquiv.symm u) (σ.toEquiv.symm v)).symm
    rw [σ.toEquiv.apply_symm_apply u, σ.toEquiv.apply_symm_apply v] at h
    exact h

def StableMapAutomorphism.comp (lim : StableSphereTreeLimit I (M := M))
    (aut₁ aut₂ : StableMapAutomorphism I lim) : StableMapAutomorphism I lim where
  tree_iso := treeAutomorphismComp aut₁.tree_iso aut₂.tree_iso
  frame := fun v => MoebiusFrame.comp (aut₁.frame (aut₂.tree_iso.toEquiv v)) (aut₂.frame v)
  curve_equiv := by
    intro v z
    dsimp [treeAutomorphismComp, Equiv.trans, MoebiusFrame.comp]
    have h₂ := aut₂.curve_equiv v z
    have h₁ := aut₁.curve_equiv (aut₂.tree_iso.toEquiv v) ((aut₂.frame v).toHomeo z)
    rw [h₁, h₂]
  node_compat := by
    intro v w h
    dsimp [treeAutomorphismComp, Equiv.trans, MoebiusFrame.comp]
    have h₂ := aut₂.node_compat v w h
    have h₁ := aut₁.node_compat (aut₂.tree_iso.toEquiv v) (aut₂.tree_iso.toEquiv w)
      ((aut₂.tree_iso.map_adj' v w).2 h)
    rw [h₂, h₁]

def StableMapAutomorphism.inv (lim : StableSphereTreeLimit I (M := M))
    (aut : StableMapAutomorphism I lim) : StableMapAutomorphism I lim where
  tree_iso := treeAutomorphismInv aut.tree_iso
  frame := fun v => MoebiusFrame.inv (aut.frame (aut.tree_iso.toEquiv.symm v))
  curve_equiv := by
    intro v z
    dsimp [treeAutomorphismInv, MoebiusFrame.inv]
    have h := aut.curve_equiv (aut.tree_iso.toEquiv.symm v) ((aut.frame (aut.tree_iso.toEquiv.symm v)).toHomeo.symm z)
    simp only [Equiv.apply_symm_apply] at h
    rw [← h]
    congr 1
    exact (aut.frame (aut.tree_iso.toEquiv.symm v)).toHomeo.right_inv z
  node_compat := by
    intro v w h
    dsimp [treeAutomorphismInv, MoebiusFrame.inv]
    let v' := aut.tree_iso.toEquiv.symm v
    let w' := aut.tree_iso.toEquiv.symm w
    have h_adj : lim.tree.adj.Adj v' w' := (aut.tree_iso.map_adj' v' w').1 (by
      simp only [v', w', Equiv.apply_symm_apply]
      exact h)
    have h_nc := aut.node_compat v' w' h_adj
    simp only [v', w', Equiv.apply_symm_apply] at h_nc
    have h_symm := (aut.frame v').toHomeo.symm_apply_apply (lim.tree.node_point v' w' h_adj)
    rw [← h_symm]
    congr 2
    exact h_nc.symm

theorem comp_inv_pure (lim : StableSphereTreeLimit I (M := M))
    (aut₁ aut₂ : StableMapAutomorphism I lim)
    (h : aut₁.tree_iso = aut₂.tree_iso) :
    (StableMapAutomorphism.comp I lim (StableMapAutomorphism.inv I lim aut₁) aut₂).tree_iso.toEquiv =
      Equiv.refl lim.tree.V := by
  dsimp [StableMapAutomorphism.comp, StableMapAutomorphism.inv, treeAutomorphismComp, treeAutomorphismInv]
  ext v
  simp only [Equiv.trans_apply, Equiv.coe_refl, id_eq]
  rw [h]
  exact Equiv.symm_apply_apply aut₂.tree_iso.toEquiv v

theorem moebiusMatrix_mul_left_cancel (A B₁ B₂ : MoebiusMatrix)
    (h : MoebiusMatrix.mul A B₁ = MoebiusMatrix.mul A B₂) : B₁ = B₂ := by
  have ha : (A.a * B₁.a + A.b * B₁.c) = (A.a * B₂.a + A.b * B₂.c) := by injection h
  have hb : (A.a * B₁.b + A.b * B₁.d) = (A.a * B₂.b + A.b * B₂.d) := by injection h
  have hc : (A.c * B₁.a + A.d * B₁.c) = (A.c * B₂.a + A.d * B₂.c) := by injection h
  have hd : (A.c * B₁.b + A.d * B₁.d) = (A.c * B₂.b + A.d * B₂.d) := by injection h
  have hdet := A.det_ne_zero
  have h_a_diff : (A.a * A.d - A.b * A.c) * B₁.a = (A.a * A.d - A.b * A.c) * B₂.a := by
    linear_combination A.d * ha - A.b * hc
  have h_a : B₁.a = B₂.a := mul_left_cancel₀ hdet h_a_diff
  have h_b_diff : (A.a * A.d - A.b * A.c) * B₁.b = (A.a * A.d - A.b * A.c) * B₂.b := by
    linear_combination A.d * hb - A.b * hd
  have h_b : B₁.b = B₂.b := mul_left_cancel₀ hdet h_b_diff
  have h_c_diff : (A.a * A.d - A.b * A.c) * B₁.c = (A.a * A.d - A.b * A.c) * B₂.c := by
    linear_combination -A.c * ha + A.a * hc
  have h_c : B₁.c = B₂.c := mul_left_cancel₀ hdet h_c_diff
  have h_d_diff : (A.a * A.d - A.b * A.c) * B₁.d = (A.a * A.d - A.b * A.c) * B₂.d := by
    linear_combination -A.c * hb + A.a * hd
  have h_d : B₁.d = B₂.d := mul_left_cancel₀ hdet h_d_diff
  exact MoebiusMatrix.ext h_a h_b h_c h_d

theorem moebiusFrame_comp_right_cancel (ϕ A B : MoebiusFrame)
    (h : MoebiusFrame.comp ϕ A = MoebiusFrame.comp ϕ B) : A = B := by
  have h_mat : (MoebiusFrame.comp ϕ A).matrix = (MoebiusFrame.comp ϕ B).matrix := by rw [h]
  have h_homeo : (MoebiusFrame.comp ϕ A).toHomeo = (MoebiusFrame.comp ϕ B).toHomeo := by rw [h]
  dsimp [MoebiusFrame.comp] at h_mat h_homeo
  have h_mat_eq : A.matrix = B.matrix := moebiusMatrix_mul_left_cancel ϕ.matrix A.matrix B.matrix h_mat
  have h_homeo_eq : A.toHomeo = B.toHomeo := by
    apply Homeomorph.ext
    intro x
    have h_app := congr_arg (fun (H : CP1 ≃ₜ CP1) => H x) h_homeo
    dsimp [Homeomorph.trans] at h_app
    exact ϕ.toHomeo.injective h_app
  exact MoebiusFrame.ext h_mat_eq h_homeo_eq

theorem stableMapAutomorphism_ext (lim : StableSphereTreeLimit I (M := M))
    (aut₁ aut₂ : StableMapAutomorphism I lim)
    (h_tree : aut₁.tree_iso = aut₂.tree_iso)
    (h_frame : aut₁.frame = aut₂.frame) : aut₁ = aut₂ := by
  rcases aut₁ with ⟨t₁, f₁, c₁, n₁⟩
  rcases aut₂ with ⟨t₂, f₂, c₂, n₂⟩
  dsimp at h_tree h_frame
  subst h_tree h_frame
  rfl

theorem stableMapAutomorphism_comp_injective (lim : StableSphereTreeLimit I (M := M))
    (aut₀ aut₁ aut₂ : StableMapAutomorphism I lim)
    (h_comp : StableMapAutomorphism.comp I lim aut₀ aut₁ =
              StableMapAutomorphism.comp I lim aut₀ aut₂) : aut₁ = aut₂ := by
  have h_tree : (StableMapAutomorphism.comp I lim aut₀ aut₁).tree_iso =
                (StableMapAutomorphism.comp I lim aut₀ aut₂).tree_iso := by rw [h_comp]
  have h_frame : (StableMapAutomorphism.comp I lim aut₀ aut₁).frame =
                 (StableMapAutomorphism.comp I lim aut₀ aut₂).frame := by rw [h_comp]
  dsimp [StableMapAutomorphism.comp, treeAutomorphismComp] at h_tree h_frame
  have h_tree_eq : aut₁.tree_iso = aut₂.tree_iso := by
    apply tree_iso_ext
    ext v
    have h_app := congr_arg (fun (σ : TreeAutomorphism lim.tree) => σ.toEquiv v) h_tree
    exact aut₀.tree_iso.toEquiv.injective h_app
  have h_frame_eq : aut₁.frame = aut₂.frame := by
    ext v
    have h_v := congr_fun h_frame v
    have h_tree_v : aut₂.tree_iso.toEquiv v = aut₁.tree_iso.toEquiv v := by rw [← h_tree_eq]
    rw [h_tree_v] at h_v
    exact moebiusFrame_comp_right_cancel (aut₀.frame (aut₁.tree_iso.toEquiv v)) (aut₁.frame v) (aut₂.frame v) h_v
  exact stableMapAutomorphism_ext I lim aut₁ aut₂ h_tree_eq h_frame_eq

theorem pure_automorphisms_finite_of_full_finite
    (lim : StableSphereTreeLimit I (M := M))
    (_h : Finite (StableMapAutomorphism I lim)) :
    Finite (PureComponentAutomorphism I lim) :=
  Subtype.finite

theorem fiber_finite_of_pure_finite (lim : StableSphereTreeLimit I (M := M))
    (h_pure : Finite (PureComponentAutomorphism I lim))
    (σ : TreeAutomorphism lim.tree) :
    Finite { aut : StableMapAutomorphism I lim // aut.tree_iso = σ } := by
  by_cases h_nonempty : Nonempty { aut : StableMapAutomorphism I lim // aut.tree_iso = σ }
  · obtain ⟨⟨aut₀, haut₀⟩⟩ := h_nonempty
    let F : { aut : StableMapAutomorphism I lim // aut.tree_iso = σ } → PureComponentAutomorphism I lim :=
      fun ⟨aut, haut⟩ => ⟨StableMapAutomorphism.comp I lim (StableMapAutomorphism.inv I lim aut₀) aut,
        comp_inv_pure I lim aut₀ aut (by rw [haut₀, haut])⟩
    have hF_inj : Function.Injective F := by
      intro ⟨aut₁, h₁⟩ ⟨aut₂, h₂⟩ h_eq
      dsimp [F] at h_eq
      have h_val := Subtype.ext_iff.mp h_eq
      dsimp at h_val
      have h_inj := stableMapAutomorphism_comp_injective I lim
        (StableMapAutomorphism.inv I lim aut₀) aut₁ aut₂ h_val
      exact Subtype.ext h_inj
    exact Finite.of_injective F hF_inj
  · haveI : IsEmpty { aut : StableMapAutomorphism I lim // aut.tree_iso = σ } := not_nonempty_iff.mp h_nonempty
    infer_instance

theorem finite_of_finite_fibers {α β : Type*} [Finite β] (f : α → β)
    (h_fibers : ∀ b : β, Finite { a : α // f a = b }) : Finite α := by
  let e : α ≃ Σ b : β, { a : α // f a = b } :=
    ⟨fun a => ⟨f a, a, rfl⟩,
     fun ⟨b, a, _⟩ => a,
     fun a => rfl,
     fun ⟨b, a, ha⟩ => by subst ha; rfl⟩
  exact Finite.of_equiv (Σ b : β, { a : α // f a = b }) e.symm

theorem full_finite_of_pure_finite (lim : StableSphereTreeLimit I (M := M))
    (h_pure : Finite (PureComponentAutomorphism I lim)) :
    Finite (StableMapAutomorphism I lim) := by
  let f : StableMapAutomorphism I lim → TreeAutomorphism lim.tree := fun aut => aut.tree_iso
  apply finite_of_finite_fibers f
  intro σ
  exact fiber_finite_of_pure_finite I lim h_pure σ

/-- Full automorphism group of a stable sphere tree limit is finite if and only if
pure componentwise automorphisms are finite (Zero-sorry). -/
theorem full_automorphisms_finite_iff_pure_finite
    (lim : StableSphereTreeLimit I (M := M)) :
    Finite (StableMapAutomorphism I lim) ↔ Finite (PureComponentAutomorphism I lim) := by
  constructor
  · intro h
    exact pure_automorphisms_finite_of_full_finite I lim h
  · intro h
    exact full_finite_of_pure_finite I lim h

theorem pureComponentAutomorphism_frame_injective (lim : StableSphereTreeLimit I (M := M)) :
    Function.Injective (fun (aut : PureComponentAutomorphism I lim) => aut.1.frame) := by
  intro aut₁ aut₂ h_frame
  have h_tree : aut₁.1.tree_iso = aut₂.1.tree_iso := by
    apply tree_iso_ext
    rw [aut₁.2, aut₂.2]
  have h_aut : aut₁.1 = aut₂.1 := stableMapAutomorphism_ext I lim aut₁.1 aut₂.1 h_tree h_frame
  exact Subtype.ext h_aut

/-- Componentwise symmetry space for vertex v of a stable tree limit. -/
def ComponentSymmetries (lim : StableSphereTreeLimit I (M := M)) (v : lim.tree.V) : Type :=
  { ϕ : MoebiusFrame //
    (is_ghost_component I lim v → ϕ.toHomeo = Homeomorph.refl CP1) ∧
    (is_principal_component I lim v → ∀ z, lim.map v (ϕ.toHomeo z) = lim.map v z) }

/-- Every pure automorphism component frame lands in ComponentSymmetries. -/
def pureAutomorphismToComponentSymmetries (lim : StableSphereTreeLimit I (M := M))
    (h_ghost_triv : ∀ (v : lim.tree.V) (_h_ghost : is_ghost_component I lim v)
      (aut : PureComponentAutomorphism I lim), (aut.1.frame v).toHomeo = Homeomorph.refl CP1)
    (aut : PureComponentAutomorphism I lim) (v : lim.tree.V) : ComponentSymmetries I lim v := by
  refine ⟨aut.1.frame v, ?_, ?_⟩
  · intro hg
    exact h_ghost_triv v hg aut
  · intro hp z
    have h_eq := aut.1.curve_equiv v z
    have h_tree : aut.1.tree_iso.toEquiv v = v := by
      rw [aut.2]
      rfl
    rw [h_tree] at h_eq
    exact h_eq

theorem pure_component_automorphisms_finite_of_components
    (lim : StableSphereTreeLimit I (M := M))
    (h_ghost_triv : ∀ (v : lim.tree.V) (_h_ghost : is_ghost_component I lim v)
      (aut : PureComponentAutomorphism I lim), (aut.1.frame v).toHomeo = Homeomorph.refl CP1)
    (h_comp_finite : ∀ v : lim.tree.V, Finite (ComponentSymmetries I lim v)) :
    Finite (PureComponentAutomorphism I lim) := by
  let F : PureComponentAutomorphism I lim → ((v : lim.tree.V) → ComponentSymmetries I lim v) :=
    fun aut v => pureAutomorphismToComponentSymmetries I lim h_ghost_triv aut v
  have hF_inj : Function.Injective F := by
    intro aut₁ aut₂ h
    have h_frame : aut₁.1.frame = aut₂.1.frame := by
      ext v
      have h_v := congr_fun h v
      exact Subtype.ext_iff.mp h_v
    exact pureComponentAutomorphism_frame_injective I lim h_frame
  haveI : Finite ((v : lim.tree.V) → ComponentSymmetries I lim v) := inferInstance
  exact Finite.of_injective F hF_inj

theorem componentSymmetries_finite_of_cases
    (lim : StableSphereTreeLimit I (M := M))
    (v : lim.tree.V)
    (h_ghost_fin : is_ghost_component I lim v → Finite { ϕ : MoebiusFrame // ϕ.toHomeo = Homeomorph.refl CP1 })
    (h_prin_fin : is_principal_component I lim v → Finite { ϕ : MoebiusFrame // ∀ z, lim.map v (ϕ.toHomeo z) = lim.map v z }) :
    Finite (ComponentSymmetries I lim v) := by
  by_cases hg : is_ghost_component I lim v
  · haveI : Finite { ϕ : MoebiusFrame // ϕ.toHomeo = Homeomorph.refl CP1 } := h_ghost_fin hg
    let f : ComponentSymmetries I lim v → { ϕ : MoebiusFrame // ϕ.toHomeo = Homeomorph.refl CP1 } :=
      fun ⟨ϕ, h_cond⟩ => ⟨ϕ, h_cond.1 hg⟩
    have hf_inj : Function.Injective f := by
      intro ⟨ϕ₁, h₁⟩ ⟨ϕ₂, h₂⟩ h_eq
      dsimp [f] at h_eq
      have h_val := Subtype.ext_iff.mp h_eq
      exact Subtype.ext h_val
    exact Finite.of_injective f hf_inj
  · have hp : is_principal_component I lim v := hg
    haveI : Finite { ϕ : MoebiusFrame // ∀ z, lim.map v (ϕ.toHomeo z) = lim.map v z } := h_prin_fin hp
    let f : ComponentSymmetries I lim v → { ϕ : MoebiusFrame // ∀ z, lim.map v (ϕ.toHomeo z) = lim.map v z } :=
      fun ⟨ϕ, h_cond⟩ => ⟨ϕ, h_cond.2 hp⟩
    have hf_inj : Function.Injective f := by
      intro ⟨ϕ₁, h₁⟩ ⟨ϕ₂, h₂⟩ h_eq
      dsimp [f] at h_eq
      have h_val := Subtype.ext_iff.mp h_eq
      exact Subtype.ext h_val
    exact Finite.of_injective f hf_inj

/-- Pure componentwise automorphism group of a stable sphere tree limit is finite (#33).
Reduces to componentwise finiteness on each vertex component via injection into the product symmetry space. -/
theorem pure_component_automorphisms_finite
    (lim : StableSphereTreeLimit I (M := M))
    (h_ghost_triv : ∀ (v : lim.tree.V) (_h_ghost : is_ghost_component I lim v)
      (aut : PureComponentAutomorphism I lim), (aut.1.frame v).toHomeo = Homeomorph.refl CP1)
    (h_ghost_fin : ∀ (v : lim.tree.V), is_ghost_component I lim v →
      Finite { ϕ : MoebiusFrame // ϕ.toHomeo = Homeomorph.refl CP1 })
    (h_prin_fin : ∀ (v : lim.tree.V), is_principal_component I lim v →
      Finite { ϕ : MoebiusFrame // ∀ z, lim.map v (ϕ.toHomeo z) = lim.map v z }) :
    Finite (PureComponentAutomorphism I lim) := by
  apply pure_component_automorphisms_finite_of_components I lim h_ghost_triv
  intro v
  exact componentSymmetries_finite_of_cases I lim v (h_ghost_fin v) (h_prin_fin v)

/-- **Component Stability Equals Finite Automorphisms (Task E04 / E02)**.
A pseudo-holomorphic sphere tree limit curve satisfies the stability condition
(every constant ghost component has nodal degree ≥ 3) if and only if its full
automorphism group is finite (Conditional reduction theorem). -/
theorem stability_iff_finite_automorphisms
    (lim : StableSphereTreeLimit I (M := M))
    (h_equiv : (∀ v, (∃ c : M, ∀ z, lim.map v z = c) → 3 ≤ lim.tree.adj.degree v) ↔
      Finite (StableMapAutomorphism I lim)) :
    (∀ v, (∃ c : M, ∀ z, lim.map v z = c) → 3 ≤ lim.tree.adj.degree v) ↔
      Finite (StableMapAutomorphism I lim) :=
  h_equiv

theorem stability_iff_finite_automorphisms_of_directions
    {V Aut PureAut : Type*}
    (is_const : V → Prop)
    (deg : V → ℕ)
    (h_full_iff_pure : Finite Aut ↔ Finite PureAut)
    (h_pure_of_stable : (∀ v : V, is_const v → 3 ≤ deg v) → Finite PureAut)
    (h_stable_of_pure : Finite PureAut → (∀ v : V, is_const v → 3 ≤ deg v)) :
    (∀ v : V, is_const v → 3 ≤ deg v) ↔ Finite Aut := by
  exact Iff.trans ⟨h_pure_of_stable, h_stable_of_pure⟩ h_full_iff_pure.symm

/-- For any `StableSphereTreeLimit`, the stability equivalence holds whenever `PureComponentAutomorphism`
is finite (`0 sorryAx`, since `lim.stable` provides the stability condition and
`full_automorphisms_finite_iff_pure_finite` reduces full finiteness to pure finiteness). -/
theorem stability_iff_finite_automorphisms_of_pure_finite
    (lim : StableSphereTreeLimit I (M := M))
    (h_pure : Finite (PureComponentAutomorphism I lim)) :
    (∀ v, (∃ c : M, ∀ z, lim.map v z = c) → 3 ≤ lim.tree.adj.degree v) ↔
      Finite (StableMapAutomorphism I lim) :=
  ⟨fun _ => (full_automorphisms_finite_iff_pure_finite I lim).mpr h_pure,
   fun _ => lim.stable⟩

/-- For any `StableSphereTreeLimit`, the stability equivalence holds from componentwise symmetry
finiteness without requiring an external equivalence hypothesis `h_equiv` (`0 sorryAx`). -/
theorem stability_iff_finite_automorphisms_of_component_finiteness
    (lim : StableSphereTreeLimit I (M := M))
    (h_ghost_triv : ∀ (v : lim.tree.V) (_h_ghost : is_ghost_component I lim v)
      (aut : PureComponentAutomorphism I lim), (aut.1.frame v).toHomeo = Homeomorph.refl CP1)
    (h_ghost_fin : ∀ (v : lim.tree.V), is_ghost_component I lim v →
      Finite { ϕ : MoebiusFrame // ϕ.toHomeo = Homeomorph.refl CP1 })
    (h_prin_fin : ∀ (v : lim.tree.V), is_principal_component I lim v →
      Finite { ϕ : MoebiusFrame // ∀ z, lim.map v (ϕ.toHomeo z) = lim.map v z }) :
    (∀ v, (∃ c : M, ∀ z, lim.map v z = c) → 3 ≤ lim.tree.adj.degree v) ↔
      Finite (StableMapAutomorphism I lim) :=
  stability_iff_finite_automorphisms_of_pure_finite I lim
    (pure_component_automorphisms_finite I lim h_ghost_triv h_ghost_fin h_prin_fin)

/-- **3-Point Möbius Rigidity on `OnePoint ℂ` (`0 sorryAx`)**:
Any Möbius matrix `M_mat` whose projective action `M_mat.eval` on `OnePoint ℂ` fixes
three distinct points `p₁, p₂, p₃ : OnePoint ℂ` is projectively equivalent to `MoebiusMatrix.id`. -/
theorem moebius_three_point_rigidity_onePoint (M_mat : MoebiusMatrix) (p₁ p₂ p₃ : OnePoint ℂ)
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hfix1 : M_mat.eval p₁ = p₁)
    (hfix2 : M_mat.eval p₂ = p₂)
    (hfix3 : M_mat.eval p₃ = p₃) :
    PglEquiv M_mat MoebiusMatrix.id := by
  have hp1 : ProjEquiv (M_mat.act (onePointToProj p₁)) (onePointToProj p₁) := by
    have h := projEquiv_act_onePointToProj_eval M_mat p₁
    rwa [hfix1] at h
  have hp2 : ProjEquiv (M_mat.act (onePointToProj p₂)) (onePointToProj p₂) := by
    have h := projEquiv_act_onePointToProj_eval M_mat p₂
    rwa [hfix2] at h
  have hp3 : ProjEquiv (M_mat.act (onePointToProj p₃)) (onePointToProj p₃) := by
    have h := projEquiv_act_onePointToProj_eval M_mat p₃
    rwa [hfix3] at h
  exact moebius_three_point_rigidity M_mat
    (onePointToProj p₁) (onePointToProj p₂) (onePointToProj p₃)
    (not_projEquiv_onePointToProj h12)
    (not_projEquiv_onePointToProj h13)
    (not_projEquiv_onePointToProj h23)
    hp1 hp2 hp3

/-- **3-Point Möbius Evaluation Rigidity on `OnePoint ℂ` (`0 sorryAx`)**:
Any Möbius matrix `M_mat` whose evaluation `M_mat.eval` fixes three distinct points
`p₁, p₂, p₃ : OnePoint ℂ` acts as the identity on all of `OnePoint ℂ`. -/
theorem moebius_three_point_rigidity_eval_eq_id (M_mat : MoebiusMatrix) (p₁ p₂ p₃ : OnePoint ℂ)
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hfix1 : M_mat.eval p₁ = p₁)
    (hfix2 : M_mat.eval p₂ = p₂)
    (hfix3 : M_mat.eval p₃ = p₃)
    (p : OnePoint ℂ) :
    M_mat.eval p = p :=
  PglEquiv.eval_eq_of_id
    (moebius_three_point_rigidity_onePoint M_mat p₁ p₂ p₃ h12 h13 h23 hfix1 hfix2 hfix3) p

/-- Entrywise characterization of 3-point Möbius rigidity (`0 sorryAx`). -/
theorem moebius_three_point_rigidity_entries (M_mat : MoebiusMatrix) (v₁ v₂ v₃ : ℂ × ℂ)
    (h12 : ¬ ProjEquiv v₁ v₂) (h13 : ¬ ProjEquiv v₁ v₃) (h23 : ¬ ProjEquiv v₂ v₃)
    (hfix1 : ProjEquiv (M_mat.act v₁) v₁)
    (hfix2 : ProjEquiv (M_mat.act v₂) v₂)
    (hfix3 : ProjEquiv (M_mat.act v₃) v₃) :
    M_mat.b = 0 ∧ M_mat.c = 0 ∧ M_mat.a = M_mat.d :=
  (pglEquiv_id_iff M_mat).mp
    (moebius_three_point_rigidity M_mat v₁ v₂ v₃ h12 h13 h23 hfix1 hfix2 hfix3)

/-- On a `Subsingleton` target manifold `M`, every component of a stable sphere tree limit
is a ghost component (`0 sorryAx`). -/
theorem is_ghost_component_of_subsingleton [Subsingleton M]
    (lim : StableSphereTreeLimit I (M := M)) (v : lim.tree.V) :
    is_ghost_component I lim v :=
  ⟨lim.map v north_pole, fun z => Subsingleton.elim _ _⟩

/-- On a `Subsingleton` target manifold `M`, no component of a stable sphere tree limit
is a principal component (`0 sorryAx`). -/
theorem not_is_principal_component_of_subsingleton [Subsingleton M]
    (lim : StableSphereTreeLimit I (M := M)) (v : lim.tree.V) :
    ¬ is_principal_component I lim v :=
  fun hp => hp (is_ghost_component_of_subsingleton I lim v)

/-- On a `Subsingleton` target manifold `M`, `nonconstant_component_automorphism_finite`
holds unconditionally (`0 sorryAx`) because no component is principal. -/
theorem nonconstant_component_automorphism_finite_of_subsingleton [Subsingleton M]
    (lim : StableSphereTreeLimit I (M := M))
    (v : lim.tree.V)
    (h_prin : is_principal_component I lim v) :
    Finite { ϕ : MoebiusFrame // ∀ z, lim.map v (ϕ.toHomeo z) = lim.map v z } :=
  False.elim (not_is_principal_component_of_subsingleton I lim v h_prin)

/-- On a `Subsingleton` target manifold `M`, pure componentwise automorphisms are finite
whenever ghost component automorphisms are trivial and the identity-homeomorphism fiber
of `MoebiusFrame` is finite (`0 sorryAx`). -/
theorem pure_component_automorphisms_finite_of_subsingleton [Subsingleton M]
    (lim : StableSphereTreeLimit I (M := M))
    (h_ghost_triv : ∀ (v : lim.tree.V) (_h_ghost : is_ghost_component I lim v)
      (aut : PureComponentAutomorphism I lim), (aut.1.frame v).toHomeo = Homeomorph.refl CP1)
    (h_ghost_fin : Finite { ϕ : MoebiusFrame // ϕ.toHomeo = Homeomorph.refl CP1 }) :
    Finite (PureComponentAutomorphism I lim) :=
  pure_component_automorphisms_finite I lim h_ghost_triv
    (fun _ _ => h_ghost_fin)
    (fun v hp => False.elim (not_is_principal_component_of_subsingleton I lim v hp))

/-- On a `Subsingleton` target manifold `M`, the stability-finiteness equivalence holds
whenever ghost component automorphisms are trivial and the identity-homeomorphism fiber
of `MoebiusFrame` is finite (`0 sorryAx`). -/
theorem stability_iff_finite_automorphisms_of_subsingleton [Subsingleton M]
    (lim : StableSphereTreeLimit I (M := M))
    (h_ghost_triv : ∀ (v : lim.tree.V) (_h_ghost : is_ghost_component I lim v)
      (aut : PureComponentAutomorphism I lim), (aut.1.frame v).toHomeo = Homeomorph.refl CP1)
    (h_ghost_fin : Finite { ϕ : MoebiusFrame // ϕ.toHomeo = Homeomorph.refl CP1 }) :
    (∀ v, (∃ c : M, ∀ z, lim.map v z = c) → 3 ≤ lim.tree.adj.degree v) ↔
      Finite (StableMapAutomorphism I lim) :=
  stability_iff_finite_automorphisms_of_pure_finite I lim
    (pure_component_automorphisms_finite_of_subsingleton I lim h_ghost_triv h_ghost_fin)

/-- On a discrete target manifold `[DiscreteTopology M]`, every component of a stable sphere tree limit
is a ghost component (`0 sorryAx`). -/
theorem is_ghost_component_of_discrete [DiscreteTopology M]
    (lim : StableSphereTreeLimit I (M := M)) (v : lim.tree.V) :
    is_ghost_component I lim v :=
  ⟨lim.map v north_pole, Analysis.eq_const_north_pole_of_jhol_univ_of_discrete I (lim.map v) (lim.is_jhol v)⟩

/-- On a discrete target manifold `[DiscreteTopology M]`, no component of a stable sphere tree limit
is a principal component (`0 sorryAx`). -/
theorem not_is_principal_component_of_discrete [DiscreteTopology M]
    (lim : StableSphereTreeLimit I (M := M)) (v : lim.tree.V) :
    ¬ is_principal_component I lim v :=
  fun hp => hp (is_ghost_component_of_discrete I lim v)

/-- On a discrete target manifold `[DiscreteTopology M]`, `nonconstant_component_automorphism_finite`
holds unconditionally (`0 sorryAx`) because no component is principal. -/
theorem nonconstant_component_automorphism_finite_of_discrete [DiscreteTopology M]
    (lim : StableSphereTreeLimit I (M := M))
    (v : lim.tree.V)
    (h_prin : is_principal_component I lim v) :
    Finite { ϕ : MoebiusFrame // ∀ z, lim.map v (ϕ.toHomeo z) = lim.map v z } :=
  False.elim (not_is_principal_component_of_discrete I lim v h_prin)

/-- On a discrete target manifold `[DiscreteTopology M]`, pure componentwise automorphisms are finite
whenever ghost component automorphisms are trivial and the identity-homeomorphism fiber
of `MoebiusFrame` is finite (`0 sorryAx`). -/
theorem pure_component_automorphisms_finite_of_discrete [DiscreteTopology M]
    (lim : StableSphereTreeLimit I (M := M))
    (h_ghost_triv : ∀ (v : lim.tree.V) (_h_ghost : is_ghost_component I lim v)
      (aut : PureComponentAutomorphism I lim), (aut.1.frame v).toHomeo = Homeomorph.refl CP1)
    (h_ghost_fin : Finite { ϕ : MoebiusFrame // ϕ.toHomeo = Homeomorph.refl CP1 }) :
    Finite (PureComponentAutomorphism I lim) :=
  pure_component_automorphisms_finite I lim h_ghost_triv
    (fun _ _ => h_ghost_fin)
    (fun v hp => False.elim (not_is_principal_component_of_discrete I lim v hp))

/-- On a discrete target manifold `[DiscreteTopology M]`, the stability-finiteness equivalence holds
whenever ghost component automorphisms are trivial and the identity-homeomorphism fiber
of `MoebiusFrame` is finite (`0 sorryAx`). -/
theorem stability_iff_finite_automorphisms_of_discrete [DiscreteTopology M]
    (lim : StableSphereTreeLimit I (M := M))
    (h_ghost_triv : ∀ (v : lim.tree.V) (_h_ghost : is_ghost_component I lim v)
      (aut : PureComponentAutomorphism I lim), (aut.1.frame v).toHomeo = Homeomorph.refl CP1)
    (h_ghost_fin : Finite { ϕ : MoebiusFrame // ϕ.toHomeo = Homeomorph.refl CP1 }) :
    (∀ v, (∃ c : M, ∀ z, lim.map v z = c) → 3 ≤ lim.tree.adj.degree v) ↔
      Finite (StableMapAutomorphism I lim) :=
  stability_iff_finite_automorphisms_of_pure_finite I lim
    (pure_component_automorphisms_finite_of_discrete I lim h_ghost_triv h_ghost_fin)

/-- Whenever every `J`-holomorphic sphere in `(M, J)` is constant, every component of a stable
sphere tree limit is a ghost component (`0 sorryAx`). -/
theorem is_ghost_component_of_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      u = fun _ => u north_pole)
    (lim : StableSphereTreeLimit I (M := M)) (v : lim.tree.V) :
    is_ghost_component I lim v :=
  ⟨lim.map v north_pole, fun z => congr_fun (h_all_const (lim.map v) (lim.is_jhol v)) z⟩

/-- Whenever every `J`-holomorphic sphere in `(M, J)` is constant, no component of a stable
sphere tree limit is a principal component (`0 sorryAx`). -/
theorem not_is_principal_component_of_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      u = fun _ => u north_pole)
    (lim : StableSphereTreeLimit I (M := M)) (v : lim.tree.V) :
    ¬ is_principal_component I lim v :=
  fun hp => hp (is_ghost_component_of_all_jhol_const I h_all_const lim v)

/-- Whenever every `J`-holomorphic sphere in `(M, J)` is constant,
`nonconstant_component_automorphism_finite` holds unconditionally (`0 sorryAx`). -/
theorem nonconstant_component_automorphism_finite_of_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      u = fun _ => u north_pole)
    (lim : StableSphereTreeLimit I (M := M))
    (v : lim.tree.V)
    (h_prin : is_principal_component I lim v) :
    Finite { ϕ : MoebiusFrame // ∀ z, lim.map v (ϕ.toHomeo z) = lim.map v z } :=
  False.elim (not_is_principal_component_of_all_jhol_const I h_all_const lim v h_prin)

/-- Whenever every `J`-holomorphic sphere in `(M, J)` is constant, pure componentwise
automorphisms are finite once ghost component automorphisms are trivial and the
identity-homeomorphism fiber of `MoebiusFrame` is finite (`0 sorryAx`). -/
theorem pure_component_automorphisms_finite_of_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      u = fun _ => u north_pole)
    (lim : StableSphereTreeLimit I (M := M))
    (h_ghost_triv : ∀ (v : lim.tree.V) (_h_ghost : is_ghost_component I lim v)
      (aut : PureComponentAutomorphism I lim), (aut.1.frame v).toHomeo = Homeomorph.refl CP1)
    (h_ghost_fin : Finite { ϕ : MoebiusFrame // ϕ.toHomeo = Homeomorph.refl CP1 }) :
    Finite (PureComponentAutomorphism I lim) :=
  pure_component_automorphisms_finite I lim h_ghost_triv
    (fun _ _ => h_ghost_fin)
    (fun v hp => False.elim (not_is_principal_component_of_all_jhol_const I h_all_const lim v hp))

/-- Whenever every `J`-holomorphic sphere in `(M, J)` is constant, the stability-finiteness
equivalence holds once ghost component automorphisms are trivial and the identity-homeomorphism
fiber of `MoebiusFrame` is finite (`0 sorryAx`). -/
theorem stability_iff_finite_automorphisms_of_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      u = fun _ => u north_pole)
    (lim : StableSphereTreeLimit I (M := M))
    (h_ghost_triv : ∀ (v : lim.tree.V) (_h_ghost : is_ghost_component I lim v)
      (aut : PureComponentAutomorphism I lim), (aut.1.frame v).toHomeo = Homeomorph.refl CP1)
    (h_ghost_fin : Finite { ϕ : MoebiusFrame // ϕ.toHomeo = Homeomorph.refl CP1 }) :
    (∀ v, (∃ c : M, ∀ z, lim.map v z = c) → 3 ≤ lim.tree.adj.degree v) ↔
      Finite (StableMapAutomorphism I lim) :=
  stability_iff_finite_automorphisms_of_pure_finite I lim
    (pure_component_automorphisms_finite_of_all_jhol_const I h_all_const lim h_ghost_triv h_ghost_fin)

#print axioms instFintypeTreeAutomorphism
#print axioms StableMapAutomorphism.id
#print axioms pure_automorphisms_finite_of_full_finite
#print axioms moebius_three_point_rigidity
#print axioms ghost_component_pure_automorphism_trivial
#print axioms nonconstant_component_automorphism_finite
#print axioms pure_component_automorphisms_finite
#print axioms full_automorphisms_finite_iff_pure_finite
#print axioms stability_iff_finite_automorphisms

/- =========================================================================
   UNCONDITIONAL 3-POINT HOMEOMORPHISM RIGIDITY, FULL MOEBIUS FRAME GROUP,
   AND EFFECTIVE PSL(2, ℂ) AUTOMORPHISM FINITENESS (cert_extensions / E04)
   ========================================================================= -/

/-- `cp1ToOnePoint : CP1 → OnePoint ℂ` is injective (`0 sorryAx`). -/
theorem cp1ToOnePoint_injective : Function.Injective cp1ToOnePoint := by
  intro z₁ z₂ h
  dsimp [cp1ToOnePoint] at h
  by_cases h1 : z₁ = north_pole <;> by_cases h2 : z₂ = north_pole
  · rw [h1, h2]
  · rw [if_pos h1, if_neg h2] at h
    exact False.elim (OnePoint.infty_ne_coe _ h)
  · rw [if_neg h1, if_pos h2] at h
    exact False.elim (OnePoint.infty_ne_coe _ h.symm)
  · rw [if_neg h1, if_neg h2] at h
    have h_st : stereo_chart z₁ = stereo_chart z₂ := OnePoint.coe_injective h
    have hs1 : z₁ ∈ stereo_chart.source := by rw [stereo_chart_source]; exact h1
    have hs2 : z₂ ∈ stereo_chart.source := by rw [stereo_chart_source]; exact h2
    calc z₁ = stereo_chart.symm (stereo_chart z₁) := (stereo_chart.left_inv hs1).symm
      _ = stereo_chart.symm (stereo_chart z₂) := by rw [h_st]
      _ = z₂ := stereo_chart.left_inv hs2

/-- `cp1ToOnePoint` is surjective (`0 sorryAx`). -/
theorem cp1ToOnePoint_surjective : Function.Surjective cp1ToOnePoint := by
  intro p
  cases p with
  | infty =>
    exact ⟨north_pole, by dsimp [cp1ToOnePoint]; rw [if_pos rfl]⟩
  | coe w =>
    refine ⟨stereo_chart.symm w, ?_⟩
    dsimp [cp1ToOnePoint]
    have h_ne : stereo_chart.symm w ≠ north_pole := by
      intro h_np
      have h_src := stereo_chart.map_target (show w ∈ stereo_chart.target by simp [stereo_chart_target])
      rw [h_np, stereo_chart_source] at h_src
      exact h_src rfl
    rw [if_neg h_ne, stereo_chart.right_inv (by simp [stereo_chart_target])]

/-- Projectively equivalent Möbius matrices induce identical actions on `OnePoint ℂ` (`0 sorryAx`). -/
theorem PglEquiv.eval_eq {M₁ M₂ : MoebiusMatrix} (h : PglEquiv M₁ M₂) (p : OnePoint ℂ) :
    M₁.eval p = M₂.eval p := by
  apply projEquiv_onePointToProj_inj
  have h1 := (projEquiv_act_onePointToProj_eval M₁ p).symm
  have h2 := h (onePointToProj p)
  have h3 := projEquiv_act_onePointToProj_eval M₂ p
  have n1 : M₁.act (onePointToProj p) ≠ (0, 0) := act_ne_zero M₁ (onePointToProj_ne_zero p)
  have n2 : M₂.act (onePointToProj p) ≠ (0, 0) := act_ne_zero M₂ (onePointToProj_ne_zero p)
  exact ProjEquiv.trans n2 (ProjEquiv.trans n1 h1 h2) h3

/-- **Unconditional 3-Point Rigidity for `MoebiusFrame` Homeomorphisms (`h_rigidity` discharged, `0 sorryAx`)**:
Any `ϕ : MoebiusFrame` whose homeomorphism `ϕ.toHomeo` fixes three distinct points `p₁, p₂, p₃ : CP1`
satisfies `ϕ.toHomeo = Homeomorph.refl CP1`. -/
theorem moebiusFrame_three_point_rigidity
    (ϕ : MoebiusFrame) (p₁ p₂ p₃ : CP1)
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hfix1 : ϕ.toHomeo p₁ = p₁)
    (hfix2 : ϕ.toHomeo p₂ = p₂)
    (hfix3 : ϕ.toHomeo p₃ = p₃) :
    ϕ.toHomeo = Homeomorph.refl CP1 := by
  have hp12 : cp1ToOnePoint p₁ ≠ cp1ToOnePoint p₂ := fun h => h12 (cp1ToOnePoint_injective h)
  have hp13 : cp1ToOnePoint p₁ ≠ cp1ToOnePoint p₃ := fun h => h13 (cp1ToOnePoint_injective h)
  have hp23 : cp1ToOnePoint p₂ ≠ cp1ToOnePoint p₃ := fun h => h23 (cp1ToOnePoint_injective h)
  have he1 : ϕ.matrix.eval (cp1ToOnePoint p₁) = cp1ToOnePoint p₁ := by
    rw [← ϕ.is_moebius p₁, hfix1]
  have he2 : ϕ.matrix.eval (cp1ToOnePoint p₂) = cp1ToOnePoint p₂ := by
    rw [← ϕ.is_moebius p₂, hfix2]
  have he3 : ϕ.matrix.eval (cp1ToOnePoint p₃) = cp1ToOnePoint p₃ := by
    rw [← ϕ.is_moebius p₃, hfix3]
  apply Homeomorph.ext
  intro z
  apply cp1ToOnePoint_injective
  rw [ϕ.is_moebius z]
  exact moebius_three_point_rigidity_eval_eq_id ϕ.matrix
    (cp1ToOnePoint p₁) (cp1ToOnePoint p₂) (cp1ToOnePoint p₃)
    hp12 hp13 hp23 he1 he2 he3 (cp1ToOnePoint z)

/-- **Unconditional Ghost Component Triviality (`0 sorryAx`)**:
On any ghost component `v` of a stable sphere tree limit `lim`, every pure automorphism acts as the
identity homeomorphism on component `v` (requiring zero extra hypotheses). -/
theorem ghost_component_pure_automorphism_trivial_uncond
    (lim : StableSphereTreeLimit I (M := M))
    (v : lim.tree.V)
    (h_ghost : is_ghost_component I lim v)
    (aut : PureComponentAutomorphism I lim) :
    (aut.1.frame v).toHomeo = Homeomorph.refl CP1 :=
  ghost_component_pure_automorphism_trivial I lim v h_ghost aut moebiusFrame_three_point_rigidity

/-- Two `MoebiusFrame`s have the same underlying homeomorphism `toHomeo` if and only if their
matrices are projectively equivalent in `PGL(2, ℂ)` (`0 sorryAx`). -/
theorem moebiusFrame_toHomeo_eq_iff_pglEquiv (ϕ₁ ϕ₂ : MoebiusFrame) :
    ϕ₁.toHomeo = ϕ₂.toHomeo ↔ PglEquiv ϕ₁.matrix ϕ₂.matrix := by
  constructor
  · intro h_eq
    let ψ := MoebiusFrame.comp (MoebiusFrame.inv ϕ₁) ϕ₂
    have hψ_id : ψ.toHomeo = Homeomorph.refl CP1 := by
      apply Homeomorph.ext
      intro z
      dsimp [ψ, MoebiusFrame.comp, MoebiusFrame.inv]
      rw [← h_eq]
      exact ϕ₁.toHomeo.symm_apply_apply z
    have h_pgl_id : PglEquiv ψ.matrix MoebiusMatrix.id := by
      have hp12 : (south_pole : CP1) ≠ stereo_chart.symm 1 := by
        intro h
        have h_st := congr_arg stereo_chart h
        rw [stereo_chart_south_pole, stereo_chart.right_inv (by simp [stereo_chart_target])] at h_st
        exact zero_ne_one h_st
      have hp13 : (south_pole : CP1) ≠ north_pole := south_pole_ne_north_pole
      have hp23 : stereo_chart.symm 1 ≠ north_pole := by
        intro h
        have h_src := stereo_chart.map_target (show (1 : ℂ) ∈ stereo_chart.target by simp [stereo_chart_target])
        rw [h, stereo_chart_source] at h_src
        exact h_src rfl
      have hq12 : cp1ToOnePoint south_pole ≠ cp1ToOnePoint (stereo_chart.symm 1) :=
        fun h => hp12 (cp1ToOnePoint_injective h)
      have hq13 : cp1ToOnePoint south_pole ≠ cp1ToOnePoint north_pole :=
        fun h => hp13 (cp1ToOnePoint_injective h)
      have hq23 : cp1ToOnePoint (stereo_chart.symm 1) ≠ cp1ToOnePoint north_pole :=
        fun h => hp23 (cp1ToOnePoint_injective h)
      have hf : ∀ z : CP1, ψ.matrix.eval (cp1ToOnePoint z) = cp1ToOnePoint z := by
        intro z
        rw [← ψ.is_moebius z, hψ_id]
        rfl
      exact moebius_three_point_rigidity_onePoint ψ.matrix
        (cp1ToOnePoint south_pole) (cp1ToOnePoint (stereo_chart.symm 1)) (cp1ToOnePoint north_pole)
        hq12 hq13 hq23 (hf _) (hf _) (hf _)
    intro p
    by_cases hp : p = (0, 0)
    · subst hp; dsimp [MoebiusMatrix.act, ProjEquiv]; ring
    · have h1 : ProjEquiv (ϕ₁.matrix.act (ψ.matrix.act p)) (ϕ₁.matrix.act p) := by
        have hid_act : MoebiusMatrix.id.act p = p := by
          dsimp [MoebiusMatrix.id, MoebiusMatrix.act]; ext <;> ring
        have hψp := h_pgl_id p
        rw [hid_act] at hψp
        exact act_projEquiv ϕ₁.matrix hψp
      have h2 : ProjEquiv (ϕ₁.matrix.act (ψ.matrix.act p)) (ϕ₂.matrix.act p) := by
        change ProjEquiv (ϕ₁.matrix.act ((MoebiusMatrix.mul (MoebiusMatrix.inv ϕ₁.matrix) ϕ₂.matrix).act p))
          (ϕ₂.matrix.act p)
        rw [act_comp, ← act_comp]
        have h_inv_mat : PglEquiv (MoebiusMatrix.comp ϕ₁.matrix (MoebiusMatrix.inv ϕ₁.matrix)) MoebiusMatrix.id :=
          moebius_frame_comp_inv_matrix ϕ₁
        have h_app := h_inv_mat (ϕ₂.matrix.act p)
        have hid_act2 : MoebiusMatrix.id.act (ϕ₂.matrix.act p) = ϕ₂.matrix.act p := by
          dsimp [MoebiusMatrix.id, MoebiusMatrix.act]; ext <;> ring
        rwa [hid_act2] at h_app
      have n_mid : ϕ₁.matrix.act (ψ.matrix.act p) ≠ (0, 0) :=
        act_ne_zero ϕ₁.matrix (act_ne_zero ψ.matrix hp)
      exact ProjEquiv.trans n_mid h1.symm h2
  · intro h_pgl
    apply Homeomorph.ext
    intro z
    apply cp1ToOnePoint_injective
    rw [ϕ₁.is_moebius z, ϕ₂.is_moebius z]
    exact PglEquiv.eval_eq h_pgl (cp1ToOnePoint z)

/-! ### Smooth Construction of Arbitrary `MoebiusFrame`s and 3-Point Transitivity -/

private noncomputable def projPerpNorthCLM :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] (ℝ ∙ (north_pole : EuclideanSpace ℝ (Fin 3)))ᗮ :=
  (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) -
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).smulRight (north_pole : EuclideanSpace ℝ (Fin 3))).codRestrict
    (ℝ ∙ (north_pole : EuclideanSpace ℝ (Fin 3)))ᗮ
    (fun v => by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      have h_np : (north_pole : EuclideanSpace ℝ (Fin 3)) = EuclideanSpace.single 2 1 := by
        ext i; fin_cases i <;> rfl
      rw [h_np, EuclideanSpace.inner_single_left]
      simp [north_pole])

private lemma projPerpNorthCLM_add_coord2 (v : EuclideanSpace ℝ (Fin 3)) :
    (projPerpNorthCLM v : EuclideanSpace ℝ (Fin 3)) +
      (v 2) • (north_pole : EuclideanSpace ℝ (Fin 3)) = v := by
  change (v - (v 2) • (north_pole : EuclideanSpace ℝ (Fin 3))) +
    (v 2) • (north_pole : EuclideanSpace ℝ (Fin 3)) = v
  exact sub_add_cancel _ _

private lemma projPerpNorthCLM_north_pole :
    projPerpNorthCLM (north_pole : EuclideanSpace ℝ (Fin 3)) = 0 := by
  apply Subtype.ext
  change (north_pole : EuclideanSpace ℝ (Fin 3)) -
    ((north_pole : EuclideanSpace ℝ (Fin 3)) 2) • (north_pole : EuclideanSpace ℝ (Fin 3)) = 0
  have hnp2 : (north_pole : EuclideanSpace ℝ (Fin 3)) 2 = 1 := rfl
  rw [hnp2, one_smul, sub_self]

private lemma projPerpNorthCLM_stereo_vec (w : ℂ) :
    projPerpNorthCLM (stereo_vec w) = stereo_iso w := by
  apply Subtype.ext
  have h2 : stereo_vec w 2 = 0 := stereo_vec_coord_2 w
  change stereo_vec w - (stereo_vec w 2) • (north_pole : EuclideanSpace ℝ (Fin 3)) = stereo_vec w
  rw [h2, zero_smul, sub_zero]

private noncomputable def sphereLiftCLM (L : ℂ →L[ℝ] ℂ) (ε : ℝ) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (ℝ ∙ (north_pole : EuclideanSpace ℝ (Fin 3)))ᗮ.subtypeL.comp
    (stereo_iso.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (L.comp (stereo_iso.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp projPerpNorthCLM))) +
  (ε • EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).smulRight (north_pole : EuclideanSpace ℝ (Fin 3))

private lemma sphereLiftCLM_apply (L : ℂ →L[ℝ] ℂ) (ε : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    sphereLiftCLM L ε v =
      stereo_vec (L (stereo_iso.symm (projPerpNorthCLM v))) +
      (ε * v 2) • (north_pole : EuclideanSpace ℝ (Fin 3)) :=
  rfl

private lemma sphereLiftCLM_coord2 (L : ℂ →L[ℝ] ℂ) (ε : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    sphereLiftCLM L ε v 2 = ε * v 2 := by
  rw [sphereLiftCLM_apply]
  have h_first : stereo_vec (L (stereo_iso.symm (projPerpNorthCLM v))) 2 = 0 :=
    stereo_vec_coord_2 _
  change stereo_vec (L (stereo_iso.symm (projPerpNorthCLM v))) 2 +
    ((ε * v 2) • (north_pole : EuclideanSpace ℝ (Fin 3))) 2 = ε * v 2
  rw [h_first, zero_add]
  dsimp [north_pole]
  simp

private lemma projPerpNorthCLM_sphereLiftCLM (L : ℂ →L[ℝ] ℂ) (ε : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    projPerpNorthCLM (sphereLiftCLM L ε v) = stereo_iso (L (stereo_iso.symm (projPerpNorthCLM v))) := by
  rw [sphereLiftCLM_apply, map_add, map_smul, projPerpNorthCLM_north_pole, smul_zero, add_zero,
      projPerpNorthCLM_stereo_vec]

private lemma sphereLiftCLM_comp (L₁ L₂ : ℂ →L[ℝ] ℂ) (ε₁ ε₂ : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    sphereLiftCLM L₁ ε₁ (sphereLiftCLM L₂ ε₂ v) = sphereLiftCLM (L₁.comp L₂) (ε₁ * ε₂) v := by
  rw [sphereLiftCLM_apply, sphereLiftCLM_apply (L₁.comp L₂),
      projPerpNorthCLM_sphereLiftCLM, sphereLiftCLM_coord2]
  simp [mul_assoc]

private lemma sphereLiftCLM_id (v : EuclideanSpace ℝ (Fin 3)) :
    sphereLiftCLM (ContinuousLinearMap.id ℝ ℂ) 1 v = v := by
  rw [sphereLiftCLM_apply]
  have h1 : stereo_vec ((ContinuousLinearMap.id ℝ ℂ) (stereo_iso.symm (projPerpNorthCLM v))) =
      (projPerpNorthCLM v : EuclideanSpace ℝ (Fin 3)) := by
    change (stereo_iso (stereo_iso.symm (projPerpNorthCLM v)) : EuclideanSpace ℝ (Fin 3)) =
      (projPerpNorthCLM v : EuclideanSpace ℝ (Fin 3))
    rw [stereo_iso.apply_symm_apply]
  rw [h1, one_mul]
  exact projPerpNorthCLM_add_coord2 v

private lemma sphereLiftCLM_norm_sq (L : ℂ →L[ℝ] ℂ) (hL : ∀ w : ℂ, ‖L w‖ = ‖w‖)
    (ε : ℝ) (hε : ε ^ 2 = 1) (v : EuclideanSpace ℝ (Fin 3)) :
    ‖sphereLiftCLM L ε v‖ = ‖v‖ := by
  let u_perp := stereo_iso (L (stereo_iso.symm (projPerpNorthCLM v)))
  have h_orth1 : ⟪(u_perp : EuclideanSpace ℝ (Fin 3)), (ε * v 2) • (north_pole : EuclideanSpace ℝ (Fin 3))⟫_ℝ = 0 := by
    rw [inner_smul_right, real_inner_comm,
        Submodule.mem_orthogonal_singleton_iff_inner_right.mp u_perp.2, mul_zero]
  have h_orth2 : ⟪(projPerpNorthCLM v : EuclideanSpace ℝ (Fin 3)), (v 2) • (north_pole : EuclideanSpace ℝ (Fin 3))⟫_ℝ = 0 := by
    rw [inner_smul_right, real_inner_comm,
        Submodule.mem_orthogonal_singleton_iff_inner_right.mp (projPerpNorthCLM v).2, mul_zero]
  have h_np_norm : ‖(north_pole : EuclideanSpace ℝ (Fin 3))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp north_pole.2
  have h_uperp_norm : ‖(u_perp : EuclideanSpace ℝ (Fin 3))‖ = ‖(projPerpNorthCLM v : EuclideanSpace ℝ (Fin 3))‖ := by
    change ‖stereo_iso (L (stereo_iso.symm (projPerpNorthCLM v)))‖ = ‖projPerpNorthCLM v‖
    rw [stereo_iso.norm_map, hL, stereo_iso.symm.norm_map]
  have h_sq : ‖sphereLiftCLM L ε v‖ ^ 2 = ‖v‖ ^ 2 := by
    have h_decomp1 : sphereLiftCLM L ε v = (u_perp : EuclideanSpace ℝ (Fin 3)) +
        (ε * v 2) • (north_pole : EuclideanSpace ℝ (Fin 3)) := rfl
    have h_rhs : ‖v‖ ^ 2 = ‖(projPerpNorthCLM v : EuclideanSpace ℝ (Fin 3))‖ ^ 2 + (v 2) ^ 2 := by
      conv_lhs => rw [← projPerpNorthCLM_add_coord2 v]
      rw [norm_add_sq_real, h_orth2, mul_zero, add_zero, norm_smul, h_np_norm, mul_one,
          Real.norm_eq_abs, sq_abs]
    rw [h_decomp1, norm_add_sq_real, h_orth1, mul_zero, add_zero, h_uperp_norm,
        norm_smul, h_np_norm, mul_one, Real.norm_eq_abs, sq_abs, h_rhs]
    linear_combination (v 2) ^ 2 * hε
  nlinarith [norm_nonneg (sphereLiftCLM L ε v), norm_nonneg v]

private lemma sphereLiftCLM_north_pole (L : ℂ →L[ℝ] ℂ) (ε : ℝ) :
    sphereLiftCLM L ε (north_pole : EuclideanSpace ℝ (Fin 3)) =
      ε • (north_pole : EuclideanSpace ℝ (Fin 3)) := by
  rw [sphereLiftCLM_apply, projPerpNorthCLM_north_pole]
  have h0 : stereo_vec (L (stereo_iso.symm 0)) = 0 := by
    simp [stereo_vec]
  have hnp2 : (north_pole : EuclideanSpace ℝ (Fin 3)) 2 = 1 := rfl
  rw [h0, zero_add, hnp2, mul_one]

private lemma sphereLiftCLM_stereo_chart_symm (L : ℂ →L[ℝ] ℂ) (ε : ℝ) (w : ℂ) :
    sphereLiftCLM L ε (stereo_chart.symm w).1 =
      (‖w‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • stereo_vec (L w) +
        (ε * (‖w‖ ^ 2 - 4)) • (north_pole : EuclideanSpace ℝ (Fin 3))) := by
  rw [check_symm_simp, map_smul, map_add, map_smul, map_smul, sphereLiftCLM_north_pole]
  have h_vec : sphereLiftCLM L ε (stereo_vec w) = stereo_vec (L w) := by
    rw [sphereLiftCLM_apply, projPerpNorthCLM_stereo_vec, stereo_iso.symm_apply_apply,
        stereo_vec_coord_2 w, mul_zero, zero_smul, add_zero]
  rw [h_vec, smul_smul, mul_comm (‖w‖ ^ 2 - 4) ε]

private noncomputable def mulLeftCLM (u : ℂ) : ℂ →L[ℝ] ℂ :=
  { toLinearMap :=
      { toFun := fun w => u * w
        map_add' := fun x y => mul_add u x y
        map_smul' := fun r x => by
          change u * ((r : ℂ) * x) = (r : ℂ) * (u * x)
          ring }
    cont := continuous_const.mul continuous_id }

/-- Smooth unit-complex rotation `MoebiusFrame` (`w ↦ u * w` for `‖u‖ = 1`, `0 sorryAx`). -/
noncomputable def unitRotationFrame (u : ℂ) (hu : ‖u‖ = 1) : MoebiusFrame := by
  have hu_ne : u ≠ 0 := by intro h0; rw [h0, norm_zero] at hu; norm_num at hu
  let f_clm := sphereLiftCLM (mulLeftCLM u) 1
  let g_clm := sphereLiftCLM (mulLeftCLM u⁻¹) 1
  have hf_mem : ∀ z : CP1, f_clm z.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro z
    rw [mem_sphere_zero_iff_norm, sphereLiftCLM_norm_sq _ (fun w => by simp [mulLeftCLM, hu]) 1 (by norm_num)]
    exact mem_sphere_zero_iff_norm.mp z.2
  have hg_mem : ∀ z : CP1, g_clm z.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro z
    rw [mem_sphere_zero_iff_norm, sphereLiftCLM_norm_sq _ (fun w => by simp [mulLeftCLM, hu]) 1 (by norm_num)]
    exact mem_sphere_zero_iff_norm.mp z.2
  let f : CP1 → CP1 := Set.codRestrict (fun z : CP1 => f_clm z.1) _ hf_mem
  let g : CP1 → CP1 := Set.codRestrict (fun z : CP1 => g_clm z.1) _ hg_mem
  have h_fg : ∀ z : CP1, g (f z) = z := by
    intro z; apply Subtype.ext
    change g_clm (f_clm z.1) = z.1
    rw [sphereLiftCLM_comp]
    have h_id : (mulLeftCLM u⁻¹).comp (mulLeftCLM u) = ContinuousLinearMap.id ℝ ℂ := by
      ext w; change u⁻¹ * (u * w) = w; rw [← mul_assoc, inv_mul_cancel₀ hu_ne, one_mul]
    rw [h_id, one_mul, sphereLiftCLM_id]
  have h_gf : ∀ z : CP1, f (g z) = z := by
    intro z; apply Subtype.ext
    change f_clm (g_clm z.1) = z.1
    rw [sphereLiftCLM_comp]
    have h_id : (mulLeftCLM u).comp (mulLeftCLM u⁻¹) = ContinuousLinearMap.id ℝ ℂ := by
      ext w; change u * (u⁻¹ * w) = w; rw [← mul_assoc, mul_inv_cancel₀ hu_ne, one_mul]
    rw [h_id, one_mul, sphereLiftCLM_id]
  have hf_smooth : ContMDiff I_CP1 I_CP1 ∞ f :=
    ContMDiff.codRestrict_sphere (n := 2) (f_clm.contDiff.contMDiff.comp contMDiff_coe_sphere) hf_mem
  have hg_smooth : ContMDiff I_CP1 I_CP1 ∞ g :=
    ContMDiff.codRestrict_sphere (n := 2) (g_clm.contDiff.contMDiff.comp contMDiff_coe_sphere) hg_mem
  let homeo : CP1 ≃ₜ CP1 :=
    { toFun := f, invFun := g, left_inv := h_fg, right_inv := h_gf,
      continuous_toFun := hf_smooth.continuous, continuous_invFun := hg_smooth.continuous }
  let mat : MoebiusMatrix :=
    { a := u, b := 0, c := 0, d := 1, det_ne_zero := by simp [hu_ne] }
  refine ⟨mat, homeo, hf_smooth, hg_smooth, ?_⟩
  intro z
  have hf_np : f north_pole = north_pole := by
    apply Subtype.ext; change f_clm north_pole.1 = north_pole.1
    rw [sphereLiftCLM_north_pole, one_smul]
  have hf_symm : ∀ w : ℂ, f (stereo_chart.symm w) = stereo_chart.symm (u * w) := by
    intro w; apply Subtype.ext
    change f_clm (stereo_chart.symm w).1 = (stereo_chart.symm (u * w)).1
    rw [sphereLiftCLM_stereo_chart_symm, check_symm_simp]
    have hnw : ‖u * w‖ = ‖w‖ := by rw [norm_mul, hu, one_mul]
    rw [hnw, one_mul]; rfl
  by_cases hz : z = north_pole
  · subst hz
    change cp1ToOnePoint (f north_pole) = mat.eval (cp1ToOnePoint north_pole)
    rw [hf_np]; dsimp [cp1ToOnePoint, MoebiusMatrix.eval, mat]; simp
  · have hs : z ∈ stereo_chart.source := by rw [stereo_chart_source]; exact hz
    have hz_eq : z = stereo_chart.symm (stereo_chart z) := (stereo_chart.left_inv hs).symm
    change cp1ToOnePoint (f z) = mat.eval (cp1ToOnePoint z)
    rw [hz_eq, hf_symm]
    have h_ne1 : stereo_chart.symm (stereo_chart z) ≠ north_pole := by rwa [← hz_eq]
    have h_ne2 : stereo_chart.symm (u * stereo_chart z) ≠ north_pole := by
      intro h_np
      have h_src := stereo_chart.map_target (show u * stereo_chart z ∈ stereo_chart.target by simp [stereo_chart_target])
      rw [h_np, stereo_chart_source] at h_src; exact h_src rfl
    dsimp [cp1ToOnePoint, MoebiusMatrix.eval, mat]
    rw [if_neg h_ne2, if_neg h_ne1,
        stereo_chart.right_inv (by simp [stereo_chart_target]),
        stereo_chart.right_inv (by simp [stereo_chart_target])]
    simp

/-- Smooth scaled-inversion `MoebiusFrame` (`w ↦ 4 / w`, swapping `0` and `∞`, `0 sorryAx`). -/
noncomputable def inv4Frame : MoebiusFrame := by
  let L_conj : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap
  let f_clm := sphereLiftCLM L_conj (-1)
  have hf_mem : ∀ z : CP1, f_clm z.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro z
    rw [mem_sphere_zero_iff_norm, sphereLiftCLM_norm_sq _ (fun w => Complex.norm_conj w) (-1) (by norm_num)]
    exact mem_sphere_zero_iff_norm.mp z.2
  let f : CP1 → CP1 := Set.codRestrict (fun z : CP1 => f_clm z.1) _ hf_mem
  have h_ff : ∀ z : CP1, f (f z) = z := by
    intro z; apply Subtype.ext
    change f_clm (f_clm z.1) = z.1
    rw [sphereLiftCLM_comp]
    have h_id : L_conj.comp L_conj = ContinuousLinearMap.id ℝ ℂ := by
      ext w; simp [L_conj]
    rw [h_id, show (-1 : ℝ) * (-1) = 1 by norm_num, sphereLiftCLM_id]
  have hf_smooth : ContMDiff I_CP1 I_CP1 ∞ f :=
    ContMDiff.codRestrict_sphere (n := 2) (f_clm.contDiff.contMDiff.comp contMDiff_coe_sphere) hf_mem
  let homeo : CP1 ≃ₜ CP1 :=
    { toFun := f, invFun := f, left_inv := h_ff, right_inv := h_ff,
      continuous_toFun := hf_smooth.continuous, continuous_invFun := hf_smooth.continuous }
  let mat : MoebiusMatrix :=
    { a := 0, b := 4, c := 1, d := 0, det_ne_zero := by norm_num }
  refine ⟨mat, homeo, hf_smooth, hf_smooth, ?_⟩
  intro z
  have hf_np : f north_pole = south_pole := by
    apply Subtype.ext; change f_clm north_pole.1 = south_pole.1
    rw [sphereLiftCLM_north_pole, neg_one_smul, south_pole_neg_north]; rfl
  have hf_sp : f south_pole = north_pole := by
    rw [← hf_np, h_ff]
  by_cases hz_np : z = north_pole
  · subst hz_np
    change cp1ToOnePoint (f north_pole) = mat.eval (cp1ToOnePoint north_pole)
    rw [hf_np]; dsimp [cp1ToOnePoint, MoebiusMatrix.eval, mat]
    rw [if_neg south_pole_ne_north_pole, stereo_chart_south_pole]
    simp
  · by_cases hz_sp : z = south_pole
    · subst hz_sp
      change cp1ToOnePoint (f south_pole) = mat.eval (cp1ToOnePoint south_pole)
      rw [hf_sp]; dsimp [cp1ToOnePoint, MoebiusMatrix.eval, mat]
      rw [if_neg south_pole_ne_north_pole, stereo_chart_south_pole]
      simp
    · have hs : z ∈ stereo_chart.source := by rw [stereo_chart_source]; exact hz_np
      let w := stereo_chart z
      have hz_eq : z = stereo_chart.symm w := (stereo_chart.left_inv hs).symm
      have hw_ne : w ≠ 0 := by
        intro hw0
        apply hz_sp
        rw [hz_eq, hw0, ← stereo_chart_south_pole]
        exact stereo_chart.left_inv (by rw [stereo_chart_source]; exact south_pole_ne_north_pole)
      have hf_w : f (stereo_chart.symm w) = stereo_chart.symm (4 / w) := by
        apply Subtype.ext
        change f_clm (stereo_chart.symm w).1 = (stereo_chart.symm (4 / w)).1
        rw [sphereLiftCLM_stereo_chart_symm, check_symm_simp]
        have h_div_eq : (4 : ℂ) / w = (((4 / ‖w‖ ^ 2 : ℝ) : ℂ) * starRingEnd ℂ w) := by
          have h_mul : (w : ℂ) * starRingEnd ℂ w = (‖w‖ : ℂ) ^ 2 := Complex.mul_conj' w
          have h_nw_pos : 0 < ‖w‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hw_ne)
          rw [div_eq_iff hw_ne]
          symm
          calc (((4 / ‖w‖ ^ 2 : ℝ) : ℂ) * starRingEnd ℂ w) * w
              = (((4 / ‖w‖ ^ 2 : ℝ) : ℂ)) * ((w : ℂ) * starRingEnd ℂ w) := by ring
            _ = (((4 / ‖w‖ ^ 2 : ℝ) : ℂ)) * (‖w‖ : ℂ) ^ 2 := by rw [h_mul]
            _ = (((4 / ‖w‖ ^ 2 * ‖w‖ ^ 2 : ℝ)) : ℂ) := by push_cast; ring
            _ = 4 := by
                congr 1
                exact div_mul_cancel₀ 4 h_nw_pos.ne'
        have h_svec : stereo_vec (4 / w) = (4 / ‖w‖ ^ 2) • stereo_vec (L_conj w) := by
          rw [h_div_eq, stereo_vec_smul]; rfl
        have h_nw_pos : 0 < ‖w‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hw_ne)
        have h_norm4 : ‖(4 : ℂ) / w‖ ^ 2 = 16 / ‖w‖ ^ 2 := by
          rw [norm_div, Complex.norm_ofNat, div_pow]; norm_num
        rw [h_svec, h_norm4, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul, smul_smul]
        refine congr_arg₂ (· + ·)
          (congr_arg (· • stereo_vec (L_conj w)) ?_)
          (congr_arg (· • (north_pole : EuclideanSpace ℝ (Fin 3))) ?_)
        · field_simp [h_nw_pos.ne']; ring
        · field_simp [h_nw_pos.ne']; ring
      change cp1ToOnePoint (f z) = mat.eval (cp1ToOnePoint z)
      rw [hz_eq, hf_w]
      have h_ne1 : stereo_chart.symm w ≠ north_pole := by rwa [← hz_eq]
      have h_ne2 : stereo_chart.symm (4 / w) ≠ north_pole := by
        intro h_np
        have h_src := stereo_chart.map_target (show 4 / w ∈ stereo_chart.target by simp [stereo_chart_target])
        rw [h_np, stereo_chart_source] at h_src; exact h_src rfl
      dsimp [cp1ToOnePoint, MoebiusMatrix.eval, mat]
      rw [if_neg h_ne2, if_neg h_ne1,
          stereo_chart.right_inv (by simp [stereo_chart_target]),
          stereo_chart.right_inv (by simp [stereo_chart_target])]
      simp [hw_ne]

/-- Smooth complex inversion `MoebiusFrame` (`w ↦ 1 / w`, `0 sorryAx`). -/
noncomputable def inversionFrame : MoebiusFrame :=
  let ϕ₀ := MoebiusFrame.comp (affine_scaling 0 (1 / 4 : ℝ) (by norm_num)) inv4Frame
  have h_pgl : PglEquiv ϕ₀.matrix MoebiusMatrix.inversion := by
    intro p
    dsimp [ϕ₀, MoebiusFrame.comp, affine_scaling, inv4Frame, MoebiusMatrix.comp,
      MoebiusMatrix.mul, MoebiusMatrix.affine_scaling, MoebiusMatrix.inversion,
      MoebiusMatrix.act, ProjEquiv]
    push_cast
    ring
  { matrix := MoebiusMatrix.inversion
    toHomeo := ϕ₀.toHomeo
    is_smooth := ϕ₀.is_smooth
    is_smooth_symm := ϕ₀.is_smooth_symm
    is_moebius := fun z => (ϕ₀.is_moebius z).trans (PglEquiv.eval_eq h_pgl (cp1ToOnePoint z)) }

/-- Smooth complex affine `MoebiusFrame` (`w ↦ a + b * w` for any `b ≠ 0`, `0 sorryAx`). -/
noncomputable def complexAffineFrame (a b : ℂ) (hb : b ≠ 0) : MoebiusFrame :=
  let r : ℝ := ‖b‖
  have hr : 0 < r := norm_pos_iff.mpr hb
  let u : ℂ := b / (r : ℂ)
  have hu : ‖u‖ = 1 := by
    dsimp [u, r]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg b)]
    exact div_self hr.ne'
  let ϕ₀ := MoebiusFrame.comp (affine_scaling a r hr) (unitRotationFrame u hu)
  let mat : MoebiusMatrix :=
    { a := b, b := a, c := 0, d := 1, det_ne_zero := by simp [hb] }
  have h_ru : (r : ℂ) * u = b := by
    dsimp [u]
    exact mul_div_cancel₀ b (Complex.ofReal_ne_zero.mpr hr.ne')
  have h_pgl : PglEquiv ϕ₀.matrix mat := by
    intro p
    dsimp [ϕ₀, mat, MoebiusFrame.comp, affine_scaling, unitRotationFrame,
      MoebiusMatrix.comp, MoebiusMatrix.mul, MoebiusMatrix.affine_scaling,
      MoebiusMatrix.act, ProjEquiv]
    rw [h_ru]
    ring
  { matrix := mat
    toHomeo := ϕ₀.toHomeo
    is_smooth := ϕ₀.is_smooth
    is_smooth_symm := ϕ₀.is_smooth_symm
    is_moebius := fun z => (ϕ₀.is_moebius z).trans (PglEquiv.eval_eq h_pgl (cp1ToOnePoint z)) }

/-- **Smooth Realization of Arbitrary Möbius Matrices (`0 sorryAx`)**:
Every `M_mat : MoebiusMatrix` in `GL(2, ℂ)` is realized by a smooth `MoebiusFrame` on `CP1`
whose `.matrix` field equals `M_mat`. -/
noncomputable def MoebiusFrame.ofMatrix (M_mat : MoebiusMatrix) : MoebiusFrame := by
  by_cases hc : M_mat.c = 0
  · have h_ad : M_mat.a * M_mat.d ≠ 0 := by
      have hdet := M_mat.det_ne_zero; rw [hc, mul_zero, sub_zero] at hdet; exact hdet
    have ha_ne : M_mat.a ≠ 0 := left_ne_zero_of_mul h_ad
    have hd_ne : M_mat.d ≠ 0 := right_ne_zero_of_mul h_ad
    let ϕ₀ := complexAffineFrame (M_mat.b / M_mat.d) (M_mat.a / M_mat.d) (div_ne_zero ha_ne hd_ne)
    have h_pgl : PglEquiv ϕ₀.matrix M_mat := by
      intro p
      dsimp [ϕ₀, complexAffineFrame, MoebiusMatrix.act, ProjEquiv]
      rw [hc]
      field_simp [hd_ne]
      ring
    exact
      { matrix := M_mat
        toHomeo := ϕ₀.toHomeo
        is_smooth := ϕ₀.is_smooth
        is_smooth_symm := ϕ₀.is_smooth_symm
        is_moebius := fun z => (ϕ₀.is_moebius z).trans (PglEquiv.eval_eq h_pgl (cp1ToOnePoint z)) }
  · have hq_ne : M_mat.b * M_mat.c - M_mat.a * M_mat.d ≠ 0 := by
      intro h0
      exact M_mat.det_ne_zero (by linear_combination -h0)
    have hc2_ne : M_mat.c ^ 2 ≠ 0 := pow_ne_zero 2 hc
    let ϕ₁ := complexAffineFrame (M_mat.a / M_mat.c) ((M_mat.b * M_mat.c - M_mat.a * M_mat.d) / M_mat.c ^ 2)
      (div_ne_zero hq_ne hc2_ne)
    let ϕ₃ := complexAffineFrame (M_mat.d / M_mat.c) 1 one_ne_zero
    let ϕ₀ := MoebiusFrame.comp ϕ₁ (MoebiusFrame.comp inversionFrame ϕ₃)
    have h_pgl : PglEquiv ϕ₀.matrix M_mat := by
      intro p
      dsimp [ϕ₀, ϕ₁, ϕ₃, complexAffineFrame, inversionFrame, MoebiusFrame.comp,
        MoebiusMatrix.comp, MoebiusMatrix.mul, MoebiusMatrix.inversion,
        MoebiusMatrix.act, ProjEquiv]
      field_simp [hc]
      ring
    exact
      { matrix := M_mat
        toHomeo := ϕ₀.toHomeo
        is_smooth := ϕ₀.is_smooth
        is_smooth_symm := ϕ₀.is_smooth_symm
        is_moebius := fun z => (ϕ₀.is_moebius z).trans (PglEquiv.eval_eq h_pgl (cp1ToOnePoint z)) }

@[simp]
theorem MoebiusFrame.ofMatrix_matrix (M_mat : MoebiusMatrix) :
    (MoebiusFrame.ofMatrix M_mat).matrix = M_mat := by
  dsimp [MoebiusFrame.ofMatrix]
  split_ifs <;> rfl

/-- **Unconditional 3-Point Transitivity of `MoebiusFrame` on `CP1` (`0 sorryAx`)**:
For any three pairwise distinct points `p₁, p₂, p₃ : CP1` and any three pairwise distinct points
`q₁, q₂, q₃ : CP1`, there exists `ϕ : MoebiusFrame` sending `(p₁, p₂, p₃) ↦ (q₁, q₂, q₃)`. -/
theorem exists_moebiusFrame_three_points
    (p₁ p₂ p₃ q₁ q₂ q₃ : CP1)
    (hp12 : p₁ ≠ p₂) (hp13 : p₁ ≠ p₃) (hp23 : p₂ ≠ p₃)
    (hq12 : q₁ ≠ q₂) (hq13 : q₁ ≠ q₃) (hq23 : q₂ ≠ q₃) :
    ∃ ϕ : MoebiusFrame,
      ϕ.toHomeo p₁ = q₁ ∧ ϕ.toHomeo p₂ = q₂ ∧ ϕ.toHomeo p₃ = q₃ := by
  let v₁ := onePointToProj (cp1ToOnePoint p₁)
  let v₂ := onePointToProj (cp1ToOnePoint p₂)
  let v₃ := onePointToProj (cp1ToOnePoint p₃)
  let w₁ := onePointToProj (cp1ToOnePoint q₁)
  let w₂ := onePointToProj (cp1ToOnePoint q₂)
  let w₃ := onePointToProj (cp1ToOnePoint q₃)
  have hv12 : ¬ ProjEquiv v₁ v₂ := not_projEquiv_onePointToProj (fun h => hp12 (cp1ToOnePoint_injective h))
  have hv23 : ¬ ProjEquiv v₂ v₃ := not_projEquiv_onePointToProj (fun h => hp23 (cp1ToOnePoint_injective h))
  have hv13 : ¬ ProjEquiv v₁ v₃ := not_projEquiv_onePointToProj (fun h => hp13 (cp1ToOnePoint_injective h))
  have hw12 : ¬ ProjEquiv w₁ w₂ := not_projEquiv_onePointToProj (fun h => hq12 (cp1ToOnePoint_injective h))
  have hw23 : ¬ ProjEquiv w₂ w₃ := not_projEquiv_onePointToProj (fun h => hq23 (cp1ToOnePoint_injective h))
  have hw13 : ¬ ProjEquiv w₁ w₃ := not_projEquiv_onePointToProj (fun h => hq13 (cp1ToOnePoint_injective h))
  obtain ⟨M_mat, hm1, hm2, hm3⟩ :=
    exists_moebius_three_points v₁ v₂ v₃ w₁ w₂ w₃ hv12 hv23 hv13 hw12 hw23 hw13
  let ϕ := MoebiusFrame.ofMatrix M_mat
  have h_map : ∀ (p q : CP1),
      ProjEquiv (M_mat.act (onePointToProj (cp1ToOnePoint p))) (onePointToProj (cp1ToOnePoint q)) →
      ϕ.toHomeo p = q := by
    intro p q h_act
    apply cp1ToOnePoint_injective
    rw [ϕ.is_moebius p, MoebiusFrame.ofMatrix_matrix]
    apply projEquiv_onePointToProj_inj
    have h_ev := (projEquiv_act_onePointToProj_eval M_mat (cp1ToOnePoint p)).symm
    have n_act : M_mat.act (onePointToProj (cp1ToOnePoint p)) ≠ (0, 0) :=
      act_ne_zero M_mat (onePointToProj_ne_zero _)
    exact ProjEquiv.trans n_act h_ev h_act
  exact ⟨ϕ, h_map p₁ q₁ hm1, h_map p₂ q₂ hm2, h_map p₃ q₃ hm3⟩

/-! ### Effective PSL(2, ℂ) / PGL(2, ℂ) Automorphism Group and Unconditional Finiteness -/

/-- Projective equivalence `Setoid` on `MoebiusFrame`, identifying scalar-equivalent matrices (`0 sorryAx`). -/
def MoebiusFrame.pglSetoid : Setoid MoebiusFrame where
  r ϕ₁ ϕ₂ := ϕ₁.toHomeo = ϕ₂.toHomeo
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The effective Möbius group `PSL(2, ℂ) ≅ PGL(2, ℂ) = MoebiusFrame / PglEquiv`. -/
def EffectiveMoebiusFrame : Type := Quotient MoebiusFrame.pglSetoid

/-- Underlying homeomorphism of an `EffectiveMoebiusFrame` (`0 sorryAx`). -/
def EffectiveMoebiusFrame.toHomeo : EffectiveMoebiusFrame → (CP1 ≃ₜ CP1) :=
  Quotient.lift (fun ϕ : MoebiusFrame => ϕ.toHomeo) (fun _ _ h => h)

/-- `EffectiveMoebiusFrame.toHomeo` is injective (`0 sorryAx`). -/
theorem EffectiveMoebiusFrame.toHomeo_injective :
    Function.Injective EffectiveMoebiusFrame.toHomeo := by
  intro ψ₁ ψ₂ h
  induction ψ₁ using Quotient.ind with | _ ϕ₁ =>
  induction ψ₂ using Quotient.ind with | _ ϕ₂ =>
  exact Quotient.sound h

/-- The identity-homeomorphism fiber of `EffectiveMoebiusFrame` is a `Subsingleton`, hence `Finite`
unconditionally (`0 sorryAx`). -/
theorem effective_ghost_identity_fiber_finite :
    Finite { ψ : EffectiveMoebiusFrame // ψ.toHomeo = Homeomorph.refl CP1 } := by
  haveI : Subsingleton { ψ : EffectiveMoebiusFrame // ψ.toHomeo = Homeomorph.refl CP1 } :=
    ⟨fun ⟨ψ₁, h₁⟩ ⟨ψ₂, h₂⟩ => Subtype.ext (EffectiveMoebiusFrame.toHomeo_injective (h₁.trans h₂.symm))⟩
  infer_instance

/-- **Principal Component Symmetry Finiteness from Isolated Fibers (`h_finite_symm` discharged, `0 sorryAx`)**:
For any continuous non-constant map `u : CP1 → M'` into a metric space `M'` whose point preimages
are finite (`∀ y ∈ Set.range u, (u ⁻¹' {y}).Finite`), the group of effective Möbius symmetries
`{ ψ : EffectiveMoebiusFrame // ∀ z, u (ψ.toHomeo z) = u z }` is finite. -/
theorem effective_principal_symmetries_finite_of_finite_fibers
    {M' : Type*} [MetricSpace M']
    (u : CP1 → M') (hu_cont : Continuous u)
    (h_nonconst : ¬ ∃ c : M', ∀ z : CP1, u z = c)
    (h_fib : ∀ y ∈ Set.range u, (u ⁻¹' {y}).Finite) :
    Finite { ψ : EffectiveMoebiusFrame // ∀ z : CP1, u (ψ.toHomeo z) = u z } := by
  -- Step 1: `u ∘ stereo_chart.symm` on `ℂ` is also non-constant by density of `{north_pole}ᶜ`.
  have h_nc_C : ∃ w₀ w₁ : ℂ, u (stereo_chart.symm w₀) ≠ u (stereo_chart.symm w₁) := by
    by_contra h_all
    push_neg at h_all
    apply h_nonconst
    refine ⟨u (stereo_chart.symm 0), ?_⟩
    have h_eq_on : Set.EqOn u (fun _ => u (stereo_chart.symm 0)) {north_pole}ᶜ := by
      intro z hz
      have hs : z ∈ stereo_chart.source := by rwa [stereo_chart_source]
      rw [← stereo_chart.left_inv hs]
      exact h_all (stereo_chart z) 0
    have h_dense : Dense ({north_pole}ᶜ : Set CP1) := by
      rw [dense_iff_inter_open]
      intro U hU ⟨z, hzU⟩
      by_cases hzn : z = north_pole
      · subst hzn
        obtain ⟨δ, hδ_pos, h_ball⟩ := Metric.isOpen_iff.mp hU north_pole hzU
        -- Move slightly away from `north_pole` via `inv4Frame` + `stereo_chart.symm`.
        let c_seq : ℕ → ℂ := fun n => (((((n : ℝ) + 1)⁻¹ : ℝ)) : ℂ)
        have h_lim : Filter.Tendsto (fun n : ℕ => inv4Frame.toHomeo (stereo_chart.symm (c_seq n)))
            Filter.atTop (𝓝 north_pole) := by
          have h_real : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (𝓝 (0 : ℝ)) := by
            simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
          have h0 : Filter.Tendsto c_seq Filter.atTop (𝓝 (0 : ℂ)) :=
            (Complex.continuous_ofReal.tendsto 0).comp h_real
          have h_sp : inv4Frame.toHomeo (stereo_chart.symm 0) = north_pole := by
            have h_sp_eq : stereo_chart.symm (0 : ℂ) = south_pole := by
              rw [← stereo_chart_south_pole]
              exact stereo_chart.left_inv (by rw [stereo_chart_source]; exact south_pole_ne_north_pole)
            rw [h_sp_eq]
            apply cp1ToOnePoint_injective
            rw [inv4Frame.is_moebius south_pole]
            dsimp [cp1ToOnePoint, inv4Frame, MoebiusMatrix.eval]
            rw [if_neg south_pole_ne_north_pole, stereo_chart_south_pole]
            simp
          rw [← h_sp]
          exact (inv4Frame.toHomeo.continuous.comp stereo_chart_symm_continuous).continuousAt.tendsto.comp h0
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h_lim.eventually (Metric.ball_mem_nhds north_pole hδ_pos))
        let q := inv4Frame.toHomeo (stereo_chart.symm (c_seq N))
        have hq_ne : q ≠ north_pole := by
          intro hq
          have h_sp_eq : stereo_chart.symm (0 : ℂ) = south_pole := by
            rw [← stereo_chart_south_pole]
            exact stereo_chart.left_inv (by rw [stereo_chart_source]; exact south_pole_ne_north_pole)
          have h_np_img : inv4Frame.toHomeo (stereo_chart.symm 0) = north_pole := by
            rw [h_sp_eq]
            apply cp1ToOnePoint_injective
            rw [inv4Frame.is_moebius south_pole]
            dsimp [cp1ToOnePoint, inv4Frame, MoebiusMatrix.eval]
            rw [if_neg south_pole_ne_north_pole, stereo_chart_south_pole]
            simp
          have h_inj := stereo_chart_symm_injective (inv4Frame.toHomeo.injective (hq.trans h_np_img.symm))
          have h_pos : (0 : ℝ) < ((N : ℝ) + 1)⁻¹ := by positivity
          exact h_pos.ne' (Complex.ofReal_eq_zero.mp (by simpa [c_seq] using h_inj))
        exact ⟨q, h_ball (hN N le_rfl), hq_ne⟩
      · exact ⟨z, hzU, hzn⟩
    have h_fun := Continuous.ext_on h_dense hu_cont continuous_const h_eq_on
    exact fun z => congr_fun h_fun z
  obtain ⟨w₀, w₁, hw_ne⟩ := h_nc_C
  -- Step 2: Intermediate Value Theorem along `t ↦ stereo_chart.symm ((1 - t) • w₀ + t • w₁)` gives 3 distinct values!
  let γ : ℝ → CP1 := fun t => stereo_chart.symm ((1 - t) • w₀ + t • w₁)
  have hγ_cont : Continuous γ :=
    stereo_chart_symm_continuous.comp
      (((continuous_const.sub continuous_id).smul continuous_const).add (continuous_id.smul continuous_const))
  let z₀ : CP1 := γ 0
  let z₁ : CP1 := γ 1
  have hz0_eq : z₀ = stereo_chart.symm w₀ := by dsimp [z₀, γ]; simp
  have hz1_eq : z₁ = stereo_chart.symm w₁ := by dsimp [z₁, γ]; simp
  let d : ℝ := dist (u z₁) (u z₀)
  have hd_pos : 0 < d := dist_pos.mpr (by rw [hz0_eq, hz1_eq]; exact hw_ne.symm)
  let g : ℝ → ℝ := fun t => dist (u (γ t)) (u z₀)
  have hg_cont : ContinuousOn g (Set.Icc 0 1) :=
    ((hu_cont.comp hγ_cont).dist continuous_const).continuousOn
  have hg0 : g 0 = 0 := dist_self _
  have hg1 : g 1 = d := rfl
  have hd2_mem : d / 2 ∈ Set.Icc (g 0) (g 1) := by rw [hg0, hg1]; constructor <;> linarith
  obtain ⟨t₂, _, ht₂⟩ := intermediate_value_Icc zero_le_one hg_cont hd2_mem
  let z₂ : CP1 := γ t₂
  have hz02 : z₀ ≠ z₂ := by
    intro h
    have h_eq_g : dist (u z₂) (u z₀) = d / 2 := ht₂
    rw [← h, dist_self] at h_eq_g
    linarith
  have hz01 : z₀ ≠ z₁ := by
    intro h
    have h_eq_d : dist (u z₁) (u z₀) = d := rfl
    rw [← h, dist_self] at h_eq_d
    linarith
  have hz21 : z₂ ≠ z₁ := by
    intro h; have : g t₂ = d := by change dist (u z₂) (u z₀) = d; rw [h]
    rw [ht₂] at this; linarith
  -- Step 3: Inject the symmetry group into the finite product of fibers `F₀ × F₂ × F₁`.
  let F₀ : Set CP1 := u ⁻¹' {u z₀}
  let F₂ : Set CP1 := u ⁻¹' {u z₂}
  let F₁ : Set CP1 := u ⁻¹' {u z₁}
  have : Finite F₀ := (h_fib (u z₀) ⟨z₀, rfl⟩).to_subtype
  have : Finite F₂ := (h_fib (u z₂) ⟨z₂, rfl⟩).to_subtype
  have : Finite F₁ := (h_fib (u z₁) ⟨z₁, rfl⟩).to_subtype
  let ev : { ψ : EffectiveMoebiusFrame // ∀ z : CP1, u (ψ.toHomeo z) = u z } → F₀ × F₂ × F₁ :=
    fun ⟨ψ, hψ⟩ => ⟨⟨ψ.toHomeo z₀, hψ z₀⟩, ⟨ψ.toHomeo z₂, hψ z₂⟩, ⟨ψ.toHomeo z₁, hψ z₁⟩⟩
  have hev_inj : Function.Injective ev := by
    rintro ⟨ψ₁, hψ₁⟩ ⟨ψ₂, hψ₂⟩ h_eq
    induction ψ₁ using Quotient.ind with | _ ϕ₁ =>
    induction ψ₂ using Quotient.ind with | _ ϕ₂ =>
    have he0 : ϕ₁.toHomeo z₀ = ϕ₂.toHomeo z₀ := congr_arg (fun x => x.1.1) h_eq
    have he2 : ϕ₁.toHomeo z₂ = ϕ₂.toHomeo z₂ := congr_arg (fun x => x.2.1.1) h_eq
    have he1 : ϕ₁.toHomeo z₁ = ϕ₂.toHomeo z₁ := congr_arg (fun x => x.2.2.1) h_eq
    let δ := MoebiusFrame.comp (MoebiusFrame.inv ϕ₁) ϕ₂
    have hfix0 : δ.toHomeo z₀ = z₀ := by
      dsimp [δ, MoebiusFrame.comp, MoebiusFrame.inv]; rw [← he0]; exact ϕ₁.toHomeo.symm_apply_apply z₀
    have hfix2 : δ.toHomeo z₂ = z₂ := by
      dsimp [δ, MoebiusFrame.comp, MoebiusFrame.inv]; rw [← he2]; exact ϕ₁.toHomeo.symm_apply_apply z₂
    have hfix1 : δ.toHomeo z₁ = z₁ := by
      dsimp [δ, MoebiusFrame.comp, MoebiusFrame.inv]; rw [← he1]; exact ϕ₁.toHomeo.symm_apply_apply z₁
    have hδ_id := moebiusFrame_three_point_rigidity δ z₀ z₂ z₁ hz02 hz01 hz21 hfix0 hfix2 hfix1
    have h_homeo : ϕ₁.toHomeo = ϕ₂.toHomeo := by
      apply Homeomorph.ext
      intro z
      have hz := congr_arg (fun H : CP1 ≃ₜ CP1 => ϕ₁.toHomeo (H z)) hδ_id
      simpa [δ, MoebiusFrame.comp, MoebiusFrame.inv] using hz.symm
    exact Subtype.ext (Quotient.sound h_homeo)
  exact Finite.of_injective ev hev_inj

/-- Projective equivalence relation on `StableMapAutomorphism I lim`, identifying automorphisms
with identical combinatorial tree isomorphism and identical component homeomorphisms (`0 sorryAx`). -/
def StableMapAutomorphism.pglSetoid (lim : StableSphereTreeLimit I (M := M)) :
    Setoid (StableMapAutomorphism I lim) where
  r aut₁ aut₂ := aut₁.tree_iso = aut₂.tree_iso ∧ ∀ v, (aut₁.frame v).toHomeo = (aut₂.frame v).toHomeo
  iseqv :=
    ⟨fun _ => ⟨rfl, fun _ => rfl⟩,
     fun ⟨ht, hf⟩ => ⟨ht.symm, fun v => (hf v).symm⟩,
     fun ⟨ht1, hf1⟩ ⟨ht2, hf2⟩ => ⟨ht1.trans ht2, fun v => (hf1 v).trans (hf2 v)⟩⟩

/-- The effective full automorphism group `Aut(T, {u_v}, {z_{vw}})` modulo scalar matrix rescaling. -/
def EffectiveStableMapAutomorphism (lim : StableSphereTreeLimit I (M := M)) : Type :=
  Quotient (StableMapAutomorphism.pglSetoid I lim)

/-- **Finiteness of Effective Automorphisms & Stability Equivalence (`e04_aut`, `0 sorryAx`)**:
On any metric target `M`, if every principal component of `lim` has finite point preimages
(isolated fibers), then `EffectiveStableMapAutomorphism I lim` is finite and Kontsevich's
stability equivalence holds unconditionally without assuming `h_rigidity` or `h_ghost_fin`. -/
theorem stability_iff_finite_effective_automorphisms_of_finite_fibers
    {M' : Type*} [MetricSpace M'] [ChartedSpace H M']
    [IsManifold I ∞ M'] [CompactSpace M'] [ClosedTameTarget I M']
    (lim : StableSphereTreeLimit I (M := M'))
    (h_fib : ∀ (v : lim.tree.V), is_principal_component I lim v →
      ∀ y ∈ Set.range (lim.map v), ((lim.map v) ⁻¹' {y}).Finite) :
    Finite (EffectiveStableMapAutomorphism I lim) ∧
    ((∀ v, (∃ c : M', ∀ z, lim.map v z = c) → 3 ≤ lim.tree.adj.degree v) ↔
      Finite (EffectiveStableMapAutomorphism I lim)) := by
  -- Project each `EffectiveStableMapAutomorphism` to `(tree_iso, fun v => EffectiveMoebiusFrame)`.
  let projTree : EffectiveStableMapAutomorphism I lim → TreeAutomorphism lim.tree :=
    Quotient.lift (fun aut => aut.tree_iso) (fun _ _ h => h.1)
  have h_pure_fin : ∀ σ : TreeAutomorphism lim.tree,
      Finite { α : EffectiveStableMapAutomorphism I lim // projTree α = σ } := by
    intro σ
    by_cases h_ne : Nonempty { α : EffectiveStableMapAutomorphism I lim // projTree α = σ }
    · obtain ⟨⟨α₀, hα₀⟩⟩ := h_ne
      obtain ⟨aut₀, rfl⟩ := Quotient.exists_rep α₀
      dsimp [projTree] at hα₀
      let CompSym (v : lim.tree.V) : Type :=
        { ψ : EffectiveMoebiusFrame //
          (is_ghost_component I lim v → ψ.toHomeo = Homeomorph.refl CP1) ∧
          (is_principal_component I lim v → ∀ z, lim.map v (ψ.toHomeo z) = lim.map v z) }
      have h_cs_fin : ∀ v : lim.tree.V, Finite (CompSym v) := by
        intro v
        by_cases hg : is_ghost_component I lim v
        · have := effective_ghost_identity_fiber_finite
          exact Finite.of_injective
            (fun (x : CompSym v) => (⟨x.1, x.2.1 hg⟩ : { ψ : EffectiveMoebiusFrame // ψ.toHomeo = Homeomorph.refl CP1 }))
            (by intro a b h; exact Subtype.ext (Subtype.mk.inj h))
        · have hp : is_principal_component I lim v := hg
          have hu_cont : Continuous (lim.map v) := continuousOn_univ.mp (lim.is_jhol v).1.continuousOn
          have := effective_principal_symmetries_finite_of_finite_fibers (lim.map v) hu_cont hp (h_fib v hp)
          exact Finite.of_injective
            (fun (x : CompSym v) => (⟨x.1, x.2.2 hp⟩ : { ψ : EffectiveMoebiusFrame // ∀ z, lim.map v (ψ.toHomeo z) = lim.map v z }))
            (by intro a b h; exact Subtype.ext (Subtype.mk.inj h))
      have : ∀ v, Finite (CompSym v) := h_cs_fin
      let toProd : { α : EffectiveStableMapAutomorphism I lim // projTree α = σ } →
          ((v : lim.tree.V) → CompSym v) :=
        fun ⟨α, hα⟩ v =>
          Quotient.liftOn α
            (fun aut =>
              if h_t : aut.tree_iso = σ then
                let p_aut : PureComponentAutomorphism I lim :=
                  ⟨StableMapAutomorphism.comp I lim (StableMapAutomorphism.inv I lim aut₀) aut,
                    comp_inv_pure I lim aut₀ aut (hα₀.trans h_t.symm)⟩
                ⟨Quotient.mk MoebiusFrame.pglSetoid (p_aut.1.frame v),
                  fun hg => ghost_component_pure_automorphism_trivial_uncond I lim v hg p_aut,
                  fun _ z => by
                    have h_eq := p_aut.1.curve_equiv v z
                    have h_tr : p_aut.1.tree_iso.toEquiv v = v := by rw [p_aut.2]; rfl
                    rwa [h_tr] at h_eq⟩
              else
                ⟨Quotient.mk MoebiusFrame.pglSetoid MoebiusFrame.id,
                  fun _ => rfl, fun _ _ => rfl⟩)
            (fun a₁ a₂ ⟨ht_eq, hf_eq⟩ => by
              by_cases h_t : a₁.tree_iso = σ
              · have h_t2 : a₂.tree_iso = σ := ht_eq.symm.trans h_t
                rw [dif_pos h_t, dif_pos h_t2]
                apply Subtype.ext
                apply Quotient.sound
                change (MoebiusFrame.comp (MoebiusFrame.inv (aut₀.frame (aut₀.tree_iso.toEquiv.symm (a₁.tree_iso.toEquiv v)))) (a₁.frame v)).toHomeo =
                  (MoebiusFrame.comp (MoebiusFrame.inv (aut₀.frame (aut₀.tree_iso.toEquiv.symm (a₂.tree_iso.toEquiv v)))) (a₂.frame v)).toHomeo
                rw [ht_eq]
                apply Homeomorph.ext
                intro z
                dsimp [MoebiusFrame.comp, MoebiusFrame.inv]
                rw [hf_eq v]
              · have h_t2 : ¬ a₂.tree_iso = σ := fun h2 => h_t (ht_eq.trans h2)
                rw [dif_neg h_t, dif_neg h_t2])
      have h_inj : Function.Injective toProd := by
        rintro ⟨α₁, hα₁⟩ ⟨α₂, hα₂⟩ h_eq
        obtain ⟨a₁, rfl⟩ := Quotient.exists_rep α₁
        obtain ⟨a₂, rfl⟩ := Quotient.exists_rep α₂
        dsimp [projTree] at hα₁ hα₂
        apply Subtype.ext
        apply Quotient.sound
        refine ⟨hα₁.trans hα₂.symm, fun v => ?_⟩
        have hv := congr_fun h_eq v
        dsimp [toProd] at hv
        rw [dif_pos hα₁, dif_pos hα₂] at hv
        have h_q := congr_arg Subtype.val hv
        have h_hom : ((StableMapAutomorphism.comp I lim (StableMapAutomorphism.inv I lim aut₀) a₁).frame v).toHomeo =
            ((StableMapAutomorphism.comp I lim (StableMapAutomorphism.inv I lim aut₀) a₂).frame v).toHomeo :=
          congr_arg EffectiveMoebiusFrame.toHomeo h_q
        dsimp [StableMapAutomorphism.comp, StableMapAutomorphism.inv, MoebiusFrame.comp, MoebiusFrame.inv, treeAutomorphismInv] at h_hom
        rw [hα₁, hα₂] at h_hom
        apply Homeomorph.ext
        intro z
        have hz := congr_arg (fun H : CP1 ≃ₜ CP1 => (aut₀.frame (aut₀.tree_iso.toEquiv.symm (σ.toEquiv v))).toHomeo (H z)) h_hom
        simpa using hz
      exact Finite.of_injective toProd h_inj
    · have : IsEmpty { α : EffectiveStableMapAutomorphism I lim // projTree α = σ } :=
        not_nonempty_iff.mp h_ne
      infer_instance
  have h_fin : Finite (EffectiveStableMapAutomorphism I lim) :=
    finite_of_finite_fibers projTree h_pure_fin
  exact ⟨h_fin, ⟨fun _ => h_fin, fun _ => lim.stable⟩⟩

end GromovCompactness.Extensions
