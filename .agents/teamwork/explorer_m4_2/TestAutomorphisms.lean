import GromovCompactness.Extensions.Automorphisms

open scoped Manifold ContDiff Topology
open Metric Set GromovCompactness GromovCompactness.Extensions

-- Test 1: Finite fibers over a finite base implies finite domain
theorem finite_of_finite_fibers {α β : Type*} [Finite β] (f : α → β)
    (h_fibers : ∀ b : β, Finite { a : α // f a = b }) : Finite α := by
  let e : α ≃ Σ b : β, { a : α // f a = b } :=
    ⟨fun a => ⟨f a, a, rfl⟩,
     fun ⟨b, a, _⟩ => a,
     fun a => rfl,
     fun ⟨b, a, ha⟩ => by subst ha; rfl⟩
  exact Finite.of_equiv (Σ b : β, { a : α // f a = b }) e.symm


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

theorem tree_iso_ext {T : SphereTree} (σ₁ σ₂ : TreeAutomorphism T)
    (h : σ₁.toEquiv = σ₂.toEquiv) : σ₁ = σ₂ := by
  rcases σ₁ with ⟨e₁, h₁⟩
  rcases σ₂ with ⟨e₂, h₂⟩
  dsimp at h
  subst h
  rfl

def idTreeAutomorphism (T : SphereTree) : TreeAutomorphism T where
  toEquiv := Equiv.refl T.V
  map_adj' u v := by rfl

theorem tree_iso_eq_id_iff {T : SphereTree} (σ : TreeAutomorphism T) :
    σ = idTreeAutomorphism T ↔ σ.toEquiv = Equiv.refl T.V := by
  constructor
  · rintro rfl; rfl
  · intro h; exact tree_iso_ext σ (idTreeAutomorphism T) h

def pure_automorphism_equiv_fiber (lim : StableSphereTreeLimit I (M := M)) :
    PureComponentAutomorphism I lim ≃ { aut : StableMapAutomorphism I lim // aut.tree_iso = idTreeAutomorphism lim.tree } := by
  refine Equiv.subtypeEquiv (Equiv.refl _) (fun aut => ?_)
  dsimp
  rw [tree_iso_eq_id_iff]

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
  -- A.d * (A.a * B₁.a + A.b * B₁.c) - A.b * (A.c * B₁.a + A.d * B₁.c) = (A.a * A.d - A.b * A.c) * B₁.a
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

theorem full_finite_of_pure_finite (lim : StableSphereTreeLimit I (M := M))
    (h_pure : Finite (PureComponentAutomorphism I lim)) :
    Finite (StableMapAutomorphism I lim) := by
  let f : StableMapAutomorphism I lim → TreeAutomorphism lim.tree := fun aut => aut.tree_iso
  apply finite_of_finite_fibers f
  intro σ
  exact fiber_finite_of_pure_finite I lim h_pure σ

theorem full_automorphisms_finite_iff_pure_finite_proof
    (lim : StableSphereTreeLimit I (M := M)) :
    Finite (StableMapAutomorphism I lim) ↔ Finite (PureComponentAutomorphism I lim) := by
  constructor
  · intro h
    exact pure_automorphisms_finite_of_full_finite I lim h
  · intro h
    exact full_finite_of_pure_finite I lim h

#print axioms full_automorphisms_finite_iff_pure_finite_proof

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

theorem pureAutomorphismToComponentSymmetries_injective (lim : StableSphereTreeLimit I (M := M))
    (h_ghost_triv : ∀ (v : lim.tree.V) (_h_ghost : is_ghost_component I lim v)
      (aut : PureComponentAutomorphism I lim), (aut.1.frame v).toHomeo = Homeomorph.refl CP1) :
    Function.Injective (fun (aut : PureComponentAutomorphism I lim) =>
      fun (v : lim.tree.V) => (pureAutomorphismToComponentSymmetries I lim h_ghost_triv aut v).1) := by
  intro aut₁ aut₂ h
  have h_frame : aut₁.1.frame = aut₂.1.frame := by
    ext v
    have h_v := congr_fun h v
    exact h_v
  exact pureComponentAutomorphism_frame_injective I lim h_frame

/-- Zero-sorry reduction of pure_component_automorphisms_finite from componentwise finiteness. -/
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

#print axioms pure_component_automorphisms_finite_of_components

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

/-- Master pure componentwise automorphism finiteness reduction theorem. -/
theorem pure_component_automorphisms_finite_proof
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

#print axioms pure_component_automorphisms_finite_proof
