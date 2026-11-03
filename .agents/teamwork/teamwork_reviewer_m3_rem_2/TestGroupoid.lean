import GromovCompactness.Geometry.Sphere

open GromovCompactness

theorem homeo_inv_comp (ϕ : MoebiusFrame) :
    (MoebiusFrame.comp (MoebiusFrame.inv ϕ) ϕ).toHomeo = Homeomorph.refl CP1 := by
  apply Homeomorph.ext; intro x
  exact ϕ.toHomeo.left_inv x

theorem homeo_comp_inv (ϕ : MoebiusFrame) :
    (MoebiusFrame.comp ϕ (MoebiusFrame.inv ϕ)).toHomeo = Homeomorph.refl CP1 := by
  apply Homeomorph.ext; intro x
  exact ϕ.toHomeo.right_inv x

theorem homeo_id_comp (ϕ : MoebiusFrame) :
    (MoebiusFrame.comp MoebiusFrame.id ϕ).toHomeo = ϕ.toHomeo := by
  apply Homeomorph.ext; intro x; rfl

theorem homeo_comp_id (ϕ : MoebiusFrame) :
    (MoebiusFrame.comp ϕ MoebiusFrame.id).toHomeo = ϕ.toHomeo := by
  apply Homeomorph.ext; intro x; rfl

theorem homeo_comp_assoc (ϕ₁ ϕ₂ ϕ₃ : MoebiusFrame) :
    (MoebiusFrame.comp (MoebiusFrame.comp ϕ₁ ϕ₂) ϕ₃).toHomeo =
    (MoebiusFrame.comp ϕ₁ (MoebiusFrame.comp ϕ₂ ϕ₃)).toHomeo := by
  apply Homeomorph.ext; intro x; rfl
