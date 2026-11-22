/-
Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
Released under the GNU Affero General Public License v3.0 (AGPLv3) for non-commercial use;
see LICENSE.md for details.
This project is licensed under non-commercial use. If you wish to use this software in a
commercial product, service, or enterprise environment, please contact the developer to purchase
a commercial license or negotiate royalty terms.
Authors: Pablo Suárez-Serrato (November 2026)
-/

import GromovCompactness.Geometry.Sphere

open GromovCompactness

theorem affine_scaling_toHomeo_is_constant_dummy (a₁ a₂ : ℂ) (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    (affine_scaling a₁ s₁ h₁).toHomeo = (affine_scaling a₂ s₂ h₂).toHomeo := rfl

theorem affine_scaling_toHomeo_is_refl (a : ℂ) (s : ℝ) (h : 0 < s) :
    (affine_scaling a s h).toHomeo = Homeomorph.refl CP1 := rfl
