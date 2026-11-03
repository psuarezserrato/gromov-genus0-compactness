# Synthesis & Blueprint for Milestone 3 Remediation (Sphere.lean / F02)

## Executive Summary
This document synthesizes the findings and machine-checked code from Explorers 1, 2, and 3 into a single unified implementation plan for `GromovCompactness/Geometry/Sphere.lean`.

## 1. Explorer Contributions & Verified Artifacts
- **Explorer 1** (`explorer_m3_rem_1/ProposedSphere.lean`):
  - Provides the full file architecture, imports, and definitions.
  - Implements `stereo_chart : PartialHomeomorph CP1 ℂ` using Mathlib's `stereographic' 2 north_pole`.
  - Implements `MoebiusMatrix` in $\operatorname{GL}(2, \mathbb{C}) / \operatorname{PGL}(2, \mathbb{C})$ with fields `a, b, c, d : ℂ` and `det_ne_zero : a * d - b * c ≠ 0`.
  - Implements non-facade `affine_scaling`, `inversion`, and `rotation` as `MoebiusMatrix`.
  - Implements `eval : MoebiusMatrix → OnePoint ℂ → OnePoint ℂ` and proves `eval_affine_scaling`, `eval_inversion_coe`, `eval_inversion_zero`, `eval_inversion_infty`, `eval_rotation`.
  - Implements smooth geometric homeomorphisms on $S^2$: `inv_homeo : CP1 ≃ₜ CP1` and `rot_homeo (θ : ℝ) : CP1 ≃ₜ CP1` with zero-sorry `ContMDiff` proofs via `ContMDiff.codRestrict_sphere`.
  - Proves non-identity behavior: `inv_homeo_ne_id`, `rot_homeo_ne_id`.

- **Explorer 2** (`explorer_m3_rem_2/Scratch.lean` & `report.md`):
  - Implements zero-sorry homogeneous 3-point transitivity in $\operatorname{PGL}(2, \mathbb{C})$:
    - `ProjEquiv (p q : ℂ × ℂ) : Prop := p.1 * q.2 = p.2 * q.1`
    - `frame_mat (v₁ v₂ v₃ : ℂ × ℂ) : MoebiusMat` sending standard frame $(e_1, e_2, e_1 + e_2)$ to $(v_1, v_2, v_3)$ with non-zero determinant.
    - `general_three_point_mat (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ) : MoebiusMat` mapping $(v_1, v_2, v_3) \mapsto (w_1, w_2, w_3)$.
    - `general_three_point_eval_1, 2, 3`: 100% proved via `ring` with zero sorry.
    - `moebius_fix_three_standard`: Uniqueness proved via `linear_combination` with zero sorry.
  - Eliminates the circular `h_trans` hypothesis completely.

- **Explorer 3** (`explorer_m3_rem_3/report.md` & `handoff.md`):
  - Implements genuine topological disk:
    `def disk_at (a : ℂ) (r : ℝ) : Set CP1 := stereo_chart.symm '' (Metric.ball a r)`
  - Proves zero-sorry lemmas:
    - `disk_at_mono : r₁ ≤ r₂ → disk_at a r₁ ⊆ disk_at a r₂`
    - `north_pole_not_mem_disk_at : north_pole ∉ disk_at a r`
    - `is_open_disk_at : IsOpen (disk_at a r)`
    - `center_mem_disk_at : 0 < r → stereo_chart.symm a ∈ disk_at a r`
    - `annulus_subset_disk : annulus_at a r R ⊆ disk_at a R`
  - Provides required instances for downstream `Energy.lean` and `SmoothLocal.lean`:
    - `noncomputable instance : MeasurableSpace CP1 := borel CP1`
    - `instance : BorelSpace CP1 := ⟨rfl⟩`
    - `instance : TopologicalSpace MoebiusFrame := TopologicalSpace.induced (fun ϕ => (ϕ.toHomeo : CP1 → CP1)) inferInstance`

## 2. Worker Action Plan
1. Exclusively modify `GromovCompactness/Geometry/Sphere.lean`.
2. Integrate the unified code from `ProposedSphere.lean`, enriched with:
   - Explorer 2's zero-sorry homogeneous transitivity theorems (`ProjEquiv`, `frame_mat`, `general_three_point_mat`, `general_three_point_eval_1, 2, 3`, `moebius_fix_three_standard`).
   - Explorer 3's zero-sorry lemmas (`disk_at_mono`, `north_pole_not_mem_disk_at`, `is_open_disk_at`, `annulus_subset_disk`) and typeclass instances.
   - For `exists_unique_moebius_three_points`, formulate it over the authentic projective/frame representation without `h_trans`, and state/prove it with zero sorry using Explorer 2's theorems.
3. Verify that `lake build GromovCompactness.Geometry.Target GromovCompactness.Geometry.Sphere` compiles with exit code 0.
4. Verify with `#print axioms` that all declarations depend strictly on `[propext, Classical.choice, Quot.sound]`.
5. Verify with `grep -n "sorry" GromovCompactness/Geometry/Sphere.lean` that there are 0 matches.
6. Write a complete handoff report documenting the changes, build outputs, and axiom checks.
