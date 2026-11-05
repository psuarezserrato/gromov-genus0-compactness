# Task Specification: Part 7 (Lemmas 17, 18 & 19 — Polar Pompeiu Disk Integral Bound, Radial–Angular FTC Integration, and the Polar Cauchy–Pompeiu Representation Formula)

We now have **Lemmas 1 through 16** completely proved and verified by `lake env lean` (`v4.16.0` / Mathlib `v4.16.0`) with zero `sorry` and standard kernel axioms `[propext, Classical.choice, Quot.sound]`:
1. `fderiv_directional_cauchyRiemann_identity`
2. `cauchy_kernel_diff_bound`
3. `polar_cauchy_pompeiu_kernel_identity`
4. `cauchy_deriv_kernel_diff_bound`
5. `holder_power_interpolation_on_disk`
6. `boundary_circleIntegral_holder_est`
7. `polar_radial_angular_cauchyRiemann_identity`
8. `boundary_circleIntegral_deriv_holder_est`
9. `polar_radial_hasDerivAt` & `polar_angular_hasDerivAt`
10. `periodic_intervalIntegral_deriv_eq_zero`
11. `polar_angular_periodicity`
12. `polar_radial_intervalIntegral_eq_sub`
13. `polar_pompeiu_angular_slice_identity`
14. `circleIntegral_sub_center_inv_eq_average`
15. `polar_jacobian_pompeiu_norm_cancel`
16. `polar_pompeiu_radial_slice_bound`

Now please provide complete, **zero-`sorry` / zero-`admit`** Lean `v4.16.0` proofs for **Part 7 (Lemmas 17, 18, and 19)** below:
- **Lemma 17 (`polar_pompeiu_disk_integral_bound`)**: Integrates Lemma 16 (`polar_pompeiu_radial_slice_bound`) over $\theta \in [0, 2\pi]$ to obtain the $L^\infty \to L^\infty$ bound for the 2D polar Pompeiu operator on the disk $B(z, R)$:
  $$\left\| \frac{1}{\pi} \int_0^{2\pi} \left( \int_0^R (\rho : \mathbb{C}) * \frac{\bar\partial f(z + \rho e^{i\theta})}{(z + \rho e^{i\theta}) - z}\,d\rho \right) d\theta \right\| \le 2 * R * M.$$
- **Lemma 18 (`polar_radial_angular_ftc_eq_sub`)**: Integrates Lemma 12 (`polar_radial_intervalIntegral_eq_sub` with $\varepsilon = 0$) over $\theta \in [0, 2\pi]$ to obtain:
  $$\int_0^{2\pi} \left(\int_0^R df(z + \rho e^{i\theta})(e^{i\theta})\,d\rho\right) d\theta = \left(\int_0^{2\pi} f(z + R e^{i\theta})\,d\theta\right) - (2 * \pi : \mathbb{C}) * f(z).$$
- **Lemma 19 (`polar_cauchy_pompeiu_representation`)**: Combines Lemma 13 (`polar_pompeiu_angular_slice_identity`), Lemma 14 (`circleIntegral_sub_center_inv_eq_average`), and Lemma 18 (`polar_radial_angular_ftc_eq_sub`) to establish the **Polar Cauchy–Pompeiu Representation Formula** for $f(z)$ on $B(z, R)$ ($R > 0$):
  $$f(z) = (2 * \pi * i)^{-1} \oint_{|\zeta - z| = R} (\zeta - z)^{-1} f(\zeta)\,d\zeta - \pi^{-1} \int_0^R \left(\int_0^{2\pi} (\rho : \mathbb{C}) * \frac{\bar\partial f(z + \rho e^{i\theta})}{(z + \rho e^{i\theta}) - z}\,d\theta\right) d\rho.$$

```lean
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

open Metric Set Complex MeasureTheory

namespace GromovCompactness.Analysis

noncomputable def cauchyRiemann (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)

-- Already proved in Parts 5 & 6:
axiom polar_radial_intervalIntegral_eq_sub
    {f : ℂ → ℂ} {z : ℂ} {ε R θ : ℝ}
    (hf_diff : ∀ r ∈ Set.uIcc ε R,
      DifferentiableAt ℝ f (z + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
    (h_int : IntervalIntegrable
      (fun r : ℝ => fderiv ℝ f (z + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (Complex.exp (Complex.I * (θ : ℂ)))) volume ε R) :
    (∫ r in ε..R,
      fderiv ℝ f (z + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (Complex.exp (Complex.I * (θ : ℂ)))) =
      f (z + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
        f (z + (ε : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

axiom polar_pompeiu_angular_slice_identity
    {f : ℂ → ℂ} {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf_diff : ∀ θ ∈ Set.uIcc 0 (2 * Real.pi),
      DifferentiableAt ℝ f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
    (h_int_rad : IntervalIntegrable
      (fun θ : ℝ => fderiv ℝ f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (Complex.exp (Complex.I * (θ : ℂ)))) volume 0 (2 * Real.pi))
    (h_int_ang : IntervalIntegrable
      (fun θ : ℝ => fderiv ℝ f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (Complex.I * ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))) volume 0 (2 * Real.pi)) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (ρ : ℂ) * (cauchyRiemann f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
        ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z))) =
      (1 / 2 : ℂ) * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        fderiv ℝ f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
          (Complex.exp (Complex.I * (θ : ℂ))))

axiom circleIntegral_sub_center_inv_eq_average
    (f : ℂ → ℂ) (z : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (∮ ζ in C(z, R), (ζ - z)⁻¹ * f ζ) =
      Complex.I * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        f (z + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

axiom polar_pompeiu_radial_slice_bound
    (f : ℂ → ℂ) (z : ℂ) {R M : ℝ} (hR : 0 ≤ R) (θ : ℝ)
    (h_bdd : ∀ ρ ∈ Set.Ioc 0 R,
      ‖cauchyRiemann f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ ≤ M) :
    ‖∫ ρ in (0 : ℝ)..R,
      (ρ : ℂ) * (cauchyRiemann f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
        ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z))‖ ≤ R * M

/-- **Lemma 17 (2D Polar Pompeiu Disk Integral $L^\infty$ Bound)**:
If $0 \le R$ and $\|\bar\partial f(z + \rho e^{i\theta})\| \le M$ for all $\theta \in (0, 2\pi]$ and $\rho \in (0, R]$, then
$$\left\| (\pi : \mathbb{C})^{-1} * \int_0^{2\pi} \left(\int_0^R (\rho : \mathbb{C}) * \frac{\bar\partial f(z + \rho e^{i\theta})}{(z + \rho e^{i\theta}) - z}\,d\rho\right) d\theta \right\| \le 2 * R * M.$$ -/
theorem polar_pompeiu_disk_integral_bound
    (f : ℂ → ℂ) (z : ℂ) {R M : ℝ} (hR : 0 ≤ R)
    (h_bdd : ∀ θ ∈ Set.Ioc 0 (2 * Real.pi), ∀ ρ ∈ Set.Ioc 0 R,
      ‖cauchyRiemann f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ ≤ M) :
    ‖((Real.pi : ℂ)⁻¹) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (∫ ρ in (0 : ℝ)..R,
        (ρ : ℂ) * (cauchyRiemann f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
          ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z)))‖ ≤ 2 * R * M := by
  -- Hint: Apply `norm_mul`, `norm_inv`, and `intervalIntegral.norm_integral_le_of_norm_le_const` on `θ ∈ (0, 2π]`
  -- with bound `R * M` from `polar_pompeiu_radial_slice_bound`, then cancel `Real.pi > 0`.
  sorry

/-- **Lemma 18 (Iterated Radial-then-Angular FTC Identity on $[0, R] \times [0, 2\pi]$)**:
Integrating the radial derivative over $\rho \in [0, R]$ and then $\theta \in [0, 2\pi]$ yields
$$\int_0^{2\pi} \left(\int_0^R df(z + \rho e^{i\theta})(e^{i\theta})\,d\rho\right) d\theta =
  \left(\int_0^{2\pi} f(z + R e^{i\theta})\,d\theta\right) - (2 * \pi : \mathbb{C}) * f(z).$$ -/
theorem polar_radial_angular_ftc_eq_sub
    {f : ℂ → ℂ} {z : ℂ} {R : ℝ}
    (hf_diff : ∀ θ ∈ Set.uIcc 0 (2 * Real.pi), ∀ r ∈ Set.uIcc 0 R,
      DifferentiableAt ℝ f (z + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
    (h_int_rad : ∀ θ ∈ Set.uIcc 0 (2 * Real.pi),
      IntervalIntegrable
        (fun r : ℝ => fderiv ℝ f (z + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
          (Complex.exp (Complex.I * (θ : ℂ)))) volume 0 R)
    (h_int_bdry : IntervalIntegrable
      (fun θ : ℝ => f (z + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) volume 0 (2 * Real.pi)) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (∫ r in (0 : ℝ)..R,
        fderiv ℝ f (z + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
          (Complex.exp (Complex.I * (θ : ℂ))))) =
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        f (z + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) -
        (2 * (Real.pi : ℂ)) * f z := by
  -- Hint: Use `intervalIntegral.integral_congr` with `polar_radial_intervalIntegral_eq_sub` (noting `z + (0 : ℂ) * exp(...) = z`),
  -- then apply `intervalIntegral.integral_sub` and `intervalIntegral.integral_const`.
  sorry

/-- **Lemma 19 (Polar Cauchy–Pompeiu Representation Formula on $B(z, R)$)**:
For $R > 0$,
$$f(z) = (2 * \pi * i)^{-1} * \oint_{|\zeta - z| = R} (\zeta - z)^{-1} f(\zeta)\,d\zeta
  - (\pi : \mathbb{C})^{-1} * \int_0^R \left(\int_0^{2\pi} (\rho : \mathbb{C}) * \frac{\bar\partial f(z + \rho e^{i\theta})}{(z + \rho e^{i\theta}) - z}\,d\theta\right) d\rho.$$ -/
theorem polar_cauchy_pompeiu_representation
    {f : ℂ → ℂ} {z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf_diff : ∀ ρ ∈ Set.uIcc 0 R, ∀ θ ∈ Set.uIcc 0 (2 * Real.pi),
      DifferentiableAt ℝ f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
    (h_int_ang_rad : ∀ ρ ∈ Set.Ioc 0 R,
      IntervalIntegrable
        (fun θ : ℝ => fderiv ℝ f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
          (Complex.exp (Complex.I * (θ : ℂ)))) volume 0 (2 * Real.pi))
    (h_int_ang_ang : ∀ ρ ∈ Set.Ioc 0 R,
      IntervalIntegrable
        (fun θ : ℝ => fderiv ℝ f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
          (Complex.I * ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))) volume 0 (2 * Real.pi))
    (h_int_rad : ∀ θ ∈ Set.uIcc 0 (2 * Real.pi),
      IntervalIntegrable
        (fun r : ℝ => fderiv ℝ f (z + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
          (Complex.exp (Complex.I * (θ : ℂ)))) volume 0 R)
    (h_int_bdry : IntervalIntegrable
      (fun θ : ℝ => f (z + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) volume 0 (2 * Real.pi))
    (h_fubini :
      (∫ ρ in (0 : ℝ)..R,
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          fderiv ℝ f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
            (Complex.exp (Complex.I * (θ : ℂ))))) =
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (∫ ρ in (0 : ℝ)..R,
          fderiv ℝ f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
            (Complex.exp (Complex.I * (θ : ℂ)))))) :
    f z =
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(z, R), (ζ - z)⁻¹ * f ζ) -
        ((Real.pi : ℂ)⁻¹) * (∫ ρ in (0 : ℝ)..R,
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            (ρ : ℂ) * (cauchyRiemann f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
              ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z)))) := by
  -- Hint:
  -- 1. Use `intervalIntegral.integral_congr_ae` on `ρ ∈ uIoc 0 R` (where `0 < ρ` since `0 < R`) with `polar_pompeiu_angular_slice_identity`
  --    to rewrite the double integral of the Pompeiu kernel as `(1 / 2 : ℂ)` times the `∫ ρ, ∫ θ` integral of `fderiv`.
  -- 2. Apply `h_fubini` and `polar_radial_angular_ftc_eq_sub` (Lemma 18).
  -- 3. Substitute `circleIntegral_sub_center_inv_eq_average` (Lemma 14) and finish by algebraic simplification (`field_simp; ring`) using `Real.pi_ne_zero` and `Complex.I_ne_zero`.
  sorry

end GromovCompactness.Analysis
```
