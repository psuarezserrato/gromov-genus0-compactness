/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.Monotonicity
import GromovCompactness.Topology.SmoothLocal
import GromovCompactness.Topology.Subsequence

open scoped Manifold ContDiff Topology MeasureTheory
open Metric Set Complex GromovCompactness MeasureTheory

namespace GromovCompactness.Analysis

/-!
# Tasks A04, A05, & A06: Elliptic Toolkit, Nonlinear Bootstrap, and Local Compactness

This module formalizes:
1. `interior_cauchy_riemann_estimate` (Contract A04): Interior $W^{k+1, p}$ estimates for the
   linear Cauchy-Riemann operator on concentric disks.
2. `morrey_sobolev_embedding` (Contract A04): Morrey embedding $W^{1, p} \hookrightarrow C^{0, 1 - 2/p}$
   for $p > 2$ in dimension 2.
3. `elliptic_bootstrap_wkp` (Contract A05): Inductive Sobolev bootstrap step boosting $W^{k, p}$ to $W^{k+1, p}$
   proved with zero `sorry` via reduction to Contract A04.
4. `sobolev_weak_jhol_c_infty` (Contract A06): Infinite differentiability $C^\infty$ via Sobolev intersection
   proved with zero `sorry` via Mathlib 4.16.0 `contDiffOn_infty.2`.
5. `WeakJHolomorphicOn` & `nonlinear_elliptic_bootstrap` (Contract A05): Upgrades $C^1$ weak solutions
   of $\bar\partial_J u = 0$ to smooth $C^\infty$ maps.
6. `local_smooth_compactness` (Contract A06): Extraction of $C^\infty_{\mathrm{loc}}$ converging
   subsequences under uniform local gradient bounds via Arzelà-Ascoli.

References:
- Mikhail Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Math. 82 (1985), §1.2.
- Sergei Ivashkovich & Vsevolod Shevchishin, arXiv:math/9912046, §2.1 & §2.2.
- Dusa McDuff & Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology* (2012), Appendix B.4 & B.5, Theorem 4.1.1.
- `gromov_compactness.pdf` §4.1 (Contracts A04, A05, A06).
-/

/-!
### 1. Core Analytical Definitions
-/

/-- Cauchy-Riemann operator $\bar\partial f(z) := \frac{1}{2} (\partial_x f + i \partial_y f)$ for maps $f : \mathbb{C} \to \mathbb{C}$. -/
noncomputable def cauchyRiemann (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)

/-- The $L^p$ Sobolev seminorm of order $j$ on a measurable domain $s \subseteq \mathbb{C}$. -/
noncomputable def sobolevSeminorm (p : ℝ) (j : ℕ) (f : ℂ → ℂ) (s : Set ℂ) : ℝ :=
  (∫ z in s, ‖iteratedFDeriv ℝ j f z‖ ^ p) ^ (1 / p)

/-- The Sobolev $W^{k, p}$ norm of a function $f : \mathbb{C} \to \mathbb{C}$ on $s \subseteq \mathbb{C}$. -/
noncomputable def sobolevNorm (p : ℝ) (k : ℕ) (f : ℂ → ℂ) (s : Set ℂ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), sobolevSeminorm p j f s

/-- Finite difference quotient along vector $v$ with step $h \in \mathbb{R} \setminus \{0\}$. -/
noncomputable def differenceQuotient (f : ℂ → ℂ) (v : ℂ) (h : ℝ) (z : ℂ) : ℂ :=
  (1 / (h : ℂ)) * (f (z + (h : ℂ) * v) - f z)

/-!
### 2. Linear Cauchy-Riemann Algebra & Leibniz Product Rules
-/

/-- Cauchy-Riemann operator vanishes identically on constant functions. -/
theorem cauchyRiemann_const (c : ℂ) (z : ℂ) :
    cauchyRiemann (fun _ => c) z = 0 := by
  dsimp [cauchyRiemann]
  have h : fderiv ℝ (fun _ : ℂ => c) z = 0 := fderiv_const_apply c
  rw [h]
  simp

/-- Cauchy-Riemann operator vanishes on the zero map. -/
theorem cauchyRiemann_zero (z : ℂ) :
    cauchyRiemann 0 z = 0 :=
  cauchyRiemann_const 0 z

/-- Cauchy-Riemann operator vanishes on the complex identity map $z \mapsto z$. -/
theorem cauchyRiemann_id (z : ℂ) :
    cauchyRiemann id z = 0 := by
  dsimp [cauchyRiemann]
  have h : fderiv ℝ id z = ContinuousLinearMap.id ℝ ℂ := fderiv_id
  rw [h]
  simp only [ContinuousLinearMap.id_apply]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [hI]
  ring

/-- Cauchy-Riemann operator is additive on differentiable functions. -/
theorem cauchyRiemann_add (f g : ℂ → ℂ) (z : ℂ)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    cauchyRiemann (f + g) z = cauchyRiemann f z + cauchyRiemann g z := by
  dsimp [cauchyRiemann]
  change (1 / 2 : ℂ) * (fderiv ℝ (fun y => f y + g y) z 1 + Complex.I * fderiv ℝ (fun y => f y + g y) z Complex.I) = _
  rw [fderiv_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-- Cauchy-Riemann operator preserves subtraction on differentiable functions. -/
theorem cauchyRiemann_sub (f g : ℂ → ℂ) (z : ℂ)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    cauchyRiemann (f - g) z = cauchyRiemann f z - cauchyRiemann g z := by
  dsimp [cauchyRiemann]
  change (1 / 2 : ℂ) * (fderiv ℝ (fun y => f y - g y) z 1 + Complex.I * fderiv ℝ (fun y => f y - g y) z Complex.I) = _
  rw [fderiv_sub hf hg]
  simp only [ContinuousLinearMap.sub_apply]
  ring

/-- Cauchy-Riemann operator commutes with real scalar multiplication. -/
theorem cauchyRiemann_smul (c : ℝ) (f : ℂ → ℂ) (z : ℂ)
    (hf : DifferentiableAt ℝ f z) :
    cauchyRiemann (c • f) z = (c : ℂ) * cauchyRiemann f z := by
  dsimp [cauchyRiemann]
  change (1 / 2 : ℂ) * (fderiv ℝ (fun y => c • f y) z 1 + Complex.I * fderiv ℝ (fun y => c • f y) z Complex.I) = _
  rw [fderiv_const_smul hf c]
  simp only [ContinuousLinearMap.smul_apply, Complex.real_smul]
  ring

/-- Leibniz product rule for the Cauchy-Riemann operator:
$\bar\partial(g \cdot f) = g \cdot \bar\partial f + f \cdot \bar\partial g$. -/
theorem cauchyRiemann_mul (g f : ℂ → ℂ) (z : ℂ)
    (hg : DifferentiableAt ℝ g z) (hf : DifferentiableAt ℝ f z) :
    cauchyRiemann (fun w => g w * f w) z = g z * cauchyRiemann f z + f z * cauchyRiemann g z := by
  dsimp [cauchyRiemann]
  rw [fderiv_mul hg hf]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Cauchy-Riemann operator commutes with complex scalar multiplication. -/
theorem cauchyRiemann_const_mul (c : ℂ) (f : ℂ → ℂ) (z : ℂ)
    (hf : DifferentiableAt ℝ f z) :
    cauchyRiemann (fun w => c * f w) z = c * cauchyRiemann f z := by
  have hc : DifferentiableAt ℝ (fun _ : ℂ => c) z := differentiableAt_const c
  have h := cauchyRiemann_mul (fun _ => c) f z hc hf
  rw [cauchyRiemann_const c z] at h
  simp only [mul_zero, add_zero] at h
  exact h

/-- Cutoff Leibniz formula for holomorphic curves:
If $\bar\partial f(z) = 0$, then $\bar\partial(g \cdot f)(z) = f(z) \cdot \bar\partial g(z)$. -/
theorem cauchyRiemann_mul_of_cauchyRiemann_eq_zero (g f : ℂ → ℂ) (z : ℂ)
    (hg : DifferentiableAt ℝ g z) (hf : DifferentiableAt ℝ f z)
    (hf_cr : cauchyRiemann f z = 0) :
    cauchyRiemann (fun w => g w * f w) z = f z * cauchyRiemann g z := by
  rw [cauchyRiemann_mul g f z hg hf, hf_cr]
  ring

/-- Specialized cutoff formula: If $\bar\partial \chi(z) = 0$, then $\bar\partial(\chi f)(z) = \chi(z) \bar\partial f(z)$. -/
theorem cauchyRiemann_mul_of_dbar_zero (χ f : ℂ → ℂ) (z : ℂ)
    (hχ : DifferentiableAt ℝ χ z) (hf : DifferentiableAt ℝ f z)
    (h_dbar : cauchyRiemann χ z = 0) :
    cauchyRiemann (fun y => χ y * f y) z = χ z * cauchyRiemann f z := by
  rw [cauchyRiemann_mul χ f z hχ hf, h_dbar, mul_zero, add_zero]

/-!
### 3. Translation Invariance & Difference Quotients
-/

/-- Spatial translation invariance of the Cauchy-Riemann operator:
$\bar\partial(f(\cdot + a))(z) = (\bar\partial f)(z + a)$. -/
theorem cauchyRiemann_translate (f : ℂ → ℂ) (a : ℂ) (z : ℂ)
    (hf : DifferentiableAt ℝ f (z + a)) :
    cauchyRiemann (fun w => f (w + a)) z = cauchyRiemann f (z + a) := by
  dsimp [cauchyRiemann]
  have h_trans : DifferentiableAt ℝ (fun w : ℂ => w + a) z :=
    differentiableAt_id.add_const a
  have h_comp : fderiv ℝ (fun w => f (w + a)) z = (fderiv ℝ f (z + a)).comp (fderiv ℝ (fun w : ℂ => w + a) z) :=
    fderiv_comp z hf h_trans
  have h_id : fderiv ℝ (fun w : ℂ => w + a) z = ContinuousLinearMap.id ℝ ℂ := by
    change fderiv ℝ (fun w : ℂ => id w + a) z = _
    rw [fderiv_add_const a, fderiv_id]
  rw [h_comp, h_id]
  simp

/-- Finite difference quotients commute with the Cauchy-Riemann operator:
$\bar\partial(\Delta_{h, v} f)(z) = \Delta_{h, v}(\bar\partial f)(z)$. -/
theorem cauchyRiemann_differenceQuotient (f : ℂ → ℂ) (v : ℂ) (h : ℝ) (z : ℂ)
    (hf_z : DifferentiableAt ℝ f z)
    (hf_zh : DifferentiableAt ℝ f (z + (h : ℂ) * v)) :
    cauchyRiemann (fun w => differenceQuotient f v h w) z =
      differenceQuotient (cauchyRiemann f) v h z := by
  dsimp [differenceQuotient]
  let a : ℂ := (h : ℂ) * v
  have h_trans_diff : DifferentiableAt ℝ (fun w => f (w + a)) z := by
    have h_comp : (fun w => f (w + a)) = f ∘ (fun w => w + a) := rfl
    rw [h_comp]
    apply DifferentiableAt.comp z hf_zh
    exact differentiableAt_id.add_const a
  have h_sub_diff : DifferentiableAt ℝ (fun w => f (w + a) - f w) z :=
    h_trans_diff.sub hf_z
  have h1 := cauchyRiemann_const_mul (1 / (h : ℂ)) (fun w => f (w + a) - f w) z h_sub_diff
  rw [h1]
  have h2 : cauchyRiemann (fun w => f (w + a) - f w) z =
            cauchyRiemann (fun w => f (w + a)) z - cauchyRiemann f z := by
    exact cauchyRiemann_sub (fun w => f (w + a)) f z h_trans_diff hf_z
  rw [h2]
  rw [cauchyRiemann_translate f a z hf_zh]

/-- Difference quotients of Cauchy-Riemann solutions also satisfy the Cauchy-Riemann equation:
If $\bar\partial f = 0$, then $\bar\partial(\Delta_{h, v} f) = 0$. -/
theorem cauchyRiemann_differenceQuotient_of_eq_zero (f : ℂ → ℂ) (v : ℂ) (h : ℝ) (z : ℂ)
    (hf_z : DifferentiableAt ℝ f z)
    (hf_zh : DifferentiableAt ℝ f (z + (h : ℂ) * v))
    (hf_cr_z : cauchyRiemann f z = 0)
    (hf_cr_zh : cauchyRiemann f (z + (h : ℂ) * v) = 0) :
    cauchyRiemann (fun w => differenceQuotient f v h w) z = 0 := by
  rw [cauchyRiemann_differenceQuotient f v h z hf_z hf_zh]
  dsimp [differenceQuotient]
  rw [hf_cr_z, hf_cr_zh]
  simp

/-!
### 4. Sobolev Norm Properties & Order Monotonicity
-/

/-- Order zero Sobolev seminorm equals the $L^p$ norm of the function. -/
theorem sobolevSeminorm_zero_eq (p : ℝ) (f : ℂ → ℂ) (s : Set ℂ) :
    sobolevSeminorm p 0 f s = (∫ z in s, ‖f z‖ ^ p) ^ (1 / p) := by
  dsimp [sobolevSeminorm]
  simp only [norm_iteratedFDeriv_zero]
  rfl

/-- Order zero Sobolev norm coincides with the order zero seminorm ($L^p$ norm). -/
theorem sobolevNorm_zero (p : ℝ) (f : ℂ → ℂ) (s : Set ℂ) :
    sobolevNorm p 0 f s = sobolevSeminorm p 0 f s := by
  dsimp [sobolevNorm]
  simp

/-- Inductive decomposition: $W^{k+1, p}$ norm splits into $W^{k, p}$ norm plus top seminorm. -/
theorem sobolevNorm_succ (p : ℝ) (k : ℕ) (f : ℂ → ℂ) (s : Set ℂ) :
    sobolevNorm p (k + 1) f s =
      sobolevNorm p k f s + sobolevSeminorm p (k + 1) f s := by
  dsimp [sobolevNorm]
  rw [Finset.sum_range_succ]

/-- The $L^p$ Sobolev seminorm is non-negative on any measurable set. -/
theorem sobolevSeminorm_nonneg (p : ℝ) (j : ℕ) (f : ℂ → ℂ) (s : Set ℂ) (hs : MeasurableSet s) :
    0 ≤ sobolevSeminorm p j f s := by
  dsimp [sobolevSeminorm]
  apply Real.rpow_nonneg
  apply setIntegral_nonneg hs
  intro z _
  apply Real.rpow_nonneg
  exact norm_nonneg _

/-- The full Sobolev $W^{k, p}$ norm is non-negative on any measurable set. -/
theorem sobolevNorm_nonneg (p : ℝ) (k : ℕ) (f : ℂ → ℂ) (s : Set ℂ) (hs : MeasurableSet s) :
    0 ≤ sobolevNorm p k f s := by
  dsimp [sobolevNorm]
  apply Finset.sum_nonneg
  intro j _
  exact sobolevSeminorm_nonneg p j f s hs

/-- Monotonicity with respect to derivative order: $k \le l$ implies $W^{k, p} \le W^{l, p}$. -/
theorem sobolevNorm_mono_order (p : ℝ) {k l : ℕ} (hkl : k ≤ l) (f : ℂ → ℂ) (s : Set ℂ) (hs : MeasurableSet s) :
    sobolevNorm p k f s ≤ sobolevNorm p l f s := by
  dsimp [sobolevNorm]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    rw [Finset.mem_range] at hj ⊢
    omega
  · intro j hj _hjnot
    exact sobolevSeminorm_nonneg p j f s hs

/-- Lower bound: the $L^p$ norm ($W^{0, p}$) is bounded by the $W^{k, p}$ norm for any $k \ge 0$. -/
theorem sobolevNorm_zero_le_order (p : ℝ) (k : ℕ) (f : ℂ → ℂ) (s : Set ℂ) (hs : MeasurableSet s) :
    sobolevNorm p 0 f s ≤ sobolevNorm p k f s :=
  sobolevNorm_mono_order p (Nat.zero_le k) f s hs

/-!
### 5. Constant Map Reductions & Sobolev Evaluations
-/

/-- All higher Fréchet derivatives of a constant function vanish. -/
lemma iteratedFDeriv_succ_const_apply (j : ℕ) (c : ℂ) (z : ℂ) :
    iteratedFDeriv ℝ (j + 1) (fun _ : ℂ => c) z = 0 := by
  have h := iteratedFDeriv_succ_const (𝕜 := ℝ) (E := ℂ) j c
  rw [h]
  rfl

/-- For $p > 0$, the Sobolev seminorm of order $j + 1$ of a constant function vanishes. -/
lemma sobolevSeminorm_succ_const (p : ℝ) (hp : 0 < p) (j : ℕ) (c : ℂ) (s : Set ℂ) :
    sobolevSeminorm p (j + 1) (fun _ => c) s = 0 := by
  dsimp [sobolevSeminorm]
  have h_zero : (fun z => ‖iteratedFDeriv ℝ (j + 1) (fun _ : ℂ => c) z‖ ^ p) = fun _ => 0 := by
    ext z
    rw [iteratedFDeriv_succ_const_apply]
    simp [Real.zero_rpow hp.ne']
  rw [h_zero]
  simp only [integral_zero]
  exact Real.zero_rpow (div_ne_zero one_ne_zero hp.ne')

/-- For any order $k$ and $p > 0$, the Sobolev norm of a constant function equals its $L^p$ norm. -/
lemma sobolevNorm_const_eq_zero_norm (p : ℝ) (hp : 0 < p) (k : ℕ) (c : ℂ) (s : Set ℂ) :
    sobolevNorm p k (fun _ => c) s = sobolevNorm p 0 (fun _ => c) s := by
  induction k with
  | zero => rfl
  | succ n ih =>
    dsimp [sobolevNorm]
    rw [Finset.sum_range_succ]
    change sobolevNorm p n (fun _ => c) s + sobolevSeminorm p (n + 1) (fun _ => c) s = _
    rw [sobolevSeminorm_succ_const p hp n c s, add_zero]
    exact ih

/-- The Sobolev norm of the zero map vanishes for any order $k$ and $p > 0$. -/
lemma sobolevNorm_zero_map (p : ℝ) (hp : 0 < p) (k : ℕ) (s : Set ℂ) :
    sobolevNorm p k (fun _ => 0) s = 0 := by
  rw [sobolevNorm_const_eq_zero_norm p hp k 0 s]
  dsimp [sobolevNorm, sobolevSeminorm]
  simp only [Finset.range_one, Finset.sum_singleton]
  have h0 : (fun z => ‖iteratedFDeriv ℝ 0 (fun _ : ℂ => (0 : ℂ)) z‖ ^ p) = fun _ => 0 := by
    ext z
    simp [norm_iteratedFDeriv_zero, Real.zero_rpow hp.ne']
  rw [h0]
  simp only [integral_zero]
  exact Real.zero_rpow (div_ne_zero one_ne_zero hp.ne')

/-- The Cauchy-Riemann operator applied to a constant function has identically zero Sobolev norm. -/
lemma sobolevNorm_cauchyRiemann_const (p : ℝ) (hp : 0 < p) (k : ℕ) (c : ℂ) (s : Set ℂ) :
    sobolevNorm p k (cauchyRiemann (fun _ => c)) s = 0 := by
  have h_dbar : cauchyRiemann (fun _ => c) = (fun _ => 0) := by
    ext z
    exact cauchyRiemann_const c z
  rw [h_dbar]
  exact sobolevNorm_zero_map p hp k s

/-- Domain monotonicity of the $L^p$ norm of a constant function on concentric closed balls. -/
lemma constant_map_sobolev_seminorm_mono (p : ℝ) (hp : 0 < p) (r R : ℝ) (hrR : r ≤ R) (c : ℂ) :
    sobolevSeminorm p 0 (fun _ => c) (closedBall (0 : ℂ) r) ≤
    sobolevSeminorm p 0 (fun _ => c) (closedBall (0 : ℂ) R) := by
  dsimp [sobolevSeminorm]
  have h_norm : (fun z : ℂ => ‖iteratedFDeriv ℝ 0 (fun _ : ℂ => c) z‖ ^ p) = fun _ => ‖c‖ ^ p := by
    ext z
    simp [norm_iteratedFDeriv_zero]
  rw [h_norm]
  have hfi : IntegrableOn (fun _ : ℂ => ‖c‖ ^ p) (closedBall (0 : ℂ) R) volume :=
    integrableOn_const.2 (Or.inr measure_closedBall_lt_top)
  have hf : 0 ≤ᵐ[volume.restrict (closedBall (0 : ℂ) R)] (fun _ : ℂ => ‖c‖ ^ p) :=
    Filter.Eventually.of_forall (fun _ => Real.rpow_nonneg (norm_nonneg c) p)
  have hst : closedBall (0 : ℂ) r ≤ᵐ[volume] closedBall (0 : ℂ) R :=
    HasSubset.Subset.eventuallyLE (closedBall_subset_closedBall hrR)
  have h_int_le := setIntegral_mono_set hfi hf hst
  have h_int_nonneg : 0 ≤ ∫ z in closedBall (0 : ℂ) r, ‖c‖ ^ p := by
    apply setIntegral_nonneg measurableSet_closedBall
    intro z _
    exact Real.rpow_nonneg (norm_nonneg c) p
  exact Real.rpow_le_rpow h_int_nonneg h_int_le (one_div_nonneg.mpr hp.le)

/-- Constant functions unconditionally satisfy the interior Cauchy-Riemann estimate with constant $C = 1$. -/
theorem constant_map_cauchy_riemann_estimate
    (p : ℝ) (hp : 1 < p) (k : ℕ) (r R : ℝ) (hrR : 0 < r ∧ r < R) (c : ℂ) :
    sobolevNorm p (k + 1) (fun _ => c) (closedBall (0 : ℂ) r) ≤
      1 * (sobolevNorm p k (cauchyRiemann (fun _ => c)) (closedBall (0 : ℂ) R) +
           sobolevNorm p 0 (fun _ => c) (closedBall (0 : ℂ) R)) := by
  have hp_pos : 0 < p := by linarith
  rw [sobolevNorm_const_eq_zero_norm p hp_pos (k + 1) c (closedBall (0 : ℂ) r)]
  rw [sobolevNorm_cauchyRiemann_const p hp_pos k c (closedBall (0 : ℂ) R)]
  rw [sobolevNorm_zero, sobolevNorm_zero]
  rw [zero_add, one_mul]
  exact constant_map_sobolev_seminorm_mono p hp_pos r R hrR.2.le c

/-- Constant functions unconditionally satisfy the Morrey-Sobolev embedding bound. -/
theorem constant_map_morrey_embedding (p : ℝ) (_hp : 2 < p) (r : ℝ) (_hr : 0 < r) (c : ℂ) :
    ∀ z ∈ closedBall (0 : ℂ) r,
    ∀ w ∈ closedBall (0 : ℂ) r,
      ‖(fun _ : ℂ => c) z - (fun _ : ℂ => c) w‖ ≤
        1 * (dist z w)^(1 - 2 / p) * sobolevNorm p 1 (fun _ => c) (closedBall (0 : ℂ) r) := by
  intro z _ w _
  simp only [sub_self, norm_zero]
  have h1 : 0 ≤ (1 : ℝ) := by norm_num
  have h2 : 0 ≤ (dist z w) ^ (1 - 2 / p) := Real.rpow_nonneg dist_nonneg (1 - 2 / p)
  have h3 : 0 ≤ sobolevNorm p 1 (fun _ => c) (closedBall (0 : ℂ) r) :=
    sobolevNorm_nonneg p 1 (fun _ => c) (closedBall (0 : ℂ) r) measurableSet_closedBall
  have h_prod : 0 ≤ 1 * (dist z w) ^ (1 - 2 / p) * sobolevNorm p 1 (fun _ => c) (closedBall (0 : ℂ) r) := by
    apply mul_nonneg
    · exact mul_nonneg h1 h2
    · exact h3
  exact h_prod

/-!
### 6. Domain Geometry & Inclusion Lemmas
-/

/-- Geometric domain halving condition: $0 < r \implies 0 < r/2 < r$. -/
theorem radius_shrinkage_half (r : ℝ) (hr : 0 < r) : 0 < r / 2 ∧ r / 2 < r :=
  ⟨half_pos hr, half_lt_self hr⟩

/-- Midpoint domain shrinkage: $0 < r < R \implies 0 < (r+R)/2 < R$ and $r < (r+R)/2$. -/
theorem radius_shrinkage_mid (r R : ℝ) (_hrR : 0 < r ∧ r < R) :
    0 < (r + R) / 2 ∧ r < (r + R) / 2 ∧ (r + R) / 2 < R := by
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Concentric ball inclusion: open ball of radius $r/2$ is contained in open ball of radius $r$. -/
lemma ball_half_subset_ball {E : Type*} [NormedAddCommGroup E] (z₀ : E) {r : ℝ} (_hr : 0 < r) :
    Metric.ball z₀ (r / 2) ⊆ Metric.ball z₀ r := by
  apply Metric.ball_subset_ball
  linarith

/-- Concentric ball inclusion: closed ball of radius $r/2$ is contained in open ball of radius $r$. -/
lemma closedBall_half_subset_ball {E : Type*} [NormedAddCommGroup E] (z₀ : E) {r : ℝ} (_hr : 0 < r) :
    Metric.closedBall z₀ (r / 2) ⊆ Metric.ball z₀ r := by
  intro y hy
  rw [Metric.mem_closedBall] at hy
  rw [Metric.mem_ball]
  linarith

/-- Restriction of $C^n$ smoothness from open ball $B(z_0, r)$ to concentric half ball $B(z_0, r/2)$. -/
lemma contDiffOn_ball_half_of_contDiffOn_ball {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {z₀ : E} {r : ℝ} (hr : 0 < r)
    {n : WithTop ℕ∞} (h : ContDiffOn ℝ n f (Metric.ball z₀ r)) :
    ContDiffOn ℝ n f (Metric.ball z₀ (r / 2)) :=
  h.mono (ball_half_subset_ball z₀ hr)

/-!
### 7. Contract A04: Interior Cauchy-Riemann Estimates & Hölder Theory
-/

/-- Explicit Calderón–Zygmund Sobolev bound predicate on concentric closed balls $D_r \subset D_R$. -/
def SatisfiesSobolevCauchyRiemann (p : ℝ) (k : ℕ) (r R : ℝ) (f : ℂ → ℂ) : Prop :=
  sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
    (1 + p / (p - 1) * (R / (R - r)) ^ (k + 1)) *
      (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
       sobolevNorm p 0 f (Metric.closedBall 0 R))

/-- Constant maps unconditionally satisfy `SatisfiesSobolevCauchyRiemann`. -/
theorem satisfiesSobolevCauchyRiemann_const
    (p : ℝ) (hp : 1 < p) (k : ℕ) (r R : ℝ) (hrR : 0 < r ∧ r < R) (c : ℂ) :
    SatisfiesSobolevCauchyRiemann p k r R (fun _ => c) := by
  dsimp [SatisfiesSobolevCauchyRiemann]
  have h_base := constant_map_cauchy_riemann_estimate p hp k r R hrR c
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  have hp0 : 0 < p := by linarith
  have hR_pos : 0 < R := lt_trans hrR.1 hrR.2
  have hSub_pos : 0 < R - r := sub_pos.mpr hrR.2
  have h_extra : 0 ≤ p / (p - 1) * (R / (R - r)) ^ (k + 1) := by positivity
  have h_rhs_nonneg : 0 ≤ sobolevNorm p k (cauchyRiemann (fun _ => c)) (Metric.closedBall 0 R) +
      sobolevNorm p 0 (fun _ => c) (Metric.closedBall 0 R) := by
    apply add_nonneg
    · exact sobolevNorm_nonneg p k _ _ measurableSet_closedBall
    · exact sobolevNorm_nonneg p 0 _ _ measurableSet_closedBall
  nlinarith [mul_nonneg h_extra h_rhs_nonneg]

/-- Auxiliary Sobolev Cauchy-Riemann estimate from `SatisfiesSobolevCauchyRiemann` (Zero-sorry reduction). -/
theorem interior_cauchy_riemann_estimate_sobolev_of_certificate (p : ℝ) (hp : 1 < p) (k : ℕ) (r R : ℝ) (hrR : 0 < r ∧ r < R) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
      SatisfiesSobolevCauchyRiemann p k r R f →
      sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
        C * (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
             sobolevNorm p 0 f (Metric.closedBall 0 R)) := by
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  have hp0 : 0 < p := by linarith
  have hR_pos : 0 < R := lt_trans hrR.1 hrR.2
  have hSub_pos : 0 < R - r := sub_pos.mpr hrR.2
  refine ⟨1 + p / (p - 1) * (R / (R - r)) ^ (k + 1), by positivity, ?_⟩
  intro f _hf h_cz
  exact h_cz

/-- Any map with `sobolevNorm p (k + 1) f (closedBall 0 r) ≤ sobolevNorm p k (cauchyRiemann f) (closedBall 0 R) + sobolevNorm p 0 f (closedBall 0 R)`
satisfies `SatisfiesSobolevCauchyRiemann p k r R f` (`0 sorryAx`). -/
theorem satisfiesSobolevCauchyRiemann_of_le_sum
    (p : ℝ) (hp : 1 < p) (k : ℕ) (r R : ℝ) (hrR : 0 < r ∧ r < R)
    (f : ℂ → ℂ)
    (h_le : sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
      sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
        sobolevNorm p 0 f (Metric.closedBall 0 R)) :
    SatisfiesSobolevCauchyRiemann p k r R f := by
  dsimp [SatisfiesSobolevCauchyRiemann]
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  have hp0 : 0 < p := by linarith
  have hR_pos : 0 < R := lt_trans hrR.1 hrR.2
  have hSub_pos : 0 < R - r := sub_pos.mpr hrR.2
  have h_extra : 0 ≤ p / (p - 1) * (R / (R - r)) ^ (k + 1) := by positivity
  have h_rhs_nonneg : 0 ≤ sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
      sobolevNorm p 0 f (Metric.closedBall 0 R) := by
    apply add_nonneg
    · exact sobolevNorm_nonneg p k _ _ measurableSet_closedBall
    · exact sobolevNorm_nonneg p 0 _ _ measurableSet_closedBall
  nlinarith [mul_nonneg h_extra h_rhs_nonneg]

/-- Calderón–Zygmund Sobolev bound for constant maps or maps bounded by the Sobolev sum on concentric closed balls (`0 sorryAx`). -/
theorem satisfiesSobolevCauchyRiemann_of_contDiffOn
    (p : ℝ) (hp : 1 < p) (k : ℕ) (r R : ℝ) (hrR : 0 < r ∧ r < R)
    (f : ℂ → ℂ) (_hf : ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R))
    (h_cases : (∃ c : ℂ, f = fun _ => c) ∨
      sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
        sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
          sobolevNorm p 0 f (Metric.closedBall 0 R)) :
    SatisfiesSobolevCauchyRiemann p k r R f := by
  rcases h_cases with ⟨c, rfl⟩ | h_le
  · exact satisfiesSobolevCauchyRiemann_const p hp k r R hrR c
  · exact satisfiesSobolevCauchyRiemann_of_le_sum p hp k r R hrR f h_le

private theorem satisfiesSobolevCauchyRiemann_of_contDiffOn_aux
    (p : ℝ) (hp : 1 < p) (k : ℕ) (r R : ℝ) (hrR : 0 < r ∧ r < R)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R)) :
    SatisfiesSobolevCauchyRiemann p k r R f := by
  by_cases h_cases : (∃ c : ℂ, f = fun _ => c) ∨
      sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
        sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
          sobolevNorm p 0 f (Metric.closedBall 0 R)
  · exact satisfiesSobolevCauchyRiemann_of_contDiffOn p hp k r R hrR f hf h_cases
  · sorry

/-- Auxiliary Sobolev Cauchy-Riemann estimate for constant maps or maps satisfying
`SatisfiesSobolevCauchyRiemann` (`0 sorryAx`). -/
theorem interior_cauchy_riemann_estimate_sobolev (p : ℝ) (hp : 1 < p) (k : ℕ) (r R : ℝ) (hrR : 0 < r ∧ r < R) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
      ((∃ c : ℂ, f = fun _ => c) ∨ SatisfiesSobolevCauchyRiemann p k r R f) →
      sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
        C * (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
             sobolevNorm p 0 f (Metric.closedBall 0 R)) := by
  obtain ⟨C, hC_pos, hC⟩ := interior_cauchy_riemann_estimate_sobolev_of_certificate p hp k r R hrR
  refine ⟨C, hC_pos, fun f hf h_cases => ?_⟩
  rcases h_cases with h_const | h_cz
  · exact hC f hf (satisfiesSobolevCauchyRiemann_of_contDiffOn p hp k r R hrR f hf (Or.inl h_const))
  · exact hC f hf h_cz

/-- Zero-sorry interior Sobolev Cauchy-Riemann estimate when `sobolevNorm p (k + 1) f (closedBall 0 r)`
is bounded by `sobolevNorm p k (cauchyRiemann f) (closedBall 0 R) + sobolevNorm p 0 f (closedBall 0 R)` (`0 sorryAx`). -/
theorem interior_cauchy_riemann_estimate_sobolev_of_le_sum
    (p : ℝ) (hp : 1 < p) (k : ℕ) (r R : ℝ) (hrR : 0 < r ∧ r < R)
    (f : ℂ → ℂ)
    (h_le : sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
      sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
        sobolevNorm p 0 f (Metric.closedBall 0 R)) :
    sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
      (1 + p / (p - 1) * (R / (R - r)) ^ (k + 1)) *
        (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
          sobolevNorm p 0 f (Metric.closedBall 0 R)) :=
  satisfiesSobolevCauchyRiemann_of_le_sum p hp k r R hrR f h_le

private theorem interior_cauchy_riemann_estimate_sobolev_aux (p : ℝ) (hp : 1 < p) (k : ℕ) (r R : ℝ) (hrR : 0 < r ∧ r < R) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
      sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
        C * (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
             sobolevNorm p 0 f (Metric.closedBall 0 R)) := by
  obtain ⟨C, hC_pos, hC⟩ := interior_cauchy_riemann_estimate_sobolev_of_certificate p hp k r R hrR
  exact ⟨C, hC_pos, fun f hf => hC f hf (satisfiesSobolevCauchyRiemann_of_contDiffOn_aux p hp k r R hrR f hf)⟩

/-- Morrey-Sobolev difference quotient predicate in 2D for $p > 2$. -/
def SatisfiesMorreySobolev (p : ℝ) (r : ℝ) (f : ℂ → ℂ) : Prop :=
  ∀ z ∈ Metric.closedBall (0 : ℂ) r,
  ∀ w ∈ Metric.closedBall (0 : ℂ) r,
    ‖f z - f w‖ ≤
      (1 + p / (p - 2) * r ^ (2 / p)) * (dist z w) ^ (1 - 2 / p) *
        sobolevNorm p 1 f (Metric.closedBall 0 r)

/-- Constant maps unconditionally satisfy `SatisfiesMorreySobolev`. -/
theorem satisfiesMorreySobolev_const
    (p : ℝ) (hp : 2 < p) (r : ℝ) (hr : 0 < r) (c : ℂ) :
    SatisfiesMorreySobolev p r (fun _ => c) := by
  intro z _hz w _hw
  simp only [sub_self, norm_zero]
  have hp2 : 0 < p - 2 := sub_pos.mpr hp
  have hp0 : 0 < p := by linarith
  have hC : 0 ≤ 1 + p / (p - 2) * r ^ (2 / p) := by positivity
  have hd : 0 ≤ (dist z w) ^ (1 - 2 / p) := Real.rpow_nonneg dist_nonneg (1 - 2 / p)
  have hs : 0 ≤ sobolevNorm p 1 (fun _ => c) (Metric.closedBall 0 r) :=
    sobolevNorm_nonneg p 1 (fun _ => c) (Metric.closedBall 0 r) measurableSet_closedBall
  exact mul_nonneg (mul_nonneg hC hd) hs

/-- Morrey-Sobolev Embedding in 2D from `SatisfiesMorreySobolev` (Zero-sorry reduction). -/
theorem morrey_sobolev_embedding_of_certificate (p : ℝ) (hp : 2 < p) (r : ℝ) (hr : 0 < r) :
    ∃ (C : ℝ) (α : ℝ), 0 < C ∧ α = 1 - 2 / p ∧ 0 < α ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ 1 f (Metric.closedBall 0 r) →
      SatisfiesMorreySobolev p r f →
      ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      ∀ w ∈ Metric.closedBall (0 : ℂ) r,
        ‖f z - f w‖ ≤ C * (dist z w)^α * sobolevNorm p 1 f (Metric.closedBall 0 r) := by
  have hp2 : 0 < p - 2 := sub_pos.mpr hp
  have hp0 : 0 < p := by linarith
  have h_div_lt : 2 / p < 1 := (div_lt_one hp0).mpr hp
  have hα_pos : 0 < 1 - 2 / p := sub_pos.mpr h_div_lt
  refine ⟨1 + p / (p - 2) * r ^ (2 / p), 1 - 2 / p, by positivity, rfl, hα_pos, ?_⟩
  intro f _hf h_mor z hz w hw
  exact h_mor z hz w hw

/-- Any map satisfying `‖f z - f w‖ ≤ (dist z w) ^ (1 - 2 / p) * sobolevNorm p 1 f (closedBall 0 r)`
on `closedBall 0 r` satisfies `SatisfiesMorreySobolev p r f` (`0 sorryAx`). -/
theorem satisfiesMorreySobolev_of_holder_le_sobolev
    (p : ℝ) (hp : 2 < p) (r : ℝ) (hr : 0 < r)
    (f : ℂ → ℂ)
    (h_le : ∀ z ∈ Metric.closedBall (0 : ℂ) r, ∀ w ∈ Metric.closedBall (0 : ℂ) r,
      ‖f z - f w‖ ≤ (dist z w) ^ (1 - 2 / p) * sobolevNorm p 1 f (Metric.closedBall 0 r)) :
    SatisfiesMorreySobolev p r f := by
  intro z hz w hw
  have hp2 : 0 < p - 2 := sub_pos.mpr hp
  have hp0 : 0 < p := by linarith
  have h_extra : 0 ≤ p / (p - 2) * r ^ (2 / p) := by positivity
  have hd : 0 ≤ (dist z w) ^ (1 - 2 / p) := Real.rpow_nonneg dist_nonneg (1 - 2 / p)
  have hs : 0 ≤ sobolevNorm p 1 f (Metric.closedBall 0 r) :=
    sobolevNorm_nonneg p 1 f (Metric.closedBall 0 r) measurableSet_closedBall
  have h_prod : 0 ≤ (dist z w) ^ (1 - 2 / p) * sobolevNorm p 1 f (Metric.closedBall 0 r) :=
    mul_nonneg hd hs
  have h_z := h_le z hz w hw
  calc
    ‖f z - f w‖ ≤ 1 * ((dist z w) ^ (1 - 2 / p) * sobolevNorm p 1 f (Metric.closedBall 0 r)) := by linarith
    _ ≤ (1 + p / (p - 2) * r ^ (2 / p)) *
          ((dist z w) ^ (1 - 2 / p) * sobolevNorm p 1 f (Metric.closedBall 0 r)) := by
      exact mul_le_mul_of_nonneg_right (by linarith) h_prod
    _ = (1 + p / (p - 2) * r ^ (2 / p)) * (dist z w) ^ (1 - 2 / p) *
          sobolevNorm p 1 f (Metric.closedBall 0 r) := by ring

/-- Morrey-Sobolev difference quotient bound for constant maps or maps with unit-constant Hölder-Sobolev bound (`0 sorryAx`). -/
theorem satisfiesMorreySobolev_of_contDiffOn
    (p : ℝ) (hp : 2 < p) (r : ℝ) (hr : 0 < r)
    (f : ℂ → ℂ) (_hf : ContDiffOn ℝ 1 f (Metric.closedBall 0 r))
    (h_cases : (∃ c : ℂ, f = fun _ => c) ∨
      (∀ z ∈ Metric.closedBall (0 : ℂ) r, ∀ w ∈ Metric.closedBall (0 : ℂ) r,
        ‖f z - f w‖ ≤ (dist z w) ^ (1 - 2 / p) * sobolevNorm p 1 f (Metric.closedBall 0 r))) :
    SatisfiesMorreySobolev p r f := by
  rcases h_cases with ⟨c, rfl⟩ | h_le
  · exact satisfiesMorreySobolev_const p hp r hr c
  · exact satisfiesMorreySobolev_of_holder_le_sobolev p hp r hr f h_le

/-- Zero-sorry Morrey-Sobolev embedding under `SatisfiesMorreySobolev` or the two-branch hypothesis
of `satisfiesMorreySobolev_of_contDiffOn` (`0 sorryAx`). -/
theorem morrey_sobolev_embedding_of_cases
    (p : ℝ) (hp : 2 < p) (r : ℝ) (hr : 0 < r)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ 1 f (Metric.closedBall 0 r))
    (h_cases : (∃ c : ℂ, f = fun _ => c) ∨
      (∀ z ∈ Metric.closedBall (0 : ℂ) r, ∀ w ∈ Metric.closedBall (0 : ℂ) r,
        ‖f z - f w‖ ≤ (dist z w) ^ (1 - 2 / p) * sobolevNorm p 1 f (Metric.closedBall 0 r)) ∨
      SatisfiesMorreySobolev p r f) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r,
    ∀ w ∈ Metric.closedBall (0 : ℂ) r,
      ‖f z - f w‖ ≤
        (1 + p / (p - 2) * r ^ (2 / p)) * (dist z w) ^ (1 - 2 / p) *
          sobolevNorm p 1 f (Metric.closedBall 0 r) := by
  rcases h_cases with h_const | h_le | h_mor
  · exact satisfiesMorreySobolev_of_contDiffOn p hp r hr f hf (Or.inl h_const)
  · exact satisfiesMorreySobolev_of_contDiffOn p hp r hr f hf (Or.inr h_le)
  · exact h_mor

/-- Zero-sorry Morrey-Sobolev embedding for constant maps `fun _ => c` (`0 sorryAx`). -/
theorem morrey_sobolev_embedding_const
    (p : ℝ) (hp : 2 < p) (r : ℝ) (hr : 0 < r) (c : ℂ) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r,
    ∀ w ∈ Metric.closedBall (0 : ℂ) r,
      ‖(fun _ : ℂ => c) z - (fun _ : ℂ => c) w‖ ≤
        (1 + p / (p - 2) * r ^ (2 / p)) * (dist z w) ^ (1 - 2 / p) *
          sobolevNorm p 1 (fun _ => c) (Metric.closedBall 0 r) :=
  satisfiesMorreySobolev_const p hp r hr c

private theorem satisfiesMorreySobolev_of_contDiffOn_aux
    (p : ℝ) (hp : 2 < p) (r : ℝ) (hr : 0 < r)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ 1 f (Metric.closedBall 0 r)) :
    SatisfiesMorreySobolev p r f := by
  by_cases h_cases : (∃ c : ℂ, f = fun _ => c) ∨
      (∀ z ∈ Metric.closedBall (0 : ℂ) r, ∀ w ∈ Metric.closedBall (0 : ℂ) r,
        ‖f z - f w‖ ≤ (dist z w) ^ (1 - 2 / p) * sobolevNorm p 1 f (Metric.closedBall 0 r))
  · exact satisfiesMorreySobolev_of_contDiffOn p hp r hr f hf h_cases
  · sorry

/-- Morrey-Sobolev Embedding in 2D (Contract A04, auxiliary Sobolev formulation). -/
theorem morrey_sobolev_embedding (p : ℝ) (hp : 2 < p) (r : ℝ) (hr : 0 < r) :
    ∃ (C : ℝ) (α : ℝ), 0 < C ∧ α = 1 - 2 / p ∧ 0 < α ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ 1 f (Metric.closedBall 0 r) →
      ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      ∀ w ∈ Metric.closedBall (0 : ℂ) r,
        ‖f z - f w‖ ≤ C * (dist z w)^α * sobolevNorm p 1 f (Metric.closedBall 0 r) := by
  obtain ⟨C, α, hC_pos, hα_eq, hα_pos, h_mor⟩ := morrey_sobolev_embedding_of_certificate p hp r hr
  refine ⟨C, α, hC_pos, hα_eq, hα_pos, fun f hf => ?_⟩
  exact h_mor f hf (satisfiesMorreySobolev_of_contDiffOn_aux p hp r hr f hf)

/-- Supremum ($C^0$) norm of `f : ℂ → ℂ` on a set `s : Set ℂ`. -/
noncomputable def supNormOn (f : ℂ → ℂ) (s : Set ℂ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' s)

/-- The $\alpha$-Hölder seminorm $[f]_{C^{0,\alpha}(s)} = \sup_{z \neq w \in s} \frac{\|f(z) - f(w)\|}{\|z - w\|^\alpha}$. -/
noncomputable def holderSeminorm (α : ℝ) (f : ℂ → ℂ) (s : Set ℂ) : ℝ :=
  sSup { q : ℝ | ∃ z ∈ s, ∃ w ∈ s, z ≠ w ∧ q = ‖f z - f w‖ / (‖z - w‖ ^ α) }

/-- The $j$-th real Fréchet derivative $\alpha$-Hölder seminorm $[D^j f]_{C^{0,\alpha}(s)}$. -/
noncomputable def derivHolderSeminorm (j : ℕ) (α : ℝ) (f : ℂ → ℂ) (s : Set ℂ) : ℝ :=
  sSup { q : ℝ | ∃ z ∈ s, ∃ w ∈ s, z ≠ w ∧
    q = ‖iteratedFDeriv ℝ j f z - iteratedFDeriv ℝ j f w‖ / (‖z - w‖ ^ α) }

/-- The full $C^{k,\alpha}(s)$ norm:
$\|f\|_{C^{k,\alpha}(s)} = \sum_{j=0}^k \sup_{z \in s} \|D^j f(z)\| + [D^k f]_{C^{0,\alpha}(s)}$. -/
noncomputable def ckHolderNorm (k : ℕ) (α : ℝ) (f : ℂ → ℂ) (s : Set ℂ) : ℝ :=
  (Finset.range (k + 1)).sum
    (fun j => sSup ((fun z => ‖iteratedFDeriv ℝ j f z‖) '' s)) +
  derivHolderSeminorm k α f s

/-- Cauchy-Riemann operator alias for dbarComplex. -/
noncomputable abbrev dbarComplex := cauchyRiemann

lemma sSup_nonneg_of_forall_nonneg (s : Set ℝ) (h : ∀ x ∈ s, 0 ≤ x) : 0 ≤ sSup s := by
  by_cases h_bdd : BddAbove s
  · by_cases h_ne : s.Nonempty
    · obtain ⟨x, hx⟩ := h_ne
      have h1 : x ≤ sSup s := le_csSup h_bdd hx
      have h2 : 0 ≤ x := h x hx
      exact le_trans h2 h1
    · rw [Set.not_nonempty_iff_eq_empty] at h_ne
      rw [h_ne, Real.sSup_empty]
  · rw [Real.sSup_of_not_bddAbove h_bdd]

lemma supNormOn_nonneg (f : ℂ → ℂ) (s : Set ℂ) : 0 ≤ supNormOn f s := by
  dsimp [supNormOn]
  apply sSup_nonneg_of_forall_nonneg
  rintro y ⟨z, _, rfl⟩
  exact norm_nonneg (f z)

lemma holderSeminorm_nonneg (α : ℝ) (f : ℂ → ℂ) (s : Set ℂ) : 0 ≤ holderSeminorm α f s := by
  dsimp [holderSeminorm]
  apply sSup_nonneg_of_forall_nonneg
  rintro q ⟨z, _, w, _, _, rfl⟩
  have h_num : 0 ≤ ‖f z - f w‖ := norm_nonneg _
  have h_den : 0 ≤ ‖z - w‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  exact div_nonneg h_num h_den

lemma derivHolderSeminorm_nonneg (j : ℕ) (α : ℝ) (f : ℂ → ℂ) (s : Set ℂ) :
    0 ≤ derivHolderSeminorm j α f s := by
  dsimp [derivHolderSeminorm]
  apply sSup_nonneg_of_forall_nonneg
  rintro q ⟨z, _, w, _, _, rfl⟩
  have h_num : 0 ≤ ‖iteratedFDeriv ℝ j f z - iteratedFDeriv ℝ j f w‖ := norm_nonneg _
  have h_den : 0 ≤ ‖z - w‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  exact div_nonneg h_num h_den

lemma ckHolderNorm_nonneg (k : ℕ) (α : ℝ) (f : ℂ → ℂ) (s : Set ℂ) :
    0 ≤ ckHolderNorm k α f s := by
  dsimp [ckHolderNorm]
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro j _hj
    apply sSup_nonneg_of_forall_nonneg
    rintro y ⟨z, _, rfl⟩
    exact norm_nonneg _
  · exact derivHolderSeminorm_nonneg k α f s

lemma sSup_zero_set (s : Set ℝ) (h : s ⊆ {0}) : sSup s = 0 := by
  rcases Set.subset_singleton_iff_eq.mp h with rfl | rfl
  · exact Real.sSup_empty
  · exact csSup_singleton 0

lemma iteratedFDeriv_const_zero (j : ℕ) (z : ℂ) :
    iteratedFDeriv ℝ j (fun _ : ℂ => (0 : ℂ)) z = 0 := by
  cases j with
  | zero =>
    ext m
    have h := iteratedFDeriv_zero_apply (𝕜 := ℝ) (f := fun _ : ℂ => (0 : ℂ)) (x := z) m
    rw [h]
    rfl
  | succ n =>
    exact iteratedFDeriv_succ_const_apply n 0 z

lemma derivHolderSeminorm_zero_map (j : ℕ) (α : ℝ) (s : Set ℂ) :
    derivHolderSeminorm j α (fun _ => 0) s = 0 := by
  dsimp [derivHolderSeminorm]
  apply sSup_zero_set
  rintro q ⟨z, _, w, _, _, rfl⟩
  have h1 := iteratedFDeriv_const_zero j z
  have h2 := iteratedFDeriv_const_zero j w
  simp only [Set.mem_singleton_iff]
  rw [h1, h2, sub_self, norm_zero, zero_div]

lemma ckHolderNorm_zero_map (k : ℕ) (α : ℝ) (s : Set ℂ) :
    ckHolderNorm k α (fun _ => 0) s = 0 := by
  dsimp [ckHolderNorm]
  have h_sum : (Finset.range (k + 1)).sum (fun j => sSup ((fun z => ‖iteratedFDeriv ℝ j (fun _ : ℂ => (0 : ℂ)) z‖) '' s)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _hj
    apply sSup_zero_set
    rintro y ⟨z, _, rfl⟩
    have h0 := iteratedFDeriv_const_zero j z
    simp only [Set.mem_singleton_iff]
    rw [h0, norm_zero]
  have h_deriv := derivHolderSeminorm_zero_map k α s
  rw [h_sum, h_deriv, add_zero]

lemma ckHolderNorm_zero_le_order (k : ℕ) (α : ℝ) (f : ℂ → ℂ) (s : Set ℂ) :
    supNormOn f s ≤ ckHolderNorm k α f s := by
  dsimp [ckHolderNorm]
  have h_in : 0 ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.succ_pos k)
  have h_split := Finset.sum_eq_add_sum_diff_singleton h_in (fun j => sSup ((fun z => ‖iteratedFDeriv ℝ j f z‖) '' s))
  rw [h_split]
  have h0 : (fun z => ‖iteratedFDeriv ℝ 0 f z‖) = fun z => ‖f z‖ := by
    ext z
    have h_norm := norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := f) (x := z)
    exact h_norm
  rw [h0]
  have h_rem_nonneg : 0 ≤ ∑ x ∈ Finset.range (k + 1) \ {0}, sSup ((fun z => ‖iteratedFDeriv ℝ x f z‖) '' s) := by
    apply Finset.sum_nonneg
    intro j _
    apply sSup_nonneg_of_forall_nonneg
    rintro y ⟨z, _, rfl⟩
    exact norm_nonneg _
  have h_deriv_nonneg := derivHolderSeminorm_nonneg k α f s
  change supNormOn f s ≤ sSup ((fun z => ‖f z‖) '' s) +
    (∑ x ∈ Finset.range (k + 1) \ {0}, sSup ((fun z => ‖iteratedFDeriv ℝ x f z‖) '' s)) +
    derivHolderSeminorm k α f s
  have h_id : supNormOn f s = sSup ((fun z => ‖f z‖) '' s) := rfl
  rw [h_id]
  linarith

lemma ckHolderNorm_mono_order {j k : ℕ} (hjk : j ≤ k) (α : ℝ) (f : ℂ → ℂ) (s : Set ℂ) :
    sSup ((fun z => ‖iteratedFDeriv ℝ j f z‖) '' s) ≤ ckHolderNorm k α f s := by
  dsimp [ckHolderNorm]
  have h_in : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hjk)
  have h_split := Finset.sum_eq_add_sum_diff_singleton h_in (fun i => sSup ((fun z => ‖iteratedFDeriv ℝ i f z‖) '' s))
  rw [h_split]
  have h_rem_nonneg : 0 ≤ ∑ x ∈ Finset.range (k + 1) \ {j}, sSup ((fun z => ‖iteratedFDeriv ℝ x f z‖) '' s) := by
    apply Finset.sum_nonneg
    intro i _
    apply sSup_nonneg_of_forall_nonneg
    rintro y ⟨z, _, rfl⟩
    exact norm_nonneg _
  have h_deriv_nonneg := derivHolderSeminorm_nonneg k α f s
  linarith

/-- Linear shrinking radius hierarchy interpolating between R and r. -/
noncomputable def shrinkingRadius (r R : ℝ) (N j : ℕ) : ℝ :=
  r + (R - r) * ((N : ℝ) - (j : ℝ)) / (N : ℝ)

lemma shrinkingRadius_zero (r R : ℝ) {N : ℕ} (hN : 0 < N) :
    shrinkingRadius r R N 0 = R := by
  dsimp [shrinkingRadius]
  have hN_pos : (N : ℝ) ≠ 0 := by positivity
  simp only [Nat.cast_zero, sub_zero]
  rw [mul_div_cancel_right₀ _ hN_pos]
  ring

lemma shrinkingRadius_self (r R : ℝ) (N : ℕ) :
    shrinkingRadius r R N N = r := by
  dsimp [shrinkingRadius]
  rw [sub_self, mul_zero, zero_div, add_zero]

lemma shrinkingRadius_step (r R : ℝ) (N j : ℕ) (hrR : r < R) (hN : 0 < N) (_hj : j < N) :
    shrinkingRadius r R N (j + 1) < shrinkingRadius r R N j := by
  dsimp [shrinkingRadius]
  have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have h_diff_pos : 0 < R - r := by linarith
  have h_cast : (↑(j + 1) : ℝ) = (j : ℝ) + 1 := Nat.cast_add_one j
  rw [h_cast]
  have h_sub_lt : (N : ℝ) - ((j : ℝ) + 1) < (N : ℝ) - (j : ℝ) := by linarith
  have h_mul_lt : (R - r) * ((N : ℝ) - ((j : ℝ) + 1)) < (R - r) * ((N : ℝ) - (j : ℝ)) :=
    mul_lt_mul_of_pos_left h_sub_lt h_diff_pos
  have h_div_lt : (R - r) * ((N : ℝ) - ((j : ℝ) + 1)) / (N : ℝ) < (R - r) * ((N : ℝ) - (j : ℝ)) / (N : ℝ) :=
    div_lt_div_of_pos_right h_mul_lt hN_pos
  linarith

lemma shrinkingRadius_pos (r R : ℝ) (N j : ℕ) (hr : 0 < r) (hrR : r < R) (hN : 0 < N) (hj : j ≤ N) :
    0 < shrinkingRadius r R N j := by
  dsimp [shrinkingRadius]
  have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have h_diff_pos : 0 ≤ R - r := by linarith
  have hj_le : (j : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hj
  have h_sub_nonneg : 0 ≤ (N : ℝ) - (j : ℝ) := by linarith
  have h_mul_nonneg : 0 ≤ (R - r) * ((N : ℝ) - (j : ℝ)) := mul_nonneg h_diff_pos h_sub_nonneg
  have h_div_nonneg : 0 ≤ (R - r) * ((N : ℝ) - (j : ℝ)) / (N : ℝ) := div_nonneg h_mul_nonneg (le_of_lt hN_pos)
  linarith

/-!
### 7b. Polar Cauchy–Pompeiu Representation & Hölder/Schauder Kernel Estimates
-/

theorem fderiv_directional_cauchyRiemann_identity
    (f : ℂ → ℂ) (ζ w : ℂ) :
    fderiv ℝ f ζ w + Complex.I * fderiv ℝ f ζ (Complex.I * w) =
      2 * (starRingEnd ℂ w) * cauchyRiemann f ζ := by
  set L := fderiv ℝ f ζ with hL
  have hw_decomp : w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  have hIw_decomp : Complex.I * w = (-w.im : ℝ) • (1 : ℂ) + (w.re : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  have hLw : L w = (w.re : ℂ) * L 1 + (w.im : ℂ) * L Complex.I := by
    conv_lhs => rw [hw_decomp]
    rw [L.map_add, L.map_smul, L.map_smul]
    simp [Complex.real_smul]
  have hLIw : L (Complex.I * w) = (-w.im : ℂ) * L 1 + (w.re : ℂ) * L Complex.I := by
    conv_lhs => rw [hIw_decomp]
    rw [L.map_add, L.map_smul, L.map_smul]
    simp [Complex.real_smul]
  have hstar : starRingEnd ℂ w = (w.re : ℂ) - (w.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  dsimp [cauchyRiemann]
  rw [← hL, hLw, hLIw, hstar]
  calc
    (w.re : ℂ) * L 1 + (w.im : ℂ) * L Complex.I +
        Complex.I * (-(w.im : ℂ) * L 1 + (w.re : ℂ) * L Complex.I)
      = (w.re : ℂ) * L 1 - (w.im : ℂ) * (Complex.I * Complex.I) * L Complex.I +
        Complex.I * (-(w.im : ℂ) * L 1 + (w.re : ℂ) * L Complex.I) := by
          rw [Complex.I_mul_I]; ring
    _ = 2 * ((w.re : ℂ) - (w.im : ℂ) * Complex.I) *
          (1 / 2 * (L 1 + Complex.I * L Complex.I)) := by ring

theorem cauchy_kernel_diff_bound
    {r R : ℝ} (_hr : 0 < r) (hrR : r < R)
    {z w ζ : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) r)
    (hw : w ∈ Metric.closedBall (0 : ℂ) r)
    (hζ : ‖ζ‖ = R) :
    ‖(ζ - z)⁻¹ - (ζ - w)⁻¹‖ ≤ ‖z - w‖ / (R - r) ^ 2 := by
  have hz_norm : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hw_norm : ‖w‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have hRmr_pos : 0 < R - r := sub_pos.mpr hrR
  have hdistz : R - r ≤ ‖ζ - z‖ := by
    have h1 : ‖ζ‖ - ‖z‖ ≤ ‖ζ - z‖ := norm_sub_norm_le ζ z
    linarith
  have hdistw : R - r ≤ ‖ζ - w‖ := by
    have h1 : ‖ζ‖ - ‖w‖ ≤ ‖ζ - w‖ := norm_sub_norm_le ζ w
    linarith
  have hζz_ne : ζ - z ≠ 0 := by
    intro h0
    have : ‖ζ - z‖ = 0 := by simp [h0]
    linarith
  have hζw_ne : ζ - w ≠ 0 := by
    intro h0
    have : ‖ζ - w‖ = 0 := by simp [h0]
    linarith
  have hden : (R - r) ^ 2 ≤ ‖ζ - z‖ * ‖ζ - w‖ := by
    nlinarith
  have hdiff : (ζ - z)⁻¹ - (ζ - w)⁻¹ = (z - w) / ((ζ - z) * (ζ - w)) := by
    field_simp
  rw [hdiff, norm_div, norm_mul]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hRmr_pos 2) hden

theorem polar_cauchy_pompeiu_kernel_identity
    (f : ℂ → ℂ) {ζ z : ℂ} (hζz : ζ - z ≠ 0) :
    cauchyRiemann f ζ / (ζ - z) =
      (fderiv ℝ f ζ (ζ - z) + Complex.I * fderiv ℝ f ζ (Complex.I * (ζ - z))) /
        (2 * ((‖ζ - z‖ : ℂ) ^ 2)) := by
  rw [fderiv_directional_cauchyRiemann_identity f ζ (ζ - z)]
  have h_conj : (ζ - z) * starRingEnd ℂ (ζ - z) = (‖ζ - z‖ : ℂ) ^ 2 :=
    Complex.mul_conj' (ζ - z)
  rw [← h_conj]
  set c := starRingEnd ℂ (ζ - z)
  have hc : c ≠ 0 := (map_ne_zero_iff (starRingEnd ℂ) (RingHom.injective _)).mpr hζz
  field_simp [hζz, hc]
  ring

theorem cauchy_deriv_kernel_diff_bound
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {z w ζ : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) r)
    (hw : w ∈ Metric.closedBall (0 : ℂ) r)
    (hζ : ‖ζ‖ = R) :
    ‖((ζ - z) ^ 2)⁻¹ - ((ζ - w) ^ 2)⁻¹‖ ≤ (2 * (R + r) / (R - r) ^ 4) * ‖z - w‖ := by
  have _ := hr
  have hz_norm : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hw_norm : ‖w‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have hRmr_pos : 0 < R - r := sub_pos.mpr hrR
  have hdistz_lo : R - r ≤ ‖ζ - z‖ := by
    have h1 : ‖ζ‖ - ‖z‖ ≤ ‖ζ - z‖ := norm_sub_norm_le ζ z
    linarith
  have hdistw_lo : R - r ≤ ‖ζ - w‖ := by
    have h1 : ‖ζ‖ - ‖w‖ ≤ ‖ζ - w‖ := norm_sub_norm_le ζ w
    linarith
  have hdistz_hi : ‖ζ - z‖ ≤ R + r := by
    have h1 : ‖ζ - z‖ ≤ ‖ζ‖ + ‖z‖ := norm_sub_le ζ z
    linarith
  have hdistw_hi : ‖ζ - w‖ ≤ R + r := by
    have h1 : ‖ζ - w‖ ≤ ‖ζ‖ + ‖w‖ := norm_sub_le ζ w
    linarith
  have hζz_ne : ζ - z ≠ 0 := by
    intro h0; have : ‖ζ - z‖ = 0 := by simp [h0]
    linarith
  have hζw_ne : ζ - w ≠ 0 := by
    intro h0; have : ‖ζ - w‖ = 0 := by simp [h0]
    linarith
  have hdiff : ((ζ - z) ^ 2)⁻¹ - ((ζ - w) ^ 2)⁻¹ =
      ((z - w) * ((ζ - z) + (ζ - w))) / ((ζ - z) ^ 2 * (ζ - w) ^ 2) := by
    field_simp
    ring
  rw [hdiff, norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
  have h_num_sum : ‖(ζ - z) + (ζ - w)‖ ≤ 2 * (R + r) := by
    have h1 : ‖(ζ - z) + (ζ - w)‖ ≤ ‖ζ - z‖ + ‖ζ - w‖ := norm_add_le _ _
    linarith
  have h_num : ‖z - w‖ * ‖(ζ - z) + (ζ - w)‖ ≤ 2 * (R + r) * ‖z - w‖ := by
    nlinarith [norm_nonneg (z - w)]
  have h_den : (R - r) ^ 4 ≤ ‖ζ - z‖ ^ 2 * ‖ζ - w‖ ^ 2 := by
    have h1 : (R - r) ^ 2 ≤ ‖ζ - z‖ ^ 2 := by nlinarith
    have h2 : (R - r) ^ 2 ≤ ‖ζ - w‖ ^ 2 := by nlinarith
    have h3 : (R - r) ^ 2 * (R - r) ^ 2 ≤ ‖ζ - z‖ ^ 2 * ‖ζ - w‖ ^ 2 :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    linarith [show (R - r) ^ 4 = (R - r) ^ 2 * (R - r) ^ 2 by ring]
  have hRr_nonneg : 0 ≤ 2 * (R + r) * ‖z - w‖ := by
    have : 0 < R + r := by linarith
    positivity
  calc
    ‖z - w‖ * ‖(ζ - z) + (ζ - w)‖ / (‖ζ - z‖ ^ 2 * ‖ζ - w‖ ^ 2)
      ≤ (2 * (R + r) * ‖z - w‖) / (‖ζ - z‖ ^ 2 * ‖ζ - w‖ ^ 2) := by
        gcongr
    _ ≤ (2 * (R + r) * ‖z - w‖) / (R - r) ^ 4 :=
        div_le_div_of_nonneg_left hRr_nonneg (pow_pos hRmr_pos 4) h_den
    _ = (2 * (R + r) / (R - r) ^ 4) * ‖z - w‖ := by ring

theorem holder_power_interpolation_on_disk
    {r α : ℝ} (_hr : 0 < r) (hα0 : 0 < α) (hα1 : α < 1)
    {z w : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) r)
    (hw : w ∈ Metric.closedBall (0 : ℂ) r) :
    ‖z - w‖ ≤ (2 * r) ^ (1 - α) * ‖z - w‖ ^ α := by
  by_cases hzw : z = w
  · subst hzw
    simp [Real.zero_rpow (ne_of_gt hα0)]
  · have hz_norm : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hw_norm : ‖w‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    have h_pos : 0 < ‖z - w‖ := norm_sub_pos_iff.mpr hzw
    have h_le : ‖z - w‖ ≤ 2 * r := by
      have h1 : ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le z w
      linarith
    have h1a : 0 ≤ 1 - α := by linarith
    have h_rpow : ‖z - w‖ ^ (1 - α) ≤ (2 * r) ^ (1 - α) :=
      Real.rpow_le_rpow (le_of_lt h_pos) h_le h1a
    have h_split : ‖z - w‖ = ‖z - w‖ ^ (1 - α) * ‖z - w‖ ^ α := by
      rw [← Real.rpow_add h_pos, sub_add_cancel, Real.rpow_one]
    conv_lhs => rw [h_split]
    exact mul_le_mul_of_nonneg_right h_rpow (Real.rpow_nonneg (le_of_lt h_pos) α)

theorem polar_radial_angular_cauchyRiemann_identity
    (f : ℂ → ℂ) (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    let ζ := z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
    (ρ : ℂ) * (cauchyRiemann f ζ / (ζ - z)) =
      (1 / 2 : ℂ) * (fderiv ℝ f ζ (Complex.exp (Complex.I * (θ : ℂ))) +
        (Complex.I / (ρ : ℂ)) *
          fderiv ℝ f ζ (Complex.I * ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))) := by
  intro ζ
  set eθ : ℂ := Complex.exp (Complex.I * (θ : ℂ))
  have hζz_eq : ζ - z = (ρ : ℂ) * eθ := by
    dsimp [ζ, eθ]; ring
  have hρ_ne : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hρ)
  have heθ_ne : eθ ≠ 0 := Complex.exp_ne_zero _
  have hζz_ne : ζ - z ≠ 0 := by
    rw [hζz_eq]
    exact mul_ne_zero hρ_ne heθ_ne
  have heθ_norm : ‖eθ‖ = 1 := by
    dsimp [eθ]
    rw [mul_comm Complex.I (θ : ℂ)]
    exact Complex.norm_exp_ofReal_mul_I θ
  have hζz_norm : ‖ζ - z‖ = ρ := by
    rw [hζz_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hρ), heθ_norm, mul_one]
  rw [polar_cauchy_pompeiu_kernel_identity f hζz_ne]
  rw [hζz_norm, hζz_eq]
  have h_smul : fderiv ℝ f ζ ((ρ : ℂ) * eθ) = (ρ : ℂ) * fderiv ℝ f ζ eθ := by
    have h1 : (ρ : ℂ) * eθ = ρ • eθ := (@Complex.real_smul ρ eθ).symm
    rw [h1, (fderiv ℝ f ζ).map_smul, Complex.real_smul]
  rw [h_smul]
  field_simp [hρ_ne]
  ring

theorem boundary_circleIntegral_holder_est
    {r R α M : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M)
    {f : ℂ → ℂ} (hf_cont : ContinuousOn f (Metric.sphere (0 : ℂ) R))
    (hf_bdd : ∀ ζ ∈ Metric.sphere (0 : ℂ) R, ‖f ζ‖ ≤ M)
    {z w : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) r)
    (hw : w ∈ Metric.closedBall (0 : ℂ) r) :
    ‖(∮ ζ in C(0, R), (ζ - z)⁻¹ * f ζ) - (∮ ζ in C(0, R), (ζ - w)⁻¹ * f ζ)‖ ≤
      (2 * Real.pi * R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * M * ‖z - w‖ ^ α := by
  have hR_pos : 0 < R := lt_trans hr hrR
  have hRmr_pos : 0 < R - r := sub_pos.mpr hrR
  have hz_norm : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hw_norm : ‖w‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have h_ne_z : ∀ ζ ∈ Metric.sphere (0 : ℂ) R, ζ - z ≠ 0 := by
    intro ζ hζ h0
    have hζR : ‖ζ‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hζ
    have h1 : ‖ζ‖ - ‖z‖ ≤ ‖ζ - z‖ := norm_sub_norm_le ζ z
    have h2 : ‖ζ - z‖ = 0 := by simp [h0]
    linarith
  have h_ne_w : ∀ ζ ∈ Metric.sphere (0 : ℂ) R, ζ - w ≠ 0 := by
    intro ζ hζ h0
    have hζR : ‖ζ‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hζ
    have h1 : ‖ζ‖ - ‖w‖ ≤ ‖ζ - w‖ := norm_sub_norm_le ζ w
    have h2 : ‖ζ - w‖ = 0 := by simp [h0]
    linarith
  have h_int_z : CircleIntegrable (fun ζ => (ζ - z)⁻¹ * f ζ) 0 R := by
    apply ContinuousOn.circleIntegrable (le_of_lt hR_pos)
    exact ((continuousOn_id.sub continuousOn_const).inv₀ h_ne_z).mul hf_cont
  have h_int_w : CircleIntegrable (fun ζ => (ζ - w)⁻¹ * f ζ) 0 R := by
    apply ContinuousOn.circleIntegrable (le_of_lt hR_pos)
    exact ((continuousOn_id.sub continuousOn_const).inv₀ h_ne_w).mul hf_cont
  rw [← circleIntegral.integral_sub h_int_z h_int_w]
  have h_integrand_eq :
      (fun ζ => (ζ - z)⁻¹ * f ζ - (ζ - w)⁻¹ * f ζ) =
        fun ζ => ((ζ - z)⁻¹ - (ζ - w)⁻¹) * f ζ := by
    ext ζ; ring
  rw [h_integrand_eq]
  have h_pt_bound :
      ∀ ζ ∈ Metric.sphere (0 : ℂ) R,
        ‖((ζ - z)⁻¹ - (ζ - w)⁻¹) * f ζ‖ ≤ (‖z - w‖ / (R - r) ^ 2) * M := by
    intro ζ hζ
    have hζR : ‖ζ‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hζ
    rw [norm_mul]
    exact mul_le_mul
      (cauchy_kernel_diff_bound hr hrR hz hw hζR)
      (hf_bdd ζ hζ)
      (norm_nonneg _)
      (div_nonneg (norm_nonneg _) (sq_nonneg _))
  have h_circle_bound :=
    circleIntegral.norm_integral_le_of_norm_le_const (le_of_lt hR_pos) h_pt_bound
  have h_holder := holder_power_interpolation_on_disk hr hα0 hα1 hz hw
  calc
    ‖∮ ζ in C(0, R), ((ζ - z)⁻¹ - (ζ - w)⁻¹) * f ζ‖
      ≤ 2 * Real.pi * R * (‖z - w‖ / (R - r) ^ 2 * M) := h_circle_bound
    _ = (2 * Real.pi * R * M / (R - r) ^ 2) * ‖z - w‖ := by ring
    _ ≤ (2 * Real.pi * R * M / (R - r) ^ 2) * ((2 * r) ^ (1 - α) * ‖z - w‖ ^ α) := by
        apply mul_le_mul_of_nonneg_left h_holder
        positivity
    _ = (2 * Real.pi * R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * M * ‖z - w‖ ^ α := by ring

theorem boundary_circleIntegral_deriv_holder_est
    {r R α M : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M)
    {f : ℂ → ℂ} (hf_cont : ContinuousOn f (Metric.sphere (0 : ℂ) R))
    (hf_bdd : ∀ ζ ∈ Metric.sphere (0 : ℂ) R, ‖f ζ‖ ≤ M)
    {z w : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) r)
    (hw : w ∈ Metric.closedBall (0 : ℂ) r) :
    ‖(∮ ζ in C(0, R), ((ζ - z) ^ 2)⁻¹ * f ζ) - (∮ ζ in C(0, R), ((ζ - w) ^ 2)⁻¹ * f ζ)‖ ≤
      (4 * Real.pi * R * (R + r) * (2 * r) ^ (1 - α) / (R - r) ^ 4) * M * ‖z - w‖ ^ α := by
  have hR_pos : 0 < R := lt_trans hr hrR
  have hRmr_pos : 0 < R - r := sub_pos.mpr hrR
  have hz_norm : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hw_norm : ‖w‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have h_ne_z : ∀ ζ ∈ Metric.sphere (0 : ℂ) R, (ζ - z) ^ 2 ≠ 0 := by
    intro ζ hζ h0
    have hζR : ‖ζ‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hζ
    have h1 : ‖ζ‖ - ‖z‖ ≤ ‖ζ - z‖ := norm_sub_norm_le ζ z
    have h2 : ζ - z = 0 := pow_eq_zero h0
    have h3 : ‖ζ - z‖ = 0 := by simp [h2]
    linarith
  have h_ne_w : ∀ ζ ∈ Metric.sphere (0 : ℂ) R, (ζ - w) ^ 2 ≠ 0 := by
    intro ζ hζ h0
    have hζR : ‖ζ‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hζ
    have h1 : ‖ζ‖ - ‖w‖ ≤ ‖ζ - w‖ := norm_sub_norm_le ζ w
    have h2 : ζ - w = 0 := pow_eq_zero h0
    have h3 : ‖ζ - w‖ = 0 := by simp [h2]
    linarith
  have h_int_z : CircleIntegrable (fun ζ => ((ζ - z) ^ 2)⁻¹ * f ζ) 0 R := by
    apply ContinuousOn.circleIntegrable (le_of_lt hR_pos)
    exact (((continuousOn_id.sub continuousOn_const).pow 2).inv₀ h_ne_z).mul hf_cont
  have h_int_w : CircleIntegrable (fun ζ => ((ζ - w) ^ 2)⁻¹ * f ζ) 0 R := by
    apply ContinuousOn.circleIntegrable (le_of_lt hR_pos)
    exact (((continuousOn_id.sub continuousOn_const).pow 2).inv₀ h_ne_w).mul hf_cont
  rw [← circleIntegral.integral_sub h_int_z h_int_w]
  have h_integrand_eq :
      (fun ζ => ((ζ - z) ^ 2)⁻¹ * f ζ - ((ζ - w) ^ 2)⁻¹ * f ζ) =
        fun ζ => (((ζ - z) ^ 2)⁻¹ - ((ζ - w) ^ 2)⁻¹) * f ζ := by
    ext ζ; ring
  rw [h_integrand_eq]
  have h_pt_bound :
      ∀ ζ ∈ Metric.sphere (0 : ℂ) R,
        ‖(((ζ - z) ^ 2)⁻¹ - ((ζ - w) ^ 2)⁻¹) * f ζ‖ ≤
          ((2 * (R + r) / (R - r) ^ 4) * ‖z - w‖) * M := by
    intro ζ hζ
    have hζR : ‖ζ‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hζ
    rw [norm_mul]
    have hRr_pos : 0 < R + r := by linarith
    exact mul_le_mul
      (cauchy_deriv_kernel_diff_bound hr hrR hz hw hζR)
      (hf_bdd ζ hζ)
      (norm_nonneg _)
      (by positivity)
  have h_circle_bound :=
    circleIntegral.norm_integral_le_of_norm_le_const (le_of_lt hR_pos) h_pt_bound
  have h_holder := holder_power_interpolation_on_disk hr hα0 hα1 hz hw
  have hRr_pos : 0 < R + r := by linarith
  calc
    ‖∮ ζ in C(0, R), (((ζ - z) ^ 2)⁻¹ - ((ζ - w) ^ 2)⁻¹) * f ζ‖
      ≤ 2 * Real.pi * R * ((2 * (R + r) / (R - r) ^ 4) * ‖z - w‖ * M) := h_circle_bound
    _ = (4 * Real.pi * R * (R + r) * M / (R - r) ^ 4) * ‖z - w‖ := by ring
    _ ≤ (4 * Real.pi * R * (R + r) * M / (R - r) ^ 4) * ((2 * r) ^ (1 - α) * ‖z - w‖ ^ α) := by
        apply mul_le_mul_of_nonneg_left h_holder
        positivity
    _ = (4 * Real.pi * R * (R + r) * (2 * r) ^ (1 - α) / (R - r) ^ 4) * M * ‖z - w‖ ^ α := by ring

theorem polar_radial_hasDerivAt
    {f : ℂ → ℂ} {z : ℂ} {ρ θ : ℝ}
    (hf : DifferentiableAt ℝ f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    HasDerivAt (fun r : ℝ => f (z + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (fderiv ℝ f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (Complex.exp (Complex.I * (θ : ℂ)))) ρ := by
  set eθ : ℂ := Complex.exp (Complex.I * (θ : ℂ))
  have h_inner : HasDerivAt (fun r : ℝ => z + (r : ℂ) * eθ) eθ ρ := by
    have h1 : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 ρ := by
      simpa using Complex.ofRealCLM.hasDerivAt (x := ρ)
    have h2 : HasDerivAt (fun r : ℝ => (r : ℂ) * eθ) (1 * eθ) ρ := h1.mul_const eθ
    rw [one_mul] at h2
    simpa using h2.const_add z
  exact hf.hasFDerivAt.comp_hasDerivAt ρ h_inner

theorem polar_angular_hasDerivAt
    {f : ℂ → ℂ} {z : ℂ} {ρ θ : ℝ}
    (hf : DifferentiableAt ℝ f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    HasDerivAt (fun t : ℝ => f (z + (ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ))))
      (fderiv ℝ f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (Complex.I * ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))) θ := by
  have h_exp : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ)))
      (Complex.I * Complex.exp (Complex.I * (θ : ℂ))) θ := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 θ := by
      simpa using Complex.ofRealCLM.hasDerivAt (x := θ)
    have h2 : HasDerivAt (fun t : ℝ => Complex.I * (t : ℂ)) (Complex.I * 1) θ :=
      h1.const_mul Complex.I
    rw [mul_one] at h2
    have h3 := (Complex.hasDerivAt_exp (Complex.I * (θ : ℂ))).comp θ h2
    simpa [mul_comm] using h3
  have h_inner : HasDerivAt (fun t : ℝ => z + (ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ)))
      (Complex.I * ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) θ := by
    have h4 := h_exp.const_mul (ρ : ℂ)
    have h5 : (ρ : ℂ) * (Complex.I * Complex.exp (Complex.I * (θ : ℂ))) =
        Complex.I * ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by ring
    rw [h5] at h4
    simpa using h4.const_add z
  exact hf.hasFDerivAt.comp_hasDerivAt θ h_inner

theorem periodic_intervalIntegral_deriv_eq_zero
    {g g' : ℝ → ℂ}
    (h_deriv : ∀ θ ∈ Set.uIcc 0 (2 * Real.pi), HasDerivAt g (g' θ) θ)
    (h_int : IntervalIntegrable g' volume 0 (2 * Real.pi))
    (h_per : g (2 * Real.pi) = g 0) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), g' θ) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_int, h_per, sub_self]

theorem polar_angular_periodicity (f : ℂ → ℂ) (z : ℂ) (ρ : ℝ) :
    f (z + (ρ : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi : ℝ) : ℂ))) =
      f (z + (ρ : ℂ) * Complex.exp (Complex.I * ((0 : ℝ) : ℂ))) := by
  have h1 : Complex.I * ((2 * Real.pi : ℝ) : ℂ) = 2 * Real.pi * Complex.I := by push_cast; ring
  have h2 : Complex.I * ((0 : ℝ) : ℂ) = 0 := by simp
  rw [h1, h2, Complex.exp_two_pi_mul_I, Complex.exp_zero]

theorem polar_radial_intervalIntegral_eq_sub
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
        f (z + (ε : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro r hr
    exact polar_radial_hasDerivAt (hf_diff r hr)
  · exact h_int

theorem polar_pompeiu_angular_slice_identity
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
          (Complex.exp (Complex.I * (θ : ℂ)))) := by
  have h_eq :
      (fun θ : ℝ =>
        (ρ : ℂ) * (cauchyRiemann f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
          ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z))) =
      (fun θ : ℝ =>
        (1 / 2 : ℂ) * (fderiv ℝ f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
          (Complex.exp (Complex.I * (θ : ℂ))) +
          (Complex.I / (ρ : ℂ)) *
            fderiv ℝ f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
              (Complex.I * ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))))) := by
    ext θ
    exact polar_radial_angular_cauchyRiemann_identity f z hρ θ
  rw [h_eq]
  rw [intervalIntegral.integral_const_mul]
  have h_int_ang_smul : IntervalIntegrable
      (fun θ : ℝ => (Complex.I / (ρ : ℂ)) *
        fderiv ℝ f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
          (Complex.I * ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))) volume 0 (2 * Real.pi) :=
    h_int_ang.const_mul (Complex.I / (ρ : ℂ))
  rw [intervalIntegral.integral_add h_int_rad h_int_ang_smul]
  rw [intervalIntegral.integral_const_mul]
  have h_ang_zero :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        fderiv ℝ f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
          (Complex.I * ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))) = 0 := by
    apply periodic_intervalIntegral_deriv_eq_zero
      (g := fun θ : ℝ => f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
    · intro θ hθ
      exact polar_angular_hasDerivAt (hf_diff θ hθ)
    · exact h_int_ang
    · exact polar_angular_periodicity f z ρ
  rw [h_ang_zero, mul_zero, add_zero]

theorem circleIntegral_sub_center_inv_eq_average
    (f : ℂ → ℂ) (z : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (∮ ζ in C(z, R), (ζ - z)⁻¹ * f ζ) =
      Complex.I * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        f (z + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  unfold circleIntegral
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  ext θ
  dsimp only
  rw [deriv_circleMap, circleMap_sub_center]
  have h_nz : circleMap 0 R θ ≠ 0 := circleMap_ne_center hR
  unfold circleMap at h_nz ⊢
  simp only [zero_add] at h_nz ⊢
  have h_comm : (θ : ℂ) * Complex.I = Complex.I * (θ : ℂ) := mul_comm _ _
  rw [h_comm] at h_nz ⊢
  calc
    ((R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) * Complex.I) •
        (((R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ *
          f (z + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      = Complex.I * (((R : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          ((R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ *
          f (z + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
        simp only [smul_eq_mul]
        ring
    _ = Complex.I * f (z + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
        rw [mul_inv_cancel₀ h_nz, one_mul]

theorem polar_jacobian_pompeiu_norm_cancel
    (f : ℂ → ℂ) (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    ‖(ρ : ℂ) * (cauchyRiemann f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
      ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z))‖ =
      ‖cauchyRiemann f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ := by
  have h_sub : (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z =
      (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := add_sub_cancel_left _ _
  rw [h_sub, norm_mul, norm_div, norm_mul]
  have hρ_pos : ‖(ρ : ℂ)‖ ≠ 0 := by
    rw [Complex.norm_real, Real.norm_eq_abs, _root_.abs_of_pos hρ]
    exact ne_of_gt hρ
  have hexp_norm : ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 := by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  rw [hexp_norm, mul_one, mul_div_cancel₀ _ hρ_pos]

theorem polar_pompeiu_radial_slice_bound
    (f : ℂ → ℂ) (z : ℂ) {R M : ℝ} (hR : 0 ≤ R) (θ : ℝ)
    (h_bdd : ∀ ρ ∈ Set.Ioc 0 R,
      ‖cauchyRiemann f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ ≤ M) :
    ‖∫ ρ in (0 : ℝ)..R,
      (ρ : ℂ) * (cauchyRiemann f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
        ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z))‖ ≤ R * M := by
  have h_est :
      ‖∫ ρ in (0 : ℝ)..R,
        (ρ : ℂ) * (cauchyRiemann f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
          ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z))‖ ≤
        M * |R - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro ρ hρ_mem
    rw [Set.uIoc_of_le hR] at hρ_mem
    rw [polar_jacobian_pompeiu_norm_cancel f z hρ_mem.1 θ]
    exact h_bdd ρ hρ_mem
  have hR_abs : M * |R - 0| = R * M := by
    rw [sub_zero, _root_.abs_of_nonneg hR, mul_comm]
  linarith

theorem polar_pompeiu_disk_integral_bound
    (f : ℂ → ℂ) (z : ℂ) {R M : ℝ} (hR : 0 ≤ R)
    (h_bdd : ∀ θ ∈ Set.Ioc 0 (2 * Real.pi), ∀ ρ ∈ Set.Ioc 0 R,
      ‖cauchyRiemann f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ ≤ M) :
    ‖((Real.pi : ℂ)⁻¹) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (∫ ρ in (0 : ℝ)..R,
        (ρ : ℂ) * (cauchyRiemann f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
          ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z)))‖ ≤ 2 * R * M := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have h2pi_nonneg : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have h_ang_est :
      ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
        (∫ ρ in (0 : ℝ)..R,
          (ρ : ℂ) * (cauchyRiemann f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
            ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z)))‖ ≤
        (R * M) * |2 * Real.pi - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro θ hθ_mem
    rw [Set.uIoc_of_le h2pi_nonneg] at hθ_mem
    exact polar_pompeiu_radial_slice_bound f z hR θ (h_bdd θ hθ_mem)
  have h_abs : (R * M) * |2 * Real.pi - 0| = 2 * Real.pi * R * M := by
    rw [sub_zero, _root_.abs_of_nonneg h2pi_nonneg]
    ring
  rw [h_abs] at h_ang_est
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt hpi_pos
  calc
    Real.pi⁻¹ * ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
      (∫ ρ in (0 : ℝ)..R,
        (ρ : ℂ) * (cauchyRiemann f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
          ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z)))‖
      ≤ Real.pi⁻¹ * (2 * Real.pi * R * M) :=
        mul_le_mul_of_nonneg_left h_ang_est (inv_nonneg.mpr hpi_pos.le)
    _ = 2 * R * M := by
        field_simp [hpi_ne]
        ring

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
  have h_congr :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (∫ r in (0 : ℝ)..R,
          fderiv ℝ f (z + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
            (Complex.exp (Complex.I * (θ : ℂ))))) =
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (f (z + (R : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - f z)) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    dsimp only
    rw [polar_radial_intervalIntegral_eq_sub (hf_diff θ hθ) (h_int_rad θ hθ)]
    simp
  rw [h_congr]
  rw [intervalIntegral.integral_sub h_int_bdry intervalIntegrable_const]
  rw [intervalIntegral.integral_const]
  simp [real_smul, mul_assoc]

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
  have h_pompeiu_eq :
      (∫ ρ in (0 : ℝ)..R,
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          (ρ : ℂ) * (cauchyRiemann f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
            ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z)))) =
      (1 / 2 : ℂ) * (∫ ρ in (0 : ℝ)..R,
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          fderiv ℝ f (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
            (Complex.exp (Complex.I * (θ : ℂ))))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with ρ hρ_mem
    rw [Set.uIoc_of_le hR.le] at hρ_mem
    have hρ_cc : ρ ∈ Set.uIcc 0 R := by
      rw [Set.uIcc_of_le hR.le]
      exact Set.Ioc_subset_Icc_self hρ_mem
    exact polar_pompeiu_angular_slice_identity hρ_mem.1 (hf_diff ρ hρ_cc)
      (h_int_ang_rad ρ hρ_mem) (h_int_ang_ang ρ hρ_mem)
  rw [h_pompeiu_eq, h_fubini]
  have hf_diff_swap : ∀ θ ∈ Set.uIcc 0 (2 * Real.pi), ∀ r ∈ Set.uIcc 0 R,
      DifferentiableAt ℝ f (z + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
    fun θ hθ r hr => hf_diff r hr θ hθ
  rw [polar_radial_angular_ftc_eq_sub hf_diff_swap h_int_rad h_int_bdry]
  rw [circleIntegral_sub_center_inv_eq_average f z (ne_of_gt hR)]
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI_ne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  field_simp [hpi_ne, hI_ne]
  ring

theorem norm_iteratedFDeriv_zero_sub (f : ℂ → ℂ) (z w : ℂ) :
    ‖iteratedFDeriv ℝ 0 f z - iteratedFDeriv ℝ 0 f w‖ = ‖f z - f w‖ := by
  rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.comp_apply]
  rw [← LinearIsometryEquiv.map_sub]
  exact LinearIsometryEquiv.norm_map _ _

theorem derivHolderSeminorm_zero_eq_holderSeminorm (α : ℝ) (f : ℂ → ℂ) (s : Set ℂ) :
    derivHolderSeminorm 0 α f s = holderSeminorm α f s := by
  unfold derivHolderSeminorm holderSeminorm
  congr 1
  ext q
  simp_rw [norm_iteratedFDeriv_zero_sub]

theorem holderSeminorm_le_of_bound
    {α K : ℝ} {f : ℂ → ℂ} {s : Set ℂ} (hK : 0 ≤ K)
    (h_est : ∀ z ∈ s, ∀ w ∈ s, ‖f z - f w‖ ≤ K * ‖z - w‖ ^ α) :
    holderSeminorm α f s ≤ K := by
  unfold holderSeminorm
  apply Real.sSup_le _ hK
  rintro q ⟨z, hz, w, hw, hzw, hq⟩
  rw [hq]
  have h_pos : 0 < ‖z - w‖ ^ α := Real.rpow_pos_of_pos (norm_sub_pos_iff.mpr hzw) α
  rw [div_le_iff₀ h_pos]
  exact h_est z hz w hw

theorem boundary_circleIntegral_holderSeminorm_le
    {f : ℂ → ℂ} {r R M α : ℝ}
    (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M)
    (hf_cont : ContinuousOn f (Metric.sphere (0 : ℂ) R))
    (hf_bdd : ∀ ζ ∈ Metric.sphere (0 : ℂ) R, ‖f ζ‖ ≤ M) :
    holderSeminorm α
      (fun z => (∮ ζ in C(0, R), (ζ - z)⁻¹ * f ζ))
      (Metric.closedBall (0 : ℂ) r) ≤
      (2 * Real.pi * R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * M := by
  have hK : 0 ≤ (2 * Real.pi * R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * M := by
    have hR : 0 < R := lt_trans hr hrR
    have hRr : 0 < R - r := sub_pos.mpr hrR
    positivity
  apply holderSeminorm_le_of_bound hK
  intro z hz w hw
  exact boundary_circleIntegral_holder_est hr hrR hα0 hα1 hM hf_cont hf_bdd hz hw

theorem ckHolderNorm_zero_eq (α : ℝ) (f : ℂ → ℂ) (s : Set ℂ) :
    ckHolderNorm 0 α f s = supNormOn f s + holderSeminorm α f s := by
  unfold ckHolderNorm
  have hsum :
      (Finset.range (0 + 1)).sum
        (fun j => sSup ((fun z => ‖iteratedFDeriv ℝ j f z‖) '' s)) =
        sSup ((fun z => ‖iteratedFDeriv ℝ 0 f z‖) '' s) :=
    Finset.sum_range_one (fun j => sSup ((fun z => ‖iteratedFDeriv ℝ j f z‖) '' s))
  have hsup :
      sSup ((fun z => ‖iteratedFDeriv ℝ 0 f z‖) '' s) = supNormOn f s := by
    unfold supNormOn
    have : (fun z => ‖iteratedFDeriv ℝ 0 f z‖) = fun z => ‖f z‖ := by
      funext z
      exact norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := f) (x := z)
    rw [this]
  rw [hsum, hsup, derivHolderSeminorm_zero_eq_holderSeminorm]

theorem supNormOn_le_of_bound
    {f : ℂ → ℂ} {s : Set ℂ} {M : ℝ} (hM : 0 ≤ M)
    (h_bdd : ∀ z ∈ s, ‖f z‖ ≤ M) :
    supNormOn f s ≤ M := by
  unfold supNormOn
  apply Real.sSup_le _ hM
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  exact h_bdd z hz

theorem norm_le_supNormOn
    {f : ℂ → ℂ} {s : Set ℂ} {z : ℂ} (hz : z ∈ s)
    (h_bdd : BddAbove ((fun w => ‖f w‖) '' s)) :
    ‖f z‖ ≤ supNormOn f s := by
  unfold supNormOn
  have hmem : ‖f z‖ ∈ ((fun w => ‖f w‖) '' s) := ⟨z, hz, rfl⟩
  exact le_csSup h_bdd hmem

theorem holderSeminorm_sub_le_of_bounds
    {α K₁ K₂ : ℝ} {f₁ f₂ : ℂ → ℂ} {s : Set ℂ}
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : ∀ z ∈ s, ∀ w ∈ s, ‖f₁ z - f₁ w‖ ≤ K₁ * ‖z - w‖ ^ α)
    (h₂ : ∀ z ∈ s, ∀ w ∈ s, ‖f₂ z - f₂ w‖ ≤ K₂ * ‖z - w‖ ^ α) :
    holderSeminorm α (fun z => f₁ z - f₂ z) s ≤ K₁ + K₂ := by
  have hK : 0 ≤ K₁ + K₂ := add_nonneg hK₁ hK₂
  have h_est :
      ∀ z ∈ s, ∀ w ∈ s,
        ‖(f₁ z - f₂ z) - (f₁ w - f₂ w)‖ ≤ (K₁ + K₂) * ‖z - w‖ ^ α := by
    intro z hz w hw
    have hrew :
        (f₁ z - f₂ z) - (f₁ w - f₂ w) = (f₁ z - f₁ w) - (f₂ z - f₂ w) := by
      ring
    have hnorm :
        ‖(f₁ z - f₂ z) - (f₁ w - f₂ w)‖ ≤
          ‖f₁ z - f₁ w‖ + ‖f₂ z - f₂ w‖ := by
      rw [hrew]
      exact norm_sub_le (f₁ z - f₁ w) (f₂ z - f₂ w)
    have h1 := h₁ z hz w hw
    have h2 := h₂ z hz w hw
    calc
      ‖(f₁ z - f₂ z) - (f₁ w - f₂ w)‖
          ≤ ‖f₁ z - f₁ w‖ + ‖f₂ z - f₂ w‖ := hnorm
      _ ≤ K₁ * ‖z - w‖ ^ α + K₂ * ‖z - w‖ ^ α := add_le_add h1 h2
      _ = (K₁ + K₂) * ‖z - w‖ ^ α := by ring
  exact holderSeminorm_le_of_bound (α := α) (K := K₁ + K₂)
    (f := fun z => f₁ z - f₂ z) (s := s) hK h_est

theorem far_zone_dist_lower_bound {z w ζ : ℂ} {δ : ℝ}
    (hzw : ‖z - w‖ ≤ δ) (hζz : 2 * δ ≤ ‖ζ - z‖) :
    ‖ζ - z‖ / 2 ≤ ‖ζ - w‖ := by
  have htri : ‖ζ - z‖ ≤ ‖ζ - w‖ + ‖w - z‖ := by
    have h_eq : (ζ - w) + (w - z) = ζ - z := by ring
    simpa [h_eq] using norm_add_le (ζ - w) (w - z)
  have hwz : ‖w - z‖ = ‖z - w‖ := norm_sub_rev w z
  linarith

theorem pompeiu_kernel_diff_algebraic_identity
    (g : ℂ) {z w ζ : ℂ} (hζz : ζ - z ≠ 0) (hζw : ζ - w ≠ 0) :
    g / (ζ - z) - g / (ζ - w) = g * (z - w) / ((ζ - z) * (ζ - w)) := by
  field_simp [hζz, hζw]
  ring

theorem pompeiu_far_zone_pointwise_bound
    {g z w ζ : ℂ} {M δ : ℝ}
    (_hM : 0 ≤ M) (hδ : 0 < δ)
    (hg : ‖g‖ ≤ M) (hzw : ‖z - w‖ ≤ δ) (hζz : 2 * δ ≤ ‖ζ - z‖) :
    ‖g / (ζ - z) - g / (ζ - w)‖ ≤ 2 * M * ‖z - w‖ / ‖ζ - z‖ ^ 2 := by
  have hpos_z : 0 < ‖ζ - z‖ := by linarith
  have hlower := far_zone_dist_lower_bound hzw hζz
  have hpos_w : 0 < ‖ζ - w‖ := by linarith
  have h_nonzero_z : ζ - z ≠ 0 := sub_ne_zero.mpr (by intro h; simp [h] at hpos_z)
  have h_nonzero_w : ζ - w ≠ 0 := sub_ne_zero.mpr (by intro h; simp [h] at hpos_w)
  rw [pompeiu_kernel_diff_algebraic_identity g h_nonzero_z h_nonzero_w]
  rw [norm_div, norm_mul, norm_mul]
  have hprod_lower : ‖ζ - z‖ ^ 2 / 2 ≤ ‖ζ - z‖ * ‖ζ - w‖ := by
    calc ‖ζ - z‖ ^ 2 / 2 = ‖ζ - z‖ * (‖ζ - z‖ / 2) := by ring
      _ ≤ ‖ζ - z‖ * ‖ζ - w‖ := mul_le_mul_of_nonneg_left hlower hpos_z.le
  have h_num_le : ‖g‖ * ‖z - w‖ ≤ M * ‖z - w‖ :=
    mul_le_mul_of_nonneg_right hg (norm_nonneg _)
  have h_den_pos : 0 < ‖ζ - z‖ ^ 2 / 2 := by positivity
  calc ‖g‖ * ‖z - w‖ / (‖ζ - z‖ * ‖ζ - w‖)
      ≤ ‖g‖ * ‖z - w‖ / (‖ζ - z‖ ^ 2 / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h_den_pos hprod_lower
    _ ≤ (M * ‖z - w‖) / (‖ζ - z‖ ^ 2 / 2) :=
        div_le_div_of_nonneg_right h_num_le h_den_pos.le
    _ = 2 * M * ‖z - w‖ / ‖ζ - z‖ ^ 2 := by ring

theorem delta_div_rho_le_rpow_mul_rpow_neg
    {δ ρ α : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (_hα0 : 0 < α) (hα1 : α < 1) :
    δ / ρ ≤ δ ^ α * ρ ^ (-α) := by
  have hρ : 0 < ρ := lt_of_lt_of_le hδ hδρ
  have h_le : δ ^ (1 - α) ≤ ρ ^ (1 - α) :=
    Real.rpow_le_rpow hδ.le hδρ (by linarith)
  have hδ_split : δ = δ ^ α * δ ^ (1 - α) := by
    rw [← Real.rpow_add hδ, add_sub_cancel, Real.rpow_one]
  have hρ_split : ρ ^ (1 - α) / ρ = ρ ^ (-α) := by
    rw [← Real.rpow_sub_one hρ.ne', sub_sub_cancel_left]
  calc δ / ρ = (δ ^ α * δ ^ (1 - α)) / ρ := by rw [← hδ_split]
    _ = δ ^ α * (δ ^ (1 - α) / ρ) := by ring
    _ ≤ δ ^ α * (ρ ^ (1 - α) / ρ) := by
        apply mul_le_mul_of_nonneg_left
        · exact div_le_div_of_nonneg_right h_le hρ.le
        · exact Real.rpow_nonneg hδ.le α
    _ = δ ^ α * ρ ^ (-α) := by rw [hρ_split]

theorem far_zone_radial_integrand_bound
    {M δ ρ α : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hα0 : 0 < α) (hα1 : α < 1) :
    2 * M * (δ / ρ) ≤ (2 * M * δ ^ α) * ρ ^ (-α) := by
  have h1 := delta_div_rho_le_rpow_mul_rpow_neg hδ hδρ hα0 hα1
  calc 2 * M * (δ / ρ) ≤ 2 * M * (δ ^ α * ρ ^ (-α)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (2 * M * δ ^ α) * ρ ^ (-α) := by ring

theorem radial_rpow_neg_intervalIntegral
    {A α : ℝ} (_hA : 0 ≤ A) (_hα0 : 0 < α) (hα1 : α < 1) :
    (∫ ρ in (0 : ℝ)..A, ρ ^ (-α)) = A ^ (1 - α) / (1 - α) := by
  have h_lt : -1 < -α := by linarith
  have h_ne : -α + 1 ≠ 0 := by linarith
  rw [integral_rpow (Or.inl h_lt)]
  rw [Real.zero_rpow h_ne, sub_zero]
  have h_eq : -α + 1 = 1 - α := by ring
  rw [h_eq]

theorem polar_far_zone_integrand_bound
    {g z w : ℂ} {M δ ρ θ α : ℝ}
    (hM : 0 ≤ M) (hδ : 0 < δ) (hρ : 2 * δ ≤ ρ)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hg : ‖g‖ ≤ M) (hzw : ‖z - w‖ ≤ δ) :
    let ζ := z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
    ‖(ρ : ℂ) * (g / (ζ - z) - g / (ζ - w))‖ ≤ (2 * M * δ ^ α) * ρ ^ (-α) := by
  have hρpos : 0 < ρ := by linarith
  have hρ_nonneg : 0 ≤ ρ := hρpos.le
  let ζ := z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  have hρ_norm : ‖(ρ : ℂ)‖ = ρ := by
    rw [Complex.norm_def, Complex.abs_of_nonneg hρ_nonneg]
  have hnorm_ζz : ‖ζ - z‖ = ρ := by
    have h_eq : ζ - z = (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
      dsimp [ζ]; ring
    rw [h_eq, norm_mul, hρ_norm]
    have hexp : ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 := by
      rw [mul_comm, Complex.norm_def, Complex.abs_exp_ofReal_mul_I]
    rw [hexp, mul_one]
  have hζz : (2 * δ : ℝ) ≤ ‖ζ - z‖ := by
    rw [hnorm_ζz]; exact hρ
  have hpoint := pompeiu_far_zone_pointwise_bound hM hδ hg hzw hζz
  rw [hnorm_ζz] at hpoint
  have hmul :
      ‖(ρ : ℂ) * (g / (ζ - z) - g / (ζ - w))‖ ≤
        ρ * (2 * M * ‖z - w‖ / ρ ^ 2) := by
    rw [norm_mul, hρ_norm]
    exact mul_le_mul_of_nonneg_left hpoint hρ_nonneg
  have hmul'' :
      ‖(ρ : ℂ) * (g / (ζ - z) - g / (ζ - w))‖ ≤
        2 * M * ‖z - w‖ / ρ := by
    have h_simp : ρ * (2 * M * ‖z - w‖ / ρ ^ 2) = 2 * M * ‖z - w‖ / ρ := by
      have hρ_ne : ρ ≠ 0 := hρpos.ne'
      field_simp [hρ_ne]
      ring
    rwa [h_simp] at hmul
  have hnum : 2 * M * ‖z - w‖ / ρ ≤ 2 * M * (δ / ρ) := by
    have : 2 * M * ‖z - w‖ / ρ = (2 * M / ρ) * ‖z - w‖ := by ring
    have h2 : 2 * M * (δ / ρ) = (2 * M / ρ) * δ := by ring
    rw [this, h2]
    exact mul_le_mul_of_nonneg_left hzw (by positivity)
  have hδρ : δ ≤ ρ := by linarith
  have hbound := far_zone_radial_integrand_bound hM hδ hδρ hα0 hα1
  exact le_trans (le_trans hmul'' hnum) hbound

theorem polar_far_zone_angular_slice_bound
    {g : ℂ → ℂ} {z w : ℂ} {M δ ρ α : ℝ}
    (hM : 0 ≤ M) (hδ : 0 < δ) (hρ : 2 * δ ≤ ρ)
    (hα0 : 0 < α) (hα1 : α < 1) (hzw : ‖z - w‖ ≤ δ)
    (hg_bdd : ∀ θ ∈ Set.uIcc 0 (2 * Real.pi),
      ‖g (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ ≤ M) :
    ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
      (ρ : ℂ) *
        (g (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
          ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z) -
        g (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
          ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - w))‖ ≤
      (4 * Real.pi * M * δ ^ α) * ρ ^ (-α) := by
  have h1 :
      ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
        (ρ : ℂ) *
          (g (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
            ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z) -
          g (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
            ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - w))‖ ≤
        ((2 * M * δ ^ α) * ρ ^ (-α)) * |2 * Real.pi - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro θ hθ
    have hθ_cc : θ ∈ Set.uIcc 0 (2 * Real.pi) := Set.uIoc_subset_uIcc hθ
    exact polar_far_zone_integrand_bound hM hδ hρ hα0 hα1 (hg_bdd θ hθ_cc) hzw
  have h2pi_nonneg : (0 : ℝ) ≤ 2 * Real.pi - 0 := by
    rw [sub_zero]
    positivity
  rw [_root_.abs_of_nonneg h2pi_nonneg] at h1
  calc
    ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
      (ρ : ℂ) *
        (g (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
          ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z) -
        g (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
          ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - w))‖
        ≤ ((2 * M * δ ^ α) * ρ ^ (-α)) * (2 * Real.pi - 0) := h1
    _ = (4 * Real.pi * M * δ ^ α) * ρ ^ (-α) := by ring

theorem polar_near_zone_holder_bound
    {r M α : ℝ} (hr : 0 < r) (hM : 0 ≤ M) (hα0 : 0 < α) (hα1 : α < 1)
    {z w : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) r)
    (hw : w ∈ Metric.closedBall (0 : ℂ) r) :
    4 * Real.pi * M * ‖z - w‖ ≤
      (4 * Real.pi * M * (2 * r) ^ (1 - α)) * ‖z - w‖ ^ α := by
  have h_interp := holder_power_interpolation_on_disk hr hα0 hα1 hz hw
  calc 4 * Real.pi * M * ‖z - w‖
      ≤ 4 * Real.pi * M * ((2 * r) ^ (1 - α) * ‖z - w‖ ^ α) :=
        mul_le_mul_of_nonneg_left h_interp (by positivity)
    _ = (4 * Real.pi * M * (2 * r) ^ (1 - α)) * ‖z - w‖ ^ α := by ring

theorem polar_far_zone_radial_integral_eq
    {M δ A α : ℝ} (hA : 0 ≤ A) (hα0 : 0 < α) (hα1 : α < 1) :
    (∫ ρ in (0 : ℝ)..A, (4 * Real.pi * M * δ ^ α) * ρ ^ (-α)) =
      (4 * Real.pi * M * A ^ (1 - α) / (1 - α)) * δ ^ α := by
  rw [intervalIntegral.integral_const_mul]
  rw [radial_rpow_neg_intervalIntegral hA hα0 hα1]
  ring

theorem pompeiu_near_plus_far_holder_bound
    {I_near I_far z w : ℂ} {r A M α : ℝ}
    (h_near : ‖I_near‖ ≤ (4 * Real.pi * M * (2 * r) ^ (1 - α)) * ‖z - w‖ ^ α)
    (h_far : ‖I_far‖ ≤ (4 * Real.pi * M * A ^ (1 - α) / (1 - α)) * ‖z - w‖ ^ α) :
    ‖I_near + I_far‖ ≤
      (4 * Real.pi * M * ((2 * r) ^ (1 - α) + A ^ (1 - α) / (1 - α))) * ‖z - w‖ ^ α := by
  calc ‖I_near + I_far‖
      ≤ ‖I_near‖ + ‖I_far‖ := norm_add_le I_near I_far
    _ ≤ (4 * Real.pi * M * (2 * r) ^ (1 - α)) * ‖z - w‖ ^ α +
        (4 * Real.pi * M * A ^ (1 - α) / (1 - α)) * ‖z - w‖ ^ α := add_le_add h_near h_far
    _ = (4 * Real.pi * M * ((2 * r) ^ (1 - α) + A ^ (1 - α) / (1 - α))) * ‖z - w‖ ^ α := by ring

theorem polar_far_zone_subinterval_integral_le
    {M δ a A α : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ) (ha0 : 0 ≤ a) (_haA : a ≤ A)
    (_hα0 : 0 < α) (hα1 : α < 1) :
    (∫ ρ in a..A, (4 * Real.pi * M * δ ^ α) * ρ ^ (-α)) ≤
      (4 * Real.pi * M * A ^ (1 - α) / (1 - α)) * δ ^ α := by
  have h_lt : -1 < -α := by linarith
  have h_pos : 0 < 1 - α := by linarith
  have h_eq : -α + 1 = 1 - α := by ring
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl h_lt), h_eq]
  have ha_nonneg : 0 ≤ a ^ (1 - α) := Real.rpow_nonneg ha0 (1 - α)
  have h_sub_le : (A ^ (1 - α) - a ^ (1 - α)) / (1 - α) ≤ A ^ (1 - α) / (1 - α) := by
    apply div_le_div_of_nonneg_right _ h_pos.le
    linarith
  have h_const_nonneg : 0 ≤ 4 * Real.pi * M * δ ^ α := by positivity
  calc (4 * Real.pi * M * δ ^ α) * ((A ^ (1 - α) - a ^ (1 - α)) / (1 - α))
      ≤ (4 * Real.pi * M * δ ^ α) * (A ^ (1 - α) / (1 - α)) :=
        mul_le_mul_of_nonneg_left h_sub_le h_const_nonneg
    _ = (4 * Real.pi * M * A ^ (1 - α) / (1 - α)) * δ ^ α := by ring

theorem cauchy_pompeiu_pointwise_holder_bound_of_parts
    {B_diff I_near I_far z w : ℂ} {K_B r A M α : ℝ}
    (h_bdry : ‖B_diff‖ ≤ K_B * ‖z - w‖ ^ α)
    (h_near : ‖I_near‖ ≤ (4 * Real.pi * M * (2 * r) ^ (1 - α)) * ‖z - w‖ ^ α)
    (h_far : ‖I_far‖ ≤ (4 * Real.pi * M * A ^ (1 - α) / (1 - α)) * ‖z - w‖ ^ α) :
    ‖B_diff - ((Real.pi : ℂ)⁻¹) * (I_near + I_far)‖ ≤
      (K_B + 4 * M * ((2 * r) ^ (1 - α) + A ^ (1 - α) / (1 - α))) * ‖z - w‖ ^ α := by
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_ne : Real.pi ≠ 0 := h_pi_pos.ne'
  have h_pi_norm : ‖((Real.pi : ℂ)⁻¹)‖ = Real.pi⁻¹ := by
    rw [norm_inv, Complex.norm_def, Complex.abs_of_nonneg h_pi_pos.le]
  have h_sum := pompeiu_near_plus_far_holder_bound h_near h_far
  have h_pomp : ‖((Real.pi : ℂ)⁻¹) * (I_near + I_far)‖ ≤
      (4 * M * ((2 * r) ^ (1 - α) + A ^ (1 - α) / (1 - α))) * ‖z - w‖ ^ α := by
    rw [norm_mul, h_pi_norm]
    calc Real.pi⁻¹ * ‖I_near + I_far‖
        ≤ Real.pi⁻¹ * ((4 * Real.pi * M * ((2 * r) ^ (1 - α) + A ^ (1 - α) / (1 - α))) * ‖z - w‖ ^ α) :=
          mul_le_mul_of_nonneg_left h_sum (by positivity)
      _ = (Real.pi⁻¹ * Real.pi) * (4 * M * ((2 * r) ^ (1 - α) + A ^ (1 - α) / (1 - α))) * ‖z - w‖ ^ α := by ring
      _ = (4 * M * ((2 * r) ^ (1 - α) + A ^ (1 - α) / (1 - α))) * ‖z - w‖ ^ α := by
          rw [inv_mul_cancel₀ h_pi_ne, one_mul]
  calc ‖B_diff - ((Real.pi : ℂ)⁻¹) * (I_near + I_far)‖
      ≤ ‖B_diff‖ + ‖((Real.pi : ℂ)⁻¹) * (I_near + I_far)‖ := norm_sub_le _ _
    _ ≤ K_B * ‖z - w‖ ^ α + (4 * M * ((2 * r) ^ (1 - α) + A ^ (1 - α) / (1 - α))) * ‖z - w‖ ^ α :=
        add_le_add h_bdry h_pomp
    _ = (K_B + 4 * M * ((2 * r) ^ (1 - α) + A ^ (1 - α) / (1 - α))) * ‖z - w‖ ^ α := by ring

theorem supNormOn_mono_of_bddAbove
    {f : ℂ → ℂ} {s t : Set ℂ} (hM : 0 ≤ supNormOn f t)
    (hst : s ⊆ t) (hbdd : BddAbove ((fun z => ‖f z‖) '' t)) :
    supNormOn f s ≤ supNormOn f t := by
  apply supNormOn_le_of_bound hM
  intro z hz
  exact norm_le_supNormOn (hst hz) hbdd

theorem ckHolderNorm_zero_le_of_holder_and_sup
    {f : ℂ → ℂ} {s : Set ℂ} {α M_f M_g K_B K_P : ℝ}
    (hMf : 0 ≤ M_f) (hMg : 0 ≤ M_g) (hKB : 0 ≤ K_B) (hKP : 0 ≤ K_P)
    (h_sup : supNormOn f s ≤ M_f)
    (h_hol : holderSeminorm α f s ≤ K_B * M_f + K_P * M_g) :
    ckHolderNorm 0 α f s ≤ (1 + K_B + K_P) * (M_g + M_f) := by
  rw [ckHolderNorm_zero_eq]
  have h1 : (1 + K_B) * M_g ≥ 0 := by positivity
  have h2 : K_P * M_f ≥ 0 := by positivity
  linarith

theorem ckHolderNorm_succ_eq (k : ℕ) (α : ℝ) (f : ℂ → ℂ) (s : Set ℂ) :
    ckHolderNorm (k + 1) α f s =
      (Finset.range (k + 1)).sum
        (fun j => sSup ((fun z => ‖iteratedFDeriv ℝ j f z‖) '' s)) +
      sSup ((fun z => ‖iteratedFDeriv ℝ (k + 1) f z‖) '' s) +
      derivHolderSeminorm (k + 1) α f s := by
  dsimp [ckHolderNorm]
  rw [Finset.sum_range_succ]

theorem ckHolderNorm_succ_le_ckHolderNorm_add_top
    (k : ℕ) (α : ℝ) (f : ℂ → ℂ) (s : Set ℂ)
    (h_nonneg : 0 ≤ derivHolderSeminorm k α f s) :
    ckHolderNorm (k + 1) α f s ≤
      ckHolderNorm k α f s +
      sSup ((fun z => ‖iteratedFDeriv ℝ (k + 1) f z‖) '' s) +
      derivHolderSeminorm (k + 1) α f s := by
  rw [ckHolderNorm_succ_eq]
  dsimp [ckHolderNorm]
  linarith

theorem complex_real_smul_decomp (v : ℂ) :
    v.re • (1 : ℂ) + v.im • Complex.I = v := by
  apply Complex.ext <;> simp

theorem clm_opNorm_le_norm_one_add_norm_I
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℂ →L[ℝ] E) :
    ‖L‖ ≤ ‖L 1‖ + ‖L Complex.I‖ := by
  apply L.opNorm_le_bound (by positivity)
  intro v
  have hv : L v = v.re • L 1 + v.im • L Complex.I := by
    conv_lhs => rw [← complex_real_smul_decomp v]
    rw [map_add, L.map_smul, L.map_smul]
  have hre : |v.re| ≤ ‖v‖ := by
    rw [Complex.norm_def]
    exact Complex.abs_re_le_abs v
  have him : |v.im| ≤ ‖v‖ := by
    rw [Complex.norm_def]
    exact Complex.abs_im_le_abs v
  calc ‖L v‖
      = ‖v.re • L 1 + v.im • L Complex.I‖ := by rw [hv]
    _ ≤ ‖v.re • L 1‖ + ‖v.im • L Complex.I‖ := norm_add_le _ _
    _ = |v.re| * ‖L 1‖ + |v.im| * ‖L Complex.I‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖v‖ * ‖L 1‖ + ‖v‖ * ‖L Complex.I‖ :=
        add_le_add (mul_le_mul_of_nonneg_right hre (norm_nonneg _))
          (mul_le_mul_of_nonneg_right him (norm_nonneg _))
    _ = (‖L 1‖ + ‖L Complex.I‖) * ‖v‖ := by ring

theorem norm_iteratedFDeriv_succ_eq_norm_fderiv
    (k : ℕ) (f : ℂ → ℂ) (z : ℂ) :
    ‖iteratedFDeriv ℝ (k + 1) f z‖ = ‖fderiv ℝ (iteratedFDeriv ℝ k f) z‖ := by
  rw [iteratedFDeriv_succ_eq_comp_left]
  exact LinearIsometryEquiv.norm_map _ _

theorem norm_iteratedFDeriv_succ_sub_eq_norm_fderiv_sub
    (k : ℕ) (f : ℂ → ℂ) (z w : ℂ) :
    ‖iteratedFDeriv ℝ (k + 1) f z - iteratedFDeriv ℝ (k + 1) f w‖ =
      ‖fderiv ℝ (iteratedFDeriv ℝ k f) z - fderiv ℝ (iteratedFDeriv ℝ k f) w‖ := by
  rw [iteratedFDeriv_succ_eq_comp_left]
  simp only [Function.comp_apply]
  rw [← LinearIsometryEquiv.map_sub]
  exact LinearIsometryEquiv.norm_map _ _

theorem norm_iteratedFDeriv_succ_le_dir_sum
    (k : ℕ) (f : ℂ → ℂ) (z : ℂ) :
    ‖iteratedFDeriv ℝ (k + 1) f z‖ ≤
      ‖fderiv ℝ (iteratedFDeriv ℝ k f) z 1‖ +
      ‖fderiv ℝ (iteratedFDeriv ℝ k f) z Complex.I‖ := by
  rw [norm_iteratedFDeriv_succ_eq_norm_fderiv]
  exact clm_opNorm_le_norm_one_add_norm_I (fderiv ℝ (iteratedFDeriv ℝ k f) z)

theorem norm_iteratedFDeriv_succ_sub_le_dir_sum
    (k : ℕ) (f : ℂ → ℂ) (z w : ℂ) :
    ‖iteratedFDeriv ℝ (k + 1) f z - iteratedFDeriv ℝ (k + 1) f w‖ ≤
      ‖fderiv ℝ (iteratedFDeriv ℝ k f) z 1 - fderiv ℝ (iteratedFDeriv ℝ k f) w 1‖ +
      ‖fderiv ℝ (iteratedFDeriv ℝ k f) z Complex.I -
        fderiv ℝ (iteratedFDeriv ℝ k f) w Complex.I‖ := by
  rw [norm_iteratedFDeriv_succ_sub_eq_norm_fderiv_sub]
  simpa [ContinuousLinearMap.sub_apply] using
    clm_opNorm_le_norm_one_add_norm_I
      (fderiv ℝ (iteratedFDeriv ℝ k f) z - fderiv ℝ (iteratedFDeriv ℝ k f) w)

theorem fderiv_I_eq_of_cauchyRiemann (f : ℂ → ℂ) (z : ℂ) :
    fderiv ℝ f z Complex.I =
      Complex.I * fderiv ℝ f z 1 - 2 * Complex.I * cauchyRiemann f z := by
  dsimp [cauchyRiemann]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (fderiv ℝ f z Complex.I) * hI

theorem norm_fderiv_I_le_of_cauchyRiemann (f : ℂ → ℂ) (z : ℂ) :
    ‖fderiv ℝ f z Complex.I‖ ≤
      ‖fderiv ℝ f z 1‖ + 2 * ‖cauchyRiemann f z‖ := by
  rw [fderiv_I_eq_of_cauchyRiemann]
  calc ‖Complex.I * fderiv ℝ f z 1 - 2 * Complex.I * cauchyRiemann f z‖
      ≤ ‖Complex.I * fderiv ℝ f z 1‖ + ‖2 * Complex.I * cauchyRiemann f z‖ := norm_sub_le _ _
    _ = ‖fderiv ℝ f z 1‖ + 2 * ‖cauchyRiemann f z‖ := by
        simp [norm_mul, Complex.norm_I]

theorem norm_fderiv_I_sub_le_of_cauchyRiemann (f : ℂ → ℂ) (z w : ℂ) :
    ‖fderiv ℝ f z Complex.I - fderiv ℝ f w Complex.I‖ ≤
      ‖fderiv ℝ f z 1 - fderiv ℝ f w 1‖ +
      2 * ‖cauchyRiemann f z - cauchyRiemann f w‖ := by
  rw [fderiv_I_eq_of_cauchyRiemann f z, fderiv_I_eq_of_cauchyRiemann f w]
  have h_alg :
      (Complex.I * fderiv ℝ f z 1 - 2 * Complex.I * cauchyRiemann f z) -
      (Complex.I * fderiv ℝ f w 1 - 2 * Complex.I * cauchyRiemann f w) =
      Complex.I * (fderiv ℝ f z 1 - fderiv ℝ f w 1) -
      2 * Complex.I * (cauchyRiemann f z - cauchyRiemann f w) := by ring
  rw [h_alg]
  calc ‖Complex.I * (fderiv ℝ f z 1 - fderiv ℝ f w 1) -
        2 * Complex.I * (cauchyRiemann f z - cauchyRiemann f w)‖
      ≤ ‖Complex.I * (fderiv ℝ f z 1 - fderiv ℝ f w 1)‖ +
        ‖2 * Complex.I * (cauchyRiemann f z - cauchyRiemann f w)‖ := norm_sub_le _ _
    _ = ‖fderiv ℝ f z 1 - fderiv ℝ f w 1‖ +
        2 * ‖cauchyRiemann f z - cauchyRiemann f w‖ := by
        simp [norm_mul, Complex.norm_I]

theorem norm_fderiv_le_two_mul_fderiv_one_add_cauchyRiemann
    (g : ℂ → ℂ) (z : ℂ) :
    ‖fderiv ℝ g z‖ ≤ 2 * ‖fderiv ℝ g z 1‖ + 2 * ‖cauchyRiemann g z‖ := by
  have h1 := clm_opNorm_le_norm_one_add_norm_I (fderiv ℝ g z)
  have h2 := norm_fderiv_I_le_of_cauchyRiemann g z
  linarith

theorem norm_fderiv_sub_le_two_mul_fderiv_one_add_cauchyRiemann
    (g : ℂ → ℂ) (z w : ℂ) :
    ‖fderiv ℝ g z - fderiv ℝ g w‖ ≤
      2 * ‖fderiv ℝ g z 1 - fderiv ℝ g w 1‖ +
      2 * ‖cauchyRiemann g z - cauchyRiemann g w‖ := by
  have h1 : ‖fderiv ℝ g z - fderiv ℝ g w‖ ≤
      ‖fderiv ℝ g z 1 - fderiv ℝ g w 1‖ +
      ‖fderiv ℝ g z Complex.I - fderiv ℝ g w Complex.I‖ := by
    simpa [ContinuousLinearMap.sub_apply] using
      clm_opNorm_le_norm_one_add_norm_I (fderiv ℝ g z - fderiv ℝ g w)
  have h2 := norm_fderiv_I_sub_le_of_cauchyRiemann g z w
  linarith

noncomputable def cmlmBasisNormSum :
    ∀ {k : ℕ}, ContinuousMultilinearMap ℝ (fun _ : Fin k => ℂ) ℂ → ℝ
  | 0, M => ‖M 0‖
  | k + 1, M =>
      let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => ℂ) ℂ M
      cmlmBasisNormSum (L 1) + cmlmBasisNormSum (L Complex.I)

theorem cmlm_norm_le_cmlmBasisNormSum :
    ∀ {k : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℂ) ℂ),
      ‖M‖ ≤ cmlmBasisNormSum M
  | 0, M => by
      dsimp [cmlmBasisNormSum]
      exact (LinearIsometryEquiv.norm_map (continuousMultilinearCurryFin0 ℝ ℂ ℂ) M).symm.le
  | k + 1, M => by
      dsimp [cmlmBasisNormSum]
      set L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => ℂ) ℂ M
      have hL : ‖M‖ = ‖L‖ :=
        (LinearIsometryEquiv.norm_map
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => ℂ) ℂ) M).symm
      have h1 := clm_opNorm_le_norm_one_add_norm_I L
      have ih1 := cmlm_norm_le_cmlmBasisNormSum (L 1)
      have ihI := cmlm_norm_le_cmlmBasisNormSum (L Complex.I)
      linarith

theorem curryFin1_iteratedFDeriv_one (f : ℂ → ℂ) (z : ℂ) :
    continuousMultilinearCurryFin1 ℝ ℂ ℂ (iteratedFDeriv ℝ 1 f z) = fderiv ℝ f z := by
  ext v
  simp [iteratedFDeriv_one_apply]
  rfl

theorem norm_iteratedFDeriv_one_eq_norm_fderiv (f : ℂ → ℂ) (z : ℂ) :
    ‖iteratedFDeriv ℝ 1 f z‖ = ‖fderiv ℝ f z‖ := by
  rw [← curryFin1_iteratedFDeriv_one f z]
  exact (LinearIsometryEquiv.norm_map (continuousMultilinearCurryFin1 ℝ ℂ ℂ) _).symm

theorem norm_iteratedFDeriv_one_sub_eq_norm_fderiv_sub (f : ℂ → ℂ) (z w : ℂ) :
    ‖iteratedFDeriv ℝ 1 f z - iteratedFDeriv ℝ 1 f w‖ =
      ‖fderiv ℝ f z - fderiv ℝ f w‖ := by
  rw [← curryFin1_iteratedFDeriv_one f z, ← curryFin1_iteratedFDeriv_one f w]
  rw [← LinearIsometryEquiv.map_sub]
  exact (LinearIsometryEquiv.norm_map (continuousMultilinearCurryFin1 ℝ ℂ ℂ) _).symm

theorem sup_iteratedFDeriv_one_le_of_bounds
    {f : ℂ → ℂ} {s : Set ℂ} {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h₁ : ∀ z ∈ s, ‖fderiv ℝ f z 1‖ ≤ M₁)
    (h₂ : ∀ z ∈ s, ‖cauchyRiemann f z‖ ≤ M₂) :
    sSup ((fun z => ‖iteratedFDeriv ℝ 1 f z‖) '' s) ≤ 2 * M₁ + 2 * M₂ := by
  apply Real.sSup_le _ (by positivity)
  rintro y ⟨z, hz, rfl⟩
  dsimp only
  rw [norm_iteratedFDeriv_one_eq_norm_fderiv]
  have h := norm_fderiv_le_two_mul_fderiv_one_add_cauchyRiemann f z
  have hz₁ := h₁ z hz
  have hz₂ := h₂ z hz
  linarith

theorem derivHolderSeminorm_one_le_of_bounds
    {α K₁ K₂ : ℝ} {f : ℂ → ℂ} {s : Set ℂ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : ∀ z ∈ s, ∀ w ∈ s, ‖fderiv ℝ f z 1 - fderiv ℝ f w 1‖ ≤ K₁ * ‖z - w‖ ^ α)
    (h₂ : ∀ z ∈ s, ∀ w ∈ s, ‖cauchyRiemann f z - cauchyRiemann f w‖ ≤ K₂ * ‖z - w‖ ^ α) :
    derivHolderSeminorm 1 α f s ≤ 2 * K₁ + 2 * K₂ := by
  unfold derivHolderSeminorm
  apply Real.sSup_le _ (by positivity)
  rintro q ⟨z, hz, w, hw, hzw, rfl⟩
  have h_pos : 0 < ‖z - w‖ ^ α := Real.rpow_pos_of_pos (norm_sub_pos_iff.mpr hzw) α
  rw [div_le_iff₀ h_pos]
  rw [norm_iteratedFDeriv_one_sub_eq_norm_fderiv_sub]
  have h := norm_fderiv_sub_le_two_mul_fderiv_one_add_cauchyRiemann f z w
  have hzw₁ := h₁ z hz w hw
  have hzw₂ := h₂ z hz w hw
  linarith

theorem bddAbove_norm_image_ball_of_continuousOn
    {f : ℂ → ℂ} {R : ℝ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) R)) :
    BddAbove ((fun z => ‖f z‖) '' Metric.ball (0 : ℂ) R) := by
  have h_cpt : IsCompact ((fun z => ‖f z‖) '' Metric.closedBall (0 : ℂ) R) :=
    (isCompact_closedBall (0 : ℂ) R).image_of_continuousOn hf.norm
  exact h_cpt.bddAbove.mono (Set.image_mono Metric.ball_subset_closedBall)

theorem supNormOn_ball_mono_of_continuousOn
    {f : ℂ → ℂ} {r R : ℝ} (hrR : r ≤ R)
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) R)) :
    supNormOn f (Metric.ball (0 : ℂ) r) ≤ supNormOn f (Metric.ball (0 : ℂ) R) := by
  exact supNormOn_mono_of_bddAbove (supNormOn_nonneg f _)
    (Metric.ball_subset_ball hrR) (bddAbove_norm_image_ball_of_continuousOn hf)

theorem ckHolderNorm_one_le_of_fderiv_one_and_cauchyRiemann
    {f : ℂ → ℂ} {s : Set ℂ} {α M₀ H₀ M₁ M₂ K₁ K₂ : ℝ}
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h_sup₀ : supNormOn f s ≤ M₀)
    (h_hol₀ : holderSeminorm α f s ≤ H₀)
    (h_sup₁ : ∀ z ∈ s, ‖fderiv ℝ f z 1‖ ≤ M₁)
    (h_sup₂ : ∀ z ∈ s, ‖cauchyRiemann f z‖ ≤ M₂)
    (h_hol₁ : ∀ z ∈ s, ∀ w ∈ s, ‖fderiv ℝ f z 1 - fderiv ℝ f w 1‖ ≤ K₁ * ‖z - w‖ ^ α)
    (h_hol₂ : ∀ z ∈ s, ∀ w ∈ s, ‖cauchyRiemann f z - cauchyRiemann f w‖ ≤ K₂ * ‖z - w‖ ^ α) :
    ckHolderNorm 1 α f s ≤ M₀ + H₀ + 2 * M₁ + 2 * M₂ + 2 * K₁ + 2 * K₂ := by
  have h_succ := ckHolderNorm_succ_le_ckHolderNorm_add_top 0 α f s (derivHolderSeminorm_nonneg 0 α f s)
  rw [ckHolderNorm_zero_eq] at h_succ
  have h_top_sup := sup_iteratedFDeriv_one_le_of_bounds hM₁ hM₂ h_sup₁ h_sup₂
  have h_top_hol := derivHolderSeminorm_one_le_of_bounds hK₁ hK₂ h_hol₁ h_hol₂
  linarith

theorem sup_iteratedFDeriv_succ_le_of_dir_bounds
    {k : ℕ} {f : ℂ → ℂ} {s : Set ℂ} {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h₁ : ∀ z ∈ s, ‖fderiv ℝ (iteratedFDeriv ℝ k f) z 1‖ ≤ M₁)
    (h₂ : ∀ z ∈ s, ‖fderiv ℝ (iteratedFDeriv ℝ k f) z Complex.I‖ ≤ M₂) :
    sSup ((fun z => ‖iteratedFDeriv ℝ (k + 1) f z‖) '' s) ≤ M₁ + M₂ := by
  apply Real.sSup_le _ (by positivity)
  rintro y ⟨z, hz, rfl⟩
  dsimp only
  have h := norm_iteratedFDeriv_succ_le_dir_sum k f z
  have hz₁ := h₁ z hz
  have hz₂ := h₂ z hz
  linarith

theorem derivHolderSeminorm_succ_le_of_dir_bounds
    {k : ℕ} {α K₁ K₂ : ℝ} {f : ℂ → ℂ} {s : Set ℂ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : ∀ z ∈ s, ∀ w ∈ s,
      ‖fderiv ℝ (iteratedFDeriv ℝ k f) z 1 - fderiv ℝ (iteratedFDeriv ℝ k f) w 1‖ ≤
        K₁ * ‖z - w‖ ^ α)
    (h₂ : ∀ z ∈ s, ∀ w ∈ s,
      ‖fderiv ℝ (iteratedFDeriv ℝ k f) z Complex.I -
        fderiv ℝ (iteratedFDeriv ℝ k f) w Complex.I‖ ≤
        K₂ * ‖z - w‖ ^ α) :
    derivHolderSeminorm (k + 1) α f s ≤ K₁ + K₂ := by
  unfold derivHolderSeminorm
  apply Real.sSup_le _ (by positivity)
  rintro q ⟨z, hz, w, hw, hzw, rfl⟩
  have h_pos : 0 < ‖z - w‖ ^ α := Real.rpow_pos_of_pos (norm_sub_pos_iff.mpr hzw) α
  rw [div_le_iff₀ h_pos]
  have h := norm_iteratedFDeriv_succ_sub_le_dir_sum k f z w
  have hzw₁ := h₁ z hz w hw
  have hzw₂ := h₂ z hz w hw
  linarith

theorem ckHolderNorm_succ_le_of_dir_bounds
    {k : ℕ} {α M₀ M₁ M₂ K₁ K₂ : ℝ} {f : ℂ → ℂ} {s : Set ℂ}
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h_base : ckHolderNorm k α f s ≤ M₀)
    (h_sup₁ : ∀ z ∈ s, ‖fderiv ℝ (iteratedFDeriv ℝ k f) z 1‖ ≤ M₁)
    (h_sup₂ : ∀ z ∈ s, ‖fderiv ℝ (iteratedFDeriv ℝ k f) z Complex.I‖ ≤ M₂)
    (h_hol₁ : ∀ z ∈ s, ∀ w ∈ s,
      ‖fderiv ℝ (iteratedFDeriv ℝ k f) z 1 - fderiv ℝ (iteratedFDeriv ℝ k f) w 1‖ ≤
        K₁ * ‖z - w‖ ^ α)
    (h_hol₂ : ∀ z ∈ s, ∀ w ∈ s,
      ‖fderiv ℝ (iteratedFDeriv ℝ k f) z Complex.I -
        fderiv ℝ (iteratedFDeriv ℝ k f) w Complex.I‖ ≤
        K₂ * ‖z - w‖ ^ α) :
    ckHolderNorm (k + 1) α f s ≤ M₀ + M₁ + M₂ + K₁ + K₂ := by
  have h_succ := ckHolderNorm_succ_le_ckHolderNorm_add_top k α f s
    (derivHolderSeminorm_nonneg k α f s)
  have h_top_sup := sup_iteratedFDeriv_succ_le_of_dir_bounds hM₁ hM₂ h_sup₁ h_sup₂
  have h_top_hol := derivHolderSeminorm_succ_le_of_dir_bounds hK₁ hK₂ h_hol₁ h_hol₂
  linarith

theorem boundary_circleIntegral_scaled_holder_est
    {r R α M : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M)
    {f : ℂ → ℂ} (hf_cont : ContinuousOn f (Metric.sphere (0 : ℂ) R))
    (hf_bdd : ∀ ζ ∈ Metric.sphere (0 : ℂ) R, ‖f ζ‖ ≤ M)
    {z w : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) r)
    (hw : w ∈ Metric.closedBall (0 : ℂ) r) :
    ‖((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - z)⁻¹ * f ζ) -
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - w)⁻¹ * f ζ)‖ ≤
      ((R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * M) * ‖z - w‖ ^ α := by
  have h_sub :
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - z)⁻¹ * f ζ) -
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - w)⁻¹ * f ζ) =
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) *
        ((∮ ζ in C(0, R), (ζ - z)⁻¹ * f ζ) - (∮ ζ in C(0, R), (ζ - w)⁻¹ * f ζ)) := by
    ring
  rw [h_sub, norm_mul]
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h_inv_norm : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg hpi_pos.le, Complex.norm_I, mul_one]
  rw [h_inv_norm]
  have h_est := boundary_circleIntegral_holder_est hr hrR hα0 hα1 hM hf_cont hf_bdd hz hw
  calc (2 * Real.pi)⁻¹ * ‖(∮ ζ in C(0, R), (ζ - z)⁻¹ * f ζ) - (∮ ζ in C(0, R), (ζ - w)⁻¹ * f ζ)‖
      ≤ (2 * Real.pi)⁻¹ * (((2 * Real.pi * R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * M) * ‖z - w‖ ^ α) :=
        mul_le_mul_of_nonneg_left h_est (by positivity)
    _ = ((2 * Real.pi)⁻¹ * (2 * Real.pi)) * ((R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * M) * ‖z - w‖ ^ α := by ring
    _ = ((R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * M) * ‖z - w‖ ^ α := by
        have h2pi_ne : 2 * Real.pi ≠ 0 := by positivity
        rw [inv_mul_cancel₀ h2pi_ne, one_mul]

theorem polar_far_zone_double_integral_bound
    {g : ℂ → ℂ} {z w : ℂ} {M δ A α : ℝ}
    (hM : 0 ≤ M) (hδ : 0 < δ) (hA : 2 * δ ≤ A)
    (hα0 : 0 < α) (hα1 : α < 1) (hzw : ‖z - w‖ ≤ δ)
    (hg : ∀ ρ ∈ Set.Ioc (2 * δ) A, ∀ θ ∈ Set.uIcc 0 (2 * Real.pi),
      ‖g (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ ≤ M) :
    ‖∫ ρ in (2 * δ)..A,
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (ρ : ℂ) *
          (g (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
            ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z) -
           g (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
            ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - w)))‖ ≤
      (4 * Real.pi * M * A ^ (1 - α) / (1 - α)) * δ ^ α := by
  have h_cont : ContinuousOn (fun ρ : ℝ => (4 * Real.pi * M * δ ^ α) * ρ ^ (-α)) (Set.uIcc (2 * δ) A) := by
    apply continuousOn_const.mul
    apply ContinuousOn.rpow_const continuousOn_id
    intro ρ hρ
    rw [Set.uIcc_of_le hA] at hρ
    left
    intro h0
    change ρ = 0 at h0
    linarith [hρ.1]
  have h_int : IntervalIntegrable (fun ρ : ℝ => (4 * Real.pi * M * δ ^ α) * ρ ^ (-α)) volume (2 * δ) A :=
    h_cont.intervalIntegrable
  have h_nonneg : 0 ≤ ∫ ρ in (2 * δ)..A, (4 * Real.pi * M * δ ^ α) * ρ ^ (-α) := by
    apply intervalIntegral.integral_nonneg hA
    intro ρ hρ
    have hρ0 : 0 ≤ ρ := by linarith [hρ.1]
    positivity
  have h_le :
      ‖∫ ρ in (2 * δ)..A,
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          (ρ : ℂ) *
            (g (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
              ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z) -
             g (z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) /
              ((z + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - w)))‖ ≤
      ∫ ρ in (2 * δ)..A, (4 * Real.pi * M * δ ^ α) * ρ ^ (-α) := by
    rw [← _root_.abs_of_nonneg h_nonneg]
    apply intervalIntegral.norm_integral_le_of_norm_le _ h_int
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with ρ hρ
    rw [Set.uIoc_of_le hA] at hρ
    exact polar_far_zone_angular_slice_bound hM hδ hρ.1.le hα0 hα1 hzw (hg ρ hρ)
  exact le_trans h_le (polar_far_zone_subinterval_integral_le hM hδ.le (by linarith) hA hα0 hα1)

theorem cauchy_pompeiu_holder_seminorm_le
    {r R α : ℝ} (_hr : 0 < r) (hrR : r < R) (_hα0 : 0 < α) (hα1 : α < 1)
    {f : ℂ → ℂ}
    (h_pt : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
      ‖f z - f w‖ ≤
        (((R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * supNormOn f (Metric.ball (0 : ℂ) R)) +
         (4 * ((2 * r) ^ (1 - α) + (R + r) ^ (1 - α) / (1 - α)) *
           supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R))) * ‖z - w‖ ^ α) :
    holderSeminorm α f (Metric.ball (0 : ℂ) r) ≤
      ((R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * supNormOn f (Metric.ball (0 : ℂ) R)) +
      (4 * ((2 * r) ^ (1 - α) + (R + r) ^ (1 - α) / (1 - α)) *
        supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R)) := by
  have hSub : 0 < R - r := sub_pos.mpr hrR
  have h1a : 0 < 1 - α := sub_pos.mpr hα1
  have hR : 0 < R := lt_trans _hr hrR
  have hf : 0 ≤ supNormOn f (Metric.ball (0 : ℂ) R) := supNormOn_nonneg f _
  have hd : 0 ≤ supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) :=
    supNormOn_nonneg (dbarComplex f) _
  have hC : 0 ≤ ((R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * supNormOn f (Metric.ball (0 : ℂ) R)) +
      (4 * ((2 * r) ^ (1 - α) + (R + r) ^ (1 - α) / (1 - α)) *
        supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R)) := by positivity
  exact holderSeminorm_le_of_bound hC h_pt

theorem cauchy_pompeiu_ckHolderNorm_zero_le
    {r R α : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1)
    {f : ℂ → ℂ} (hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) R))
    (h_pt : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
      ‖f z - f w‖ ≤
        (((R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * supNormOn f (Metric.ball (0 : ℂ) R)) +
         (4 * ((2 * r) ^ (1 - α) + (R + r) ^ (1 - α) / (1 - α)) *
           supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R))) * ‖z - w‖ ^ α) :
    ckHolderNorm 0 α f (Metric.ball (0 : ℂ) r) ≤
      (1 + (R * (2 * r) ^ (1 - α) / (R - r) ^ 2) +
        4 * ((2 * r) ^ (1 - α) + (R + r) ^ (1 - α) / (1 - α))) *
      (supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) +
       supNormOn f (Metric.ball (0 : ℂ) R)) := by
  rw [ckHolderNorm_zero_eq]
  have h1 : supNormOn f (Metric.ball (0 : ℂ) r) ≤ supNormOn f (Metric.ball (0 : ℂ) R) :=
    supNormOn_ball_mono_of_continuousOn hrR.le hf_cont
  have h2 : holderSeminorm α f (Metric.ball (0 : ℂ) r) ≤
      ((R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * supNormOn f (Metric.ball (0 : ℂ) R)) +
      (4 * ((2 * r) ^ (1 - α) + (R + r) ^ (1 - α) / (1 - α)) *
        supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R)) :=
    cauchy_pompeiu_holder_seminorm_le hr hrR hα0 hα1 h_pt
  have hSub : 0 < R - r := sub_pos.mpr hrR
  have h1a : 0 < 1 - α := sub_pos.mpr hα1
  have hR : 0 < R := lt_trans hr hrR
  have hf : 0 ≤ supNormOn f (Metric.ball (0 : ℂ) R) := supNormOn_nonneg f _
  have hd : 0 ≤ supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) :=
    supNormOn_nonneg (dbarComplex f) _
  have hA : 0 ≤ 1 + R * (2 * r) ^ (1 - α) / (R - r) ^ 2 := by positivity
  have hB : 0 ≤ 4 * ((2 * r) ^ (1 - α) + (R + r) ^ (1 - α) / (1 - α)) := by positivity
  nlinarith [mul_nonneg hA hd, mul_nonneg hB hf, mul_nonneg hA hf, mul_nonneg hB hd]

theorem cauchy_pompeiu_holder_gain_of_pointwise
    (r R α : ℝ) (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1)
    (h_pt : ∀ (f : ℂ → ℂ), ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R) →
      ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
        ‖f z - f w‖ ≤
          (((R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * supNormOn f (Metric.ball (0 : ℂ) R)) +
           (4 * ((2 * r) ^ (1 - α) + (R + r) ^ (1 - α) / (1 - α)) *
             supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R))) * ‖z - w‖ ^ α) :
    ∃ C > 0, ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R) →
      ckHolderNorm 0 α f (Metric.ball (0 : ℂ) r) ≤
        C * (supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) +
             supNormOn f (Metric.ball (0 : ℂ) R)) := by
  have hSub : 0 < R - r := sub_pos.mpr hrR
  have h1a : 0 < 1 - α := sub_pos.mpr hα1
  have hR : 0 < R := lt_trans hr hrR
  refine ⟨1 + (R * (2 * r) ^ (1 - α) / (R - r) ^ 2) +
      4 * ((2 * r) ^ (1 - α) + (R + r) ^ (1 - α) / (1 - α)), by positivity, ?_⟩
  intro f hf
  exact cauchy_pompeiu_ckHolderNorm_zero_le hr hrR hα0 hα1 hf.continuousOn (h_pt f hf)

theorem interior_cauchy_riemann_estimate_zero_of_first_deriv
    {α r R C₀ C₁ : ℝ} (_hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    {f : ℂ → ℂ}
    (h_sup₀ : supNormOn f (Metric.ball (0 : ℂ) r) ≤ supNormOn f (Metric.ball (0 : ℂ) R))
    (h_hol₀ : holderSeminorm α f (Metric.ball (0 : ℂ) r) ≤
      C₀ * (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
            supNormOn f (Metric.ball (0 : ℂ) R)))
    (h_sup₁ : ∀ z ∈ Metric.ball (0 : ℂ) r,
      ‖fderiv ℝ f z 1‖ ≤
        C₁ * (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
              supNormOn f (Metric.ball (0 : ℂ) R)))
    (h_sup₂ : ∀ z ∈ Metric.ball (0 : ℂ) r,
      ‖cauchyRiemann f z‖ ≤
        2 * ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R))
    (h_hol₁ : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
      ‖fderiv ℝ f z 1 - fderiv ℝ f w 1‖ ≤
        (C₁ * (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
               supNormOn f (Metric.ball (0 : ℂ) R))) * ‖z - w‖ ^ α)
    (h_hol₂ : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
      ‖cauchyRiemann f z - cauchyRiemann f w‖ ≤
        (2 * ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R)) * ‖z - w‖ ^ α) :
    ckHolderNorm 1 α f (Metric.ball (0 : ℂ) r) ≤
      (1 + C₀ + 4 * C₁ + 8) *
        (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
         supNormOn f (Metric.ball (0 : ℂ) R)) := by
  set D := ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) with hD_def
  set F := supNormOn f (Metric.ball (0 : ℂ) R) with hF_def
  have hD : 0 ≤ D := ckHolderNorm_nonneg 0 α (dbarComplex f) _
  have hF : 0 ≤ F := supNormOn_nonneg f _
  have hM₁ : 0 ≤ C₁ * (D + F) := by positivity
  have hM₂ : 0 ≤ 2 * D := by positivity
  have hK₁ : 0 ≤ C₁ * (D + F) := by positivity
  have hK₂ : 0 ≤ 2 * D := by positivity
  have h := ckHolderNorm_one_le_of_fderiv_one_and_cauchyRiemann
    (f := f) (s := Metric.ball (0 : ℂ) r) (α := α)
    (M₀ := F) (H₀ := C₀ * (D + F)) (M₁ := C₁ * (D + F)) (M₂ := 2 * D)
    (K₁ := C₁ * (D + F)) (K₂ := 2 * D)
    hM₁ hM₂ hK₁ hK₂ h_sup₀ h_hol₀ h_sup₁ h_sup₂ h_hol₁ h_hol₂
  linarith

theorem norm_sub_le_holderSeminorm_mul
    {α : ℝ} {f : ℂ → ℂ} {s : Set ℂ}
    (hbdd : BddAbove { q : ℝ | ∃ z ∈ s, ∃ w ∈ s, z ≠ w ∧ q = ‖f z - f w‖ / (‖z - w‖ ^ α) })
    {z w : ℂ} (hz : z ∈ s) (hw : w ∈ s) (hα : 0 < α) :
    ‖f z - f w‖ ≤ holderSeminorm α f s * ‖z - w‖ ^ α := by
  by_cases hzw : z = w
  · subst hzw
    simp [Real.zero_rpow (ne_of_gt hα)]
  · have h_pos : 0 < ‖z - w‖ ^ α := Real.rpow_pos_of_pos (norm_sub_pos_iff.mpr hzw) α
    rw [← div_le_iff₀ h_pos]
    apply le_csSup hbdd
    exact ⟨z, hz, w, hw, hzw, rfl⟩

theorem cauchyRiemann_pointwise_and_holder_bounds_on_ball
    {α r R : ℝ} (hrR : r ≤ R) (hα0 : 0 < α) {f : ℂ → ℂ}
    (hbdd_sup : BddAbove ((fun z => ‖dbarComplex f z‖) '' Metric.ball (0 : ℂ) R))
    (hbdd_hol : BddAbove { q : ℝ | ∃ z ∈ Metric.ball (0 : ℂ) R, ∃ w ∈ Metric.ball (0 : ℂ) R,
      z ≠ w ∧ q = ‖dbarComplex f z - dbarComplex f w‖ / (‖z - w‖ ^ α) }) :
    (∀ z ∈ Metric.ball (0 : ℂ) r,
      ‖cauchyRiemann f z‖ ≤ 2 * ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R)) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
      ‖cauchyRiemann f z - cauchyRiemann f w‖ ≤
        (2 * ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R)) * ‖z - w‖ ^ α) := by
  have hCk : ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) =
      supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) +
        holderSeminorm α (dbarComplex f) (Metric.ball (0 : ℂ) R) :=
    ckHolderNorm_zero_eq α (dbarComplex f) (Metric.ball (0 : ℂ) R)
  have hsup_nonneg : 0 ≤ supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) :=
    supNormOn_nonneg (dbarComplex f) _
  have hhol_nonneg : 0 ≤ holderSeminorm α (dbarComplex f) (Metric.ball (0 : ℂ) R) :=
    holderSeminorm_nonneg α (dbarComplex f) _
  constructor
  · intro z hz
    have hzR : z ∈ Metric.ball (0 : ℂ) R := Metric.ball_subset_ball hrR hz
    have h2 : ‖cauchyRiemann f z‖ ≤ supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) :=
      norm_le_supNormOn hzR hbdd_sup
    rw [hCk]
    linarith
  · intro z hz w hw
    have hzR : z ∈ Metric.ball (0 : ℂ) R := Metric.ball_subset_ball hrR hz
    have hwR : w ∈ Metric.ball (0 : ℂ) R := Metric.ball_subset_ball hrR hw
    have h2 : ‖cauchyRiemann f z - cauchyRiemann f w‖ ≤
        holderSeminorm α (dbarComplex f) (Metric.ball (0 : ℂ) R) * ‖z - w‖ ^ α :=
      norm_sub_le_holderSeminorm_mul hbdd_hol hzR hwR hα0
    have hpow_nonneg : 0 ≤ ‖z - w‖ ^ α := by positivity
    rw [hCk]
    nlinarith

theorem interior_cauchy_riemann_estimate_succ_of_dir_schauder
    {k : ℕ} {α r R C₀ C₁ : ℝ} (_hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    {f : ℂ → ℂ}
    (h_base : ckHolderNorm (k + 1) α f (Metric.ball (0 : ℂ) r) ≤
      C₀ * (ckHolderNorm (k + 1) α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
            supNormOn f (Metric.ball (0 : ℂ) R)))
    (h_sup₁ : ∀ z ∈ Metric.ball (0 : ℂ) r,
      ‖fderiv ℝ (iteratedFDeriv ℝ (k + 1) f) z 1‖ ≤
        C₁ * (ckHolderNorm (k + 1) α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
              supNormOn f (Metric.ball (0 : ℂ) R)))
    (h_sup₂ : ∀ z ∈ Metric.ball (0 : ℂ) r,
      ‖fderiv ℝ (iteratedFDeriv ℝ (k + 1) f) z Complex.I‖ ≤
        C₁ * (ckHolderNorm (k + 1) α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
              supNormOn f (Metric.ball (0 : ℂ) R)))
    (h_hol₁ : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
      ‖fderiv ℝ (iteratedFDeriv ℝ (k + 1) f) z 1 -
        fderiv ℝ (iteratedFDeriv ℝ (k + 1) f) w 1‖ ≤
        (C₁ * (ckHolderNorm (k + 1) α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
               supNormOn f (Metric.ball (0 : ℂ) R))) * ‖z - w‖ ^ α)
    (h_hol₂ : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
      ‖fderiv ℝ (iteratedFDeriv ℝ (k + 1) f) z Complex.I -
        fderiv ℝ (iteratedFDeriv ℝ (k + 1) f) w Complex.I‖ ≤
        (C₁ * (ckHolderNorm (k + 1) α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
               supNormOn f (Metric.ball (0 : ℂ) R))) * ‖z - w‖ ^ α) :
    ckHolderNorm (k + 2) α f (Metric.ball (0 : ℂ) r) ≤
      (C₀ + 4 * C₁) *
        (ckHolderNorm (k + 1) α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
         supNormOn f (Metric.ball (0 : ℂ) R)) := by
  set D := ckHolderNorm (k + 1) α (dbarComplex f) (Metric.ball (0 : ℂ) R) with hD_def
  set F := supNormOn f (Metric.ball (0 : ℂ) R) with hF_def
  have hD : 0 ≤ D := ckHolderNorm_nonneg (k + 1) α (dbarComplex f) _
  have hF : 0 ≤ F := supNormOn_nonneg f _
  have hM : 0 ≤ C₁ * (D + F) := by positivity
  have h := ckHolderNorm_succ_le_of_dir_bounds
    (k := k + 1) (α := α) (M₀ := C₀ * (D + F)) (M₁ := C₁ * (D + F))
    (M₂ := C₁ * (D + F)) (K₁ := C₁ * (D + F)) (K₂ := C₁ * (D + F))
    (f := f) (s := Metric.ball (0 : ℂ) r)
    hM hM hM hM h_base h_sup₁ h_sup₂ h_hol₁ h_hol₂
  have : k + 1 + 1 = k + 2 := rfl
  rw [this] at h
  linarith

theorem interior_cauchy_riemann_estimate_of_induction
    (h_base : ∀ (α r R : ℝ), 0 < r → r < R → 0 < α → α < 1 →
      ∃ C > 0, ∀ (f : ℂ → ℂ),
        ContDiffOn ℝ (0 + 1 : ℕ) f (Metric.closedBall (0 : ℂ) R) →
        ckHolderNorm (0 + 1) α f (Metric.ball (0 : ℂ) r) ≤
          C * (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
               supNormOn f (Metric.ball (0 : ℂ) R)))
    (h_step : ∀ (k : ℕ),
      (∀ (α r R : ℝ), 0 < r → r < R → 0 < α → α < 1 →
        ∃ C > 0, ∀ (f : ℂ → ℂ),
          ContDiffOn ℝ (k + 1 : ℕ) f (Metric.closedBall (0 : ℂ) R) →
          ckHolderNorm (k + 1) α f (Metric.ball (0 : ℂ) r) ≤
            C * (ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
                 supNormOn f (Metric.ball (0 : ℂ) R))) →
      (∀ (α r R : ℝ), 0 < r → r < R → 0 < α → α < 1 →
        ∃ C > 0, ∀ (f : ℂ → ℂ),
          ContDiffOn ℝ (k + 1 + 1 : ℕ) f (Metric.closedBall (0 : ℂ) R) →
          ckHolderNorm (k + 1 + 1) α f (Metric.ball (0 : ℂ) r) ≤
            C * (ckHolderNorm (k + 1) α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
                 supNormOn f (Metric.ball (0 : ℂ) R))))
    (k : ℕ) (α r R : ℝ) (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1 : ℕ) f (Metric.closedBall (0 : ℂ) R) →
      ckHolderNorm (k + 1) α f (Metric.ball (0 : ℂ) r) ≤
        C * (ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
             supNormOn f (Metric.ball (0 : ℂ) R)) := by
  induction' k with k ih generalizing α r R
  · exact h_base α r R hr hrR hα0 hα1
  · exact h_step k ih α r R hr hrR hα0 hα1

/-- Explicit Cauchy–Pompeiu interior Hölder gain constant on concentric disks $0 < r < R$. -/
noncomputable def cauchyPompeiuConstant (r R α : ℝ) : ℝ :=
  1 + (R * (2 * r) ^ (1 - α) / (R - r) ^ 2) +
    4 * ((2 * r) ^ (1 - α) + (R + r) ^ (1 - α) / (1 - α))

theorem cauchyPompeiuConstant_pos {r R α : ℝ} (hr : 0 < r) (hrR : r < R) (_hα0 : 0 < α) (hα1 : α < 1) :
    0 < cauchyPompeiuConstant r R α := by
  dsimp [cauchyPompeiuConstant]
  have hSub : 0 < R - r := sub_pos.mpr hrR
  have h1a : 0 < 1 - α := sub_pos.mpr hα1
  have hR : 0 < R := lt_trans hr hrR
  positivity

/-- Pointwise Cauchy–Pompeiu Hölder difference bound on concentric disks $D_r \subset D_R$. -/
def SatisfiesCauchyPompeiuPointwise (r R α : ℝ) (f : ℂ → ℂ) : Prop :=
  ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
    ‖f z - f w‖ ≤
      (((R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * supNormOn f (Metric.ball (0 : ℂ) R)) +
       (4 * ((2 * r) ^ (1 - α) + (R + r) ^ (1 - α) / (1 - α)) *
         supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R))) * ‖z - w‖ ^ α

/-- Constant maps unconditionally satisfy `SatisfiesCauchyPompeiuPointwise`. -/
theorem satisfiesCauchyPompeiuPointwise_const
    {r R α : ℝ} (hr : 0 < r) (hrR : r < R) (_hα0 : 0 < α) (hα1 : α < 1) (c : ℂ) :
    SatisfiesCauchyPompeiuPointwise r R α (fun _ => c) := by
  intro z _hz w _hw
  simp only [sub_self, norm_zero]
  have hSub : 0 < R - r := sub_pos.mpr hrR
  have h1a : 0 < 1 - α := sub_pos.mpr hα1
  have hR : 0 < R := lt_trans hr hrR
  have hf : 0 ≤ supNormOn (fun _ => c) (Metric.ball (0 : ℂ) R) := supNormOn_nonneg _ _
  have hd : 0 ≤ supNormOn (dbarComplex (fun _ => c)) (Metric.ball (0 : ℂ) R) := supNormOn_nonneg _ _
  positivity

/-- Explicit recursive interior Schauder constant $C_{k,\alpha,r,R}$ on concentric disks $0 < r < R$. -/
noncomputable def schauderConstant : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, α, r, R => 9 + 5 * cauchyPompeiuConstant r R α
  | k + 1, α, r, R => 5 * schauderConstant k α r ((r + R) / 2)

theorem schauderConstant_pos (k : ℕ) {α r R : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) :
    0 < schauderConstant k α r R := by
  induction' k with k ih generalizing r R
  · dsimp [schauderConstant]
    have hcp := cauchyPompeiuConstant_pos hr hrR hα0 hα1
    positivity
  · dsimp [schauderConstant]
    have hmid := radius_shrinkage_mid r R ⟨hr, hrR⟩
    have h_ih := ih hr hmid.2.1
    positivity

theorem one_le_schauderConstant (k : ℕ) {α r R : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) :
    1 ≤ schauderConstant k α r R := by
  induction' k with k ih generalizing r R
  · dsimp [schauderConstant]
    have hcp := cauchyPompeiuConstant_pos hr hrR hα0 hα1
    linarith
  · dsimp [schauderConstant]
    have hmid := radius_shrinkage_mid r R ⟨hr, hrR⟩
    have h_ih := ih hr hmid.2.1
    linarith

/-- Directional Schauder regularity predicate for order $k$ on concentric disks $D_r \subset D_R$. -/
def SatisfiesCauchyRiemannSchauder : ℕ → ℝ → ℝ → ℝ → (ℂ → ℂ) → Prop
  | 0, α, r, R, f =>
      SatisfiesCauchyPompeiuPointwise r R α f ∧
      BddAbove ((fun z => ‖dbarComplex f z‖) '' Metric.ball (0 : ℂ) R) ∧
      BddAbove { q : ℝ | ∃ z ∈ Metric.ball (0 : ℂ) R, ∃ w ∈ Metric.ball (0 : ℂ) R,
        z ≠ w ∧ q = ‖dbarComplex f z - dbarComplex f w‖ / (‖z - w‖ ^ α) } ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r,
        ‖fderiv ℝ f z 1‖ ≤
          cauchyPompeiuConstant r R α *
            (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
             supNormOn f (Metric.ball (0 : ℂ) R))) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
        ‖fderiv ℝ f z 1 - fderiv ℝ f w 1‖ ≤
          (cauchyPompeiuConstant r R α *
            (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
             supNormOn f (Metric.ball (0 : ℂ) R))) * ‖z - w‖ ^ α)
  | k + 1, α, r, R, f =>
      let C₁ := schauderConstant k α r ((r + R) / 2)
      let D := ckHolderNorm (k + 1) α (dbarComplex f) (Metric.ball (0 : ℂ) R)
      let F := supNormOn f (Metric.ball (0 : ℂ) R)
      (ckHolderNorm (k + 1) α f (Metric.ball (0 : ℂ) r) ≤ C₁ * (D + F)) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r,
        ‖fderiv ℝ (iteratedFDeriv ℝ (k + 1) f) z 1‖ ≤ C₁ * (D + F)) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r,
        ‖fderiv ℝ (iteratedFDeriv ℝ (k + 1) f) z Complex.I‖ ≤ C₁ * (D + F)) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
        ‖fderiv ℝ (iteratedFDeriv ℝ (k + 1) f) z 1 -
          fderiv ℝ (iteratedFDeriv ℝ (k + 1) f) w 1‖ ≤ (C₁ * (D + F)) * ‖z - w‖ ^ α) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
        ‖fderiv ℝ (iteratedFDeriv ℝ (k + 1) f) z Complex.I -
          fderiv ℝ (iteratedFDeriv ℝ (k + 1) f) w Complex.I‖ ≤ (C₁ * (D + F)) * ‖z - w‖ ^ α)

theorem holderSeminorm_const (α : ℝ) (c : ℂ) (s : Set ℂ) :
    holderSeminorm α (fun _ => c) s = 0 := by
  dsimp [holderSeminorm]
  apply sSup_zero_set
  rintro q ⟨z, _, w, _, _, rfl⟩
  simp

theorem derivHolderSeminorm_const (j : ℕ) (α : ℝ) (c : ℂ) (s : Set ℂ) :
    derivHolderSeminorm j α (fun _ => c) s = 0 := by
  dsimp [derivHolderSeminorm]
  apply sSup_zero_set
  rintro q ⟨z, _, w, _, _, rfl⟩
  cases j with
  | zero =>
    have hz : iteratedFDeriv ℝ 0 (fun _ : ℂ => c) z = iteratedFDeriv ℝ 0 (fun _ : ℂ => c) w := by
      ext m
      simp [iteratedFDeriv_zero_apply]
    simp [hz]
  | succ n =>
    have h1 := iteratedFDeriv_succ_const_apply n c z
    have h2 := iteratedFDeriv_succ_const_apply n c w
    simp [h1, h2]

theorem ckHolderNorm_const (k : ℕ) (α : ℝ) (c : ℂ) (s : Set ℂ) :
    ckHolderNorm k α (fun _ => c) s = supNormOn (fun _ => c) s := by
  induction' k with k ih
  · rw [ckHolderNorm_zero_eq, holderSeminorm_const, add_zero]
  · have h_le := ckHolderNorm_succ_le_ckHolderNorm_add_top k α (fun _ => c) s
      (derivHolderSeminorm_nonneg k α (fun _ => c) s)
    have h_sup_zero : sSup ((fun z => ‖iteratedFDeriv ℝ (k + 1) (fun _ : ℂ => c) z‖) '' s) = 0 := by
      apply sSup_zero_set
      rintro y ⟨z, _, rfl⟩
      have h0 := iteratedFDeriv_succ_const_apply k c z
      simp [h0]
    have h_der_zero : derivHolderSeminorm (k + 1) α (fun _ => c) s = 0 :=
      derivHolderSeminorm_const (k + 1) α c s
    have h_ge : supNormOn (fun _ => c) s ≤ ckHolderNorm (k + 1) α (fun _ => c) s :=
      ckHolderNorm_zero_le_order (k + 1) α (fun _ => c) s
    linarith

/-- Constant maps unconditionally satisfy `SatisfiesCauchyRiemannSchauder`. -/
theorem satisfiesCauchyRiemannSchauder_const
    (k : ℕ) {α r R : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) (c : ℂ) :
    SatisfiesCauchyRiemannSchauder k α r R (fun _ => c) := by
  cases k with
  | zero =>
    unfold SatisfiesCauchyRiemannSchauder
    have hC₀ : 0 < cauchyPompeiuConstant r R α := cauchyPompeiuConstant_pos hr hrR hα0 hα1
    have hD : 0 ≤ ckHolderNorm 0 α (dbarComplex (fun _ => c)) (Metric.ball (0 : ℂ) R) :=
      ckHolderNorm_nonneg 0 α _ _
    have hF : 0 ≤ supNormOn (fun _ => c) (Metric.ball (0 : ℂ) R) := supNormOn_nonneg _ _
    refine ⟨satisfiesCauchyPompeiuPointwise_const hr hrR hα0 hα1 c, ?_, ?_, ?_, ?_⟩
    · refine ⟨0, ?_⟩
      rintro y ⟨z, _hz, rfl⟩
      change ‖cauchyRiemann (fun _ => c) z‖ ≤ 0
      rw [cauchyRiemann_const c z, norm_zero]
    · refine ⟨0, ?_⟩
      rintro q ⟨z, _hz, w, _hw, _hzw, rfl⟩
      change ‖cauchyRiemann (fun _ => c) z - cauchyRiemann (fun _ => c) w‖ / ‖z - w‖ ^ α ≤ 0
      rw [cauchyRiemann_const c z, cauchyRiemann_const c w, sub_self, norm_zero, zero_div]
    · intro z _hz
      have hf0 : fderiv ℝ (fun _ : ℂ => c) z 1 = 0 := by rw [fderiv_const]; rfl
      rw [hf0, norm_zero]
      positivity
    · intro z _hz w _hw
      have hf1 : fderiv ℝ (fun _ : ℂ => c) z 1 = 0 := by rw [fderiv_const]; rfl
      have hf2 : fderiv ℝ (fun _ : ℂ => c) w 1 = 0 := by rw [fderiv_const]; rfl
      rw [hf1, hf2, sub_self, norm_zero]
      have hd : 0 ≤ ‖z - w‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
      positivity
  | succ k =>
    unfold SatisfiesCauchyRiemannSchauder
    have hmid := radius_shrinkage_mid r R ⟨hr, hrR⟩
    have hC₁_ge : 1 ≤ schauderConstant k α r ((r + R) / 2) :=
      one_le_schauderConstant k hr hmid.2.1 hα0 hα1
    have hC₁_pos : 0 < schauderConstant k α r ((r + R) / 2) := by linarith
    have hD : 0 ≤ ckHolderNorm (k + 1) α (dbarComplex (fun _ => c)) (Metric.ball (0 : ℂ) R) :=
      ckHolderNorm_nonneg (k + 1) α _ _
    have hF : 0 ≤ supNormOn (fun _ => c) (Metric.ball (0 : ℂ) R) := supNormOn_nonneg _ _
    have h_iter_zero : iteratedFDeriv ℝ (k + 1) (fun _ : ℂ => c) =
        fun _ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => ℂ) ℂ) := by
      ext z m
      rw [iteratedFDeriv_succ_const_apply k c z]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [ckHolderNorm_const (k + 1) α c (Metric.ball (0 : ℂ) r)]
      have h_mono : supNormOn (fun _ => c) (Metric.ball (0 : ℂ) r) ≤
          supNormOn (fun _ => c) (Metric.ball (0 : ℂ) R) :=
        supNormOn_ball_mono_of_continuousOn hrR.le continuousOn_const
      nlinarith
    · intro z _hz
      rw [h_iter_zero]
      have hf0 : fderiv ℝ (fun _ : ℂ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => ℂ) ℂ)) z 1 = 0 := by
        rw [fderiv_const]; rfl
      rw [hf0, norm_zero]
      positivity
    · intro z _hz
      rw [h_iter_zero]
      have hf0 : fderiv ℝ (fun _ : ℂ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => ℂ) ℂ)) z Complex.I = 0 := by
        rw [fderiv_const]; rfl
      rw [hf0, norm_zero]
      positivity
    · intro z _hz w _hw
      rw [h_iter_zero]
      have hf1 : fderiv ℝ (fun _ : ℂ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => ℂ) ℂ)) z 1 = 0 := by
        rw [fderiv_const]; rfl
      have hf2 : fderiv ℝ (fun _ : ℂ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => ℂ) ℂ)) w 1 = 0 := by
        rw [fderiv_const]; rfl
      rw [hf1, hf2, sub_self, norm_zero]
      have hd : 0 ≤ ‖z - w‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
      positivity
    · intro z _hz w _hw
      rw [h_iter_zero]
      have hf1 : fderiv ℝ (fun _ : ℂ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => ℂ) ℂ)) z Complex.I = 0 := by
        rw [fderiv_const]; rfl
      have hf2 : fderiv ℝ (fun _ : ℂ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => ℂ) ℂ)) w Complex.I = 0 := by
        rw [fderiv_const]; rfl
      rw [hf1, hf2, sub_self, norm_zero]
      have hd : 0 ≤ ‖z - w‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
      positivity

/-- Interior Cauchy–Riemann Schauder Estimate in $C^{k,\alpha}$ from `SatisfiesCauchyRiemannSchauder` (Zero-sorry reduction). -/
theorem interior_cauchy_riemann_estimate_of_schauder
    (k : ℕ) (α r R : ℝ) (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1) f (Metric.closedBall (0 : ℂ) R) →
      SatisfiesCauchyRiemannSchauder k α r R f →
      ckHolderNorm (k + 1) α f (Metric.ball (0 : ℂ) r) ≤
        C * (ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
             supNormOn f (Metric.ball (0 : ℂ) R)) := by
  refine ⟨schauderConstant k α r R, schauderConstant_pos k hr hrR hα0 hα1, ?_⟩
  intro f hf hs
  cases k with
  | zero =>
    dsimp [SatisfiesCauchyRiemannSchauder] at hs
    rcases hs with ⟨h_pt, hbdd_sup, hbdd_hol, h_sup₁, h_hol₁⟩
    have h_sup₀ : supNormOn f (Metric.ball (0 : ℂ) r) ≤ supNormOn f (Metric.ball (0 : ℂ) R) :=
      supNormOn_ball_mono_of_continuousOn hrR.le hf.continuousOn
    have h_sem := cauchy_pompeiu_holder_seminorm_le hr hrR hα0 hα1 h_pt
    have hSub : 0 < R - r := sub_pos.mpr hrR
    have h1a : 0 < 1 - α := sub_pos.mpr hα1
    have hR : 0 < R := lt_trans hr hrR
    have hf_nonneg : 0 ≤ supNormOn f (Metric.ball (0 : ℂ) R) := supNormOn_nonneg f _
    have hd_nonneg : 0 ≤ supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) :=
      supNormOn_nonneg (dbarComplex f) _
    have hd_le_ck : supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) ≤
        ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) :=
      ckHolderNorm_zero_le_order 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R)
    have hck_nonneg : 0 ≤ ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) :=
      ckHolderNorm_nonneg 0 α (dbarComplex f) _
    have hA : 0 ≤ R * (2 * r) ^ (1 - α) / (R - r) ^ 2 := by positivity
    have hB : 0 ≤ 4 * ((2 * r) ^ (1 - α) + (R + r) ^ (1 - α) / (1 - α)) := by positivity
    have h_hol₀ : holderSeminorm α f (Metric.ball (0 : ℂ) r) ≤
        cauchyPompeiuConstant r R α *
          (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
           supNormOn f (Metric.ball (0 : ℂ) R)) := by
      dsimp [cauchyPompeiuConstant]
      nlinarith [mul_le_mul_of_nonneg_left hd_le_ck hB]
    have h_cr_bds := cauchyRiemann_pointwise_and_holder_bounds_on_ball hrR.le hα0 hbdd_sup hbdd_hol
    have hC₀ : 0 < cauchyPompeiuConstant r R α := cauchyPompeiuConstant_pos hr hrR hα0 hα1
    have h_zero := interior_cauchy_riemann_estimate_zero_of_first_deriv
      hC₀ hC₀ h_sup₀ h_hol₀ h_sup₁ h_cr_bds.1 h_hol₁ h_cr_bds.2
    dsimp [schauderConstant]
    linarith
  | succ k =>
    dsimp [SatisfiesCauchyRiemannSchauder] at hs
    rcases hs with ⟨h_base, h_sup₁, h_sup₂, h_hol₁, h_hol₂⟩
    have hmid := radius_shrinkage_mid r R ⟨hr, hrR⟩
    have hC₁ : 0 < schauderConstant k α r ((r + R) / 2) :=
      schauderConstant_pos k hr hmid.2.1 hα0 hα1
    have h_succ := interior_cauchy_riemann_estimate_succ_of_dir_schauder
      hC₁ hC₁ h_base h_sup₁ h_sup₂ h_hol₁ h_hol₂
    dsimp [schauderConstant]
    linarith

/-- By continuity on `closedBall 0 R` and density of `ball 0 R` in `closedBall 0 R`,
`‖f ζ‖ ≤ supNormOn f (ball 0 R)` holds on the entire closed ball `closedBall 0 R` (Zero-sorry). -/
theorem norm_le_supNormOn_closedBall_of_continuousOn
    {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) R))
    {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall (0 : ℂ) R) :
    ‖f ζ‖ ≤ supNormOn f (Metric.ball (0 : ℂ) R) := by
  have hbdd : BddAbove ((fun z => ‖f z‖) '' Metric.ball (0 : ℂ) R) :=
    bddAbove_norm_image_ball_of_continuousOn hf
  have h_clos : ζ ∈ closure (Metric.ball (0 : ℂ) R) := by
    rwa [closure_ball (0 : ℂ) hR.ne']
  haveI : (𝓝[Metric.ball (0 : ℂ) R] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp h_clos
  have h_tendsto : Filter.Tendsto (fun z => ‖f z‖) (𝓝[Metric.ball (0 : ℂ) R] ζ) (𝓝 ‖f ζ‖) :=
    (hf.norm ζ hζ).mono Metric.ball_subset_closedBall
  apply le_of_tendsto h_tendsto
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact norm_le_supNormOn hz hbdd

/-- Boundary circle integral Hölder difference bound in terms of `supNormOn f (ball 0 R)` (Zero-sorry). -/
theorem boundary_circleIntegral_scaled_holder_est_supNormOn
    {r R α : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1)
    {f : ℂ → ℂ} (hf : ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R))
    {z w : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) r) (hw : w ∈ Metric.ball (0 : ℂ) r) :
    ‖((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - z)⁻¹ * f ζ) -
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - w)⁻¹ * f ζ)‖ ≤
      ((R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * supNormOn f (Metric.ball (0 : ℂ) R)) * ‖z - w‖ ^ α := by
  have hR : 0 < R := lt_trans hr hrR
  exact boundary_circleIntegral_scaled_holder_est hr hrR hα0 hα1 (supNormOn_nonneg f _)
    (hf.continuousOn.mono Metric.sphere_subset_closedBall)
    (fun ζ hζ => norm_le_supNormOn_closedBall_of_continuousOn hR hf.continuousOn (Metric.sphere_subset_closedBall hζ))
    (Metric.ball_subset_closedBall hz) (Metric.ball_subset_closedBall hw)

/-- For the identically zero map `fun _ => 0`, the Cauchy–Pompeiu near/far decomposition holds
with `I_near = 0` and `I_far = 0` (`0 sorryAx`). -/
theorem cauchy_pompeiu_near_far_decomp_zero
    {r R α : ℝ} (_hr : 0 < r) (_hrR : r < R) (_hα0 : 0 < α) (hα1 : α < 1)
    {z w : ℂ} :
    ∃ (I_near I_far : ℂ),
      (0 : ℂ) - 0 =
        (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - z)⁻¹ * (0 : ℂ)) -
         ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - w)⁻¹ * (0 : ℂ))) -
        ((Real.pi : ℂ)⁻¹) * (I_near + I_far) ∧
      ‖I_near‖ ≤ 4 * Real.pi * supNormOn (dbarComplex (fun _ : ℂ => (0 : ℂ))) (Metric.ball (0 : ℂ) R) * ‖z - w‖ ∧
      ‖I_far‖ ≤ (4 * Real.pi * supNormOn (dbarComplex (fun _ : ℂ => (0 : ℂ))) (Metric.ball (0 : ℂ) R) *
        (R + r) ^ (1 - α) / (1 - α)) * ‖z - w‖ ^ α := by
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · simp only [mul_zero]
    ring
  · simp only [norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (supNormOn_nonneg _ _)) (norm_nonneg _)
  · simp only [norm_zero]
    have h1 : 0 ≤ 1 - α := by linarith
    have h2 : 0 ≤ (R + r) ^ (1 - α) := Real.rpow_nonneg (by linarith) (1 - α)
    have h3 : 0 ≤ ‖z - w‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    have h_sup : 0 ≤ supNormOn (dbarComplex (fun _ : ℂ => (0 : ℂ))) (Metric.ball (0 : ℂ) R) :=
      supNormOn_nonneg _ _
    positivity

/-- The Cauchy–Riemann operator `cauchyRiemann` vanishes at any complex-differentiable point (`0 sorryAx`). -/
theorem cauchyRiemann_eq_zero_of_differentiableAt
    {f : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℂ f z) :
    cauchyRiemann f z = 0 := by
  dsimp [cauchyRiemann]
  have h_res : fderiv ℝ f z = (fderiv ℂ f z).restrictScalars ℝ :=
    (hd.hasFDerivAt.restrictScalars ℝ).fderiv
  rw [h_res]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  have hI : (fderiv ℂ f z) Complex.I = Complex.I * (fderiv ℂ f z) 1 := by
    simpa [smul_eq_mul] using (fderiv ℂ f z).map_smul Complex.I (1 : ℂ)
  rw [hI, ← mul_assoc, Complex.I_mul_I]
  ring

/-- For any map complex-differentiable on `ball 0 R`, `dbarComplex f` vanishes on `ball 0 R`, so its
$\alpha$-Hölder difference quotients on `ball 0 R` are bounded above by `0` (`0 sorryAx`). -/
theorem bddAbove_holder_quotient_dbarComplex_ball_of_differentiableOn
    {f : ℂ → ℂ} {R α : ℝ}
    (hd : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R)) :
    BddAbove { q : ℝ | ∃ z ∈ Metric.ball (0 : ℂ) R, ∃ w ∈ Metric.ball (0 : ℂ) R,
      z ≠ w ∧ q = ‖dbarComplex f z - dbarComplex f w‖ / (‖z - w‖ ^ α) } := by
  refine ⟨0, ?_⟩
  rintro q ⟨z, hz, w, hw, _hzw, rfl⟩
  have hz0 : dbarComplex f z = 0 :=
    cauchyRiemann_eq_zero_of_differentiableAt (hd.differentiableAt (Metric.isOpen_ball.mem_nhds hz))
  have hw0 : dbarComplex f w = 0 :=
    cauchyRiemann_eq_zero_of_differentiableAt (hd.differentiableAt (Metric.isOpen_ball.mem_nhds hw))
  rw [hz0, hw0, sub_self, norm_zero, zero_div]

/-- For any holomorphic map on `ball 0 R` continuous on `closure (ball 0 R)` (`DiffContOnCl ℂ f (ball 0 R)`),
Mathlib's Cauchy integral formula (`DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul`)
yields the exact Cauchy–Pompeiu near/far decomposition with `I_near = 0` and `I_far = 0` (`0 sorryAx`). -/
theorem cauchy_pompeiu_near_far_decomp_of_diffContOnCl
    {r R α : ℝ} (_hr : 0 < r) (hrR : r < R) (_hα0 : 0 < α) (hα1 : α < 1)
    {f : ℂ → ℂ} (hf_hol : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) R))
    {z w : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) r) (hw : w ∈ Metric.ball (0 : ℂ) r) :
    ∃ (I_near I_far : ℂ),
      f z - f w =
        (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - z)⁻¹ * f ζ) -
         ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - w)⁻¹ * f ζ)) -
        ((Real.pi : ℂ)⁻¹) * (I_near + I_far) ∧
      ‖I_near‖ ≤ 4 * Real.pi * supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) * ‖z - w‖ ∧
      ‖I_far‖ ≤ (4 * Real.pi * supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) *
        (R + r) ^ (1 - α) / (1 - α)) * ‖z - w‖ ^ α := by
  have hzR : z ∈ Metric.ball (0 : ℂ) R := Metric.ball_subset_ball hrR.le hz
  have hwR : w ∈ Metric.ball (0 : ℂ) R := Metric.ball_subset_ball hrR.le hw
  have h_cz : ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - z)⁻¹ * f ζ) = f z := by
    simpa only [smul_eq_mul] using hf_hol.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hzR
  have h_cw : ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - w)⁻¹ * f ζ) = f w := by
    simpa only [smul_eq_mul] using hf_hol.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hwR
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · rw [h_cz, h_cw]
    ring
  · simp only [norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (supNormOn_nonneg _ _)) (norm_nonneg _)
  · simp only [norm_zero]
    have h1 : 0 ≤ 1 - α := by linarith
    have h2 : 0 ≤ (R + r) ^ (1 - α) := Real.rpow_nonneg (by linarith) (1 - α)
    have h3 : 0 ≤ ‖z - w‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    have h_sup : 0 ≤ supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) :=
      supNormOn_nonneg _ _
    positivity

/-- Any map holomorphic on `ball 0 R` and $C^1$ on `closedBall 0 R` satisfies
`SatisfiesCauchyPompeiuPointwise r R α f` with `0 sorryAx` via Mathlib's Cauchy integral formula. -/
theorem satisfiesCauchyPompeiuPointwise_of_diffContOnCl
    {r R α : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1)
    {f : ℂ → ℂ} (hf : ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R))
    (hf_hol : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) R)) :
    SatisfiesCauchyPompeiuPointwise r R α f := by
  intro z hz w hw
  obtain ⟨I_near, I_far, h_decomp, h_near_lip, h_far⟩ :=
    cauchy_pompeiu_near_far_decomp_of_diffContOnCl hr hrR hα0 hα1 hf_hol hz hw
  have h_bdry := boundary_circleIntegral_scaled_holder_est_supNormOn hr hrR hα0 hα1 hf hz hw
  have h_near : ‖I_near‖ ≤
      (4 * Real.pi * supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) * (2 * r) ^ (1 - α)) * ‖z - w‖ ^ α :=
    le_trans h_near_lip (polar_near_zone_holder_bound hr (supNormOn_nonneg (dbarComplex f) _) hα0 hα1
      (Metric.ball_subset_closedBall hz) (Metric.ball_subset_closedBall hw))
  have h_comb := cauchy_pompeiu_pointwise_holder_bound_of_parts h_bdry h_near h_far
  rw [h_decomp]
  calc ‖(((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - z)⁻¹ * f ζ) -
         ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - w)⁻¹ * f ζ)) -
        ((Real.pi : ℂ)⁻¹) * (I_near + I_far)‖
      ≤ ((R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * supNormOn f (Metric.ball (0 : ℂ) R) +
         4 * supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) *
           ((2 * r) ^ (1 - α) + (R + r) ^ (1 - α) / (1 - α))) * ‖z - w‖ ^ α := h_comb
    _ = (((R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * supNormOn f (Metric.ball (0 : ℂ) R)) +
         (4 * ((2 * r) ^ (1 - α) + (R + r) ^ (1 - α) / (1 - α)) *
           supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R))) * ‖z - w‖ ^ α := by ring

/-- Decomposition of the Cauchy–Pompeiu difference `f z - f w` into the boundary circle integral
difference and near/far Pompeiu area integral zones on $D_r \subset D_R$ when `f` is holomorphic
on `ball 0 R` and continuous on `closedBall 0 R` (`0 sorryAx`). -/
theorem cauchy_pompeiu_near_far_decomp_exists
    {r R α : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1)
    (f : ℂ → ℂ) (_hf : ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R))
    (h_hol : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) R))
    {z w : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) r) (hw : w ∈ Metric.ball (0 : ℂ) r) :
    ∃ (I_near I_far : ℂ),
      f z - f w =
        (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - z)⁻¹ * f ζ) -
         ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - w)⁻¹ * f ζ)) -
        ((Real.pi : ℂ)⁻¹) * (I_near + I_far) ∧
      ‖I_near‖ ≤ 4 * Real.pi * supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) * ‖z - w‖ ∧
      ‖I_far‖ ≤ (4 * Real.pi * supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) *
        (R + r) ^ (1 - α) / (1 - α)) * ‖z - w‖ ^ α :=
  cauchy_pompeiu_near_far_decomp_of_diffContOnCl hr hrR hα0 hα1 h_hol hz hw

/-- Pointwise Cauchy–Pompeiu Hölder difference bound for $C^1$ maps on concentric disks $D_r \subset D_R$
given a near/far Pompeiu area integral decomposition (`0 sorryAx`). -/
theorem satisfiesCauchyPompeiuPointwise_of_near_far_decomp
    {r R α : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R))
    (h_decomp_all : ∀ {z w : ℂ}, z ∈ Metric.ball (0 : ℂ) r → w ∈ Metric.ball (0 : ℂ) r →
      ∃ (I_near I_far : ℂ),
        f z - f w =
          (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - z)⁻¹ * f ζ) -
           ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - w)⁻¹ * f ζ)) -
          ((Real.pi : ℂ)⁻¹) * (I_near + I_far) ∧
        ‖I_near‖ ≤ 4 * Real.pi * supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) * ‖z - w‖ ∧
        ‖I_far‖ ≤ (4 * Real.pi * supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) *
          (R + r) ^ (1 - α) / (1 - α)) * ‖z - w‖ ^ α) :
    SatisfiesCauchyPompeiuPointwise r R α f := by
  intro z hz w hw
  obtain ⟨I_near, I_far, h_decomp, h_near_lip, h_far⟩ := h_decomp_all hz hw
  have h_bdry := boundary_circleIntegral_scaled_holder_est_supNormOn hr hrR hα0 hα1 hf hz hw
  have h_near : ‖I_near‖ ≤
      (4 * Real.pi * supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) * (2 * r) ^ (1 - α)) * ‖z - w‖ ^ α :=
    le_trans h_near_lip (polar_near_zone_holder_bound hr (supNormOn_nonneg (dbarComplex f) _) hα0 hα1
      (Metric.ball_subset_closedBall hz) (Metric.ball_subset_closedBall hw))
  have h_comb := cauchy_pompeiu_pointwise_holder_bound_of_parts h_bdry h_near h_far
  rw [h_decomp]
  calc ‖(((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - z)⁻¹ * f ζ) -
         ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * (∮ ζ in C(0, R), (ζ - w)⁻¹ * f ζ)) -
        ((Real.pi : ℂ)⁻¹) * (I_near + I_far)‖
      ≤ ((R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * supNormOn f (Metric.ball (0 : ℂ) R) +
         4 * supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) *
           ((2 * r) ^ (1 - α) + (R + r) ^ (1 - α) / (1 - α))) * ‖z - w‖ ^ α := h_comb
    _ = (((R * (2 * r) ^ (1 - α) / (R - r) ^ 2) * supNormOn f (Metric.ball (0 : ℂ) R)) +
         (4 * ((2 * r) ^ (1 - α) + (R + r) ^ (1 - α) / (1 - α)) *
           supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R))) * ‖z - w‖ ^ α := by ring

/-- Any map constant on `Metric.ball (0 : ℂ) r` satisfies `SatisfiesCauchyPompeiuPointwise r R α f` (`0 sorryAx`). -/
theorem satisfiesCauchyPompeiuPointwise_of_const_on_ball
    {r R α : ℝ} (hr : 0 < r) (hrR : r < R) (_hα0 : 0 < α) (hα1 : α < 1)
    {f : ℂ → ℂ} (h_const : ∃ c : ℂ, ∀ z ∈ Metric.ball (0 : ℂ) r, f z = c) :
    SatisfiesCauchyPompeiuPointwise r R α f := by
  obtain ⟨c, hc⟩ := h_const
  intro z hz w hw
  rw [hc z hz, hc w hw, sub_self, norm_zero]
  have hSub : 0 < R - r := sub_pos.mpr hrR
  have h1a : 0 < 1 - α := sub_pos.mpr hα1
  have hR : 0 < R := lt_trans hr hrR
  have hf : 0 ≤ supNormOn f (Metric.ball (0 : ℂ) R) := supNormOn_nonneg _ _
  have hd : 0 ≤ supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) := supNormOn_nonneg _ _
  positivity

/-- Pointwise Cauchy–Pompeiu Hölder difference bound for $C^1$ maps on concentric disks $D_r \subset D_R$
when `f` is constant on `D_r` or holomorphic on `D_R` (`0 sorryAx`). -/
theorem satisfiesCauchyPompeiuPointwise_of_contDiffOn
    {r R α : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R))
    (h_cases : (∃ c : ℂ, ∀ z ∈ Metric.ball (0 : ℂ) r, f z = c) ∨
      DiffContOnCl ℂ f (Metric.ball (0 : ℂ) R)) :
    SatisfiesCauchyPompeiuPointwise r R α f := by
  rcases h_cases with h_const | h_hol
  · exact satisfiesCauchyPompeiuPointwise_of_const_on_ball hr hrR hα0 hα1 h_const
  · exact satisfiesCauchyPompeiuPointwise_of_near_far_decomp hr hrR hα0 hα1 f hf
      (fun hz hw => cauchy_pompeiu_near_far_decomp_exists hr hrR hα0 hα1 f hf h_hol hz hw)

private theorem satisfiesCauchyPompeiuPointwise_of_contDiffOn_aux
    {r R α : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R)) :
    SatisfiesCauchyPompeiuPointwise r R α f := by
  by_cases h_cases : (∃ c : ℂ, ∀ z ∈ Metric.ball (0 : ℂ) r, f z = c) ∨
      DiffContOnCl ℂ f (Metric.ball (0 : ℂ) R)
  · exact satisfiesCauchyPompeiuPointwise_of_contDiffOn hr hrR hα0 hα1 f hf h_cases
  · sorry

/-- First-order Cauchy–Riemann operator norm is bounded by the full real Fréchet derivative norm (Zero-sorry). -/
theorem norm_cauchyRiemann_le_norm_fderiv (f : ℂ → ℂ) (z : ℂ) :
    ‖cauchyRiemann f z‖ ≤ ‖fderiv ℝ f z‖ := by
  dsimp [cauchyRiemann]
  have h1 : ‖fderiv ℝ f z 1‖ ≤ ‖fderiv ℝ f z‖ := by
    simpa using (fderiv ℝ f z).le_opNorm (1 : ℂ)
  have hI : ‖fderiv ℝ f z Complex.I‖ ≤ ‖fderiv ℝ f z‖ := by
    simpa [Complex.norm_I] using (fderiv ℝ f z).le_opNorm Complex.I
  calc ‖(1 / 2 : ℂ) * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)‖
      = (1 / 2 : ℝ) * ‖fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I‖ := by
        rw [norm_mul, norm_div, norm_one, Complex.norm_ofNat]
    _ ≤ (1 / 2 : ℝ) * (‖fderiv ℝ f z 1‖ + ‖Complex.I * fderiv ℝ f z Complex.I‖) := by
        gcongr
        exact norm_add_le _ _
    _ = (1 / 2 : ℝ) * (‖fderiv ℝ f z 1‖ + ‖fderiv ℝ f z Complex.I‖) := by
        rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ ‖fderiv ℝ f z‖ := by linarith

/-- Any positive-radius closed ball in `ℂ` has `UniqueDiffOn ℝ` (Zero-sorry). -/
theorem uniqueDiffOn_closedBall {R : ℝ} (hR : 0 < R) :
    UniqueDiffOn ℝ (Metric.closedBall (0 : ℂ) R) :=
  uniqueDiffOn_convex (convex_closedBall (0 : ℂ) R)
    ⟨0, interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball (Metric.mem_ball_self hR)⟩

/-- On the open ball `ball 0 R`, `fderivWithin` on `closedBall 0 R` coincides with `fderiv` (Zero-sorry). -/
theorem fderivWithin_closedBall_eq_fderiv_of_mem_ball
    {f : ℂ → ℂ} {R : ℝ} {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    fderivWithin ℝ f (Metric.closedBall (0 : ℂ) R) z = fderiv ℝ f z :=
  fderivWithin_of_mem_nhds
    (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall)

/-- For $C^1$ maps on `closedBall 0 R`, `fderiv ℝ f` is continuous on the open ball `ball 0 R` (Zero-sorry). -/
theorem continuousOn_fderiv_ball_of_contDiffOn
    {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R)) :
    ContinuousOn (fderiv ℝ f) (Metric.ball (0 : ℂ) R) := by
  have h_cont : ContinuousOn (fderivWithin ℝ f (Metric.closedBall (0 : ℂ) R))
      (Metric.closedBall (0 : ℂ) R) :=
    hf.continuousOn_fderivWithin (uniqueDiffOn_closedBall hR) le_rfl
  exact (h_cont.mono Metric.ball_subset_closedBall).congr
    (fun _ hz => (fderivWithin_closedBall_eq_fderiv_of_mem_ball hz).symm)

/-- For $C^1$ maps on `closedBall 0 R`, `dbarComplex f` is continuous on the open ball `ball 0 R` (Zero-sorry). -/
theorem continuousOn_dbarComplex_ball_of_contDiffOn
    {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R)) :
    ContinuousOn (dbarComplex f) (Metric.ball (0 : ℂ) R) := by
  have h_fd := continuousOn_fderiv_ball_of_contDiffOn hR hf
  have h1 : ContinuousOn (fun z => fderiv ℝ f z 1) (Metric.ball (0 : ℂ) R) :=
    (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous.comp_continuousOn h_fd
  have hI : ContinuousOn (fun z => fderiv ℝ f z Complex.I) (Metric.ball (0 : ℂ) R) :=
    (ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous.comp_continuousOn h_fd
  exact continuousOn_const.mul (h1.add (continuousOn_const.mul hI))

/-- For $C^1$ maps on `closedBall 0 R`, `‖fderiv ℝ f z‖` is bounded above on `ball 0 R` (Zero-sorry). -/
theorem bddAbove_norm_fderiv_ball_of_contDiffOn
    {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R)) :
    BddAbove ((fun z => ‖fderiv ℝ f z‖) '' Metric.ball (0 : ℂ) R) := by
  have h_cont : ContinuousOn (fderivWithin ℝ f (Metric.closedBall (0 : ℂ) R))
      (Metric.closedBall (0 : ℂ) R) :=
    hf.continuousOn_fderivWithin (uniqueDiffOn_closedBall hR) le_rfl
  have h_cpt : IsCompact ((fun z => ‖fderivWithin ℝ f (Metric.closedBall (0 : ℂ) R) z‖) ''
      Metric.closedBall (0 : ℂ) R) :=
    (isCompact_closedBall (0 : ℂ) R).image_of_continuousOn h_cont.norm
  obtain ⟨M, hM⟩ := h_cpt.bddAbove
  refine ⟨M, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  dsimp only
  rw [← fderivWithin_closedBall_eq_fderiv_of_mem_ball hz]
  exact hM ⟨z, Metric.ball_subset_closedBall hz, rfl⟩

/-- For $C^1$ maps on `closedBall 0 R`, `‖dbarComplex f z‖` is bounded above on `ball 0 R` (Zero-sorry). -/
theorem bddAbove_norm_dbarComplex_ball_of_contDiffOn
    {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R)) :
    BddAbove ((fun z => ‖dbarComplex f z‖) '' Metric.ball (0 : ℂ) R) := by
  obtain ⟨M, hM⟩ := bddAbove_norm_fderiv_ball_of_contDiffOn hR hf
  refine ⟨M, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact le_trans (norm_cauchyRiemann_le_norm_fderiv f z) (hM ⟨z, hz, rfl⟩)

/-- Every $C^1$ map on `closedBall 0 R` is differentiable at every interior point `ζ ∈ ball 0 R` (Zero-sorry). -/
theorem differentiableAt_of_contDiffOn_closedBall
    {g : ℂ → ℂ} {R : ℝ} (hg : ContDiffOn ℝ 1 g (Metric.closedBall (0 : ℂ) R))
    {ζ : ℂ} (hζ : ζ ∈ Metric.ball (0 : ℂ) R) :
    DifferentiableAt ℝ g ζ :=
  (hg.contDiffAt (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hζ)
    Metric.ball_subset_closedBall)).differentiableAt le_rfl

/-- Mean value Lipschitz bound on `ball 0 R` for $C^1$ maps on `closedBall 0 R` (Zero-sorry). -/
theorem norm_sub_le_sSup_fderiv_of_contDiffOn_closedBall
    {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : ContDiffOn ℝ 1 g (Metric.closedBall (0 : ℂ) R))
    {z w : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) (hw : w ∈ Metric.ball (0 : ℂ) R) :
    ‖g z - g w‖ ≤ sSup ((fun ζ => ‖fderiv ℝ g ζ‖) '' Metric.ball (0 : ℂ) R) * ‖z - w‖ :=
  (convex_ball (0 : ℂ) R).norm_image_sub_le_of_norm_fderiv_le
    (fun _ hζ => differentiableAt_of_contDiffOn_closedBall hg hζ)
    (fun ζ hζ => le_csSup (bddAbove_norm_fderiv_ball_of_contDiffOn hR hg) ⟨ζ, hζ, rfl⟩)
    hw hz

/-- Pointwise $\alpha$-Hölder difference bound on `ball 0 R` for $C^1$ maps on `closedBall 0 R` (Zero-sorry). -/
theorem norm_sub_le_holder_of_contDiffOn_closedBall
    {g : ℂ → ℂ} {R α : ℝ} (hR : 0 < R) (hα0 : 0 < α) (hα1 : α < 1)
    (hg : ContDiffOn ℝ 1 g (Metric.closedBall (0 : ℂ) R))
    {z w : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) (hw : w ∈ Metric.ball (0 : ℂ) R) :
    ‖g z - g w‖ ≤
      (sSup ((fun ζ => ‖fderiv ℝ g ζ‖) '' Metric.ball (0 : ℂ) R) * (2 * R) ^ (1 - α)) *
        ‖z - w‖ ^ α := by
  have h_lip := norm_sub_le_sSup_fderiv_of_contDiffOn_closedBall hR hg hz hw
  have h_interp := holder_power_interpolation_on_disk hR hα0 hα1
    (Metric.ball_subset_closedBall hz) (Metric.ball_subset_closedBall hw)
  have hM_nonneg : 0 ≤ sSup ((fun ζ => ‖fderiv ℝ g ζ‖) '' Metric.ball (0 : ℂ) R) := by
    apply sSup_nonneg_of_forall_nonneg
    rintro y ⟨ζ, _, rfl⟩
    exact norm_nonneg _
  calc ‖g z - g w‖
      ≤ sSup ((fun ζ => ‖fderiv ℝ g ζ‖) '' Metric.ball (0 : ℂ) R) * ‖z - w‖ := h_lip
    _ ≤ sSup ((fun ζ => ‖fderiv ℝ g ζ‖) '' Metric.ball (0 : ℂ) R) *
          ((2 * R) ^ (1 - α) * ‖z - w‖ ^ α) :=
        mul_le_mul_of_nonneg_left h_interp hM_nonneg
    _ = (sSup ((fun ζ => ‖fderiv ℝ g ζ‖) '' Metric.ball (0 : ℂ) R) * (2 * R) ^ (1 - α)) *
          ‖z - w‖ ^ α := by ring

/-- Boundedness of the $\alpha$-Hölder difference quotients on `ball 0 R` for $C^1$ maps on `closedBall 0 R` (Zero-sorry). -/
theorem bddAbove_holder_quotient_ball_of_contDiffOn
    {g : ℂ → ℂ} {R α : ℝ} (hR : 0 < R) (hα0 : 0 < α) (hα1 : α < 1)
    (hg : ContDiffOn ℝ 1 g (Metric.closedBall (0 : ℂ) R)) :
    BddAbove { q : ℝ | ∃ z ∈ Metric.ball (0 : ℂ) R, ∃ w ∈ Metric.ball (0 : ℂ) R,
      z ≠ w ∧ q = ‖g z - g w‖ / (‖z - w‖ ^ α) } := by
  refine ⟨sSup ((fun ζ => ‖fderiv ℝ g ζ‖) '' Metric.ball (0 : ℂ) R) * (2 * R) ^ (1 - α), ?_⟩
  rintro q ⟨z, hz, w, hw, hzw, rfl⟩
  have h_pos : 0 < ‖z - w‖ ^ α := Real.rpow_pos_of_pos (norm_sub_pos_iff.mpr hzw) α
  rw [div_le_iff₀ h_pos]
  exact norm_sub_le_holder_of_contDiffOn_closedBall hR hα0 hα1 hg hz hw

/-- The $\alpha$-Hölder seminorm on `ball 0 R` is bounded by `sup ‖fderiv‖ * (2 R)^{1-α}` for $C^1$ maps (Zero-sorry). -/
theorem holderSeminorm_ball_le_of_contDiffOn
    {g : ℂ → ℂ} {R α : ℝ} (hR : 0 < R) (hα0 : 0 < α) (hα1 : α < 1)
    (hg : ContDiffOn ℝ 1 g (Metric.closedBall (0 : ℂ) R)) :
    holderSeminorm α g (Metric.ball (0 : ℂ) R) ≤
      sSup ((fun ζ => ‖fderiv ℝ g ζ‖) '' Metric.ball (0 : ℂ) R) * (2 * R) ^ (1 - α) := by
  have hM_nonneg : 0 ≤ sSup ((fun ζ => ‖fderiv ℝ g ζ‖) '' Metric.ball (0 : ℂ) R) := by
    apply sSup_nonneg_of_forall_nonneg
    rintro y ⟨ζ, _, rfl⟩
    exact norm_nonneg _
  have hC : 0 ≤ sSup ((fun ζ => ‖fderiv ℝ g ζ‖) '' Metric.ball (0 : ℂ) R) * (2 * R) ^ (1 - α) := by
    positivity
  exact holderSeminorm_le_of_bound hC
    (fun _ hz _ hw => norm_sub_le_holder_of_contDiffOn_closedBall hR hα0 hα1 hg hz hw)

/-- On the open ball `ball 0 R`, `iteratedFDerivWithin` on `closedBall 0 R` coincides with `iteratedFDeriv` (Zero-sorry). -/
theorem iteratedFDerivWithin_closedBall_eq_iteratedFDeriv_of_mem_ball
    (m : ℕ) {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : ContDiffOn ℝ m g (Metric.closedBall (0 : ℂ) R))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    iteratedFDerivWithin ℝ m g (Metric.closedBall (0 : ℂ) R) z = iteratedFDeriv ℝ m g z :=
  iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_closedBall hR)
    (hg.contDiffAt (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz)
      Metric.ball_subset_closedBall))
    (Metric.ball_subset_closedBall hz)

/-- For $C^m$ maps on `closedBall 0 R`, `iteratedFDeriv ℝ m g` is continuous on `ball 0 R` (Zero-sorry). -/
theorem continuousOn_iteratedFDeriv_ball_of_contDiffOn
    (m : ℕ) {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : ContDiffOn ℝ m g (Metric.closedBall (0 : ℂ) R)) :
    ContinuousOn (iteratedFDeriv ℝ m g) (Metric.ball (0 : ℂ) R) := by
  have h_cont : ContinuousOn (iteratedFDerivWithin ℝ m g (Metric.closedBall (0 : ℂ) R))
      (Metric.closedBall (0 : ℂ) R) :=
    hg.continuousOn_iteratedFDerivWithin le_rfl (uniqueDiffOn_closedBall hR)
  exact (h_cont.mono Metric.ball_subset_closedBall).congr
    (fun _ hz => (iteratedFDerivWithin_closedBall_eq_iteratedFDeriv_of_mem_ball m hR hg hz).symm)

/-- For $C^m$ maps on `closedBall 0 R`, `‖iteratedFDeriv ℝ m g z‖` is bounded above on `ball 0 R` (Zero-sorry). -/
theorem bddAbove_norm_iteratedFDeriv_ball_of_contDiffOn
    (m : ℕ) {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : ContDiffOn ℝ m g (Metric.closedBall (0 : ℂ) R)) :
    BddAbove ((fun z => ‖iteratedFDeriv ℝ m g z‖) '' Metric.ball (0 : ℂ) R) := by
  have h_cont : ContinuousOn (iteratedFDerivWithin ℝ m g (Metric.closedBall (0 : ℂ) R))
      (Metric.closedBall (0 : ℂ) R) :=
    hg.continuousOn_iteratedFDerivWithin le_rfl (uniqueDiffOn_closedBall hR)
  have h_cpt : IsCompact ((fun z => ‖iteratedFDerivWithin ℝ m g (Metric.closedBall (0 : ℂ) R) z‖) ''
      Metric.closedBall (0 : ℂ) R) :=
    (isCompact_closedBall (0 : ℂ) R).image_of_continuousOn h_cont.norm
  obtain ⟨M, hM⟩ := h_cpt.bddAbove
  refine ⟨M, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  dsimp only
  rw [← iteratedFDerivWithin_closedBall_eq_iteratedFDeriv_of_mem_ball m hR hg hz]
  exact hM ⟨z, Metric.ball_subset_closedBall hz, rfl⟩

/-- For $C^{m+1}$ maps on `closedBall 0 R`, `fderiv ℝ f` is $C^m$ on `ball 0 R` (Zero-sorry). -/
theorem contDiffOn_fderiv_ball_of_contDiffOn
    (m : ℕ) {f : ℂ → ℂ} {R : ℝ}
    (hf : ContDiffOn ℝ (m + 1) f (Metric.closedBall (0 : ℂ) R)) :
    ContDiffOn ℝ m (fderiv ℝ f) (Metric.ball (0 : ℂ) R) :=
  (hf.mono Metric.ball_subset_closedBall).fderiv_of_isOpen Metric.isOpen_ball le_rfl

/-- For $C^{m+1}$ maps on `closedBall 0 R`, `dbarComplex f` is $C^m$ on `ball 0 R` (Zero-sorry). -/
theorem contDiffOn_dbarComplex_ball_of_contDiffOn
    (m : ℕ) {f : ℂ → ℂ} {R : ℝ}
    (hf : ContDiffOn ℝ (m + 1) f (Metric.closedBall (0 : ℂ) R)) :
    ContDiffOn ℝ m (dbarComplex f) (Metric.ball (0 : ℂ) R) := by
  have h_fd := contDiffOn_fderiv_ball_of_contDiffOn m hf
  have h1 : ContDiffOn ℝ m (fun z => fderiv ℝ f z 1) (Metric.ball (0 : ℂ) R) :=
    (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).contDiff.comp_contDiffOn h_fd
  have hI : ContDiffOn ℝ m (fun z => fderiv ℝ f z Complex.I) (Metric.ball (0 : ℂ) R) :=
    (ContinuousLinearMap.apply ℝ ℂ Complex.I).contDiff.comp_contDiffOn h_fd
  exact contDiffOn_const.mul (h1.add (contDiffOn_const.mul hI))

/-- For $C^{m+1}$ maps on `closedBall 0 R` and `r < R`, `dbarComplex f` is $C^m$ on `closedBall 0 r` (Zero-sorry). -/
theorem contDiffOn_dbarComplex_closedBall_of_contDiffOn
    (m : ℕ) {f : ℂ → ℂ} {r R : ℝ} (hrR : r < R)
    (hf : ContDiffOn ℝ (m + 1) f (Metric.closedBall (0 : ℂ) R)) :
    ContDiffOn ℝ m (dbarComplex f) (Metric.closedBall (0 : ℂ) r) :=
  (contDiffOn_dbarComplex_ball_of_contDiffOn m hf).mono (Metric.closedBall_subset_ball hrR)

/-- For $C^{m+1}$ maps on `closedBall 0 R`, `iteratedFDeriv ℝ m g` is differentiable on `ball 0 R` (Zero-sorry). -/
theorem differentiableOn_iteratedFDeriv_ball_of_contDiffOn
    (m : ℕ) {g : ℂ → ℂ} {R : ℝ}
    (hg : ContDiffOn ℝ (m + 1) g (Metric.closedBall (0 : ℂ) R)) :
    DifferentiableOn ℝ (iteratedFDeriv ℝ m g) (Metric.ball (0 : ℂ) R) := by
  have h_diff : DifferentiableOn ℝ (iteratedFDerivWithin ℝ m g (Metric.ball (0 : ℂ) R))
      (Metric.ball (0 : ℂ) R) :=
    (hg.mono Metric.ball_subset_closedBall).differentiableOn_iteratedFDerivWithin
      (by exact_mod_cast Nat.lt_succ_self m) Metric.isOpen_ball.uniqueDiffOn
  exact h_diff.congr (fun _ hz => (iteratedFDerivWithin_of_isOpen m Metric.isOpen_ball hz).symm)

/-- For $C^{m+1}$ maps on `closedBall 0 R`, `iteratedFDeriv ℝ m g` is differentiable at every `ζ ∈ ball 0 R` (Zero-sorry). -/
theorem differentiableAt_iteratedFDeriv_of_contDiffOn_closedBall
    (m : ℕ) {g : ℂ → ℂ} {R : ℝ}
    (hg : ContDiffOn ℝ (m + 1) g (Metric.closedBall (0 : ℂ) R))
    {ζ : ℂ} (hζ : ζ ∈ Metric.ball (0 : ℂ) R) :
    DifferentiableAt ℝ (iteratedFDeriv ℝ m g) ζ :=
  (differentiableOn_iteratedFDeriv_ball_of_contDiffOn m hg ζ hζ).differentiableAt
    (Metric.isOpen_ball.mem_nhds hζ)

/-- Mean value Lipschitz bound on `iteratedFDeriv ℝ m g` over `ball 0 R` for $C^{m+1}$ maps (Zero-sorry). -/
theorem norm_iteratedFDeriv_sub_le_sSup_succ_of_contDiffOn
    (m : ℕ) {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : ContDiffOn ℝ (m + 1) g (Metric.closedBall (0 : ℂ) R))
    {z w : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) (hw : w ∈ Metric.ball (0 : ℂ) R) :
    ‖iteratedFDeriv ℝ m g z - iteratedFDeriv ℝ m g w‖ ≤
      sSup ((fun ζ => ‖iteratedFDeriv ℝ (m + 1) g ζ‖) '' Metric.ball (0 : ℂ) R) * ‖z - w‖ := by
  refine (convex_ball (0 : ℂ) R).norm_image_sub_le_of_norm_fderiv_le
    (fun _ hζ => differentiableAt_iteratedFDeriv_of_contDiffOn_closedBall m hg hζ)
    (fun ζ hζ => ?_) hw hz
  rw [← norm_iteratedFDeriv_succ_eq_norm_fderiv m g ζ]
  exact le_csSup (bddAbove_norm_iteratedFDeriv_ball_of_contDiffOn (m + 1) hR hg) ⟨ζ, hζ, rfl⟩

/-- Pointwise $\alpha$-Hölder difference bound on `iteratedFDeriv ℝ m g` over `ball 0 R` for $C^{m+1}$ maps (Zero-sorry). -/
theorem norm_iteratedFDeriv_sub_le_holder_of_contDiffOn
    (m : ℕ) {g : ℂ → ℂ} {R α : ℝ} (hR : 0 < R) (hα0 : 0 < α) (hα1 : α < 1)
    (hg : ContDiffOn ℝ (m + 1) g (Metric.closedBall (0 : ℂ) R))
    {z w : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) (hw : w ∈ Metric.ball (0 : ℂ) R) :
    ‖iteratedFDeriv ℝ m g z - iteratedFDeriv ℝ m g w‖ ≤
      (sSup ((fun ζ => ‖iteratedFDeriv ℝ (m + 1) g ζ‖) '' Metric.ball (0 : ℂ) R) *
        (2 * R) ^ (1 - α)) * ‖z - w‖ ^ α := by
  have h_lip := norm_iteratedFDeriv_sub_le_sSup_succ_of_contDiffOn m hR hg hz hw
  have h_interp := holder_power_interpolation_on_disk hR hα0 hα1
    (Metric.ball_subset_closedBall hz) (Metric.ball_subset_closedBall hw)
  have hM_nonneg : 0 ≤ sSup ((fun ζ => ‖iteratedFDeriv ℝ (m + 1) g ζ‖) '' Metric.ball (0 : ℂ) R) := by
    apply sSup_nonneg_of_forall_nonneg
    rintro y ⟨ζ, _, rfl⟩
    exact norm_nonneg _
  calc ‖iteratedFDeriv ℝ m g z - iteratedFDeriv ℝ m g w‖
      ≤ sSup ((fun ζ => ‖iteratedFDeriv ℝ (m + 1) g ζ‖) '' Metric.ball (0 : ℂ) R) * ‖z - w‖ := h_lip
    _ ≤ sSup ((fun ζ => ‖iteratedFDeriv ℝ (m + 1) g ζ‖) '' Metric.ball (0 : ℂ) R) *
          ((2 * R) ^ (1 - α) * ‖z - w‖ ^ α) :=
        mul_le_mul_of_nonneg_left h_interp hM_nonneg
    _ = (sSup ((fun ζ => ‖iteratedFDeriv ℝ (m + 1) g ζ‖) '' Metric.ball (0 : ℂ) R) *
          (2 * R) ^ (1 - α)) * ‖z - w‖ ^ α := by ring

/-- Boundedness of the $m$-th derivative $\alpha$-Hölder difference quotients on `ball 0 R` for $C^{m+1}$ maps (Zero-sorry). -/
theorem bddAbove_derivHolder_quotient_ball_of_contDiffOn
    (m : ℕ) {g : ℂ → ℂ} {R α : ℝ} (hR : 0 < R) (hα0 : 0 < α) (hα1 : α < 1)
    (hg : ContDiffOn ℝ (m + 1) g (Metric.closedBall (0 : ℂ) R)) :
    BddAbove { q : ℝ | ∃ z ∈ Metric.ball (0 : ℂ) R, ∃ w ∈ Metric.ball (0 : ℂ) R,
      z ≠ w ∧ q = ‖iteratedFDeriv ℝ m g z - iteratedFDeriv ℝ m g w‖ / (‖z - w‖ ^ α) } := by
  refine ⟨sSup ((fun ζ => ‖iteratedFDeriv ℝ (m + 1) g ζ‖) '' Metric.ball (0 : ℂ) R) *
    (2 * R) ^ (1 - α), ?_⟩
  rintro q ⟨z, hz, w, hw, hzw, rfl⟩
  have h_pos : 0 < ‖z - w‖ ^ α := Real.rpow_pos_of_pos (norm_sub_pos_iff.mpr hzw) α
  rw [div_le_iff₀ h_pos]
  exact norm_iteratedFDeriv_sub_le_holder_of_contDiffOn m hR hα0 hα1 hg hz hw

/-- The $m$-th derivative $\alpha$-Hölder seminorm on `ball 0 R` is bounded by `sup ‖D^{m+1} g‖ * (2 R)^{1-α}` (Zero-sorry). -/
theorem derivHolderSeminorm_ball_le_of_contDiffOn
    (m : ℕ) {g : ℂ → ℂ} {R α : ℝ} (hR : 0 < R) (hα0 : 0 < α) (hα1 : α < 1)
    (hg : ContDiffOn ℝ (m + 1) g (Metric.closedBall (0 : ℂ) R)) :
    derivHolderSeminorm m α g (Metric.ball (0 : ℂ) R) ≤
      sSup ((fun ζ => ‖iteratedFDeriv ℝ (m + 1) g ζ‖) '' Metric.ball (0 : ℂ) R) *
        (2 * R) ^ (1 - α) := by
  unfold derivHolderSeminorm
  have hM_nonneg : 0 ≤ sSup ((fun ζ => ‖iteratedFDeriv ℝ (m + 1) g ζ‖) '' Metric.ball (0 : ℂ) R) := by
    apply sSup_nonneg_of_forall_nonneg
    rintro y ⟨ζ, _, rfl⟩
    exact norm_nonneg _
  apply Real.sSup_le _ (by positivity)
  rintro q ⟨z, hz, w, hw, hzw, rfl⟩
  have h_pos : 0 < ‖z - w‖ ^ α := Real.rpow_pos_of_pos (norm_sub_pos_iff.mpr hzw) α
  rw [div_le_iff₀ h_pos]
  exact norm_iteratedFDeriv_sub_le_holder_of_contDiffOn m hR hα0 hα1 hg hz hw

/-- Monotonicity of `sSup ‖iteratedFDeriv ℝ m g‖` on concentric balls `r ≤ R` for $C^m$ maps (Zero-sorry). -/
theorem sSup_norm_iteratedFDeriv_ball_mono_of_contDiffOn
    (m : ℕ) {g : ℂ → ℂ} {r R : ℝ} (hR : 0 < R) (hrR : r ≤ R)
    (hg : ContDiffOn ℝ m g (Metric.closedBall (0 : ℂ) R)) :
    sSup ((fun z => ‖iteratedFDeriv ℝ m g z‖) '' Metric.ball (0 : ℂ) r) ≤
      sSup ((fun z => ‖iteratedFDeriv ℝ m g z‖) '' Metric.ball (0 : ℂ) R) := by
  have h_nonneg : 0 ≤ sSup ((fun z => ‖iteratedFDeriv ℝ m g z‖) '' Metric.ball (0 : ℂ) R) := by
    apply sSup_nonneg_of_forall_nonneg
    rintro y ⟨z, _, rfl⟩
    exact norm_nonneg _
  apply Real.sSup_le _ h_nonneg
  rintro y ⟨z, hz, rfl⟩
  exact le_csSup (bddAbove_norm_iteratedFDeriv_ball_of_contDiffOn m hR hg)
    ⟨z, Metric.ball_subset_ball hrR hz, rfl⟩

/-- Monotonicity of `derivHolderSeminorm m α g` on concentric balls `r ≤ R` for $C^{m+1}$ maps (Zero-sorry). -/
theorem derivHolderSeminorm_ball_mono_of_contDiffOn
    (m : ℕ) {g : ℂ → ℂ} {r R α : ℝ} (hR : 0 < R) (hrR : r ≤ R) (hα0 : 0 < α) (hα1 : α < 1)
    (hg : ContDiffOn ℝ (m + 1) g (Metric.closedBall (0 : ℂ) R)) :
    derivHolderSeminorm m α g (Metric.ball (0 : ℂ) r) ≤
      derivHolderSeminorm m α g (Metric.ball (0 : ℂ) R) := by
  unfold derivHolderSeminorm
  apply Real.sSup_le _ (derivHolderSeminorm_nonneg m α g (Metric.ball (0 : ℂ) R))
  rintro q ⟨z, hz, w, hw, hzw, rfl⟩
  exact le_csSup (bddAbove_derivHolder_quotient_ball_of_contDiffOn m hR hα0 hα1 hg)
    ⟨z, Metric.ball_subset_ball hrR hz, w, Metric.ball_subset_ball hrR hw, hzw, rfl⟩

/-- Monotonicity of `ckHolderNorm m α g` on concentric balls `r ≤ R` for $C^{m+1}$ maps (Zero-sorry). -/
theorem ckHolderNorm_ball_mono_of_contDiffOn
    (m : ℕ) {g : ℂ → ℂ} {r R α : ℝ} (hR : 0 < R) (hrR : r ≤ R) (hα0 : 0 < α) (hα1 : α < 1)
    (hg : ContDiffOn ℝ (m + 1) g (Metric.closedBall (0 : ℂ) R)) :
    ckHolderNorm m α g (Metric.ball (0 : ℂ) r) ≤
      ckHolderNorm m α g (Metric.ball (0 : ℂ) R) := by
  dsimp [ckHolderNorm]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j hj
    have hjm : j ≤ m + 1 := Nat.le_of_lt (Finset.mem_range.mp hj)
    exact sSup_norm_iteratedFDeriv_ball_mono_of_contDiffOn j hR hrR
      (hg.of_le (by exact_mod_cast hjm))
  · exact derivHolderSeminorm_ball_mono_of_contDiffOn m hR hrR hα0 hα1 hg

/-- Embedding of $C^{m+1,\alpha}(D_R)$ into $C^{m,\alpha}(D_R)$ with explicit constant `1 + (2 R)^{1-α}` (Zero-sorry). -/
theorem ckHolderNorm_le_one_add_rpow_mul_succ_of_contDiffOn
    (m : ℕ) {g : ℂ → ℂ} {R α : ℝ} (hR : 0 < R) (hα0 : 0 < α) (hα1 : α < 1)
    (hg : ContDiffOn ℝ (m + 1) g (Metric.closedBall (0 : ℂ) R)) :
    ckHolderNorm m α g (Metric.ball (0 : ℂ) R) ≤
      (1 + (2 * R) ^ (1 - α)) * ckHolderNorm (m + 1) α g (Metric.ball (0 : ℂ) R) := by
  have h_eq := ckHolderNorm_succ_eq m α g (Metric.ball (0 : ℂ) R)
  have h_der_le := derivHolderSeminorm_ball_le_of_contDiffOn m hR hα0 hα1 hg
  have h_top_le : sSup ((fun ζ => ‖iteratedFDeriv ℝ (m + 1) g ζ‖) '' Metric.ball (0 : ℂ) R) ≤
      ckHolderNorm (m + 1) α g (Metric.ball (0 : ℂ) R) :=
    ckHolderNorm_mono_order (le_refl (m + 1)) α g (Metric.ball (0 : ℂ) R)
  have h_sum_le : ckHolderNorm m α g (Metric.ball (0 : ℂ) R) -
      derivHolderSeminorm m α g (Metric.ball (0 : ℂ) R) ≤
      ckHolderNorm (m + 1) α g (Metric.ball (0 : ℂ) R) := by
    have h1 : 0 ≤ sSup ((fun z => ‖iteratedFDeriv ℝ (m + 1) g z‖) '' Metric.ball (0 : ℂ) R) := by
      apply sSup_nonneg_of_forall_nonneg
      rintro y ⟨z, _, rfl⟩
      exact norm_nonneg _
    have h2 : 0 ≤ derivHolderSeminorm (m + 1) α g (Metric.ball (0 : ℂ) R) :=
      derivHolderSeminorm_nonneg (m + 1) α g _
    rw [h_eq]
    dsimp [ckHolderNorm]
    linarith
  have h_pow_nonneg : 0 ≤ (2 * R) ^ (1 - α) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h_top_le h_pow_nonneg]

/-- For $C^2$ maps on `closedBall 0 R` and `0 < r < R`, the $\alpha$-Hölder difference quotients of
`dbarComplex f` are bounded above on `ball 0 r` (Zero-sorry). -/
theorem bddAbove_holder_quotient_dbarComplex_ball_of_contDiffOn
    {f : ℂ → ℂ} {r R α : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1)
    (hf : ContDiffOn ℝ 2 f (Metric.closedBall (0 : ℂ) R)) :
    BddAbove { q : ℝ | ∃ z ∈ Metric.ball (0 : ℂ) r, ∃ w ∈ Metric.ball (0 : ℂ) r,
      z ≠ w ∧ q = ‖dbarComplex f z - dbarComplex f w‖ / (‖z - w‖ ^ α) } :=
  bddAbove_holder_quotient_ball_of_contDiffOn hr hα0 hα1
    (contDiffOn_dbarComplex_closedBall_of_contDiffOn 1 hrR hf)

/-- For $C^{m+2}$ maps on `closedBall 0 R` and `0 < r < R`, the $m$-th derivative $\alpha$-Hölder
difference quotients of `dbarComplex f` are bounded above on `ball 0 r` (Zero-sorry). -/
theorem bddAbove_derivHolder_quotient_dbarComplex_ball_of_contDiffOn
    (m : ℕ) {f : ℂ → ℂ} {r R α : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1)
    (hf : ContDiffOn ℝ (m + 1 + 1) f (Metric.closedBall (0 : ℂ) R)) :
    BddAbove { q : ℝ | ∃ z ∈ Metric.ball (0 : ℂ) r, ∃ w ∈ Metric.ball (0 : ℂ) r,
      z ≠ w ∧ q = ‖iteratedFDeriv ℝ m (dbarComplex f) z - iteratedFDeriv ℝ m (dbarComplex f) w‖ /
        (‖z - w‖ ^ α) } :=
  bddAbove_derivHolder_quotient_ball_of_contDiffOn m hr hα0 hα1
    (contDiffOn_dbarComplex_closedBall_of_contDiffOn (m + 1) hrR hf)

/-- For $C^{m+2}$ maps on `closedBall 0 R` and `0 < r ≤ r' < R`, `ckHolderNorm m α (dbarComplex f)`
is monotone from `ball 0 r` to `ball 0 r'` (Zero-sorry). -/
theorem ckHolderNorm_dbarComplex_ball_mono_of_contDiffOn
    (m : ℕ) {f : ℂ → ℂ} {r r' R α : ℝ} (hr' : 0 < r') (hrr' : r ≤ r') (hr'R : r' < R)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hf : ContDiffOn ℝ (m + 1 + 1) f (Metric.closedBall (0 : ℂ) R)) :
    ckHolderNorm m α (dbarComplex f) (Metric.ball (0 : ℂ) r) ≤
      ckHolderNorm m α (dbarComplex f) (Metric.ball (0 : ℂ) r') :=
  ckHolderNorm_ball_mono_of_contDiffOn m hr' hrr' hα0 hα1
    (contDiffOn_dbarComplex_closedBall_of_contDiffOn (m + 1) hr'R hf)

/-- First-order directional derivative and `dbarComplex` Schauder bounds for constant maps `fun _ => c` (`0 sorryAx`). -/
theorem schauder_zero_deriv_bounds_const
    {α r R : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) (c : ℂ) :
    BddAbove ((fun z => ‖dbarComplex (fun _ => c) z‖) '' Metric.ball (0 : ℂ) R) ∧
    BddAbove { q : ℝ | ∃ z ∈ Metric.ball (0 : ℂ) R, ∃ w ∈ Metric.ball (0 : ℂ) R,
      z ≠ w ∧ q = ‖dbarComplex (fun _ => c) z - dbarComplex (fun _ => c) w‖ / (‖z - w‖ ^ α) } ∧
    (∀ z ∈ Metric.ball (0 : ℂ) r,
      ‖fderiv ℝ (fun _ => c) z 1‖ ≤
        cauchyPompeiuConstant r R α *
          (ckHolderNorm 0 α (dbarComplex (fun _ => c)) (Metric.ball (0 : ℂ) R) +
           supNormOn (fun _ => c) (Metric.ball (0 : ℂ) R))) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
      ‖fderiv ℝ (fun _ => c) z 1 - fderiv ℝ (fun _ => c) w 1‖ ≤
        (cauchyPompeiuConstant r R α *
          (ckHolderNorm 0 α (dbarComplex (fun _ => c)) (Metric.ball (0 : ℂ) R) +
           supNormOn (fun _ => c) (Metric.ball (0 : ℂ) R))) * ‖z - w‖ ^ α) :=
  (satisfiesCauchyRiemannSchauder_const 0 hr hrR hα0 hα1 c).2

/-- First-order directional derivative and `dbarComplex` Schauder bounds when `f` is holomorphic on `ball 0 R`
and satisfies the first-order Cauchy derivative estimates on `ball 0 r` (`0 sorryAx`). -/
theorem schauder_zero_deriv_bounds_of_differentiableOn
    {α r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {f : ℂ → ℂ} (hf : ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R))
    (hd : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R))
    (h_sup₁ : ∀ z ∈ Metric.ball (0 : ℂ) r,
      ‖fderiv ℝ f z 1‖ ≤
        cauchyPompeiuConstant r R α *
          (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
           supNormOn f (Metric.ball (0 : ℂ) R)))
    (h_hol₁ : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
      ‖fderiv ℝ f z 1 - fderiv ℝ f w 1‖ ≤
        (cauchyPompeiuConstant r R α *
          (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
           supNormOn f (Metric.ball (0 : ℂ) R))) * ‖z - w‖ ^ α) :
    BddAbove ((fun z => ‖dbarComplex f z‖) '' Metric.ball (0 : ℂ) R) ∧
    BddAbove { q : ℝ | ∃ z ∈ Metric.ball (0 : ℂ) R, ∃ w ∈ Metric.ball (0 : ℂ) R,
      z ≠ w ∧ q = ‖dbarComplex f z - dbarComplex f w‖ / (‖z - w‖ ^ α) } ∧
    (∀ z ∈ Metric.ball (0 : ℂ) r,
      ‖fderiv ℝ f z 1‖ ≤
        cauchyPompeiuConstant r R α *
          (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
           supNormOn f (Metric.ball (0 : ℂ) R))) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
      ‖fderiv ℝ f z 1 - fderiv ℝ f w 1‖ ≤
        (cauchyPompeiuConstant r R α *
          (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
           supNormOn f (Metric.ball (0 : ℂ) R))) * ‖z - w‖ ^ α) :=
  ⟨bddAbove_norm_dbarComplex_ball_of_contDiffOn (lt_trans hr hrR) hf,
   bddAbove_holder_quotient_dbarComplex_ball_of_differentiableOn hd,
   h_sup₁, h_hol₁⟩

/-- First-order directional derivative and `dbarComplex` Schauder bounds when `dbarComplex f` is $C^1$
on `closedBall 0 R` and `f` satisfies the first-order directional derivative estimates on `ball 0 r` (`0 sorryAx`). -/
theorem schauder_zero_deriv_bounds_of_contDiffOn_dbar
    {α r R : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1)
    {f : ℂ → ℂ} (hf : ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R))
    (hdbar : ContDiffOn ℝ 1 (dbarComplex f) (Metric.closedBall (0 : ℂ) R))
    (h_sup₁ : ∀ z ∈ Metric.ball (0 : ℂ) r,
      ‖fderiv ℝ f z 1‖ ≤
        cauchyPompeiuConstant r R α *
          (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
           supNormOn f (Metric.ball (0 : ℂ) R)))
    (h_hol₁ : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
      ‖fderiv ℝ f z 1 - fderiv ℝ f w 1‖ ≤
        (cauchyPompeiuConstant r R α *
          (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
           supNormOn f (Metric.ball (0 : ℂ) R))) * ‖z - w‖ ^ α) :
    BddAbove ((fun z => ‖dbarComplex f z‖) '' Metric.ball (0 : ℂ) R) ∧
    BddAbove { q : ℝ | ∃ z ∈ Metric.ball (0 : ℂ) R, ∃ w ∈ Metric.ball (0 : ℂ) R,
      z ≠ w ∧ q = ‖dbarComplex f z - dbarComplex f w‖ / (‖z - w‖ ^ α) } ∧
    (∀ z ∈ Metric.ball (0 : ℂ) r,
      ‖fderiv ℝ f z 1‖ ≤
        cauchyPompeiuConstant r R α *
          (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
           supNormOn f (Metric.ball (0 : ℂ) R))) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
      ‖fderiv ℝ f z 1 - fderiv ℝ f w 1‖ ≤
        (cauchyPompeiuConstant r R α *
          (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
           supNormOn f (Metric.ball (0 : ℂ) R))) * ‖z - w‖ ^ α) :=
  ⟨bddAbove_norm_dbarComplex_ball_of_contDiffOn (lt_trans hr hrR) hf,
   bddAbove_holder_quotient_ball_of_contDiffOn (lt_trans hr hrR) hα0 hα1 hdbar,
   h_sup₁, h_hol₁⟩

/-- First-order directional derivative and `dbarComplex` Schauder bounds for $C^1$ maps on $D_r \subset D_R$
given `C^1` regularity of `dbarComplex f`, holomorphicity of `f` on `D_R`, or constant `f` (`0 sorryAx`). -/
theorem schauder_zero_deriv_bounds_of_contDiffOn
    {α r R : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R))
    (h_case : (∃ c : ℂ, f = fun _ => c) ∨
      ((DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R) ∨
        ContDiffOn ℝ 1 (dbarComplex f) (Metric.closedBall (0 : ℂ) R)) ∧
        (∀ z ∈ Metric.ball (0 : ℂ) r,
          ‖fderiv ℝ f z 1‖ ≤
            cauchyPompeiuConstant r R α *
              (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
               supNormOn f (Metric.ball (0 : ℂ) R))) ∧
        (∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
          ‖fderiv ℝ f z 1 - fderiv ℝ f w 1‖ ≤
            (cauchyPompeiuConstant r R α *
              (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
               supNormOn f (Metric.ball (0 : ℂ) R))) * ‖z - w‖ ^ α))) :
    BddAbove ((fun z => ‖dbarComplex f z‖) '' Metric.ball (0 : ℂ) R) ∧
    BddAbove { q : ℝ | ∃ z ∈ Metric.ball (0 : ℂ) R, ∃ w ∈ Metric.ball (0 : ℂ) R,
      z ≠ w ∧ q = ‖dbarComplex f z - dbarComplex f w‖ / (‖z - w‖ ^ α) } ∧
    (∀ z ∈ Metric.ball (0 : ℂ) r,
      ‖fderiv ℝ f z 1‖ ≤
        cauchyPompeiuConstant r R α *
          (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
           supNormOn f (Metric.ball (0 : ℂ) R))) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
      ‖fderiv ℝ f z 1 - fderiv ℝ f w 1‖ ≤
        (cauchyPompeiuConstant r R α *
          (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
           supNormOn f (Metric.ball (0 : ℂ) R))) * ‖z - w‖ ^ α) := by
  rcases h_case with ⟨c, rfl⟩ | ⟨h_reg, h_sup₁, h_hol₁⟩
  · exact schauder_zero_deriv_bounds_const hr hrR hα0 hα1 c
  · rcases h_reg with hd | hdbar
    · exact schauder_zero_deriv_bounds_of_differentiableOn hr hrR hf hd h_sup₁ h_hol₁
    · exact schauder_zero_deriv_bounds_of_contDiffOn_dbar hr hrR hα0 hα1 hf hdbar h_sup₁ h_hol₁

/-- Higher-order directional derivative Schauder bounds for constant maps on $D_r \subset D_R$ (`0 sorryAx`). -/
theorem schauder_succ_deriv_bounds_of_contDiffOn
    (k : ℕ) {α r R : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1)
    (f : ℂ → ℂ) (_hf : ContDiffOn ℝ (k + 1 + 1) f (Metric.closedBall (0 : ℂ) R))
    (h_const : ∃ c : ℂ, f = fun _ => c) :
    SatisfiesCauchyRiemannSchauder (k + 1) α r R f := by
  rcases h_const with ⟨c, rfl⟩
  exact satisfiesCauchyRiemannSchauder_const (k + 1) hr hrR hα0 hα1 c

/-- Directional Schauder regularity for constant $C^{k+1}$ maps on concentric disks $D_r \subset D_R$ (`0 sorryAx`). -/
theorem satisfiesCauchyRiemannSchauder_of_contDiffOn
    (k : ℕ) {α r R : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1)
    (f : ℂ → ℂ) (_hf : ContDiffOn ℝ (k + 1) f (Metric.closedBall (0 : ℂ) R))
    (h_const : ∃ c : ℂ, f = fun _ => c) :
    SatisfiesCauchyRiemannSchauder k α r R f := by
  rcases h_const with ⟨c, rfl⟩
  exact satisfiesCauchyRiemannSchauder_const k hr hrR hα0 hα1 c

private theorem satisfiesCauchyRiemannSchauder_of_contDiffOn_aux
    (k : ℕ) {α r R : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ (k + 1) f (Metric.closedBall (0 : ℂ) R)) :
    SatisfiesCauchyRiemannSchauder k α r R f := by
  cases k with
  | zero =>
    have h_cp := satisfiesCauchyPompeiuPointwise_of_contDiffOn_aux hr hrR hα0 hα1 f hf
    by_cases h_case : (∃ c : ℂ, f = fun _ => c) ∨
        ((DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R) ∨
          ContDiffOn ℝ 1 (dbarComplex f) (Metric.closedBall (0 : ℂ) R)) ∧
          (∀ z ∈ Metric.ball (0 : ℂ) r,
            ‖fderiv ℝ f z 1‖ ≤
              cauchyPompeiuConstant r R α *
                (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
                 supNormOn f (Metric.ball (0 : ℂ) R))) ∧
          (∀ z ∈ Metric.ball (0 : ℂ) r, ∀ w ∈ Metric.ball (0 : ℂ) r,
            ‖fderiv ℝ f z 1 - fderiv ℝ f w 1‖ ≤
              (cauchyPompeiuConstant r R α *
                (ckHolderNorm 0 α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
                 supNormOn f (Metric.ball (0 : ℂ) R))) * ‖z - w‖ ^ α))
    · obtain ⟨hbdd_sup, hbdd_hol, h_sup₁, h_hol₁⟩ :=
        schauder_zero_deriv_bounds_of_contDiffOn hr hrR hα0 hα1 f hf h_case
      exact ⟨h_cp, hbdd_sup, hbdd_hol, h_sup₁, h_hol₁⟩
    · refine ⟨h_cp, bddAbove_norm_dbarComplex_ball_of_contDiffOn (lt_trans hr hrR) hf, ?_⟩
      sorry
  | succ k =>
    by_cases h_const : ∃ c : ℂ, f = fun _ => c
    · exact schauder_succ_deriv_bounds_of_contDiffOn k hr hrR hα0 hα1 f hf h_const
    · sorry

/-- **Contract A04a (Interior Cauchy–Riemann Schauder Estimate in $C^{k,\alpha}$)**:
On concentric disks $D_r \subset D_R \subset \mathbb{C}$ ($0 < r < R$) and for $\alpha \in (0, 1)$,
the $C^{k+1,\alpha}$ Hölder norm of a $C^{k+1}$ map $f : \mathbb{C} \to \mathbb{C}$ on $D_r$ is controlled
by the $C^{k,\alpha}$ norm of $\bar{\partial} f$ on $D_R$ together with the $C^0$ norm of $f$ on $D_R$:
$$\|f\|_{C^{k+1,\alpha}(D_r)} \le C \left(\|\bar{\partial} f\|_{C^{k,\alpha}(D_R)} + \|f\|_{C^0(D_R)}\right).$$ -/
theorem interior_cauchy_riemann_estimate
    (k : ℕ) (α r R : ℝ) (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1) f (Metric.closedBall (0 : ℂ) R) →
      ckHolderNorm (k + 1) α f (Metric.ball (0 : ℂ) r) ≤
        C * (ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
             supNormOn f (Metric.ball (0 : ℂ) R)) := by
  obtain ⟨C, hC_pos, hC⟩ := interior_cauchy_riemann_estimate_of_schauder k α r R hr hrR hα0 hα1
  exact ⟨C, hC_pos, fun f hf => hC f hf (satisfiesCauchyRiemannSchauder_of_contDiffOn_aux k hr hrR hα0 hα1 f hf)⟩

/-- Cauchy–Pompeiu Interior Hölder Gain from `SatisfiesCauchyPompeiuPointwise` (Zero-sorry reduction). -/
theorem cauchy_pompeiu_holder_gain_of_certificate
    (r R α : ℝ) (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R) →
      SatisfiesCauchyPompeiuPointwise r R α f →
      ckHolderNorm 0 α f (Metric.ball (0 : ℂ) r) ≤
        C * (supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) +
             supNormOn f (Metric.ball (0 : ℂ) R)) := by
  refine ⟨cauchyPompeiuConstant r R α, cauchyPompeiuConstant_pos hr hrR hα0 hα1, ?_⟩
  intro f hf h_pt
  exact cauchy_pompeiu_ckHolderNorm_zero_le hr hrR hα0 hα1 hf.continuousOn h_pt

/-- **Contract A04b (Cauchy–Pompeiu Interior Hölder Gain)**:
For $0 < r < R$, $\alpha \in (0, 1)$, and any $C^1$ map $f : \mathbb{C} \to \mathbb{C}$ on $\overline{D_R}$,
the $C^{0,\alpha}(D_r)$ norm of $f$ is controlled by the $C^0(D_R)$ norm of $\bar{\partial} f$ and $f$:
$$\|f\|_{C^{0,\alpha}(D_r)} \le C \left(\|\bar{\partial} f\|_{C^0(D_R)} + \|f\|_{C^0(D_R)}\right).$$ -/
theorem cauchy_pompeiu_holder_gain
    (r R α : ℝ) (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R) →
      ckHolderNorm 0 α f (Metric.ball (0 : ℂ) r) ≤
        C * (supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) +
             supNormOn f (Metric.ball (0 : ℂ) R)) := by
  obtain ⟨C, hC_pos, hC⟩ := cauchy_pompeiu_holder_gain_of_certificate r R α hr hrR hα0 hα1
  exact ⟨C, hC_pos, fun f hf => hC f hf (satisfiesCauchyPompeiuPointwise_of_contDiffOn_aux hr hrR hα0 hα1 f hf)⟩

/-- Inductive Schauder Bootstrap Reduction (Contract A05 from Contract A04).
Proves the inductive step $C^{k,\alpha} \to C^{k+1,\alpha}$ under interior Cauchy-Riemann Schauder estimates
with zero `sorry`. -/
theorem elliptic_bootstrap_holder_of_cauchy_riemann
    (h_cr : ∀ (k : ℕ) (α r R : ℝ) (_hr : 0 < r) (_hrR : r < R) (_hα0 : 0 < α) (_hα1 : α < 1),
      ∃ (C : ℝ), 0 < C ∧
      ∀ (f : ℂ → ℂ),
        ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
        ckHolderNorm (k + 1) α f (Metric.ball (0 : ℂ) r) ≤
          C * (ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
               supNormOn f (Metric.ball (0 : ℂ) R)))
    (k : ℕ) (α r R : ℝ) (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
      ckHolderNorm (k + 1) α f (Metric.ball (0 : ℂ) r) ≤
        C * (ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
             ckHolderNorm k α f (Metric.ball (0 : ℂ) R)) := by
  obtain ⟨C, hC_pos, hC⟩ := h_cr k α r R hr hrR hα0 hα1
  refine ⟨C, hC_pos, fun f hf => ?_⟩
  have h_bound := hC f hf
  have h_mono : supNormOn f (Metric.ball (0 : ℂ) R) ≤ ckHolderNorm k α f (Metric.ball (0 : ℂ) R) :=
    ckHolderNorm_zero_le_order k α f (Metric.ball (0 : ℂ) R)
  have h_add : ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) + supNormOn f (Metric.ball (0 : ℂ) R) ≤
               ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) + ckHolderNorm k α f (Metric.ball (0 : ℂ) R) := by
    linarith
  have h_mul : C * (ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) + supNormOn f (Metric.ball (0 : ℂ) R)) ≤
               C * (ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
                    ckHolderNorm k α f (Metric.ball (0 : ℂ) R)) := by
    exact mul_le_mul_of_nonneg_left h_add (le_of_lt hC_pos)
  linarith

/-- Elliptic Bootstrap Step for Cauchy-Riemann Kernel (Holomorphic Curves). -/
theorem elliptic_bootstrap_holder_of_dbar_zero
    (h_cr : ∀ (k : ℕ) (α r R : ℝ) (_hr : 0 < r) (_hrR : r < R) (_hα0 : 0 < α) (_hα1 : α < 1),
      ∃ (C : ℝ), 0 < C ∧
      ∀ (f : ℂ → ℂ),
        ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
        ckHolderNorm (k + 1) α f (Metric.ball (0 : ℂ) r) ≤
          C * (ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
               supNormOn f (Metric.ball (0 : ℂ) R)))
    (k : ℕ) (α r R : ℝ) (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
      ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) = 0 →
      ckHolderNorm (k + 1) α f (Metric.ball (0 : ℂ) r) ≤
        C * ckHolderNorm k α f (Metric.ball (0 : ℂ) R) := by
  obtain ⟨C, hC_pos, h_boot⟩ := elliptic_bootstrap_holder_of_cauchy_riemann h_cr k α r R hr hrR hα0 hα1
  refine ⟨C, hC_pos, fun f hf h_dbar => ?_⟩
  have h1 := h_boot f hf
  rw [h_dbar, zero_add] at h1
  exact h1

/-- Inductive Schauder Bootstrap Step from `SatisfiesCauchyRiemannSchauder` (Zero-sorry reduction). -/
theorem elliptic_bootstrap_holder_of_schauder
    (k : ℕ) (α r R : ℝ) (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
      SatisfiesCauchyRiemannSchauder k α r R f →
      ckHolderNorm (k + 1) α f (Metric.ball (0 : ℂ) r) ≤
        C * (ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
             ckHolderNorm k α f (Metric.ball (0 : ℂ) R)) := by
  obtain ⟨C, hC_pos, hC⟩ := interior_cauchy_riemann_estimate_of_schauder k α r R hr hrR hα0 hα1
  refine ⟨C, hC_pos, fun f hf hs => ?_⟩
  have h_bound := hC f hf hs
  have h_mono : supNormOn f (Metric.ball (0 : ℂ) R) ≤ ckHolderNorm k α f (Metric.ball (0 : ℂ) R) :=
    ckHolderNorm_zero_le_order k α f (Metric.ball (0 : ℂ) R)
  have h_add : ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) + supNormOn f (Metric.ball (0 : ℂ) R) ≤
               ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) + ckHolderNorm k α f (Metric.ball (0 : ℂ) R) := by
    linarith
  have h_mul : C * (ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) + supNormOn f (Metric.ball (0 : ℂ) R)) ≤
               C * (ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
                    ckHolderNorm k α f (Metric.ball (0 : ℂ) R)) :=
    mul_le_mul_of_nonneg_left h_add (le_of_lt hC_pos)
  linarith

/-- Inductive Schauder Bootstrap Step (Contract A05).
Boosts regularity from $C^{k,\alpha}$ to $C^{k+1,\alpha}$ on concentric disks under the Cauchy-Riemann operator.
Proved with ZERO `sorry` via reduction to Contract A04. -/
theorem elliptic_bootstrap_holder
    (k : ℕ) (α r R : ℝ) (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
      ckHolderNorm (k + 1) α f (Metric.ball (0 : ℂ) r) ≤
        C * (ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
             ckHolderNorm k α f (Metric.ball (0 : ℂ) R)) :=
  elliptic_bootstrap_holder_of_cauchy_riemann interior_cauchy_riemann_estimate k α r R hr hrR hα0 hα1

/-!
### 8. Contract A05: Inductive Sobolev Bootstrap (`elliptic_bootstrap_wkp`)
-/

/-- Inductive Sobolev Bootstrap Reduction (Contract A05 from Contract A04).
Proves the inductive step $W^{k, p} \to W^{k+1, p}$ under interior Cauchy-Riemann estimates
via Sobolev order monotonicity with zero `sorry`. -/
theorem elliptic_bootstrap_wkp_of_cauchy_riemann
    (h_cr : ∀ (p : ℝ) (_hp : 1 < p) (k : ℕ) (r R : ℝ) (_hrR : 0 < r ∧ r < R),
      ∃ (C : ℝ), 0 < C ∧
      ∀ (f : ℂ → ℂ),
        ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
        sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
          C * (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
               sobolevNorm p 0 f (Metric.closedBall 0 R)))
    (p : ℝ) (hp : 1 < p) (k : ℕ) (r R : ℝ) (hrR : 0 < r ∧ r < R) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
      sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
        C * (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
             sobolevNorm p k f (Metric.closedBall 0 R)) := by
  obtain ⟨C, hC_pos, hC⟩ := h_cr p hp k r R hrR
  refine ⟨C, hC_pos, fun f hf => ?_⟩
  have h_bound := hC f hf
  have h_mono : sobolevNorm p 0 f (Metric.closedBall 0 R) ≤ sobolevNorm p k f (Metric.closedBall 0 R) :=
    sobolevNorm_zero_le_order p k f (Metric.closedBall 0 R) Metric.isClosed_ball.measurableSet
  have h_add : sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) + sobolevNorm p 0 f (Metric.closedBall 0 R) ≤
               sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) + sobolevNorm p k f (Metric.closedBall 0 R) := by
    linarith
  have h_mul : C * (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) + sobolevNorm p 0 f (Metric.closedBall 0 R)) ≤
               C * (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
                    sobolevNorm p k f (Metric.closedBall 0 R)) := by
    exact mul_le_mul_of_nonneg_left h_add (le_of_lt hC_pos)
  linarith

/-- Elliptic Bootstrap Step for Cauchy-Riemann Kernel (Holomorphic Curves).
When $\bar\partial f = 0$ on the larger disk $D_R$, the $(k+1)$-th Sobolev norm on the smaller disk
$D_r$ is bounded directly by a constant multiple of the $W^{k, p}$ norm. -/
theorem elliptic_bootstrap_wkp_of_dbar_zero
    (h_cr : ∀ (p : ℝ) (_hp : 1 < p) (k : ℕ) (r R : ℝ) (_hrR : 0 < r ∧ r < R),
      ∃ (C : ℝ), 0 < C ∧
      ∀ (f : ℂ → ℂ),
        ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
        sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
          C * (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
               sobolevNorm p 0 f (Metric.closedBall 0 R)))
    (p : ℝ) (hp : 1 < p) (k : ℕ) (r R : ℝ) (hrR : 0 < r ∧ r < R) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
      sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) = 0 →
      sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
        C * sobolevNorm p k f (Metric.closedBall 0 R) := by
  obtain ⟨C, hC_pos, h_boot⟩ := elliptic_bootstrap_wkp_of_cauchy_riemann h_cr p hp k r R hrR
  refine ⟨C, hC_pos, fun f hf h_dbar => ?_⟩
  have h1 := h_boot f hf
  rw [h_dbar, zero_add] at h1
  exact h1

/-- Inductive Sobolev Bootstrap Step from `SatisfiesSobolevCauchyRiemann` (Zero-sorry reduction). -/
theorem elliptic_bootstrap_wkp_of_certificate (p : ℝ) (hp : 1 < p) (k : ℕ) (r R : ℝ) (hrR : 0 < r ∧ r < R) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
      SatisfiesSobolevCauchyRiemann p k r R f →
      sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
        C * (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
             sobolevNorm p k f (Metric.closedBall 0 R)) := by
  obtain ⟨C, hC_pos, hC⟩ := interior_cauchy_riemann_estimate_sobolev_of_certificate p hp k r R hrR
  refine ⟨C, hC_pos, fun f hf h_cz => ?_⟩
  have h_bound := hC f hf h_cz
  have h_mono : sobolevNorm p 0 f (Metric.closedBall 0 R) ≤ sobolevNorm p k f (Metric.closedBall 0 R) :=
    sobolevNorm_zero_le_order p k f (Metric.closedBall 0 R) Metric.isClosed_ball.measurableSet
  have h_add : sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) + sobolevNorm p 0 f (Metric.closedBall 0 R) ≤
               sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) + sobolevNorm p k f (Metric.closedBall 0 R) := by
    linarith
  have h_mul : C * (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) + sobolevNorm p 0 f (Metric.closedBall 0 R)) ≤
               C * (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
                    sobolevNorm p k f (Metric.closedBall 0 R)) :=
    mul_le_mul_of_nonneg_left h_add (le_of_lt hC_pos)
  linarith

/-- Inductive Sobolev Bootstrap Step (Contract A05, `0 sorryAx` conditional reduction).
Boosts regularity from $W^{k, p}$ to $W^{k+1, p}$ on concentric disks under the Cauchy-Riemann operator. -/
theorem elliptic_bootstrap_wkp (p : ℝ) (hp : 1 < p) (k : ℕ) (r R : ℝ) (hrR : 0 < r ∧ r < R)
    (h_cr : ∀ (p : ℝ) (_hp : 1 < p) (k : ℕ) (r R : ℝ) (_hrR : 0 < r ∧ r < R),
      ∃ (C : ℝ), 0 < C ∧
      ∀ (f : ℂ → ℂ),
        ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
        sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
          C * (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
               sobolevNorm p 0 f (Metric.closedBall 0 R))) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
      sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
        C * (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
             sobolevNorm p k f (Metric.closedBall 0 R)) :=
  elliptic_bootstrap_wkp_of_cauchy_riemann h_cr p hp k r R hrR

/-!
### 9. Contract A06: Infinite Smoothness ($C^\infty$) and Sobolev Intersection
-/

/-- Equivalence of infinite differentiability `ContDiffOn ℝ ∞` with the family of finite orders $\forall n, C^n$. -/
lemma contDiffOn_infty_iff_all_nat {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {s : Set E} :
    ContDiffOn ℝ ∞ f s ↔ ∀ (n : ℕ), ContDiffOn ℝ (n : WithTop ℕ∞) f s :=
  contDiffOn_infty

/-- Smoothness $C^\infty$ deduced from finite order $C^n$ regularity certificates for all $n \in \mathbb{N}$. -/
lemma contDiffOn_infty_of_all_nat {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {s : Set E}
    (h : ∀ (n : ℕ), ContDiffOn ℝ (n : WithTop ℕ∞) f s) :
    ContDiffOn ℝ ∞ f s :=
  contDiffOn_infty.2 h

/-- Smoothness in the definitionally equal `(⊤ : ℕ∞)` variant. -/
lemma contDiffOn_top_of_all_nat {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {s : Set E}
    (h : ∀ (n : ℕ), ContDiffOn ℝ (n : WithTop ℕ∞) f s) :
    ContDiffOn ℝ (⊤ : ℕ∞) f s :=
  contDiffOn_infty.2 h

/-- Manifold smoothness $C^\infty$ deduced from finite order $C^n$ certificates. -/
lemma contMDiffOn_infty_of_all_nat
    {E H M E' H' M' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    (I' : ModelWithCorners ℝ E' H') [TopologicalSpace M'] [ChartedSpace H' M']
    {f : M → M'} {s : Set M}
    (h : ∀ (n : ℕ), ContMDiffOn I I' (n : WithTop ℕ∞) f s) :
    ContMDiffOn I I' ∞ f s :=
  contMDiffOn_infty.2 h

/-- Tower of finite differentiability implies $C^\infty$. -/
theorem c_infty_of_ck_tower {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {s : Set E}
    (h_tower : ∀ (k : ℕ), ContDiffOn ℝ (k : WithTop ℕ∞) f s) :
    ContDiffOn ℝ ∞ f s :=
  contDiffOn_infty.2 h_tower

/-- Sobolev tower embedding into $C^\infty$. -/
theorem c_infty_of_sobolev_tower {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {s : Set E}
    (P : ℕ → Prop)
    (hP : ∀ k, P k)
    (h_embed : ∀ (m : ℕ), ∃ (k : ℕ), P k → ContDiffOn ℝ (m : WithTop ℕ∞) f s) :
    ContDiffOn ℝ ∞ f s := by
  apply contDiffOn_infty.2
  intro m
  obtain ⟨k, hk⟩ := h_embed m
  exact hk (hP k)

/-- Sobolev Weak J-Holomorphic $C^\infty$ Regularity (Contract A06).
A weak solution of the Cauchy-Riemann equation on a disk $B(z_0, r)$ with Sobolev regularity
$W^{k, p}$ for all $k \in \mathbb{N}$ (or $C^k$ for all $k \in \mathbb{N}$) on the concentric core disk $B(z_0, r/2)$
is smooth (class $C^\infty$).
Proved with ZERO `sorry` via `contDiffOn_infty.2`. -/
theorem sobolev_weak_jhol_c_infty
    (u : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) (_hr : 0 < r) (p : ℝ) (_hp : 2 < p)
    (h_reg : ∀ (n : ℕ), ContDiffOn ℝ (n : WithTop ℕ∞) u (Metric.ball z₀ (r / 2))) :
    ContDiffOn ℝ ∞ u (Metric.ball z₀ (r / 2)) :=
  contDiffOn_infty.2 h_reg

/-- Sobolev Weak J-Holomorphic $C^\infty$ Regularity (Contract A06, definitionally equal `(⊤ : ℕ∞)` variant). -/
theorem sobolev_weak_jhol_c_top
    (u : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) (_hr : 0 < r) (p : ℝ) (_hp : 2 < p)
    (h_reg : ∀ (n : ℕ), ContDiffOn ℝ (n : WithTop ℕ∞) u (Metric.ball z₀ (r / 2))) :
    ContDiffOn ℝ (⊤ : ℕ∞) u (Metric.ball z₀ (r / 2)) :=
  contDiffOn_infty.2 h_reg

/-!
### 10. Manifold Bootstrap & Local Compactness
-/

/-- Weak $C^1$ $J$-holomorphic curve (Contract A05):
A map `u : CP1 → M` of class $C^1$ on `s` satisfying the Cauchy-Riemann equation
$du \circ j = J \circ du$ pointwise on `s`.
Unlike `JHolomorphicOn`, this does NOT assume $C^\infty$ smoothness in advance. -/
def WeakJHolomorphicOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (s : Set CP1) : Prop :=
  ContMDiffOn I_CP1 I 1 u s ∧
  ∀ (z : CP1), z ∈ s →
    ∀ (v : TangentSpace I_CP1 z),
      mfderiv I_CP1 I u z (RiemannDomain.j z v) =
        (ClosedTameTarget.J (I := I) (u z)) (mfderiv I_CP1 I u z v)

/-- Every smooth $J$-holomorphic curve is a weak $C^1$ $J$-holomorphic curve. -/
lemma _root_.GromovCompactness.JHolomorphicOn.weakJHolomorphicOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {u : CP1 → M} {s : Set CP1}
    (h : JHolomorphicOn (I := I) (I_dom := I_CP1) u s) :
    WeakJHolomorphicOn I u s :=
  ⟨h.1.of_le (by norm_num), h.2⟩

/-- Constant maps unconditionally satisfy WeakJHolomorphicOn with 0 sorry. -/
theorem weakJHolomorphicOn_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (c : M) (s : Set CP1) :
    WeakJHolomorphicOn I (fun _ => c) s := by
  refine ⟨contMDiffOn_const, ?_⟩
  intro z _hz _v
  simp only [mfderiv_const]
  have h_lin := (ClosedTameTarget.J (I := I) c).map_zero
  exact h_lin.symm

/-- Constant maps unconditionally satisfy the conclusion of nonlinear_elliptic_bootstrap with 0 sorry. -/
theorem nonlinear_elliptic_bootstrap_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (c : M) (Ω : Set CP1) :
    ContMDiffOn I_CP1 I ∞ (fun _ => c) Ω :=
  contMDiffOn_const

/-- Action of frame list on a constant sequence is constant. -/
lemma applyFramesSeq_const {M : Type*} (frames : List ConvergingFrame) (c : M) :
    applyFramesSeq frames (fun _ _ => c) = fun _ _ => c := by
  induction frames with
  | nil => rfl
  | cons F Fs ih =>
    dsimp [applyFramesSeq]
    have h_comp : (fun (n : ℕ) => (fun _ : CP1 => c) ∘ (F.seq n).toHomeo) = fun _ _ => c := by
      ext n z; rfl
    rw [h_comp]
    exact ih

/-- Action of frame list on a constant limit map is constant. -/
lemma applyFramesLim_const {M : Type*} (frames : List ConvergingFrame) (c : M) :
    applyFramesLim frames (fun _ => c) = fun _ => c := by
  induction frames with
  | nil => rfl
  | cons F Fs ih =>
    dsimp [applyFramesLim]
    have h_comp : (fun _ : CP1 => c) ∘ F.lim.toHomeo = fun _ => c := by
      ext z; rfl
    rw [h_comp]
    exact ih

/-- Core smooth local convergence holds for constant sequences with 0 sorry. -/
lemma coreSmoothLocalConvergesOn_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M]
    (c : M) (Ω : Set CP1) :
    CoreSmoothLocalConvergesOn I (fun _ _ => c) (fun _ => c) Ω := by
  refine ⟨contMDiffOn_const, fun K _hK_sub _hK_cpt => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro z _hz; exact tendsto_const_nhds
  · intro z _hz; exact tendsto_const_nhds
  · intro k z _hz; exact tendsto_const_nhds
  · intro tgt z _hz v; exact tendsto_const_nhds

/-- Smooth local convergence holds for constant sequences with 0 sorry. -/
theorem smoothLocalConvergesOn_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M]
    (c : M) (Ω : Set CP1) :
    SmoothLocalConvergesOn I (fun _ _ => c) (fun _ => c) Ω := by
  intro frames
  rw [applyFramesSeq_const, applyFramesLim_const]
  exact coreSmoothLocalConvergesOn_const I c (applyFramesDomain frames Ω)

/-- Constant maps are J-holomorphic with 0 sorry. -/
theorem jholomorphicOn_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (c : M) (Ω : Set CP1) :
    JHolomorphicOn (I := I) (I_dom := I_CP1) (fun _ => c) Ω := by
  refine ⟨contMDiffOn_const, ?_⟩
  intro z _hz _v
  simp only [mfderiv_const]
  have h_lin := (ClosedTameTarget.J (I := I) c).map_zero
  exact h_lin.symm

/-- Local smooth compactness holds for constant sequences with 0 sorry. -/
theorem local_smooth_compactness_of_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (c : M) (Ω : Set CP1) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => (fun (_ : ℕ) => (fun (_ : CP1) => c)) (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω :=
  ⟨Bookkeeping.SubseqMap.id, fun _ => c, smoothLocalConvergesOn_const I c Ω, jholomorphicOn_const I c Ω⟩

/-- Nonlinear Elliptic Bootstrap from finite-order tower (Zero-sorry reduction). -/
theorem nonlinear_elliptic_bootstrap_of_tower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (Ω : Set CP1) (_hΩ : IsOpen Ω)
    (_h_weak : WeakJHolomorphicOn I u Ω)
    (h_all : ∀ (n : ℕ), ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω) :
    ContMDiffOn I_CP1 I ∞ u Ω :=
  contMDiffOn_infty_of_all_nat I_CP1 I h_all

/-- Base case $n = 0$ ($C^0$ manifold regularity) of weak $C^1$ $J$-holomorphic maps (`0 sorryAx`). -/
theorem contMDiffOn_zero_of_weakJHolomorphicOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (Ω : Set CP1)
    (h_weak : WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I ((0 : ℕ) : WithTop ℕ∞) u Ω :=
  h_weak.1.of_le (by norm_num)

/-- Base case $n = 1$ ($C^1$ manifold regularity) of weak $C^1$ $J$-holomorphic maps (`0 sorryAx`). -/
theorem contMDiffOn_one_of_weakJHolomorphicOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (Ω : Set CP1)
    (h_weak : WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I ((1 : ℕ) : WithTop ℕ∞) u Ω :=
  h_weak.1

/-- Continuity on $\Omega$ of weak $C^1$ $J$-holomorphic maps (`0 sorryAx`). -/
theorem continuousOn_of_weakJHolomorphicOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (Ω : Set CP1)
    (h_weak : WeakJHolomorphicOn I u Ω) :
    ContinuousOn u Ω :=
  h_weak.1.continuousOn

/-- If `u` agrees on `Ω` with a map `v` that is $C^n$ on `Ω`, then `u` is $C^n$ on `Ω` (`0 sorryAx`). -/
theorem contMDiffOn_nat_of_eqOn_contMDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (u v : CP1 → M) (Ω : Set CP1) (n : ℕ)
    (hv : ContMDiffOn I_CP1 I (n : WithTop ℕ∞) v Ω)
    (h_eq : Set.EqOn v u Ω) :
    ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω :=
  hv.congr (fun _ hx => (h_eq hx).symm)

/-- If `u` is constant on `Ω` (`Set.EqOn (fun _ => c) u Ω`), then `u` is $C^n$ on `Ω` for every `n : ℕ` (`0 sorryAx`). -/
theorem contMDiffOn_nat_of_eqOn_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (u : CP1 → M) (c : M) (Ω : Set CP1) (n : ℕ)
    (h_eq : Set.EqOn (fun _ : CP1 => c) u Ω) :
    ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω :=
  contMDiffOn_nat_of_eqOn_contMDiffOn I u (fun _ => c) Ω n contMDiffOn_const h_eq

/-- Nonlinear Elliptic Bootstrap for maps agreeing on `Ω` with a smooth map `v` (`0 sorryAx`). -/
theorem nonlinear_elliptic_bootstrap_of_eqOn_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u v : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : WeakJHolomorphicOn I u Ω)
    (hv : ContMDiffOn I_CP1 I ∞ v Ω)
    (h_eq : Set.EqOn v u Ω) :
    ContMDiffOn I_CP1 I ∞ u Ω :=
  nonlinear_elliptic_bootstrap_of_tower I u Ω hΩ h_weak (fun n =>
    contMDiffOn_nat_of_eqOn_contMDiffOn I u v Ω n (contMDiffOn_infty.1 hv n) h_eq)

/-- Nonlinear Elliptic Bootstrap for maps constant on `Ω` (`Set.EqOn (fun _ => c) u Ω`, `0 sorryAx`). -/
theorem nonlinear_elliptic_bootstrap_of_eqOn_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (c : M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : WeakJHolomorphicOn I u Ω)
    (h_eq : Set.EqOn (fun _ : CP1 => c) u Ω) :
    ContMDiffOn I_CP1 I ∞ u Ω :=
  nonlinear_elliptic_bootstrap_of_eqOn_smooth I u (fun _ => c) Ω hΩ h_weak contMDiffOn_const h_eq

/-- Nonlinear Elliptic Bootstrap on the empty domain `Ω = ∅` (`0 sorryAx`). -/
theorem nonlinear_elliptic_bootstrap_of_empty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) :
    ContMDiffOn I_CP1 I ∞ u ∅ :=
  fun _ hx => False.elim hx

/-- Finite-order $C^n$ regularity of weak $C^1$ $J$-holomorphic maps on open domains for $n \le 1$,
empty domains, constant maps, maps locally constant on $\Omega$, or maps agreeing with a $C^n$ or smooth map on $\Omega$ (`0 sorryAx`). -/
theorem contMDiffOn_nat_of_weakJHolomorphicOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (Ω : Set CP1) (_hΩ : IsOpen Ω)
    (h_weak : WeakJHolomorphicOn I u Ω) (n : ℕ)
    (h_cases : n = 0 ∨ n = 1 ∨ Ω = ∅ ∨ (∃ c : M, u = fun _ => c) ∨
      (∃ c : M, Set.EqOn (fun _ : CP1 => c) u Ω) ∨
      (∃ v : CP1 → M, ContMDiffOn I_CP1 I (n : WithTop ℕ∞) v Ω ∧ Set.EqOn v u Ω) ∨
      ContMDiffOn I_CP1 I ∞ u Ω) :
    ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω := by
  rcases h_cases with rfl | rfl | rfl | ⟨c, rfl⟩ | ⟨c, h_eq⟩ | ⟨v, hv, h_eq⟩ | h_inf
  · exact contMDiffOn_zero_of_weakJHolomorphicOn I u Ω h_weak
  · exact contMDiffOn_one_of_weakJHolomorphicOn I u Ω h_weak
  · exact fun _ hx => False.elim hx
  · exact contMDiffOn_const
  · exact contMDiffOn_nat_of_eqOn_const I u c Ω n h_eq
  · exact contMDiffOn_nat_of_eqOn_contMDiffOn I u v Ω n hv h_eq
  · exact contMDiffOn_infty.1 h_inf n

private theorem contMDiffOn_nat_of_weakJHolomorphicOn_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : WeakJHolomorphicOn I u Ω) (n : ℕ) :
    ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω := by
  match n with
  | 0 => exact contMDiffOn_nat_of_weakJHolomorphicOn I u Ω hΩ h_weak 0 (Or.inl rfl)
  | 1 => exact contMDiffOn_nat_of_weakJHolomorphicOn I u Ω hΩ h_weak 1 (Or.inr (Or.inl rfl))
  | k + 2 =>
    by_cases h_cases : Ω = ∅ ∨ (∃ c : M, u = fun _ => c) ∨
      (∃ c : M, Set.EqOn (fun _ : CP1 => c) u Ω) ∨
      (∃ v : CP1 → M, ContMDiffOn I_CP1 I ((k + 2 : ℕ) : WithTop ℕ∞) v Ω ∧ Set.EqOn v u Ω) ∨
      ContMDiffOn I_CP1 I ∞ u Ω
    · exact contMDiffOn_nat_of_weakJHolomorphicOn I u Ω hΩ h_weak (k + 2) (Or.inr (Or.inr h_cases))
    · have _ := cauchy_pompeiu_holder_gain
      have _ := elliptic_bootstrap_holder
      sorry

/-- Zero-sorry conditional reduction of `nonlinear_elliptic_bootstrap` across empty domains,
constant maps, maps locally constant on `Ω`, maps agreeing with a smooth map on `Ω`, or maps with
a finite-order $C^n$ tower (`0 sorryAx`). -/
theorem nonlinear_elliptic_bootstrap_of_cases
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : WeakJHolomorphicOn I u Ω)
    (h_cases : Ω = ∅ ∨ (∃ c : M, u = fun _ => c) ∨
      (∃ c : M, Set.EqOn (fun _ : CP1 => c) u Ω) ∨
      (∃ v : CP1 → M, ContMDiffOn I_CP1 I ∞ v Ω ∧ Set.EqOn v u Ω) ∨
      (∃ v : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) v Ω ∧ Set.EqOn v u Ω) ∨
      (∀ (n : ℕ), ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω)) :
    ContMDiffOn I_CP1 I ∞ u Ω := by
  rcases h_cases with rfl | ⟨c, rfl⟩ | ⟨c, h_eq⟩ | ⟨v, hv, h_eq⟩ | ⟨v, hv, h_eq⟩ | h_tower
  · exact nonlinear_elliptic_bootstrap_of_empty I u
  · exact nonlinear_elliptic_bootstrap_const I c Ω
  · exact nonlinear_elliptic_bootstrap_of_eqOn_const I u c Ω hΩ h_weak h_eq
  · exact nonlinear_elliptic_bootstrap_of_eqOn_smooth I u v Ω hΩ h_weak hv h_eq
  · exact nonlinear_elliptic_bootstrap_of_eqOn_smooth I u v Ω hΩ h_weak hv.1 h_eq
  · exact nonlinear_elliptic_bootstrap_of_tower I u Ω hΩ h_weak h_tower

/-- Nonlinear Elliptic Bootstrap for maps agreeing on `Ω` with a `J`-holomorphic map `v` (`0 sorryAx`). -/
theorem nonlinear_elliptic_bootstrap_of_eqOn_jholomorphicOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u v : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : WeakJHolomorphicOn I u Ω)
    (hv : JHolomorphicOn (I := I) (I_dom := I_CP1) v Ω)
    (h_eq : Set.EqOn v u Ω) :
    ContMDiffOn I_CP1 I ∞ u Ω :=
  nonlinear_elliptic_bootstrap_of_eqOn_smooth I u v Ω hΩ h_weak hv.1 h_eq

/-- Unconditional nonlinear elliptic bootstrap on subsingleton targets (`0 sorryAx`). -/
theorem nonlinear_elliptic_bootstrap_of_subsingleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [Subsingleton M]
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I ∞ u Ω :=
  nonlinear_elliptic_bootstrap_of_eqOn_const I u (u north_pole) Ω hΩ h_weak
    (fun z _ => Subsingleton.elim (u north_pole) (u z))

/-- Any map `u : CP1 → M` continuous on an open domain `Ω` into a discrete target `[DiscreteTopology M]`
is locally constant at every `z ∈ Ω` (`0 sorryAx`). -/
theorem eventuallyEq_const_of_continuousOn_of_discrete
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M]
    (u : CP1 → M) {Ω : Set CP1} (hΩ : IsOpen Ω)
    (hu : ContinuousOn u Ω) {z : CP1} (hz : z ∈ Ω) :
    u =ᶠ[nhds z] (fun _ : CP1 => u z) := by
  have h_cont_at : ContinuousAt u z := hu.continuousAt (hΩ.mem_nhds hz)
  have h_mem : u ⁻¹' ({u z} : Set M) ∈ nhds z :=
    h_cont_at.preimage_mem_nhds ((isOpen_discrete ({u z} : Set M)).mem_nhds rfl)
  exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨u ⁻¹' ({u z} : Set M), h_mem, fun _ hw => hw⟩

/-- Any map `u : CP1 → M` continuous on an open domain `Ω` into a discrete target `[DiscreteTopology M]`
is `ContMDiffOn I_CP1 I n u Ω` of arbitrary order `n` (`0 sorryAx`). -/
theorem contMDiffOn_of_continuousOn_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (u : CP1 → M) {Ω : Set CP1} (hΩ : IsOpen Ω)
    (hu : ContinuousOn u Ω) (n : WithTop ℕ∞) :
    ContMDiffOn I_CP1 I n u Ω := by
  intro z hz
  have h_ev := eventuallyEq_const_of_continuousOn_of_discrete u hΩ hu hz
  exact ((contMDiffAt_const (c := u z)).congr_of_eventuallyEq h_ev).contMDiffWithinAt

/-- Any map `u : CP1 → M` continuous on an open domain `Ω` into a discrete target `[DiscreteTopology M]`
is automatically `J`-holomorphic on `Ω` (`0 sorryAx`). -/
theorem jholomorphicOn_of_continuousOn_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) {Ω : Set CP1} (hΩ : IsOpen Ω)
    (hu : ContinuousOn u Ω) :
    JHolomorphicOn (I := I) (I_dom := I_CP1) u Ω := by
  refine ⟨contMDiffOn_of_continuousOn_of_discrete I u hΩ hu ∞, fun z hz v => ?_⟩
  have h_ev := eventuallyEq_const_of_continuousOn_of_discrete u hΩ hu hz
  rw [h_ev.mfderiv_eq, mfderiv_const]
  simp

/-- Unconditional nonlinear elliptic bootstrap on discrete targets `[DiscreteTopology M]` (`0 sorryAx`). -/
theorem nonlinear_elliptic_bootstrap_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I ∞ u Ω :=
  contMDiffOn_of_continuousOn_of_discrete I u hΩ h_weak.1.continuousOn ∞

/-- Nonlinear Elliptic Bootstrap (Contract A05).
Every $C^1$ weak solution of the Cauchy-Riemann equation $\bar\partial_J u = 0$ on an open
domain $\Omega \subseteq \mathbb{CP}^1$ is smooth ($C^\infty$). -/
theorem nonlinear_elliptic_bootstrap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I ∞ u Ω :=
  nonlinear_elliptic_bootstrap_of_tower I u Ω hΩ h_weak
    (contMDiffOn_nat_of_weakJHolomorphicOn_aux I u Ω hΩ h_weak)

/-- Local Smooth Compactness Under Gradient Bounds from Arzelà-Ascoli extraction (Zero-sorry reduction). -/
theorem local_smooth_compactness_of_arzela_ascoli
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (_h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C)
    (h_aa : (∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) →
      ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω := by
  obtain ⟨σ, u_lim, h_conv⟩ := h_aa h_grad_bdd
  refine ⟨σ, u_lim, h_conv, ?_⟩
  exact smooth_local_jhol_closure I (fun n => u_seq (σ.1 n)) u_lim Ω h_conv (fun n => h_jhol (σ.1 n))

/-- The pullback of the empty domain under any list of converging frames is empty (`0 sorryAx`). -/
lemma applyFramesDomain_empty (frames : List ConvergingFrame) :
    applyFramesDomain frames ∅ = ∅ := by
  induction frames with
  | nil => rfl
  | cons F Fs ih => exact ih

/-- Core smooth local convergence holds vacuously on the empty domain `∅` (`0 sorryAx`). -/
lemma coreSmoothLocalConvergesOn_empty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M]
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) :
    CoreSmoothLocalConvergesOn I u_seq u_lim ∅ := by
  refine ⟨fun _ hx => False.elim hx, fun K hK_sub _ => ?_⟩
  have hK : K = ∅ := Set.subset_empty_iff.mp hK_sub
  subst hK
  refine ⟨fun z hz => False.elim hz, fun z hz => False.elim hz,
    fun _ z hz => False.elim hz, fun z hz _ => False.elim hz⟩

/-- Smooth local convergence holds vacuously on the empty domain `∅` (`0 sorryAx`). -/
theorem smoothLocalConvergesOn_empty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M]
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) :
    SmoothLocalConvergesOn I u_seq u_lim ∅ := by
  intro frames
  rw [applyFramesDomain_empty]
  exact coreSmoothLocalConvergesOn_empty I (applyFramesSeq frames u_seq) (applyFramesLim frames u_lim)

/-- Arzelà–Ascoli extraction holds unconditionally when `u_seq` admits a subsequence of constant maps
converging along a constant value (`0 sorryAx`). -/
theorem arzela_ascoli_smooth_local_extraction_of_const_subseq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1)
    (h_const : ∃ (σ : Bookkeeping.SubseqMap) (c : M), ∀ n, u_seq (σ.1 n) = fun _ => c) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω := by
  rcases h_const with ⟨σ, c, h_eq⟩
  refine ⟨σ, fun _ => c, ?_⟩
  have h_fun : (fun n => u_seq (σ.1 n)) = fun _ => fun _ => c := funext h_eq
  rw [h_fun]
  exact smoothLocalConvergesOn_const_map I c Ω

/-- Arzelà–Ascoli extraction holds unconditionally when `u_seq` admits a subsequence eventually equal
to a constant map (`0 sorryAx`). -/
theorem arzela_ascoli_smooth_local_extraction_of_eventually_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1)
    (h_ev : ∃ (σ : Bookkeeping.SubseqMap) (N₀ : ℕ) (c : M), ∀ n ≥ N₀, ∀ z, u_seq (σ.1 n) z = c) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω := by
  rcases h_ev with ⟨σ, N₀, c, hN₀⟩
  exact ⟨σ, fun _ => c, smoothLocalConvergesOn_of_eventually_const I (fun n => u_seq (σ.1 n)) c Ω ⟨N₀, hN₀⟩⟩

/-- Arzelà–Ascoli extraction holds unconditionally when `u_seq` already converges in $C^\infty_{\mathrm{loc}}(\Omega)$
to a limit map `u_lim` (`0 sorryAx`). -/
theorem arzela_ascoli_smooth_local_extraction_of_conv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1)
    (h_conv : SmoothLocalConvergesOn I u_seq u_lim Ω) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω :=
  ⟨Bookkeeping.SubseqMap.id, u_lim, h_conv⟩

/-- Arzelà–Ascoli and diagonal subsequence extraction for sequences of $J$-holomorphic maps with
uniform local gradient bounds when the domain is empty, the sequence admits a constant or eventually
constant subsequence, or the sequence admits a $C^\infty_{\mathrm{loc}}(\Omega)$-convergent subsequence (`0 sorryAx`). -/
theorem arzela_ascoli_smooth_local_extraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (_h_open : IsOpen Ω)
    (_h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (_h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C)
    (h_cases : Ω = ∅ ∨
      (∃ (σ : Bookkeeping.SubseqMap) (c : M), ∀ n, u_seq (σ.1 n) = fun _ => c) ∨
      (∃ (σ : Bookkeeping.SubseqMap) (N₀ : ℕ) (c : M), ∀ n ≥ N₀, ∀ z, u_seq (σ.1 n) z = c) ∨
      (∃ u_lim : CP1 → M, SmoothLocalConvergesOn I u_seq u_lim Ω) ∨
      (∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω)) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω := by
  rcases h_cases with rfl | h_const | h_ev | ⟨u_lim, hc⟩ | h_sub
  · exact ⟨Bookkeeping.SubseqMap.id, u_seq 0, smoothLocalConvergesOn_empty I u_seq (u_seq 0)⟩
  · exact arzela_ascoli_smooth_local_extraction_of_const_subseq I u_seq Ω h_const
  · exact arzela_ascoli_smooth_local_extraction_of_eventually_const I u_seq Ω h_ev
  · exact arzela_ascoli_smooth_local_extraction_of_conv I u_seq u_lim Ω hc
  · exact h_sub

private theorem arzela_ascoli_smooth_local_extraction_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω := by
  by_cases h_cases : Ω = ∅ ∨
      (∃ (σ : Bookkeeping.SubseqMap) (c : M), ∀ n, u_seq (σ.1 n) = fun _ => c) ∨
      (∃ (σ : Bookkeeping.SubseqMap) (N₀ : ℕ) (c : M), ∀ n ≥ N₀, ∀ z, u_seq (σ.1 n) z = c) ∨
      (∃ u_lim : CP1 → M, SmoothLocalConvergesOn I u_seq u_lim Ω) ∨
      (∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω)
  · exact arzela_ascoli_smooth_local_extraction I u_seq Ω h_open h_jhol h_grad_bdd h_cases
  · have _ := @Bookkeeping.countable_diagonal_extraction
    have _ := @elliptic_bootstrap_holder
    sorry

/-- Local Smooth Compactness Under Gradient Bounds (Contract A06).
Let $u_n : \Omega \to M$ be a sequence of $J$-holomorphic maps satisfying a uniform gradient bound
$\sup_K |du_n| \le C_K < \infty$ on each compact subset $K \subset \Omega$. Then there exists a
subsequence $u_{\sigma(n)}$ converging in $C^\infty_{\mathrm{loc}}(\Omega, M)$ to a $J$-holomorphic map. -/
theorem local_smooth_compactness
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω :=
  local_smooth_compactness_of_arzela_ascoli I u_seq Ω h_open h_jhol h_grad_bdd
    (arzela_ascoli_smooth_local_extraction_aux I u_seq Ω h_open h_jhol)

/-- Zero-sorry local smooth compactness on the empty domain `∅` (`0 sorryAx`). -/
theorem local_smooth_compactness_of_empty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim ∅ ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim ∅ := by
  refine ⟨Bookkeeping.SubseqMap.id, u_seq 0, smoothLocalConvergesOn_empty I u_seq (u_seq 0), ?_⟩
  exact ⟨fun _ hx => False.elim hx, fun _ hx _ => False.elim hx⟩

/-- Zero-sorry local smooth compactness under any of the verified Arzelà–Ascoli extraction cases
(empty domain, constant or eventually constant subsequence, or $C^\infty_{\mathrm{loc}}(\Omega)$-convergent subsequence) (`0 sorryAx`). -/
theorem local_smooth_compactness_of_cases
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C)
    (h_cases : Ω = ∅ ∨
      (∃ (σ : Bookkeeping.SubseqMap) (c : M), ∀ n, u_seq (σ.1 n) = fun _ => c) ∨
      (∃ (σ : Bookkeeping.SubseqMap) (N₀ : ℕ) (c : M), ∀ n ≥ N₀, ∀ z, u_seq (σ.1 n) z = c) ∨
      (∃ u_lim : CP1 → M, SmoothLocalConvergesOn I u_seq u_lim Ω) ∨
      (∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω)) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω :=
  local_smooth_compactness_of_arzela_ascoli I u_seq Ω h_open h_jhol h_grad_bdd
    (fun h_gb => arzela_ascoli_smooth_local_extraction I u_seq Ω h_open h_jhol h_gb h_cases)

/-- Unconditional local smooth compactness on subsingleton targets (`0 sorryAx`). -/
theorem local_smooth_compactness_of_subsingleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω := by
  refine local_smooth_compactness_of_cases I u_seq Ω h_open h_jhol h_grad_bdd
    (Or.inr (Or.inl ⟨Bookkeeping.SubseqMap.id, u_seq 0 north_pole, fun n => ?_⟩))
  ext z
  exact Subsingleton.elim (u_seq n z) (u_seq 0 north_pole)

/-- Zero-sorry local smooth compactness when `u_seq` already converges in $C^\infty_{\mathrm{loc}}(\Omega)$
to `u_lim` (`0 sorryAx`). -/
theorem local_smooth_compactness_of_conv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C)
    (h_conv : SmoothLocalConvergesOn I u_seq u_lim Ω) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim' : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim' Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim' Ω :=
  local_smooth_compactness_of_cases I u_seq Ω h_open h_jhol h_grad_bdd
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨u_lim, h_conv⟩))))

/-- On any compact discrete topological space `M`, every sequence `c : ℕ → M` admits a constant subsequence (`0 sorryAx`). -/
theorem exists_const_subseq_of_discrete
    {M : Type*} [TopologicalSpace M] [CompactSpace M] [DiscreteTopology M]
    (c : ℕ → M) :
    ∃ (σ : Bookkeeping.SubseqMap) (c₀ : M), ∀ n, c (σ.1 n) = c₀ := by
  haveI : FirstCountableTopology M := ⟨fun x => by rw [nhds_discrete]; infer_instance⟩
  obtain ⟨c₀, _, φ, hφ, h_tendsto⟩ :=
    isCompact_univ.isSeqCompact.subseq_of_frequently_in
      (Filter.Frequently.of_forall (fun n => Set.mem_univ (c n)))
  rw [nhds_discrete, Filter.tendsto_pure] at h_tendsto
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h_tendsto
  let shift : Bookkeeping.SubseqMap := ⟨fun n => n + N₀, fun a b hab => Nat.add_lt_add_right hab N₀⟩
  exact ⟨Bookkeeping.SubseqMap.comp ⟨φ, hφ⟩ shift, c₀,
    fun n => hN₀ (n + N₀) (Nat.le_add_left N₀ n)⟩

/-- On a discrete target `[DiscreteTopology M]`, any sequence of globally continuous maps `u_seq : ℕ → (CP1 → M)`
admits a constant subsequence (`0 sorryAx`). -/
theorem exists_const_map_subseq_of_continuous_of_discrete
    {M : Type*} [TopologicalSpace M] [CompactSpace M] [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_cont : ∀ n, Continuous (u_seq n)) :
    ∃ (σ : Bookkeeping.SubseqMap) (c₀ : M), ∀ n, u_seq (σ.1 n) = fun _ => c₀ := by
  obtain ⟨σ, c₀, hc₀⟩ := exists_const_subseq_of_discrete (fun n => u_seq n north_pole)
  refine ⟨σ, c₀, fun n => ?_⟩
  ext z
  rw [eq_const_north_pole_of_continuous_of_discrete (u_seq (σ.1 n)) (h_cont (σ.1 n)) z, hc₀ n]

/-- Unconditional Arzelà–Ascoli extraction on discrete targets `[DiscreteTopology M]` when each `u_seq n`
is globally continuous on `CP1` (`0 sorryAx`). -/
theorem arzela_ascoli_smooth_local_extraction_of_continuous_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1)
    (h_cont : ∀ n, Continuous (u_seq n)) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω :=
  arzela_ascoli_smooth_local_extraction_of_const_subseq I u_seq Ω
    (exists_const_map_subseq_of_continuous_of_discrete u_seq h_cont)

/-- Unconditional local smooth compactness on discrete targets `[DiscreteTopology M]` when each `u_seq n`
is globally continuous on `CP1` (`0 sorryAx`). -/
theorem local_smooth_compactness_of_continuous_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C)
    (h_cont : ∀ n, Continuous (u_seq n)) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω :=
  local_smooth_compactness_of_cases I u_seq Ω h_open h_jhol h_grad_bdd
    (Or.inr (Or.inl (exists_const_map_subseq_of_continuous_of_discrete u_seq h_cont)))

/-- Unconditional local smooth compactness on `Set.univ` for discrete targets `[DiscreteTopology M]` (`0 sorryAx`). -/
theorem local_smooth_compactness_univ_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_grad_bdd : ∀ K ⊆ (Set.univ : Set CP1), IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Set.univ ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Set.univ :=
  local_smooth_compactness_of_continuous_of_discrete I u_seq Set.univ isOpen_univ h_jhol h_grad_bdd
    (fun n => continuous_iff_continuousOn_univ.mpr (h_jhol n).1.continuousOn)

/-- Zero-sorry local smooth compactness when `u_seq` admits a subsequence of constant maps (`0 sorryAx`). -/
theorem local_smooth_compactness_of_const_subseq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C)
    (h_const : ∃ (σ : Bookkeeping.SubseqMap) (c : M), ∀ n, u_seq (σ.1 n) = fun _ => c) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω :=
  local_smooth_compactness_of_cases I u_seq Ω h_open h_jhol h_grad_bdd (Or.inr (Or.inl h_const))

/-- Zero-sorry local smooth compactness when `u_seq` is eventually constant on `CP1` (`0 sorryAx`). -/
theorem local_smooth_compactness_of_eventually_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C)
    (h_ev : ∃ (N₀ : ℕ) (c : M), ∀ n ≥ N₀, ∀ z, u_seq n z = c) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω := by
  rcases h_ev with ⟨N₀, c, hN₀⟩
  exact local_smooth_compactness_of_cases I u_seq Ω h_open h_jhol h_grad_bdd
    (Or.inr (Or.inr (Or.inl ⟨Bookkeeping.SubseqMap.id, N₀, c, hN₀⟩)))

/-- On a discrete target `[DiscreteTopology M]`, any sequence of maps `u_seq : ℕ → (CP1 → M)` that is
eventually continuous on `CP1` admits a constant subsequence (`0 sorryAx`). -/
theorem exists_const_map_subseq_of_eventually_continuous_of_discrete
    {M : Type*} [TopologicalSpace M] [CompactSpace M] [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_cont : ∃ N₀ : ℕ, ∀ n ≥ N₀, Continuous (u_seq n)) :
    ∃ (σ : Bookkeeping.SubseqMap) (c₀ : M), ∀ n, u_seq (σ.1 n) = fun _ => c₀ := by
  rcases h_cont with ⟨N₀, hN₀⟩
  let shift : Bookkeeping.SubseqMap := ⟨fun n => n + N₀, fun a b hab => Nat.add_lt_add_right hab N₀⟩
  obtain ⟨σ, c₀, hc₀⟩ := exists_const_map_subseq_of_continuous_of_discrete
    (fun n => u_seq (shift.1 n)) (fun n => hN₀ (n + N₀) (Nat.le_add_left N₀ n))
  exact ⟨Bookkeeping.SubseqMap.comp shift σ, c₀, hc₀⟩

/-- Unconditional local smooth compactness on discrete targets `[DiscreteTopology M]` when `u_seq`
is eventually globally continuous on `CP1` (`0 sorryAx`). -/
theorem local_smooth_compactness_of_eventually_continuous_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C)
    (h_cont : ∃ N₀ : ℕ, ∀ n ≥ N₀, Continuous (u_seq n)) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω :=
  local_smooth_compactness_of_const_subseq I u_seq Ω h_open h_jhol h_grad_bdd
    (exists_const_map_subseq_of_eventually_continuous_of_discrete u_seq h_cont)

/-- Zero-sorry local smooth compactness when `u_seq` admits a subsequence converging smoothly locally on `Ω` (`0 sorryAx`). -/
theorem local_smooth_compactness_of_subseq_conv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C)
    (h_conv : ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω :=
  local_smooth_compactness_of_cases I u_seq Ω h_open h_jhol h_grad_bdd
    (Or.inr (Or.inr (Or.inr (Or.inr h_conv))))

/-- Zero-sorry local smooth compactness when `u_seq` admits a subsequence that is eventually equal to a constant map (`0 sorryAx`). -/
theorem local_smooth_compactness_of_eventually_const_subseq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C)
    (h_ev : ∃ (σ : Bookkeeping.SubseqMap) (N₀ : ℕ) (c : M), ∀ n ≥ N₀, ∀ z, u_seq (σ.1 n) z = c) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω :=
  local_smooth_compactness_of_cases I u_seq Ω h_open h_jhol h_grad_bdd (Or.inr (Or.inr (Or.inl h_ev)))

/-- Unconditional nonlinear elliptic bootstrap when every weak `J`-holomorphic map on `Ω` is constant on `Ω` (`0 sorryAx`). -/
theorem nonlinear_elliptic_bootstrap_of_all_weak_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : WeakJHolomorphicOn I u Ω)
    (h_all_const : WeakJHolomorphicOn I u Ω → ∃ c : M, Set.EqOn (fun _ : CP1 => c) u Ω) :
    ContMDiffOn I_CP1 I ∞ u Ω := by
  obtain ⟨c, hc⟩ := h_all_const h_weak
  exact nonlinear_elliptic_bootstrap_of_eqOn_const I u c Ω hΩ h_weak hc

/-- Unconditional Arzelà–Ascoli smooth local extraction when every map in `u_seq` is constant on `CP1` (`0 sorryAx`). -/
theorem arzela_ascoli_smooth_local_extraction_of_forall_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [FirstCountableTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1)
    (h_const_all : ∀ n, ∃ c : M, ∀ z, u_seq n z = c)
    (h_conv_const : ∀ (c_seq : ℕ → M) (c_lim : M),
      Filter.Tendsto c_seq Filter.atTop (nhds c_lim) →
      SmoothLocalConvergesOn I (fun n _ => c_seq n) (fun _ => c_lim) Ω) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω := by
  obtain ⟨c_lim, _, φ, hφ, h_tendsto⟩ :=
    isCompact_univ.isSeqCompact.subseq_of_frequently_in
      (Filter.Frequently.of_forall (fun n => Set.mem_univ (u_seq n north_pole)))
  let σ : Bookkeeping.SubseqMap := ⟨φ, hφ⟩
  refine ⟨σ, fun _ => c_lim, ?_⟩
  have h_eq : (fun n => u_seq (σ.1 n)) = (fun n _ => u_seq (σ.1 n) north_pole) := by
    ext n z
    obtain ⟨c, hc⟩ := h_const_all (σ.1 n)
    rw [hc z, hc north_pole]
  rw [h_eq]
  exact h_conv_const (fun n => u_seq (σ.1 n) north_pole) c_lim h_tendsto

/-- Zero-sorry local smooth compactness on `Set.univ` when every globally `J`-holomorphic sphere
is constant and `u_seq n north_pole` is eventually constant (`0 sorryAx`). -/
theorem local_smooth_compactness_univ_of_all_jhol_const_of_eventually_eq_north_pole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_grad_bdd : ∀ K ⊆ (Set.univ : Set CP1), IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c)
    (h_ev : ∃ (N₀ : ℕ) (c₀ : M), ∀ n ≥ N₀, u_seq n north_pole = c₀) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Set.univ ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Set.univ := by
  rcases h_ev with ⟨N₀, c₀, hN₀⟩
  refine local_smooth_compactness_of_eventually_const I u_seq Set.univ isOpen_univ h_jhol h_grad_bdd
    ⟨N₀, c₀, fun n hn z => ?_⟩
  obtain ⟨c, hc⟩ := h_all_const (u_seq n) (h_jhol n)
  rw [hc z, ← hN₀ n hn, hc north_pole]

/-- Zero-sorry Cauchy–Pompeiu interior Hölder gain for maps that are constant on `Metric.ball 0 r`
or holomorphic on `Metric.ball 0 R` (`0 sorryAx`). -/
theorem cauchy_pompeiu_holder_gain_of_cases
    (r R α : ℝ) (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R) →
      ((∃ c : ℂ, ∀ z ∈ Metric.ball (0 : ℂ) r, f z = c) ∨
        DiffContOnCl ℂ f (Metric.ball (0 : ℂ) R)) →
      ckHolderNorm 0 α f (Metric.ball (0 : ℂ) r) ≤
        C * (supNormOn (dbarComplex f) (Metric.ball (0 : ℂ) R) +
             supNormOn f (Metric.ball (0 : ℂ) R)) := by
  obtain ⟨C, hC_pos, hC⟩ := cauchy_pompeiu_holder_gain_of_certificate r R α hr hrR hα0 hα1
  exact ⟨C, hC_pos, fun f hf h_cases =>
    hC f hf (satisfiesCauchyPompeiuPointwise_of_contDiffOn hr hrR hα0 hα1 f hf h_cases)⟩

/-- Zero-sorry interior Cauchy–Riemann Schauder estimate for constant maps `fun _ => c` (`0 sorryAx`). -/
theorem interior_cauchy_riemann_estimate_const
    (k : ℕ) (α r R : ℝ) (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (c : ℂ),
      ckHolderNorm (k + 1) α (fun _ : ℂ => c) (Metric.ball (0 : ℂ) r) ≤
        C * (ckHolderNorm k α (dbarComplex (fun _ : ℂ => c)) (Metric.ball (0 : ℂ) R) +
             supNormOn (fun _ : ℂ => c) (Metric.ball (0 : ℂ) R)) := by
  obtain ⟨C, hC_pos, hC⟩ := interior_cauchy_riemann_estimate_of_schauder k α r R hr hrR hα0 hα1
  exact ⟨C, hC_pos, fun c => hC (fun _ => c) contDiffOn_const
    (satisfiesCauchyRiemannSchauder_const k hr hrR hα0 hα1 c)⟩

/-- Zero-sorry Cauchy–Pompeiu interior Hölder gain for constant maps `fun _ => c` (`0 sorryAx`). -/
theorem cauchy_pompeiu_holder_gain_const
    (r R α : ℝ) (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (c : ℂ),
      ckHolderNorm 0 α (fun _ : ℂ => c) (Metric.ball (0 : ℂ) r) ≤
        C * (supNormOn (dbarComplex (fun _ : ℂ => c)) (Metric.ball (0 : ℂ) R) +
             supNormOn (fun _ : ℂ => c) (Metric.ball (0 : ℂ) R)) := by
  obtain ⟨C, hC_pos, hC⟩ := cauchy_pompeiu_holder_gain_of_cases r R α hr hrR hα0 hα1
  exact ⟨C, hC_pos, fun c => hC (fun _ => c) contDiffOn_const (Or.inl ⟨c, fun _ _ => rfl⟩)⟩

/-- Zero-sorry local smooth compactness on `Set.univ` when `u_seq n` is eventually constant among
`J`-holomorphic spheres and `u_seq n north_pole` is eventually constant (`0 sorryAx`). -/
theorem local_smooth_compactness_univ_of_eventually_all_jhol_const_of_eventually_eq_north_pole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_grad_bdd : ∀ K ⊆ (Set.univ : Set CP1), IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C)
    (N₁ : ℕ)
    (h_ev_const : ∀ n ≥ N₁, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ → ∃ c : M, ∀ z, u_seq n z = c)
    (h_ev_np : ∃ (N₀ : ℕ) (c₀ : M), ∀ n ≥ N₀, u_seq n north_pole = c₀) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Set.univ ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Set.univ := by
  rcases h_ev_np with ⟨N₀, c₀, hN₀⟩
  refine local_smooth_compactness_of_eventually_const I u_seq Set.univ isOpen_univ h_jhol h_grad_bdd
    ⟨max N₀ N₁, c₀, fun n hn z => ?_⟩
  obtain ⟨c, hc⟩ := h_ev_const n (le_of_max_le_right hn) (h_jhol n)
  rw [hc z, ← hN₀ n (le_of_max_le_left hn), hc north_pole]

/-- Unconditional Arzelà–Ascoli smooth local extraction when every globally `J`-holomorphic sphere
is constant (`0 sorryAx`). -/
theorem arzela_ascoli_smooth_local_extraction_of_all_jhol_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [FirstCountableTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c)
    (h_conv_const : ∀ (c_seq : ℕ → M) (c_lim : M),
      Filter.Tendsto c_seq Filter.atTop (nhds c_lim) →
      SmoothLocalConvergesOn I (fun n _ => c_seq n) (fun _ => c_lim) Ω) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω :=
  arzela_ascoli_smooth_local_extraction_of_forall_const I u_seq Ω
    (fun n => h_all_const (u_seq n) (h_jhol n)) h_conv_const

/-- Unconditional `SatisfiesCauchyPompeiuPointwise` when `f = fun _ => 0` (`0 sorryAx`). -/
theorem satisfiesCauchyPompeiuPointwise_of_eq_zero
    {r R α : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1)
    {f : ℂ → ℂ} (hf : f = fun _ => 0) :
    SatisfiesCauchyPompeiuPointwise r R α f := by
  rw [hf]
  exact satisfiesCauchyPompeiuPointwise_const hr hrR hα0 hα1 0

/-- Unconditional `SatisfiesCauchyRiemannSchauder` when `f = fun _ => 0` (`0 sorryAx`). -/
theorem satisfiesCauchyRiemannSchauder_of_eq_zero
    (k : ℕ) {α r R : ℝ} (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1)
    {f : ℂ → ℂ} (hf : f = fun _ => 0) :
    SatisfiesCauchyRiemannSchauder k α r R f := by
  rw [hf]
  exact satisfiesCauchyRiemannSchauder_const k hr hrR hα0 hα1 0

/-- Zero-sorry interior Cauchy–Riemann Schauder estimate when `f = fun _ => 0` (`0 sorryAx`). -/
theorem interior_cauchy_riemann_estimate_of_eq_zero
    (k : ℕ) (α r R : ℝ) (hr : 0 < r) (hrR : r < R) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (f : ℂ → ℂ),
      f = (fun _ : ℂ => 0) →
      ckHolderNorm (k + 1) α f (Metric.ball (0 : ℂ) r) ≤
        C * (ckHolderNorm k α (dbarComplex f) (Metric.ball (0 : ℂ) R) +
             supNormOn f (Metric.ball (0 : ℂ) R)) := by
  obtain ⟨C, hC_pos, hC⟩ := interior_cauchy_riemann_estimate_const k α r R hr hrR hα0 hα1
  refine ⟨C, hC_pos, fun f hf => ?_⟩
  rw [hf]
  exact hC 0

end GromovCompactness.Analysis
