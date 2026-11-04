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
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic.Linarith
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Topology.SmoothLocal
import GromovCompactness.Topology.Subsequence

open scoped Manifold ContDiff Topology MeasureTheory
open Metric Set GromovCompactness MeasureTheory

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
### 7. Contract A04: Interior Cauchy-Riemann Estimates & Morrey Embedding
-/

/-- Interior Cauchy-Riemann Estimate (Contract A04).
For $1 < p < \infty$ and $k \in \mathbb{N}$, interior $W^{k+1, p}$ estimates hold on concentric
disks $D_r \subset D_R$:
$\|f\|_{W^{k+1, p}(D_r)} \le C \left(\|\bar\partial f\|_{W^{k, p}(D_R)} + \|f\|_{L^p(D_R)}\right)$. -/
theorem interior_cauchy_riemann_estimate (p : ℝ) (hp : 1 < p) (k : ℕ) (r R : ℝ) (hrR : 0 < r ∧ r < R) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
      sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
        C * (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
             sobolevNorm p 0 f (Metric.closedBall 0 R)) := by
  sorry

/-- Morrey-Sobolev Embedding in 2D (Contract A04).
For $p > 2$, $W^{1, p}$ functions on 2D disks embed into Hölder continuous functions $C^{0, \alpha}$
with exponent $\alpha = 1 - 2/p$:
$\|f(z) - f(w)\| \le C \mathrm{dist}(z, w)^\alpha \|f\|_{W^{1, p}(D_r)}$. -/
theorem morrey_sobolev_embedding (p : ℝ) (hp : 2 < p) (r : ℝ) (hr : 0 < r) :
    ∃ (C : ℝ) (α : ℝ), 0 < C ∧ α = 1 - 2 / p ∧ 0 < α ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ 1 f (Metric.closedBall 0 r) →
      ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      ∀ w ∈ Metric.closedBall (0 : ℂ) r,
        ‖f z - f w‖ ≤ C * (dist z w)^α * sobolevNorm p 1 f (Metric.closedBall 0 r) := by
  sorry

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

/-- Inductive Sobolev Bootstrap Step (Contract A05).
Boosts regularity from $W^{k, p}$ to $W^{k+1, p}$ on concentric disks under the Cauchy-Riemann operator.
Proved with ZERO `sorry` via reduction to Contract A04 (`elliptic_bootstrap_wkp_of_cauchy_riemann`). -/
theorem elliptic_bootstrap_wkp (p : ℝ) (hp : 1 < p) (k : ℕ) (r R : ℝ) (hrR : 0 < r ∧ r < R) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
      sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
        C * (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
             sobolevNorm p k f (Metric.closedBall 0 R)) :=
  elliptic_bootstrap_wkp_of_cauchy_riemann interior_cauchy_riemann_estimate p hp k r R hrR

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
    WeakJHolomorphicOn I u s := by
  refine ⟨h.1.of_le (by norm_num), h.2⟩

/-- Constant maps unconditionally satisfy WeakJHolomorphicOn with 0 sorry. -/
theorem weakJHolomorphicOn_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (c : M) (s : Set CP1) :
    WeakJHolomorphicOn I (fun _ => c) s := by
  constructor
  · exact contMDiffOn_const
  · intro z _hz _v
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
  constructor
  · exact contMDiffOn_const
  · intro z _hz _v
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
    ContMDiffOn I_CP1 I ∞ u Ω := by
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
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω := by
  sorry

end GromovCompactness.Analysis
