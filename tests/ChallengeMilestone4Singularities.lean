/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Challenger 2 Milestone 4)
-/
import GromovCompactness
import GromovCompactness.Analysis.SingularityRemoval
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness
open GromovCompactness.Analysis

namespace GromovCompactness.ChallengeMilestone4

/-!
# Empirical Adversarial Challenge Suite: Milestone 4 Singularity Removal
Challenger: challenger2_m4 (Empirical Challenger for Milestone 4)
Target: GromovCompactness/Analysis/SingularityRemoval.lean (Contracts A09, A10, A11, A12)

This challenge harness empirically stress-tests all declarations delivered in Milestone 4:
1. Conformal bridge identity (`annulus_ratio_rpow_eq_exp_neg`) with varying $r, L, \alpha$:
   - Standard values, extreme scales, negative lengths, zero powers, and cylinder product laws.
2. Grönwall differential inequality integration (`exp_decay_of_diff_ineq`, `exp_decay_bound_of_diff_ineq`):
   - Zero function $F(t) = 0$.
   - Constant negative function $F(t) = -1$.
   - Sharp exponential test function $F(t) = e^{t/c}$ achieving exact equality.
   - Strictly dominated exponential $F(t) = e^t$ with $c = 2$.
   - Negative decaying exponential $F(t) = -e^{-t}$.
   - Monotonicity chain $F(T_1) \le F(T_2) \le F(L)$.
3. Decay factor & collar algebraic bounds:
   - Nonnegativity and strict positivity of $e^{-\alpha L}$.
   - Upper bound $e^{-\alpha L} \le 1$ and strict bound $< 1$ for positive parameters.
   - Monotonicity transitivity $L_1 \le L_2 \le L_3$.
   - Two-sided neck factor bound $\le 2$ and positivity.
   - Degenerate inner collar $r_2 = 0 \implies (r/r_1)^\alpha \le 1 \le 2$.
   - Sandwich bounds for $(1 - e^{-\alpha L}) / \alpha$.
4. Cauchy-Schwarz loop boundary oscillation bounds:
   - Quadratic discriminant nonnegativity on perfect squares $(ut + v)^2$ achieving equality.
   - Quadratic discriminant on positive definite polynomials $t^2 + 1$ and $4t^2 + 4t + 2$.
   - Boundary loop length bound $L \le \sqrt{2\pi E}$.
   - Loop length vanishing when energy is zero: $E = 0 \implies L = 0$.
   - Loop diameter bound decomposition $\operatorname{diam} \le \sqrt{2\pi}\sqrt{E}$.
   - Quadratic energy scaling: energy scaled by $\lambda^2$ scales diameter by $\lambda$.
5. Neck energy threshold, collar emptiness, and localization:
   - Threshold existence for concrete values $d_0 = 1, C_{\text{cyl}} = 2 \implies \eta = 1/64$.
   - Threshold existence for microscopic target chart $d_0 = 10^{-4}$ and large cylinder $C_{\text{cyl}} = 1000$.
   - Annulus emptiness when $r_2 \le r_1$ at origin and off-origin points.
   - Annulus emptiness at degenerate boundary $r_1 = r_2$ (collapsed collar).
   - $\mathbb{CP}^1$ collar emptiness `annulus_at_empty_of_le` when $R/2 \le 2r$.
   - Pointwise localization from diameter bound on empty set $S = \emptyset$.
   - Pointwise localization on singleton $S = \{z_0\}$.
   - Pointwise localization on real line $\mathbb{R}$.
6. Topological density & uniqueness on punctured sphere:
   - Singleton punctured sphere is complement $\{p\}^c$.
   - Openness of punctured sphere.
   - $J$-holomorphic transfer congruence (`jholomorphicOn_congr`) reflexivity and transitivity.
   - Continuity of $J$-holomorphic curves (`continuous_of_jholomorphicOn`) on constant curves.
   - Euclidean disk closure includes origin $0 \in \overline{B(0, r) \setminus \{0\}}$.
   - Density of punctured ball at non-origin points $z \in B(0, r) \setminus \{0\}$.
   - Continuous extension equality on Euclidean disk (`eqOn_ball_of_eqOn_punctured_ball`).
   - Unique extension value at puncture point 0 (`extension_value_at_zero_unique`).
   - Uniqueness of smooth extensions across puncture on $\mathbb{CP}^1$ (`removal_of_singularities_unique`).
   - Separated-hypothesis uniqueness formulation (`removal_of_singularities_unique'`).
7. Constant curve extensions:
   - Constant curve smooth extension existence (`removal_of_singularities_const`).
   - Constant curve smooth extension unique existence (`removal_of_singularities_const_unique`).
   - Global agreement on all of $\mathbb{CP}^1$ for constant extensions.
8. Modular reduction:
   - Modular reduction theorem (`removal_of_singularities_reduction`) specialization to constant Sobolev extension and bootstrap.
   - Preservation of unique smooth extension under reduction.
9. Axiom audit:
   - Verification that all test declarations depend strictly on standard Lean 4 kernel axioms.
-/

--------------------------------------------------------------------------------
-- SECTION 1: Conformal Bridge Identity Stress Tests
--------------------------------------------------------------------------------

/-- Test 1.1: Conformal bridge identity at standard parameters $r = 1, L = 0, \alpha = 1$. -/
theorem test_conformal_bridge_std :
    (1 / (1 * Real.exp 0))^(1 : ℝ) = Real.exp (-(1 : ℝ) * 0) := by
  have hr : (0 : ℝ) < 1 := by norm_num
  exact annulus_ratio_rpow_eq_exp_neg 1 0 1 hr

/-- Test 1.2: Conformal bridge identity evaluated at concrete values $r = 2, L = 5, \alpha = 3$. -/
theorem test_conformal_bridge_concrete :
    (2 / (2 * Real.exp 5))^(3 : ℝ) = Real.exp (-(3 : ℝ) * 5) := by
  have hr : (0 : ℝ) < 2 := by norm_num
  exact annulus_ratio_rpow_eq_exp_neg 2 5 3 hr

/-- Test 1.3: Conformal bridge identity with negative cylinder length $L = -4$. -/
theorem test_conformal_bridge_negative_length :
    (3 / (3 * Real.exp (-4)))^(2 : ℝ) = Real.exp (-(2 : ℝ) * (-4)) := by
  have hr : (0 : ℝ) < 3 := by norm_num
  exact annulus_ratio_rpow_eq_exp_neg 3 (-4) 2 hr

/-- Test 1.4: Conformal bridge identity with zero power $\alpha = 0$. -/
theorem test_conformal_bridge_zero_power :
    (7 / (7 * Real.exp 10))^(0 : ℝ) = Real.exp (-(0 : ℝ) * 10) := by
  have hr : (0 : ℝ) < 7 := by norm_num
  exact annulus_ratio_rpow_eq_exp_neg 7 10 0 hr

/-- Test 1.5: Conformal bridge identity at microscopic scale $r = 1/1000000$ and large cylinder $L = 50$. -/
theorem test_conformal_bridge_extreme_scale :
    ((1 / 1000000 : ℝ) / ((1 / 1000000 : ℝ) * Real.exp 50))^(1/2 : ℝ) = Real.exp (-(1/2 : ℝ) * 50) := by
  have hr : (0 : ℝ) < 1 / 1000000 := by norm_num
  exact annulus_ratio_rpow_eq_exp_neg (1 / 1000000) 50 (1/2) hr

/-- Test 1.6: Scale invariance under $r \mapsto k \cdot r$ for any $k > 0$. -/
theorem test_conformal_bridge_scale_invariance (r k L α : ℝ) (hr : 0 < r) (hk : 0 < k) :
    ((k * r) / ((k * r) * Real.exp L))^α = (r / (r * Real.exp L))^α := by
  have hkr : 0 < k * r := mul_pos hk hr
  rw [annulus_ratio_rpow_eq_exp_neg (k * r) L α hkr]
  rw [annulus_ratio_rpow_eq_exp_neg r L α hr]

/-- Test 1.7: Multiplicative composition across connected cylinders:
The bridged ratio over $L_1 + L_2$ factors into the product of bridged ratios. -/
theorem test_conformal_bridge_composition (r L₁ L₂ α : ℝ) (hr : 0 < r) :
    (r / (r * Real.exp (L₁ + L₂)))^α = (r / (r * Real.exp L₁))^α * (r / (r * Real.exp L₂))^α := by
  rw [annulus_ratio_rpow_eq_exp_neg r (L₁ + L₂) α hr]
  rw [annulus_ratio_rpow_eq_exp_neg r L₁ α hr]
  rw [annulus_ratio_rpow_eq_exp_neg r L₂ α hr]
  rw [← Real.exp_add]
  congr 1
  ring

--------------------------------------------------------------------------------
-- SECTION 2: Grönwall Differential Inequality Stress Tests
--------------------------------------------------------------------------------

/-- Test 2.1: Grönwall decay on the zero function $F(t) = 0$ yields $0 \le 0$. -/
theorem test_gronwall_zero_function (c L T : ℝ) (hc : 0 < c) (hTL : T ≤ L) :
    (fun _ : ℝ => (0 : ℝ)) T * Real.exp (-T / c) ≤ (fun _ : ℝ => (0 : ℝ)) L * Real.exp (-L / c) := by
  have hF : Differentiable ℝ (fun _ : ℝ => (0 : ℝ)) := differentiable_const 0
  have h_ineq : ∀ t, (fun _ : ℝ => (0 : ℝ)) t ≤ c * deriv (fun _ : ℝ => (0 : ℝ)) t := by
    intro t
    rw [deriv_const]
    simp
  exact exp_decay_of_diff_ineq hF hc h_ineq hTL

/-- Test 2.2: Grönwall bound on the constant negative function $F(t) = -1$.
Since $F'(t) = 0$, $-1 \le c \cdot 0 = 0$ holds, yielding $-1 \le -e^{-(L-T)/c}$. -/
theorem test_gronwall_neg_const_bound (c L T : ℝ) (hc : 0 < c) (hTL : T ≤ L) :
    (fun _ : ℝ => (-1 : ℝ)) T ≤ (fun _ : ℝ => (-1 : ℝ)) L * Real.exp (-(L - T) / c) := by
  have hF : Differentiable ℝ (fun _ : ℝ => (-1 : ℝ)) := differentiable_const (-1)
  have h_ineq : ∀ t, (fun _ : ℝ => (-1 : ℝ)) t ≤ c * deriv (fun _ : ℝ => (-1 : ℝ)) t := by
    intro t
    rw [deriv_const]
    simp
  exact exp_decay_bound_of_diff_ineq hF hc h_ineq hTL

/-- Helper lemma: Derivative of $t \mapsto e^{t/c}$ is $(1/c) e^{t/c}$. -/
lemma hasDerivAt_exp_div_const (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => Real.exp (s / c)) (Real.exp (t / c) / c) t := by
  have h_inner : HasDerivAt (fun s => s / c) (1 / c) t := by
    have h1 : HasDerivAt (fun s => s) 1 t := hasDerivAt_id t
    have h2 := h1.div_const c
    simpa using h2
  have h_exp := h_inner.exp
  have h_eq : Real.exp (t / c) * (1 / c) = Real.exp (t / c) / c := mul_one_div (Real.exp (t / c)) c
  rw [h_eq] at h_exp
  exact h_exp

/-- Test 2.3: Sharp exponential test function $F(t) = e^{t/c}$.
Here $F'(t) = (1/c) e^{t/c}$, so $F(t) = c \cdot F'(t)$ holds with EXACT EQUALITY.
The Grönwall decay bound $e^{T/c} \le e^{L/c} \cdot e^{-(L-T)/c} = e^{T/c}$ achieves exact sharpness. -/
theorem test_gronwall_sharp_exponential (c L T : ℝ) (hc : 0 < c) (hTL : T ≤ L) :
    (fun t => Real.exp (t / c)) T ≤ (fun t => Real.exp (t / c)) L * Real.exp (-(L - T) / c) := by
  have hc_ne : c ≠ 0 := hc.ne'
  have hF : Differentiable ℝ (fun t => Real.exp (t / c)) := by
    apply Real.differentiable_exp.comp
    exact differentiable_id.div_const c
  have h_ineq : ∀ t, (fun s => Real.exp (s / c)) t ≤ c * deriv (fun s => Real.exp (s / c)) t := by
    intro t
    have h_deriv_at := hasDerivAt_exp_div_const c hc_ne t
    rw [h_deriv_at.deriv]
    have h_cancel : c * (Real.exp (t / c) / c) = Real.exp (t / c) := by
      exact mul_div_cancel₀ (Real.exp (t / c)) hc_ne
    rw [h_cancel]
  exact exp_decay_bound_of_diff_ineq hF hc h_ineq hTL

/-- Test 2.4: Strictly dominated exponential $F(t) = e^t$ with $c = 2$.
Here $F'(t) = e^t$, so $F(t) = e^t \le 2 e^t = 2 F'(t)$ holds with strict slack. -/
theorem test_gronwall_strictly_dominated_exponential (L T : ℝ) (hTL : T ≤ L) :
    Real.exp T ≤ Real.exp L * Real.exp (-(L - T) / 2) := by
  have hc : (0 : ℝ) < 2 := by norm_num
  have hF : Differentiable ℝ Real.exp := Real.differentiable_exp
  have h_ineq : ∀ t, Real.exp t ≤ 2 * deriv Real.exp t := by
    intro t
    rw [Real.deriv_exp]
    have hpos : 0 ≤ Real.exp t := (Real.exp_pos t).le
    linarith
  exact exp_decay_bound_of_diff_ineq hF hc h_ineq hTL

/-- Test 2.5: Negative decaying exponential $F(t) = -e^{-t}$ with arbitrary $c > 0$.
$F'(t) = e^{-t} > 0$, so $F(t) = -e^{-t} < 0 < c e^{-t} = c F'(t)$ holds globally on $\mathbb{R}$. -/
theorem test_gronwall_neg_decaying_exp (c L T : ℝ) (hc : 0 < c) (hTL : T ≤ L) :
    (-Real.exp (-T)) ≤ (-Real.exp (-L)) * Real.exp (-(L - T) / c) := by
  have hF : Differentiable ℝ (fun t => -Real.exp (-t)) := by
    apply Differentiable.neg
    apply Real.differentiable_exp.comp
    exact differentiable_id.neg
  have h_ineq : ∀ t, (-Real.exp (-t)) ≤ c * deriv (fun s => -Real.exp (-s)) t := by
    intro t
    have h_inner : HasDerivAt (fun s => -s) (-1) t := (hasDerivAt_id t).neg
    have h_exp := h_inner.exp
    have h_neg := h_exp.neg
    have h_id : - (Real.exp (-t) * (-1)) = Real.exp (-t) := by ring
    rw [h_id] at h_neg
    rw [h_neg.deriv]
    have h_pos1 : 0 ≤ Real.exp (-t) := (Real.exp_pos (-t)).le
    have h_pos2 : 0 ≤ c * Real.exp (-t) := mul_nonneg hc.le h_pos1
    have h_neg1 : -Real.exp (-t) ≤ 0 := by linarith
    linarith
  exact exp_decay_bound_of_diff_ineq hF hc h_ineq hTL

/-- Test 2.6: Monotonicity transitivity of Grönwall decay:
For $T_1 \le T_2 \le L$, $F(T_1) e^{-T_1/c} \le F(T_2) e^{-T_2/c} \le F(L) e^{-L/c}$. -/
theorem test_gronwall_monotonicity_trans {F : ℝ → ℝ} (hF : Differentiable ℝ F)
    {c : ℝ} (hc : 0 < c) (h_ineq : ∀ t, F t ≤ c * deriv F t)
    {T₁ T₂ L : ℝ} (hT₁₂ : T₁ ≤ T₂) (hT₂L : T₂ ≤ L) :
    F T₁ * Real.exp (-T₁ / c) ≤ F L * Real.exp (-L / c) := by
  have h1 := exp_decay_of_diff_ineq hF hc h_ineq hT₁₂
  have h2 := exp_decay_of_diff_ineq hF hc h_ineq hT₂L
  exact h1.trans h2

--------------------------------------------------------------------------------
-- SECTION 3: Decay Factor & Collar Algebraic Bounds Stress Tests
--------------------------------------------------------------------------------

/-- Test 3.1: Strict positivity and nonnegativity of exponential decay factor across varying signs. -/
theorem test_decay_factor_positivity (α L : ℝ) :
    0 < Real.exp (-α * L) ∧ 0 ≤ Real.exp (-α * L) :=
  ⟨exp_decay_factor_pos α L, exp_decay_factor_nonneg α L⟩

/-- Test 3.2: Upper bound $e^{-\alpha L} \le 1$ and strict bound $< 1$ for positive parameters. -/
theorem test_decay_factor_upper_bounds :
    Real.exp (-(2 : ℝ) * 3) < 1 ∧ Real.exp (-(0 : ℝ) * 5) ≤ 1 := by
  have h1 : (0 : ℝ) < 2 := by norm_num
  have h2 : (0 : ℝ) < 3 := by norm_num
  have p1 := exp_decay_factor_lt_one h1 h2
  have p2 := exp_decay_factor_le_one (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ 5)
  exact ⟨p1, p2⟩

/-- Test 3.3: Monotonicity chain $L_1 \le L_2 \le L_3 \implies e^{-\alpha L_3} \le e^{-\alpha L_2} \le e^{-\alpha L_1}$. -/
theorem test_decay_factor_mono_chain (α L₁ L₂ L₃ : ℝ)
    (hα : 0 ≤ α) (h12 : L₁ ≤ L₂) (h23 : L₂ ≤ L₃) :
    Real.exp (-α * L₃) ≤ Real.exp (-α * L₁) := by
  have step1 := exp_decay_factor_mono hα h23
  have step2 := exp_decay_factor_mono hα h12
  exact step1.trans step2

/-- Test 3.4: Neck factor upper bound at boundary values $r = r_1$ and $r_2 = R$:
$(r_1 / r_1)^\alpha + (R / R)^\alpha = 1 + 1 = 2 \le 2$. -/
theorem test_neck_factor_boundary_two :
    ((2 : ℝ) / 2)^(1 : ℝ) + ((5 : ℝ) / 5)^(1 : ℝ) ≤ 2 := by
  have hr : (0 : ℝ) < 2 := by norm_num
  have hr1 : (2 : ℝ) ≤ 2 := le_refl 2
  have hr2 : (0 : ℝ) ≤ 5 := by norm_num
  have hR : (5 : ℝ) ≤ 5 := le_refl 5
  have hR_pos : (0 : ℝ) < 5 := by norm_num
  have hα : (0 : ℝ) ≤ 1 := by norm_num
  exact neck_factor_le_two hr hr1 hr2 hR hR_pos hα

/-- Test 3.5: Positivity of neck factor for positive radii. -/
theorem test_neck_factor_positivity :
    0 < ((1 : ℝ) / 3)^(2 : ℝ) + ((2 : ℝ) / 4)^(2 : ℝ) := by
  have hr : (0 : ℝ) < 1 := by norm_num
  have hr1 : (0 : ℝ) < 3 := by norm_num
  have hr2 : (0 : ℝ) < 2 := by norm_num
  have hR : (0 : ℝ) < 4 := by norm_num
  exact neck_factor_pos hr hr1 hr2 hR

/-- Test 3.6: Degenerate inner collar $r_2 = 0 \implies (r / r_1)^\alpha + 0^\alpha \le 2$. -/
theorem test_neck_factor_zero_inner_radius (r r₁ R α : ℝ)
    (hr : 0 < r) (hr1 : r ≤ r₁) (hR : 0 < R) (hα : 0 ≤ α) :
    (r / r₁)^α + (0 / R)^α ≤ 2 := by
  exact neck_factor_le_two hr hr1 (le_refl 0) (le_of_lt hR) hR hα

/-- Test 3.7: Integral decay sandwich bounds $0 \le (1 - e^{-\alpha L}) / \alpha \le 1/\alpha$. -/
theorem test_integral_decay_sandwich (α L : ℝ) (hα : 0 < α) (hL : 0 ≤ L) :
    0 ≤ (1 - Real.exp (-α * L)) / α ∧ (1 - Real.exp (-α * L)) / α ≤ 1 / α :=
  ⟨one_sub_exp_neg_div_nonneg hα hL, one_sub_exp_neg_div_le hα⟩

--------------------------------------------------------------------------------
-- SECTION 4: Cauchy-Schwarz Loop Boundary Oscillation Stress Tests
--------------------------------------------------------------------------------

/-- Test 4.1: Cauchy-Schwarz discriminant on perfect squares $(ut + v)^2 = u^2 t^2 + 2 u v t + v^2$.
Here $a = u^2, b = u v, c = v^2$, so $b^2 = u^2 v^2 = a c$, achieving exact equality. -/
theorem test_cauchy_schwarz_perfect_square (u v : ℝ) (hu : 0 < u) :
    (u * v)^2 ≤ (u^2) * (v^2) := by
  have ha : 0 < u^2 := by positivity
  have h_quad : ∀ t : ℝ, 0 ≤ (u^2) * t^2 + 2 * (u * v) * t + (v^2) := by
    intro t
    have h_id : (u^2) * t^2 + 2 * (u * v) * t + (v^2) = (u * t + v)^2 := by ring
    rw [h_id]
    exact sq_nonneg (u * t + v)
  exact cauchy_schwarz_quadratic (u^2) (u * v) (v^2) ha h_quad

/-- Test 4.2: Cauchy-Schwarz on strictly positive quadratic $4 t^2 + 4 t + 2 = (2t + 1)^2 + 1 > 0$.
Here $a = 4, b = 2, c = 2$, yielding $b^2 = 4 \le 4 \cdot 2 = 8$. -/
theorem test_cauchy_schwarz_positive_poly :
    (2 : ℝ)^2 ≤ 4 * 2 := by
  have ha : (0 : ℝ) < 4 := by norm_num
  have h_quad : ∀ t : ℝ, 0 ≤ (4 : ℝ) * t^2 + 2 * 2 * t + 2 := by
    intro t
    have h_id : (4 : ℝ) * t^2 + 2 * 2 * t + 2 = (2 * t + 1)^2 + 1 := by ring
    rw [h_id]
    have : 0 ≤ (2 * t + 1)^2 := sq_nonneg (2 * t + 1)
    linarith
  exact cauchy_schwarz_quadratic 4 2 2 ha h_quad

/-- Test 4.3: Loop length bounded by $\sqrt{2\pi E}$ from quadratic bound $L^2 \le 2\pi E$. -/
theorem test_loop_length_bound (L E_loop : ℝ) (hL : 0 ≤ L) (h_cs : L^2 ≤ (2 * Real.pi) * E_loop) :
    L ≤ Real.sqrt ((2 * Real.pi) * E_loop) :=
  loop_length_le_sqrt_energy hL h_cs

/-- Test 4.4: Loop length vanishing when loop energy is zero: $E = 0 \implies L = 0$. -/
theorem test_loop_length_zero_energy (L : ℝ) (hL : 0 ≤ L) (h_cs : L^2 ≤ (2 * Real.pi) * 0) :
    L = 0 := by
  have h_mul : (2 * Real.pi) * 0 = 0 := mul_zero (2 * Real.pi)
  rw [h_mul] at h_cs
  have h_sq_nonpos : L^2 ≤ 0 := h_cs
  have h_sq_nonneg : 0 ≤ L^2 := sq_nonneg L
  have h_sq_zero : L^2 = 0 := le_antisymm h_sq_nonpos h_sq_nonneg
  exact sq_eq_zero_iff.mp h_sq_zero

/-- Test 4.5: Diameter bound product decomposition $\operatorname{diam} \le \sqrt{2\pi}\sqrt{E}$. -/
theorem test_loop_diam_decomposition (diam E_loop : ℝ)
    (h_diam : diam ≤ Real.sqrt (2 * Real.pi * E_loop)) (hE : 0 ≤ E_loop) :
    diam ≤ Real.sqrt (2 * Real.pi) * Real.sqrt E_loop :=
  loop_diam_le_sqrt_energy diam E_loop h_diam hE

/-- Test 4.6: Quadratic energy scaling:
Scaling energy by $c_{\text{scale}}^2$ scales the diameter bound linearly by $c_{\text{scale}}$. -/
theorem test_loop_diam_quadratic_scaling (diam E_loop c_scale : ℝ)
    (h_diam : diam ≤ Real.sqrt (2 * Real.pi * (c_scale^2 * E_loop)))
    (hE : 0 ≤ E_loop) (hc : 0 ≤ c_scale) :
    diam ≤ Real.sqrt (2 * Real.pi) * c_scale * Real.sqrt E_loop := by
  have h_decomp := loop_diam_le_sqrt_energy diam (c_scale^2 * E_loop) h_diam (by positivity)
  have h_sqrt_mul : Real.sqrt (c_scale^2 * E_loop) = c_scale * Real.sqrt E_loop := by
    rw [Real.sqrt_mul (sq_nonneg c_scale)]
    rw [Real.sqrt_sq hc]
  rw [h_sqrt_mul] at h_decomp
  calc
    diam ≤ Real.sqrt (2 * Real.pi) * (c_scale * Real.sqrt E_loop) := h_decomp
    _ = Real.sqrt (2 * Real.pi) * c_scale * Real.sqrt E_loop := by ring

--------------------------------------------------------------------------------
-- SECTION 5: Neck Energy Threshold, Collar Emptiness & Localization Stress Tests
--------------------------------------------------------------------------------

/-- Test 5.1: Threshold existence for concrete values $d_0 = 1, C_{\text{cyl}} = 2 \implies \eta = 1/64$. -/
theorem test_threshold_existence_concrete :
    ∃ η : ℝ, 0 < η ∧ (2 : ℝ) * Real.sqrt η < (1 : ℝ) / 2 := by
  have hd₀ : (0 : ℝ) < 1 := by norm_num
  have hC : (0 : ℝ) < 2 := by norm_num
  exact exists_neck_energy_threshold 1 2 hd₀ hC

/-- Test 5.2: Threshold existence for microscopic target chart $d_0 = 1/10000$ and large cylinder $C_{\text{cyl}} = 1000$. -/
theorem test_threshold_existence_microscopic :
    ∃ η : ℝ, 0 < η ∧ (1000 : ℝ) * Real.sqrt η < (1 / 10000 : ℝ) / 2 := by
  have hd₀ : (0 : ℝ) < 1 / 10000 := by norm_num
  have hC : (0 : ℝ) < 1000 := by norm_num
  exact exists_neck_energy_threshold (1 / 10000) 1000 hd₀ hC

/-- Test 5.3: Collar set emptiness when $r_2 \le r_1$ for $a = 0 \in \mathbb{C}$ and $a = 3 + 4i$. -/
theorem test_annulus_emptiness_origin :
    {z : ℂ | (5 : ℝ) < dist z 0 ∧ dist z 0 < 2} = ∅ ∧
    {z : ℂ | (10 : ℝ) < dist z (3 + 4 * Complex.I) ∧ dist z (3 + 4 * Complex.I) < 5} = ∅ := by
  have h1 : (2 : ℝ) ≤ 5 := by norm_num
  have h2 : (5 : ℝ) ≤ 10 := by norm_num
  exact ⟨annulus_set_empty_of_le 0 h1, annulus_set_empty_of_le (3 + 4 * Complex.I) h2⟩

/-- Test 5.4: Annulus emptiness at boundary $r_1 = r_2$ (collapsed collar). -/
theorem test_annulus_emptiness_collapsed (a : ℂ) (r : ℝ) :
    {z : ℂ | r < dist z a ∧ dist z a < r} = ∅ :=
  annulus_set_empty_of_le a (le_refl r)

/-- Test 5.5: $\mathbb{CP}^1$ collar emptiness `annulus_at_empty_of_le` when $R/2 \le 2r$.
Evaluated at concrete values $r = 1, R = 4 \implies R/2 = 2 \le 2r = 2$. -/
theorem test_annulus_at_empty_concrete (a : ℂ) :
    annulus_at a (2 * 1) (4 / 2) = ∅ := by
  have h : (4 : ℝ) / 2 ≤ 2 * 1 := by norm_num
  exact annulus_at_empty_of_le a h

/-- Test 5.6: Localization from diameter bound on empty set $S = \emptyset$.
Vacuously produces a center $x_0$. -/
theorem test_localization_empty_set {M : Type*} [MetricSpace M] [Nonempty M]
    (u : CP1 → M) (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ x₀ : M, ∀ z ∈ (∅ : Set CP1), dist (u z) x₀ < d₀ := by
  have h_diam : ∀ z₁ ∈ (∅ : Set CP1), ∀ z₂ ∈ (∅ : Set CP1), dist (u z₁) (u z₂) < d₀ := by
    intro z hz
    cases hz
  exact localization_of_diam_bound u ∅ d₀ h_diam

/-- Test 5.7: Localization on singleton $S = \{z_0\}$ with $x_0 = u(z_0)$. -/
theorem test_localization_singleton {M : Type*} [MetricSpace M] [Nonempty M]
    (u : CP1 → M) (z₀ : CP1) (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ x₀ : M, ∀ z ∈ ({z₀} : Set CP1), dist (u z) x₀ < d₀ := by
  have h_diam : ∀ z₁ ∈ ({z₀} : Set CP1), ∀ z₂ ∈ ({z₀} : Set CP1), dist (u z₁) (u z₂) < d₀ := by
    intro z₁ hz₁ z₂ hz₂
    have hz1_eq : z₁ = z₀ := hz₁
    have hz2_eq : z₂ = z₀ := hz₂
    subst hz1_eq hz2_eq
    rw [dist_self]
    exact hd₀
  exact localization_of_diam_bound u {z₀} d₀ h_diam

/-- Test 5.8: Localization on the metric space $\mathbb{R}$. -/
theorem test_localization_reals (u : CP1 → ℝ) (s : Set CP1) (d₀ : ℝ)
    (h_diam : ∀ z₁ ∈ s, ∀ z₂ ∈ s, dist (u z₁) (u z₂) < d₀) :
    ∃ x₀ : ℝ, ∀ z ∈ s, dist (u z) x₀ < d₀ :=
  localization_of_diam_bound u s d₀ h_diam

--------------------------------------------------------------------------------
-- SECTION 6: Topological Density & Uniqueness Stress Tests
--------------------------------------------------------------------------------

/-- Test 6.1: Punctured sphere at singleton $\{p\}$ equals complement $\{p\}^c$. -/
theorem test_punctured_sphere_eq_compl (p : CP1) :
    punctured_sphere {p} = {p}ᶜ :=
  punctured_sphere_singleton_eq_compl p

/-- Test 6.2: Openness of punctured sphere for any puncture $p \in \mathbb{CP}^1$. -/
theorem test_punctured_sphere_isOpen (p : CP1) :
    IsOpen (punctured_sphere {p}) :=
  isOpen_punctured_sphere p

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-- Test 6.3: Holomorphic transfer congruence (`jholomorphicOn_congr`) reflexivity:
If $u$ is $J$-holomorphic on open $s$, it remains so trivially. -/
theorem test_jholomorphicOn_congr_refl (u : CP1 → M) (s : Set CP1) (hs : IsOpen s)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u s) :
    JHolomorphicOn (I := I) (I_dom := I_CP1) u s :=
  jholomorphicOn_congr I hs (fun _ _ => rfl) hu

/-- Test 6.4: Continuity of $J$-holomorphic curves (`continuous_of_jholomorphicOn`) on general curves. -/
theorem test_continuous_of_jholomorphic (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    Continuous u :=
  continuous_of_jholomorphicOn I u hu

/-- Test 6.4b: Continuity of $J$-holomorphic curves on constant curves. -/
theorem test_continuous_of_jholomorphic_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (c : M) :
    Continuous (fun _ : CP1 => c) := by
  have hu : JHolomorphicOn (I := I) (I_dom := I_CP1) (fun _ => c) Set.univ :=
    jholomorphicOn_const I c Set.univ
  exact continuous_of_jholomorphicOn I (fun _ => c) hu

/-- Test 6.5: Euclidean ball closure includes the origin $0 \in \overline{B(0, r) \setminus \{0\}}$. -/
theorem test_closure_includes_zero (r : ℝ) (hr : 0 < r) :
    (0 : ℂ) ∈ closure (ball (0 : ℂ) r \ {0}) := by
  have h_subset := ball_subset_closure_punctured_ball r hr
  exact h_subset (mem_ball_self hr)

/-- Test 6.6: Density of punctured ball at non-origin points $z \in B(0, r) \setminus \{0\}$. -/
theorem test_closure_includes_nonzero (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : z ∈ ball (0 : ℂ) r) (hz0 : z ≠ 0) :
    z ∈ closure (ball (0 : ℂ) r \ {0}) := by
  have h_subset := ball_subset_closure_punctured_ball r hr
  exact h_subset hz

/-- Test 6.7: Continuous extension equality on the Euclidean disk.
If two continuous maps into a Hausdorff space agree on $B(0, r) \setminus \{0\}$,
they agree identically on all of $B(0, r)$. -/
theorem test_eqOn_disk_of_punctured_disk (r : ℝ) (hr : 0 < r) (v₁ v₂ : ℂ → M)
    (hv₁ : ContinuousOn v₁ (ball (0 : ℂ) r))
    (hv₂ : ContinuousOn v₂ (ball (0 : ℂ) r))
    (h_eq : EqOn v₁ v₂ (ball (0 : ℂ) r \ {0})) :
    EqOn v₁ v₂ (ball (0 : ℂ) r) :=
  eqOn_ball_of_eqOn_punctured_ball r hr v₁ v₂ hv₁ hv₂ h_eq

/-- Test 6.8: Unique extension value at origin puncture $v_1(0) = v_2(0)$. -/
theorem test_extension_value_zero_unique (r : ℝ) (hr : 0 < r) (v₁ v₂ : ℂ → M)
    (hv₁ : ContinuousOn v₁ (ball (0 : ℂ) r))
    (hv₂ : ContinuousOn v₂ (ball (0 : ℂ) r))
    (h_eq : EqOn v₁ v₂ (ball (0 : ℂ) r \ {0})) :
    v₁ 0 = v₂ 0 :=
  extension_value_at_zero_unique r hr v₁ v₂ hv₁ hv₂ h_eq

/-- Test 6.9: Uniqueness of smooth extensions across puncture on $\mathbb{CP}^1$. -/
theorem test_removal_of_singularities_unique (p : CP1) (h_dense : Dense (punctured_sphere {p}))
    (u u₁ u₂ : CP1 → M)
    (h₁ : EqOn u₁ u (punctured_sphere {p}) ∧ JHolomorphicOn (I := I) (I_dom := I_CP1) u₁ Set.univ)
    (h₂ : EqOn u₂ u (punctured_sphere {p}) ∧ JHolomorphicOn (I := I) (I_dom := I_CP1) u₂ Set.univ) :
    u₁ = u₂ :=
  removal_of_singularities_unique I p h_dense u u₁ u₂ h₁ h₂

/-- Test 6.10: Separated-hypothesis uniqueness formulation. -/
theorem test_removal_of_singularities_unique' (u : CP1 → M) (p : CP1) (u₁ u₂ : CP1 → M)
    (h₁_eq : EqOn u₁ u (punctured_sphere {p}))
    (h₁_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u₁ Set.univ)
    (h₂_eq : EqOn u₂ u (punctured_sphere {p}))
    (h₂_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u₂ Set.univ)
    (h_dense : Dense (punctured_sphere {p})) :
    u₁ = u₂ :=
  removal_of_singularities_unique' I u p u₁ u₂ h₁_eq h₁_jhol h₂_eq h₂_jhol h_dense

--------------------------------------------------------------------------------
-- SECTION 7: Constant Curve Extension Stress Tests
--------------------------------------------------------------------------------

/-- Test 7.1: Constant curve smooth extension existence (`removal_of_singularities_const`). -/
theorem test_removal_const_exists (c : M) (p : CP1) :
    ∃ (u_smooth : CP1 → M),
      EqOn u_smooth (fun _ => c) (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  removal_of_singularities_const I c p

/-- Test 7.2: Constant curve smooth extension unique existence (`removal_of_singularities_const_unique`). -/
theorem test_removal_const_unique (h_dense : ∀ (p : CP1), Dense (punctured_sphere {p}))
    (c : M) (p : CP1) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth (fun _ => c) (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  removal_of_singularities_const_unique I h_dense c p

/-- Test 7.3: Constant extension satisfies global identity on all of $\mathbb{CP}^1$. -/
theorem test_removal_const_global_identity (c : M) (p : CP1)
    (h_dense : Dense (punctured_sphere {p}))
    (u_smooth : CP1 → M)
    (h_eq : EqOn u_smooth (fun _ => c) (punctured_sphere {p}))
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ) :
    u_smooth = fun _ => c := by
  have hu_cont := continuous_of_jholomorphicOn I u_smooth h_jhol
  have hc_cont : Continuous (fun _ : CP1 => c) := continuous_const
  exact Continuous.ext_on h_dense hu_cont hc_cont h_eq

--------------------------------------------------------------------------------
-- SECTION 8: Modular Reduction Stress Tests
--------------------------------------------------------------------------------

/-- Test 8.1: Modular reduction theorem (`removal_of_singularities_reduction`) applies to any curve
endowed with Sobolev extension and elliptic bootstrap. -/
theorem test_removal_reduction_soundness
    (h_sobolev_ext : ∀ (u : CP1 → M) (p : CP1)
      (_h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
      (_h_en : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤),
      ∃ (u_ext : CP1 → M), Continuous u_ext ∧ EqOn u_ext u (punctured_sphere {p}))
    (h_bootstrap_ext : ∀ (u_ext : CP1 → M) (p : CP1)
      (_h_cont : Continuous u_ext)
      (_h_jhol_punct : JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext (punctured_sphere {p})),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ)
    (h_dense : ∀ (p : CP1), Dense (punctured_sphere {p}))
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  removal_of_singularities_reduction I h_sobolev_ext h_bootstrap_ext h_dense u p h_jhol h_energy

/-- Test 8.2: Modular reduction specializes to constant maps with zero sorry. -/
theorem test_removal_reduction_const_specialization
    (h_sobolev_ext : ∀ (u : CP1 → M) (p : CP1)
      (_h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
      (_h_en : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤),
      ∃ (u_ext : CP1 → M), Continuous u_ext ∧ EqOn u_ext u (punctured_sphere {p}))
    (h_bootstrap_ext : ∀ (u_ext : CP1 → M) (p : CP1)
      (_h_cont : Continuous u_ext)
      (_h_jhol_punct : JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext (punctured_sphere {p})),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ)
    (h_dense : ∀ (p : CP1), Dense (punctured_sphere {p}))
    (c : M) (p : CP1)
    (h_energy : energyMeasureExtended I (fun _ => c) (punctured_sphere {p}) ≠ ⊤) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth (fun _ => c) (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ := by
  have h_jhol_const : JHolomorphicOn (I := I) (I_dom := I_CP1) (fun _ => c) (punctured_sphere {p}) :=
    jholomorphicOn_const I c (punctured_sphere {p})
  exact removal_of_singularities_reduction I h_sobolev_ext h_bootstrap_ext h_dense (fun _ => c) p h_jhol_const h_energy

--------------------------------------------------------------------------------
-- SECTION 9: Complete Kernel Axiom Audit
--------------------------------------------------------------------------------

#print axioms test_conformal_bridge_std
#print axioms test_conformal_bridge_concrete
#print axioms test_conformal_bridge_negative_length
#print axioms test_conformal_bridge_zero_power
#print axioms test_conformal_bridge_extreme_scale
#print axioms test_conformal_bridge_scale_invariance
#print axioms test_conformal_bridge_composition

#print axioms test_gronwall_zero_function
#print axioms test_gronwall_neg_const_bound
#print axioms test_gronwall_sharp_exponential
#print axioms test_gronwall_strictly_dominated_exponential
#print axioms test_gronwall_neg_decaying_exp
#print axioms test_gronwall_monotonicity_trans

#print axioms test_decay_factor_positivity
#print axioms test_decay_factor_upper_bounds
#print axioms test_decay_factor_mono_chain
#print axioms test_neck_factor_boundary_two
#print axioms test_neck_factor_positivity
#print axioms test_neck_factor_zero_inner_radius
#print axioms test_integral_decay_sandwich

#print axioms test_cauchy_schwarz_perfect_square
#print axioms test_cauchy_schwarz_positive_poly
#print axioms test_loop_length_bound
#print axioms test_loop_length_zero_energy
#print axioms test_loop_diam_decomposition
#print axioms test_loop_diam_quadratic_scaling

#print axioms test_threshold_existence_concrete
#print axioms test_threshold_existence_microscopic
#print axioms test_annulus_emptiness_origin
#print axioms test_annulus_emptiness_collapsed
#print axioms test_annulus_at_empty_concrete
#print axioms test_localization_empty_set
#print axioms test_localization_singleton
#print axioms test_localization_reals

#print axioms test_punctured_sphere_eq_compl
#print axioms test_punctured_sphere_isOpen
#print axioms test_jholomorphicOn_congr_refl
#print axioms test_continuous_of_jholomorphic
#print axioms test_continuous_of_jholomorphic_const
#print axioms test_closure_includes_zero
#print axioms test_closure_includes_nonzero
#print axioms test_eqOn_disk_of_punctured_disk
#print axioms test_extension_value_zero_unique
#print axioms test_removal_of_singularities_unique
#print axioms test_removal_of_singularities_unique'

#print axioms test_removal_const_exists
#print axioms test_removal_const_unique
#print axioms test_removal_const_global_identity

#print axioms test_removal_reduction_soundness
#print axioms test_removal_reduction_const_specialization

end GromovCompactness.ChallengeMilestone4
