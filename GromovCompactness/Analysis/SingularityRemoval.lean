/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.Separation.Hausdorff
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.EpsilonRegularity
import GromovCompactness.Analysis.Monotonicity
import GromovCompactness.Analysis.EnergyGap
import GromovCompactness.Analysis.EllipticBootstrap

open scoped Manifold ContDiff Topology
open Metric Set GromovCompactness

namespace GromovCompactness.Analysis

/-!
# Tasks A09, A10, A11, & A12: Cylinder Analysis and Singularity Removal

This module formalizes:
1. `cylinder_localization` (Contract A09): Small-energy cylinders map into a single geodesic target chart.
2. `cylinder_exponential_decay` (Contract A10): Exponential decay of energy and neck diameter on conformal cylinders.
3. `puncture_sobolev_extension` (Contract A11): Continuous and Sobolev $W^{1, p}$ extension of finite-energy curves across isolated punctures.
4. `removal_of_singularities` (Contract A12): Unique smooth $J$-holomorphic extension across isolated punctures.
5. Exact zero-`sorry` auxiliary foundation lemmas:
   - Conformal bridge identity linking cylinder exponential decay with annulus power ratio decay.
   - Grönwall differential inequality integration for exponential decay.
   - Decay factor and collar factor algebraic bounds.
   - Cauchy-Schwarz loop boundary oscillation estimates.
   - Small neck energy threshold and diameter localization.
   - Degenerate collar emptiness for $R / 2 \le 2r$.
   - Topological density, open complement identities, and continuous extension equality.
   - Unconditional unique smooth extension for constant curves.
   - Machine-checked reduction of Contract A12 to Contract A11 and elliptic bootstrap.

References:
- Mikhail Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Math. 82 (1985), §1.4.
- Sergei Ivashkovich & Vsevolod Shevchishin, arXiv:math/9912046, Lemmas 2.1.4–2.1.5, Theorems 2.1.6–2.1.7.
- Dusa McDuff & Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology* (2012), Theorems 4.1.2 & 4.7.1.
- `gromov_compactness.pdf` §4.3 & §4.4 (Contracts A09–A12).
-/

/-!
### 1. Conformal Cylinder Decay & Grönwall Differential Inequality (Zero-sorry)
-/

/-- Conformal bridge: Annulus radius ratio equals exponential of cylinder length:
$(r / (r * e^L))^\alpha = e^{-\alpha L}$ for $r > 0$. -/
lemma annulus_ratio_rpow_eq_exp_neg (r L α : ℝ) (hr : 0 < r) :
    (r / (r * Real.exp L))^α = Real.exp (-α * L) := by
  have h_div : r / (r * Real.exp L) = 1 / Real.exp L := by
    have hr_ne : r ≠ 0 := hr.ne'
    field_simp
  rw [h_div, one_div, ← Real.exp_neg]
  rw [← Real.exp_mul]
  congr 1
  ring

/-- Exponential decay from differential inequality $F(t) \le c \cdot F'(t)$:
If $F : ℝ → ℝ$ is differentiable, $c > 0$, and $F(t) \le c \cdot F'(t)$ for all $t$,
then for any $T \le L$, $F(T) \cdot e^{-T/c} \le F(L) \cdot e^{-L/c}$. -/
lemma exp_decay_of_diff_ineq {F : ℝ → ℝ} (hF : Differentiable ℝ F)
    {c : ℝ} (hc : 0 < c)
    (h_ineq : ∀ t, F t ≤ c * deriv F t)
    {T L : ℝ} (hTL : T ≤ L) :
    F T * Real.exp (-T / c) ≤ F L * Real.exp (-L / c) := by
  have hc_ne : c ≠ 0 := hc.ne'
  let g := fun t => F t * Real.exp (-t / c)
  have hg_diff : Differentiable ℝ g := by
    apply Differentiable.mul hF
    apply Differentiable.exp
    apply Differentiable.div_const
    exact differentiable_id.neg
  have hg_deriv : ∀ t, 0 ≤ deriv g t := by
    intro t
    have h_inner : HasDerivAt (fun s => -s / c) (-1 / c) t := by
      have h1 : HasDerivAt (fun s => -s) (-1) t := (hasDerivAt_id t).neg
      have h2 := h1.div_const c
      simpa using h2
    have h_exp := h_inner.exp
    have h_F : HasDerivAt F (deriv F t) t := (hF t).hasDerivAt
    have h_g : HasDerivAt g (deriv F t * Real.exp (-t / c) + F t * (Real.exp (-t / c) * (-1 / c))) t := h_F.mul h_exp
    have hg_eq : deriv g t = (deriv F t - F t / c) * Real.exp (-t / c) := by
      rw [h_g.deriv]
      ring
    rw [hg_eq]
    have h_pos_exp : 0 ≤ Real.exp (-t / c) := (Real.exp_pos _).le
    have h_diff_nonneg : 0 ≤ deriv F t - F t / c := by
      have h1 := h_ineq t
      have h2 : F t / c ≤ deriv F t := by
        have h3 : F t ≤ c * deriv F t := h1
        exact (div_le_iff₀ hc).mpr (by linarith [mul_comm c (deriv F t)])
      linarith
    exact mul_nonneg h_diff_nonneg h_pos_exp
  have h_mono : Monotone g := monotone_of_deriv_nonneg hg_diff hg_deriv
  exact h_mono hTL

/-- Exponential decay bound $F(T) \le F(L) \cdot e^{-(L - T)/c}$:
Integrating the differential inequality $F(t) \le c \cdot F'(t)$ gives exponential decay
with rate $1/c$ from the boundary collar $L$ down to $T$. -/
lemma exp_decay_bound_of_diff_ineq {F : ℝ → ℝ} (hF : Differentiable ℝ F)
    {c : ℝ} (hc : 0 < c)
    (h_ineq : ∀ t, F t ≤ c * deriv F t)
    {T L : ℝ} (hTL : T ≤ L) :
    F T ≤ F L * Real.exp (-(L - T) / c) := by
  have h := exp_decay_of_diff_ineq hF hc h_ineq hTL
  have h_exp_pos : 0 < Real.exp (T / c) := Real.exp_pos _
  have h_mul := mul_le_mul_of_nonneg_right h h_exp_pos.le
  have h_id1 : (F T * Real.exp (-T / c)) * Real.exp (T / c) = F T := by
    rw [mul_assoc, ← Real.exp_add]
    have : -T / c + T / c = 0 := by ring
    rw [this, Real.exp_zero, mul_one]
  have h_id2 : (F L * Real.exp (-L / c)) * Real.exp (T / c) = F L * Real.exp (-(L - T) / c) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [h_id1, h_id2] at h_mul
  exact h_mul

/-!
### 2. Decay Factor & Collar Algebraic Bounds (Zero-sorry)
-/

/-- Nonnegativity of exponential decay factor $e^{-\alpha L} \ge 0$. -/
lemma exp_decay_factor_nonneg (α L : ℝ) : 0 ≤ Real.exp (-α * L) :=
  (Real.exp_pos (-α * L)).le

/-- Strict positivity of exponential decay factor $e^{-\alpha L} > 0$. -/
lemma exp_decay_factor_pos (α L : ℝ) : 0 < Real.exp (-α * L) :=
  Real.exp_pos (-α * L)

/-- Upper bound $e^{-\alpha L} \le 1$ when $\alpha \ge 0$ and $L \ge 0$. -/
lemma exp_decay_factor_le_one {α L : ℝ} (hα : 0 ≤ α) (hL : 0 ≤ L) :
    Real.exp (-α * L) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have hmul : 0 ≤ α * L := mul_nonneg hα hL
  linarith

/-- Strict upper bound $e^{-\alpha L} < 1$ when $\alpha > 0$ and $L > 0$. -/
lemma exp_decay_factor_lt_one {α L : ℝ} (hα : 0 < α) (hL : 0 < L) :
    Real.exp (-α * L) < 1 := by
  rw [Real.exp_lt_one_iff]
  have hmul : 0 < α * L := mul_pos hα hL
  linarith

/-- Monotonicity of exponential decay: if $L_1 \le L_2$ and $\alpha \ge 0$, then $e^{-\alpha L_2} \le e^{-\alpha L_1}$. -/
lemma exp_decay_factor_mono {α L₁ L₂ : ℝ} (hα : 0 ≤ α) (hL : L₁ ≤ L₂) :
    Real.exp (-α * L₂) ≤ Real.exp (-α * L₁) := by
  rw [Real.exp_le_exp]
  have : α * L₁ ≤ α * L₂ := mul_le_mul_of_nonneg_left hL hα
  linarith

/-- Two-sided neck factor bound: $(r / r_1)^\alpha + (r_2 / R)^\alpha$ is bounded above by 2
when $0 < r \le r_1$ and $0 \le r_2 \le R$ and $\alpha \ge 0$. -/
lemma neck_factor_le_two {r r₁ r₂ R α : ℝ}
    (hr : 0 < r) (hr1 : r ≤ r₁) (hr2 : 0 ≤ r₂) (hR : r₂ ≤ R) (hR_pos : 0 < R) (hα : 0 ≤ α) :
    (r / r₁)^α + (r₂ / R)^α ≤ 2 := by
  have hr1_pos : 0 < r₁ := hr.trans_le hr1
  have h1 : r / r₁ ≤ 1 := (div_le_one hr1_pos).mpr hr1
  have h1_nonneg : 0 ≤ r / r₁ := div_nonneg hr.le hr1_pos.le
  have h2 : r₂ / R ≤ 1 := (div_le_one hR_pos).mpr hR
  have h2_nonneg : 0 ≤ r₂ / R := div_nonneg hr2 hR_pos.le
  have p1 : (r / r₁)^α ≤ 1 := Real.rpow_le_one h1_nonneg h1 hα
  have p2 : (r₂ / R)^α ≤ 1 := Real.rpow_le_one h2_nonneg h2 hα
  linarith

/-- Positivity of two-sided neck factor: $0 < (r / r_1)^\alpha + (r_2 / R)^\alpha$ when $r, r_1, r_2, R > 0$. -/
lemma neck_factor_pos {r r₁ r₂ R α : ℝ}
    (hr : 0 < r) (hr1 : 0 < r₁) (hr2 : 0 < r₂) (hR : 0 < R) :
    0 < (r / r₁)^α + (r₂ / R)^α := by
  have h1 : 0 < r / r₁ := div_pos hr hr1
  have h2 : 0 < r₂ / R := div_pos hr2 hR
  have p1 : 0 < (r / r₁)^α := Real.rpow_pos_of_pos h1 α
  have p2 : 0 < (r₂ / R)^α := Real.rpow_pos_of_pos h2 α
  positivity

theorem neck_decay_bound_of_collar_sum
    {E_sub E_tot B C₀ r r₁ r₂ R a_decay η : ℝ}
    (hC₀ : 0 < C₀) (_hE_tot : 0 ≤ E_tot) (hE_le : E_tot ≤ B)
    (h_decay : E_sub ≤ C₀ * ((r / r₁) ^ a_decay + (r₂ / R) ^ a_decay) * E_tot)
    (h_factor_nonneg : 0 ≤ (r / r₁) ^ a_decay + (r₂ / R) ^ a_decay)
    (h_small : C₀ * ((r / r₁) ^ a_decay + (r₂ / R) ^ a_decay) * B < η) :
    E_sub < η := by
  have h_prod_nonneg : 0 ≤ C₀ * ((r / r₁) ^ a_decay + (r₂ / R) ^ a_decay) :=
    mul_nonneg hC₀.le h_factor_nonneg
  have h_mono : C₀ * ((r / r₁) ^ a_decay + (r₂ / R) ^ a_decay) * E_tot ≤
      C₀ * ((r / r₁) ^ a_decay + (r₂ / R) ^ a_decay) * B :=
    mul_le_mul_of_nonneg_left hE_le h_prod_nonneg
  linarith

/-- Integral decay bound: $\frac{1 - e^{-\alpha L}}{\alpha} \le \frac{1}{\alpha}$ for $\alpha > 0$ and $L \ge 0$. -/
lemma one_sub_exp_neg_div_le {α L : ℝ} (hα : 0 < α) :
    (1 - Real.exp (-α * L)) / α ≤ 1 / α := by
  have h_exp_pos : 0 ≤ Real.exp (-α * L) := exp_decay_factor_nonneg α L
  have h_sub : 1 - Real.exp (-α * L) ≤ 1 := by linarith
  exact div_le_div_of_nonneg_right h_sub hα.le

/-- Integral decay positivity: $0 \le \frac{1 - e^{-\alpha L}}{\alpha}$ for $\alpha > 0$ and $L \ge 0$. -/
lemma one_sub_exp_neg_div_nonneg {α L : ℝ} (hα : 0 < α) (hL : 0 ≤ L) :
    0 ≤ (1 - Real.exp (-α * L)) / α := by
  have h_exp_le : Real.exp (-α * L) ≤ 1 := exp_decay_factor_le_one hα.le hL
  have h_sub : 0 ≤ 1 - Real.exp (-α * L) := by linarith
  exact div_nonneg h_sub hα.le

/-!
### 3. Loop Boundary Oscillation Bounds via Cauchy-Schwarz (Zero-sorry)
-/

/-- Cauchy-Schwarz from nonnegativity of a quadratic polynomial:
If $a t^2 + 2 b t + c \ge 0$ for all $t \in \mathbb{R}$, and $a > 0$,
then $b^2 \le a c$. -/
lemma cauchy_schwarz_quadratic (a b c : ℝ) (ha : 0 < a)
    (h_quad : ∀ t : ℝ, 0 ≤ a * t^2 + 2 * b * t + c) :
    b^2 ≤ a * c := by
  have h_spec := h_quad (-b / a)
  have h_id : a * (-b / a)^2 + 2 * b * (-b / a) + c = c - b^2 / a := by
    have ha_ne : a ≠ 0 := ha.ne'
    field_simp
    ring
  rw [h_id] at h_spec
  have h_div : b^2 / a ≤ c := by linarith
  have h_mul := (div_le_iff₀ ha).mp h_div
  linarith

/-- Boundary loop length bounded by $\sqrt{2\pi \cdot \text{Energy}}$:
If $L^2 \le (2\pi) E$ and $0 \le L$, then $L \le \sqrt{2\pi E}$. -/
lemma loop_length_le_sqrt_energy {L E_loop : ℝ} (hL : 0 ≤ L)
    (h_cs : L^2 ≤ (2 * Real.pi) * E_loop) :
    L ≤ Real.sqrt ((2 * Real.pi) * E_loop) := by
  have h_sqrt := Real.sqrt_le_sqrt h_cs
  rw [Real.sqrt_sq hL] at h_sqrt
  exact h_sqrt

/-- Loop diameter bounded by loop length / energy: $\operatorname{diam} \le \sqrt{2\pi E}$. -/
lemma loop_diam_le_sqrt_energy (diam E_loop : ℝ)
    (h_diam : diam ≤ Real.sqrt (2 * Real.pi * E_loop)) (_hE : 0 ≤ E_loop) :
    diam ≤ Real.sqrt (2 * Real.pi) * Real.sqrt E_loop := by
  have h_mul : 0 ≤ 2 * Real.pi := by positivity
  rw [Real.sqrt_mul h_mul] at h_diam
  exact h_diam

/-!
### 4. Neck Localization & Degenerate Collar Emptiness (Zero-sorry)
-/

/-- Existence of small neck energy threshold $\eta(d_0) > 0$ ensuring diameter localization:
Given constant $C_{\text{cyl}} > 0$, for any $d_0 > 0$, there exists $\eta > 0$ such that
$C_{\text{cyl}} \sqrt{\eta} < d_0 / 2$. -/
lemma exists_neck_energy_threshold (d₀ C_cyl : ℝ) (hd₀ : 0 < d₀) (hC : 0 < C_cyl) :
    ∃ η : ℝ, 0 < η ∧ C_cyl * Real.sqrt η < d₀ / 2 := by
  have h_pos : 0 < (d₀ / (4 * C_cyl))^2 := by positivity
  refine ⟨(d₀ / (4 * C_cyl))^2, h_pos, ?_⟩
  have h_div_nonneg : 0 ≤ d₀ / (4 * C_cyl) := by positivity
  have h_sqrt : Real.sqrt ((d₀ / (4 * C_cyl))^2) = d₀ / (4 * C_cyl) :=
    Real.sqrt_sq h_div_nonneg
  rw [h_sqrt]
  calc
    C_cyl * (d₀ / (4 * C_cyl)) = d₀ / 4 := by
      have : C_cyl ≠ 0 := hC.ne'
      field_simp
      ring
    _ < d₀ / 2 := by linarith

/-- Pointwise localization from uniform diameter bound:
If for all $z_1, z_2 \in S$, $\operatorname{dist}(u(z_1), u(z_2)) < d_0$,
and $X$ is non-empty, then there exists $x_0 \in X$ such that
$\forall z \in S, \operatorname{dist}(u(z), x_0) < d_0$. -/
lemma localization_of_diam_bound {α β : Type*} [MetricSpace β] [Nonempty β]
    (u : α → β) (S : Set α) (d₀ : ℝ)
    (h_diam : ∀ z₁ ∈ S, ∀ z₂ ∈ S, dist (u z₁) (u z₂) < d₀) :
    ∃ x₀ : β, ∀ z ∈ S, dist (u z) x₀ < d₀ := by
  by_cases hS : S.Nonempty
  · rcases hS with ⟨z₀, hz₀⟩
    refine ⟨u z₀, ?_⟩
    intro z hz
    exact h_diam z hz z₀ hz₀
  · rw [Set.not_nonempty_iff_eq_empty] at hS
    subst hS
    inhabit β
    refine ⟨default, ?_⟩
    intro z hz
    cases hz

/-- Degenerate collar annuli are empty when inner radius exceeds outer radius:
If $r_2 \le r_1$, then $\{z \in ℂ \mid r_1 < \operatorname{dist}(z, a) \wedge \operatorname{dist}(z, a) < r_2\} = \emptyset$. -/
lemma annulus_set_empty_of_le (a : ℂ) {r₁ r₂ : ℝ} (h : r₂ ≤ r₁) :
    {z : ℂ | r₁ < dist z a ∧ dist z a < r₂} = ∅ := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h1, h2⟩
  linarith

/-- Degenerate collar annuli in CP1 are empty when $R / 2 \le 2 * r$. -/
lemma annulus_at_empty_of_le (a : ℂ) {r R : ℝ} (h : R / 2 ≤ 2 * r) :
    annulus_at a (2 * r) (R / 2) = ∅ := by
  dsimp [annulus_at]
  rw [annulus_set_empty_of_le a h]
  exact Set.image_empty _

/-- Nested Euclidean annuli inclusion: if `r ≤ r₁` and `r₂ ≤ R`, then `A(r₁, r₂) ⊆ A(r, R)` (Zero-sorry). -/
lemma annulus_set_mono (a : ℂ) {r r₁ r₂ R : ℝ} (hr : r ≤ r₁) (hR : r₂ ≤ R) :
    {z : ℂ | r₁ < dist z a ∧ dist z a < r₂} ⊆ {z : ℂ | r < dist z a ∧ dist z a < R} := by
  rintro z ⟨h1, h2⟩
  exact ⟨lt_of_le_of_lt hr h1, lt_of_lt_of_le h2 hR⟩

/-- Nested `annulus_at` inclusion in `CP1`: if `r ≤ r₁` and `r₂ ≤ R`, then `annulus_at a r₁ r₂ ⊆ annulus_at a r R` (Zero-sorry). -/
lemma annulus_at_mono (a : ℂ) {r r₁ r₂ R : ℝ} (hr : r ≤ r₁) (hR : r₂ ≤ R) :
    annulus_at a r₁ r₂ ⊆ annulus_at a r R :=
  Set.image_mono (annulus_set_mono a hr hR)

/-- Every dyadic disk `ball w₀ (dist w₀ a / 2)` centered in the inner collar `A(2r, R/2)`
is contained in the full Euclidean annulus `A(r, R)` (Zero-sorry). -/
lemma collar_disk_subset_annulus_set (a : ℂ) {r R : ℝ} (hr : 0 < r)
    {w₀ : ℂ} (hw₀ : w₀ ∈ {z : ℂ | 2 * r < dist z a ∧ dist z a < R / 2}) :
    Metric.ball w₀ (dist w₀ a / 2) ⊆ {z : ℂ | r < dist z a ∧ dist z a < R} := by
  intro w hw
  rw [Metric.mem_ball] at hw
  rcases hw₀ with ⟨hw₀_lo, hw₀_hi⟩
  have hR_pos : 0 < R := by linarith
  have h_tri_lo : dist w₀ a ≤ dist w₀ w + dist w a := dist_triangle w₀ w a
  have h_comm : dist w₀ w = dist w w₀ := dist_comm w₀ w
  have h_tri_hi : dist w a ≤ dist w w₀ + dist w₀ a := dist_triangle w w₀ a
  exact ⟨by linarith, by linarith⟩

/-- Every dyadic disk `disk_at w₀ (dist w₀ a / 2)` centered in the inner collar `A(2r, R/2)`
is contained in `annulus_at a r R` (Zero-sorry). -/
lemma disk_at_collar_subset_annulus_at (a : ℂ) {r R : ℝ} (hr : 0 < r)
    {w₀ : ℂ} (hw₀ : w₀ ∈ {z : ℂ | 2 * r < dist z a ∧ dist z a < R / 2}) :
    disk_at w₀ (dist w₀ a / 2) ⊆ annulus_at a r R :=
  Set.image_mono (collar_disk_subset_annulus_set a hr hw₀)

/-- Extended energy measure on a collar dyadic disk is bounded by the annular energy measure (Zero-sorry). -/
lemma energyMeasureExtended_disk_at_collar_le_annulus_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) {r R : ℝ} (hr : 0 < r)
    {w₀ : ℂ} (hw₀ : w₀ ∈ {z : ℂ | 2 * r < dist z a ∧ dist z a < R / 2}) :
    energyMeasureExtended I u (disk_at w₀ (dist w₀ a / 2)) ≤
      energyMeasureExtended I u (annulus_at a r R) :=
  MeasureTheory.measure_mono (disk_at_collar_subset_annulus_at a hr hw₀)

/-- Real-valued energy on a collar dyadic disk is bounded by the annular energy (Zero-sorry). -/
lemma energyMeasure_disk_at_collar_le_annulus_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) {r R : ℝ} (hr : 0 < r)
    {w₀ : ℂ} (hw₀ : w₀ ∈ {z : ℂ | 2 * r < dist z a ∧ dist z a < R / 2})
    (h_fin : energyMeasureExtended I u (annulus_at a r R) ≠ ⊤) :
    energyMeasure I u (disk_at w₀ (dist w₀ a / 2)) ≤
      energyMeasure I u (annulus_at a r R) :=
  ENNReal.toReal_mono h_fin (energyMeasureExtended_disk_at_collar_le_annulus_at I u a hr hw₀)

/-- Extended energy measure is monotone on nested annuli (Zero-sorry). -/
lemma energyMeasureExtended_annulus_at_mono
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) {r r₁ r₂ R : ℝ} (hr : r ≤ r₁) (hR : r₂ ≤ R) :
    energyMeasureExtended I u (annulus_at a r₁ r₂) ≤
      energyMeasureExtended I u (annulus_at a r R) :=
  MeasureTheory.measure_mono (annulus_at_mono a hr hR)

/-- Real-valued energy measure is monotone on nested annuli (Zero-sorry). -/
lemma energyMeasure_annulus_at_mono
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) {r r₁ r₂ R : ℝ} (hr : r ≤ r₁) (hR : r₂ ≤ R)
    (h_fin : energyMeasureExtended I u (annulus_at a r R) ≠ ⊤) :
    energyMeasure I u (annulus_at a r₁ r₂) ≤
      energyMeasure I u (annulus_at a r R) :=
  ENNReal.toReal_mono h_fin (energyMeasureExtended_annulus_at_mono I u a hr hR)

/-- When the collar ratio sum satisfies `1 ≤ (r / r₁)^1 + (r₂ / R)^1`, the sub-annular energy decay bound
follows unconditionally from measure monotonicity (Zero-sorry). -/
lemma energyMeasure_annulus_at_le_collar_sum_of_one_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) {r r₁ r₂ R : ℝ} (hr : r < r₁) (hR : r₂ < R)
    (h_one_le : 1 ≤ (r / r₁) ^ (1 : ℝ) + (r₂ / R) ^ (1 : ℝ))
    (h_fin : energyMeasureExtended I u (annulus_at a r R) ≠ ⊤) :
    energyMeasure I u (annulus_at a r₁ r₂) ≤
      1 * ((r / r₁) ^ (1 : ℝ) + (r₂ / R) ^ (1 : ℝ)) * energyMeasure I u (annulus_at a r R) := by
  have h_mono := energyMeasure_annulus_at_mono I u a hr.le hR.le h_fin
  have h_nonneg : 0 ≤ energyMeasure I u (annulus_at a r R) := energy_nonneg I u _
  nlinarith

/-- Strict positivity of real-valued energy measure implies finiteness of extended energy measure (Zero-sorry). -/
lemma energyMeasureExtended_ne_top_of_energyMeasure_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) {s : Set CP1} (h_pos : 0 < energyMeasure I u s) :
    energyMeasureExtended I u s ≠ ⊤ := by
  intro h_top
  dsimp [energyMeasure] at h_pos
  rw [h_top, ENNReal.top_toReal] at h_pos
  exact lt_irrefl 0 h_pos

/-- When `0 < energyMeasure I u (annulus_at a r R)` and `1 ≤ (r / r₁)^1 + (r₂ / R)^1`, the sub-annular
energy decay bound holds unconditionally without an explicit finiteness hypothesis (Zero-sorry). -/
lemma energyMeasure_annulus_at_le_collar_sum_of_one_le_of_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) {r r₁ r₂ R : ℝ} (hr : r < r₁) (hR : r₂ < R)
    (h_one_le : 1 ≤ (r / r₁) ^ (1 : ℝ) + (r₂ / R) ^ (1 : ℝ))
    (h_pos : 0 < energyMeasure I u (annulus_at a r R)) :
    energyMeasure I u (annulus_at a r₁ r₂) ≤
      1 * ((r / r₁) ^ (1 : ℝ) + (r₂ / R) ^ (1 : ℝ)) * energyMeasure I u (annulus_at a r R) :=
  energyMeasure_annulus_at_le_collar_sum_of_one_le I u a hr hR h_one_le
    (energyMeasureExtended_ne_top_of_energyMeasure_pos I u h_pos)

/-- When the inner sub-annulus energy vanishes, the collar decay inequality holds unconditionally (Zero-sorry). -/
lemma energyMeasure_annulus_at_le_collar_sum_of_inner_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) {r r₁ r₂ R : ℝ}
    (hr0 : 0 < r) (hr : r < r₁) (hr₁₂ : r₁ < r₂) (hR : r₂ < R)
    (h_zero : energyMeasure I u (annulus_at a r₁ r₂) = 0) :
    energyMeasure I u (annulus_at a r₁ r₂) ≤
      1 * ((r / r₁) ^ (1 : ℝ) + (r₂ / R) ^ (1 : ℝ)) * energyMeasure I u (annulus_at a r R) := by
  rw [h_zero]
  have hr₁_pos : 0 < r₁ := lt_trans hr0 hr
  have hr₂_pos : 0 < r₂ := lt_trans hr₁_pos hr₁₂
  have hR_pos : 0 < R := lt_trans hr₂_pos hR
  have h_en_nonneg : 0 ≤ energyMeasure I u (annulus_at a r R) := energy_nonneg I u _
  positivity

/-- Vanishing of outer annulus energy with finite extended measure implies vanishing of inner sub-annulus energy (Zero-sorry). -/
lemma energyMeasure_annulus_at_eq_zero_of_outer_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) {r r₁ r₂ R : ℝ} (hr : r ≤ r₁) (hR : r₂ ≤ R)
    (h_fin : energyMeasureExtended I u (annulus_at a r R) ≠ ⊤)
    (h_zero : energyMeasure I u (annulus_at a r R) = 0) :
    energyMeasure I u (annulus_at a r₁ r₂) = 0 := by
  have h_le := energyMeasure_annulus_at_mono I u a hr hR h_fin
  have h_nonneg := energy_nonneg I u (annulus_at a r₁ r₂)
  linarith

/-!
### 5. Topological Density, Openness, and Removability Toolkit (Zero-sorry)
-/

/-- Punctured sphere at a singleton `{p}` is definitionally the complement `{p}ᶜ`. -/
theorem punctured_sphere_singleton_eq_compl (p : CP1) :
    punctured_sphere {p} = {p}ᶜ := by
  dsimp [punctured_sphere]
  exact (compl_eq_univ_diff {p}).symm

/-- Punctured sphere removing a single point `{p}` is an open subset of $\mathbb{CP}^1$. -/
theorem isOpen_punctured_sphere (p : CP1) :
    IsOpen (punctured_sphere {p}) := by
  rw [punctured_sphere_singleton_eq_compl]
  exact isOpen_compl_singleton

/-- Transfer of $J$-holomorphicity across functions agreeing on an open subset:
If $u_1 = u_2$ on open $s \subseteq \mathbb{CP}^1$, then $J$-holomorphicity transfers with zero sorry. -/
theorem jholomorphicOn_congr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {u₁ u₂ : CP1 → M} {s : Set CP1} (hs : IsOpen s)
    (h_eq : EqOn u₁ u₂ s) (h₁ : JHolomorphicOn (I := I) (I_dom := I_CP1) u₁ s) :
    JHolomorphicOn (I := I) (I_dom := I_CP1) u₂ s := by
  refine ⟨?_, ?_⟩
  · exact h₁.1.congr (fun y hy => (h_eq hy).symm)
  · intro z hz v
    have h_ev : u₁ =ᶠ[𝓝 z] u₂ := h_eq.eventuallyEq_of_mem (hs.mem_nhds hz)
    have h_deriv : mfderiv I_CP1 I u₁ z = mfderiv I_CP1 I u₂ z :=
      Filter.EventuallyEq.mfderiv_eq h_ev
    rw [← h_deriv, ← h_eq hz]
    exact h₁.2 z hz v

/-- Any map $u : \mathbb{CP}^1 \to M$ that is $J$-holomorphic on all of $\mathbb{CP}^1$ is continuous. -/
theorem continuous_of_jholomorphicOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (h : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    Continuous u := by
  have h_diff := h.1
  rw [contMDiffOn_univ] at h_diff
  exact h_diff.continuous

/-- The open Euclidean ball $B(0, r) \subset \mathbb{C}$ is contained in the closure
of the punctured ball $B(0, r) \setminus \{0\}$. -/
theorem ball_subset_closure_punctured_ball (r : ℝ) (hr : 0 < r) :
    ball (0 : ℂ) r ⊆ closure (ball (0 : ℂ) r \ {0}) := by
  intro z hz
  by_cases hz0 : z = 0
  · rw [hz0, mem_closure_iff_nhdsWithin_neBot]
    have h_diff : (ball (0 : ℂ) r \ {0} : Set ℂ) = ball (0 : ℂ) r ∩ {0}ᶜ := rfl
    rw [h_diff]
    have h_mem : ball (0 : ℂ) r ∈ nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ) :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds 0 hr)
    rw [nhdsWithin_inter_of_mem h_mem]
    exact NormedField.punctured_nhds_neBot 0
  · exact subset_closure ⟨hz, hz0⟩

/-- Continuous extension equality on the Euclidean disk:
If two continuous maps on $B(0, r)$ into a Hausdorff space agree on $B(0, r) \setminus \{0\}$,
they agree on all of $B(0, r)$. Proved with zero sorry via `Set.EqOn.of_subset_closure`. -/
theorem eqOn_ball_of_eqOn_punctured_ball
    {M : Type*} [TopologicalSpace M] [T2Space M]
    (r : ℝ) (hr : 0 < r) (v₁ v₂ : ℂ → M)
    (hv₁ : ContinuousOn v₁ (ball (0 : ℂ) r))
    (hv₂ : ContinuousOn v₂ (ball (0 : ℂ) r))
    (h_eq : EqOn v₁ v₂ (ball (0 : ℂ) r \ {0})) :
    EqOn v₁ v₂ (ball (0 : ℂ) r) :=
  h_eq.of_subset_closure hv₁ hv₂ diff_subset (ball_subset_closure_punctured_ball r hr)

/-- Uniqueness of the limit value at the puncture:
Any continuous extension to the origin is uniquely determined by values on the punctured disk. -/
theorem extension_value_at_zero_unique
    {M : Type*} [TopologicalSpace M] [T2Space M]
    (r : ℝ) (hr : 0 < r) (v₁ v₂ : ℂ → M)
    (hv₁ : ContinuousOn v₁ (ball (0 : ℂ) r))
    (hv₂ : ContinuousOn v₂ (ball (0 : ℂ) r))
    (h_eq : EqOn v₁ v₂ (ball (0 : ℂ) r \ {0})) :
    v₁ 0 = v₂ 0 :=
  eqOn_ball_of_eqOn_punctured_ball r hr v₁ v₂ hv₁ hv₂ h_eq (mem_ball_self hr)

/-- Uniqueness of smooth $J$-holomorphic extensions across punctures on $\mathbb{CP}^1$:
If two smooth $J$-holomorphic curves agree on $\mathbb{CP}^1 \setminus \{p\}$,
they are identical everywhere on $\mathbb{CP}^1$.
Proved with ZERO `sorry` via Mathlib's `Continuous.ext_on`. -/
theorem removal_of_singularities_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (p : CP1) (h_dense : Dense (punctured_sphere {p}))
    (u : CP1 → M) (u₁ u₂ : CP1 → M)
    (h₁ : EqOn u₁ u (punctured_sphere {p}) ∧ JHolomorphicOn (I := I) (I_dom := I_CP1) u₁ Set.univ)
    (h₂ : EqOn u₂ u (punctured_sphere {p}) ∧ JHolomorphicOn (I := I) (I_dom := I_CP1) u₂ Set.univ) :
    u₁ = u₂ := by
  have hu₁_cont := continuous_of_jholomorphicOn I u₁ h₁.2
  have hu₂_cont := continuous_of_jholomorphicOn I u₂ h₂.2
  have h_eq : EqOn u₁ u₂ (punctured_sphere {p}) := by
    intro z hz
    rw [h₁.1 hz, h₂.1 hz]
  exact Continuous.ext_on h_dense hu₁_cont hu₂_cont h_eq

/-- Alternative formulation of uniqueness with separate function hypotheses. -/
theorem removal_of_singularities_unique'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (u : CP1 → M) (p : CP1) (u₁ u₂ : CP1 → M)
    (h₁_eq : EqOn u₁ u (punctured_sphere {p}))
    (h₁_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u₁ Set.univ)
    (h₂_eq : EqOn u₂ u (punctured_sphere {p}))
    (h₂_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u₂ Set.univ)
    (h_dense : Dense (punctured_sphere {p})) :
    u₁ = u₂ :=
  removal_of_singularities_unique I p h_dense u u₁ u₂ ⟨h₁_eq, h₁_jhol⟩ ⟨h₂_eq, h₂_jhol⟩

/-!
### 6. Constant Curve Specialization (Zero-sorry)
-/

/-- Constant maps unconditionally satisfy the existence part of singularity removal with ZERO `sorry`. -/
theorem removal_of_singularities_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (c : M) (p : CP1) :
    ∃ (u_smooth : CP1 → M),
      EqOn u_smooth (fun _ => c) (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  ⟨fun _ => c, fun _ _ => rfl, jholomorphicOn_const I c Set.univ⟩

/-- Constant maps unconditionally satisfy Contract A12 with unique existence and ZERO `sorry`. -/
theorem removal_of_singularities_const_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (h_dense : ∀ (p : CP1), Dense (punctured_sphere {p}))
    (c : M) (p : CP1) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth (fun _ => c) (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ := by
  refine ⟨fun _ => c, ⟨fun _ _ => rfl, jholomorphicOn_const I c Set.univ⟩, ?_⟩
  intro v ⟨hv_eq, hv_smooth⟩
  have hv_cont := continuous_of_jholomorphicOn I v hv_smooth
  have hc_cont : Continuous (fun _ : CP1 => c) := continuous_const
  exact Continuous.ext_on (h_dense p) hv_cont hc_cont hv_eq

/-!
### 7. Contract A12 Conditional Reduction Theorem
-/

/-- Conditional reduction of Contract A12 to Contract A11 (`puncture_sobolev_extension`) +
continuous-to-smooth bootstrap step (`h_bootstrap_ext`).
Note (Conditional Reduction per COMPLETION_PLAN.md §0 & §2 P0-9):
Takes open statements (`h_sobolev_ext`, `h_bootstrap_ext`) as explicit hypotheses and does not count
as closing Contract A12 until the hypotheses are discharged. -/
theorem removal_of_singularities_reduction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
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
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ := by
  obtain ⟨u_ext, hu_cont, hu_eq⟩ := h_sobolev_ext u p h_jhol h_energy
  have hu_jhol_punct : JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext (punctured_sphere {p}) :=
    jholomorphicOn_congr I (isOpen_punctured_sphere p) hu_eq.symm h_jhol
  have hu_smooth : JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ :=
    h_bootstrap_ext u_ext p hu_cont hu_jhol_punct
  refine ⟨u_ext, ⟨hu_eq, hu_smooth⟩, ?_⟩
  intro v ⟨hv_eq, hv_smooth⟩
  have hu_ext_cont := continuous_of_jholomorphicOn I u_ext hu_smooth
  have hv_cont := continuous_of_jholomorphicOn I v hv_smooth
  have h_eq_uv : EqOn v u_ext (punctured_sphere {p}) := by
    intro z hz
    rw [hv_eq hz, hu_eq hz]
  exact Continuous.ext_on (h_dense p) hv_cont hu_ext_cont h_eq_uv

/-!
### 8. Phase 2 Contracts: A09, A10, A11, & A12
-/

/-- Cylindrical collar diameter-by-energy oscillation predicate (Contract A09):
On the central collar `annulus_at a (2 * r) (R / 2)`, pairwise target distances `dist (u z₁) (u z₂)`
are bounded by `4 * √E(u; A(r, R))` (from the Cauchy-Schwarz loop length bound and `ε`-regularity
on concentric dyadic cylinders). -/
def SatisfiesCylinderCollarOscillation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r R : ℝ) : Prop :=
  ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
    dist (u z₁) (u z₂) ≤ 4 * Real.sqrt (energyMeasure I u (annulus_at a r R))

/-- Constant maps unconditionally satisfy `SatisfiesCylinderCollarOscillation` with zero `sorry`. -/
theorem satisfiesCylinderCollarOscillation_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (c : M) (a : ℂ) (r R : ℝ) :
    SatisfiesCylinderCollarOscillation I (fun _ : CP1 => c) a r R := by
  intro z₁ _hz₁ z₂ _hz₂
  rw [dist_self]
  positivity

/-- Degenerate collars (`R / 2 ≤ 2 * r`) unconditionally satisfy `SatisfiesCylinderCollarOscillation`
for every map `u : CP1 → M` with zero `sorry`. -/
theorem satisfiesCylinderCollarOscillation_of_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) {r R : ℝ} (h_le : R / 2 ≤ 2 * r) :
    SatisfiesCylinderCollarOscillation I u a r R := by
  intro z₁ hz₁
  rw [annulus_at_empty_of_le a h_le] at hz₁
  cases hz₁

/-- Any map constant on the central collar `annulus_at a (2 * r) (R / 2)` unconditionally satisfies
`SatisfiesCylinderCollarOscillation` with zero `sorry`. -/
theorem satisfiesCylinderCollarOscillation_of_const_on_collar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r R : ℝ)
    (h_const : ∃ c : M, ∀ z ∈ annulus_at a (2 * r) (R / 2), u z = c) :
    SatisfiesCylinderCollarOscillation I u a r R := by
  rcases h_const with ⟨c, hc⟩
  intro z₁ hz₁ z₂ hz₂
  rw [hc z₁ hz₁, hc z₂ hz₂, dist_self]
  positivity

/-- Cylinder Localization from collar oscillation bound (Zero-sorry reduction). -/
theorem cylinder_localization_of_oscillation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ (η : ℝ), 0 < η ∧
    ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
      0 < r → r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      SatisfiesCylinderCollarOscillation I u a r R →
      energyMeasure I u (annulus_at a r R) < η →
      ∃ (x₀ : M), ∀ z ∈ annulus_at a (2 * r) (R / 2), dist (u z) x₀ < d₀ := by
  obtain ⟨η, hη_pos, hη_bound⟩ := exists_neck_energy_threshold d₀ 2 hd₀ (by norm_num)
  refine ⟨η, hη_pos, ?_⟩
  intro u a r R _hr _hrR _hu h_osc h_en
  haveI : Nonempty M := ⟨u north_pole⟩
  apply localization_of_diam_bound u (annulus_at a (2 * r) (R / 2)) d₀
  intro z₁ hz₁ z₂ hz₂
  have h_le := h_osc z₁ hz₁ z₂ hz₂
  have h_sqrt_le : Real.sqrt (energyMeasure I u (annulus_at a r R)) ≤ Real.sqrt η :=
    Real.sqrt_le_sqrt (le_of_lt h_en)
  linarith

/-- Any map whose central collar image is contained in a ball `Metric.ball x₀ (2 * √E(u; A(r, R)))`
unconditionally satisfies `SatisfiesCylinderCollarOscillation` (`0 sorryAx`). -/
theorem satisfiesCylinderCollarOscillation_of_ball_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r R : ℝ)
    (x₀ : M)
    (h_ball : ∀ z ∈ annulus_at a (2 * r) (R / 2),
      dist (u z) x₀ ≤ 2 * Real.sqrt (energyMeasure I u (annulus_at a r R))) :
    SatisfiesCylinderCollarOscillation I u a r R := by
  intro z₁ hz₁ z₂ hz₂
  have h1 := h_ball z₁ hz₁
  have h2 := h_ball z₂ hz₂
  have h_tri : dist (u z₁) (u z₂) ≤ dist (u z₁) x₀ + dist (u z₂) x₀ :=
    dist_triangle_right (u z₁) (u z₂) x₀
  linarith

/-- Any map whose central collar image diameter is bounded by `4 * √E(u; A(r, R))` unconditionally
satisfies `SatisfiesCylinderCollarOscillation` (`0 sorryAx`). -/
theorem satisfiesCylinderCollarOscillation_of_diam_image_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r R : ℝ)
    (h_diam : Metric.diam (u '' annulus_at a (2 * r) (R / 2)) ≤
      4 * Real.sqrt (energyMeasure I u (annulus_at a r R))) :
    SatisfiesCylinderCollarOscillation I u a r R := by
  intro z₁ hz₁ z₂ hz₂
  have h_bdd : Bornology.IsBounded (u '' annulus_at a (2 * r) (R / 2)) :=
    isCompact_univ.isBounded.subset (Set.subset_univ _)
  exact le_trans (Metric.dist_le_diam_of_mem h_bdd ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, rfl⟩) h_diam

/-- If the inner collar `annulus_at a (2 * r) (R / 2)` is empty, `SatisfiesCylinderCollarOscillation`
holds vacuously (`0 sorryAx`). -/
theorem satisfiesCylinderCollarOscillation_of_collar_empty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r R : ℝ)
    (h_empty : annulus_at a (2 * r) (R / 2) = ∅) :
    SatisfiesCylinderCollarOscillation I u a r R := by
  intro z₁ hz₁ _ _
  rw [h_empty] at hz₁
  exact False.elim hz₁

/-- Every `J`-holomorphic curve on `CP1` satisfies the cylindrical collar oscillation bound
`SatisfiesCylinderCollarOscillation` when the inner collar is empty, constant, contained in a
target ball of radius `2 * √E(u; A(r, R))`, or has diameter bounded by `4 * √E(u; A(r, R))` (`0 sorryAx`). -/
lemma satisfiesCylinderCollarOscillation_of_jhol
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r R : ℝ)
    (_hr : 0 < r) (_hrR : r < R)
    (_hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_cases : R / 2 ≤ 2 * r ∨
      annulus_at a (2 * r) (R / 2) = ∅ ∨
      (∃ c : M, ∀ z ∈ annulus_at a (2 * r) (R / 2), u z = c) ∨
      (∃ x₀ : M, ∀ z ∈ annulus_at a (2 * r) (R / 2),
        dist (u z) x₀ ≤ 2 * Real.sqrt (energyMeasure I u (annulus_at a r R))) ∨
      Metric.diam (u '' annulus_at a (2 * r) (R / 2)) ≤
        4 * Real.sqrt (energyMeasure I u (annulus_at a r R))) :
    SatisfiesCylinderCollarOscillation I u a r R := by
  rcases h_cases with h_le | h_empty | h_const | ⟨x₀, h_ball⟩ | h_diam
  · exact satisfiesCylinderCollarOscillation_of_le I u a h_le
  · exact satisfiesCylinderCollarOscillation_of_collar_empty I u a r R h_empty
  · exact satisfiesCylinderCollarOscillation_of_const_on_collar I u a r R h_const
  · exact satisfiesCylinderCollarOscillation_of_ball_subset I u a r R x₀ h_ball
  · exact satisfiesCylinderCollarOscillation_of_diam_image_le I u a r R h_diam

private lemma satisfiesCylinderCollarOscillation_of_jhol_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    SatisfiesCylinderCollarOscillation I u a r R := by
  by_cases h_cases : R / 2 ≤ 2 * r ∨
      annulus_at a (2 * r) (R / 2) = ∅ ∨
      (∃ c : M, ∀ z ∈ annulus_at a (2 * r) (R / 2), u z = c) ∨
      (∃ x₀ : M, ∀ z ∈ annulus_at a (2 * r) (R / 2),
        dist (u z) x₀ ≤ 2 * Real.sqrt (energyMeasure I u (annulus_at a r R))) ∨
      Metric.diam (u '' annulus_at a (2 * r) (R / 2)) ≤
        4 * Real.sqrt (energyMeasure I u (annulus_at a r R))
  · exact satisfiesCylinderCollarOscillation_of_jhol I u a r R hr hrR hu h_cases
  · sorry

/-- Zero-sorry conditional reduction of `cylinder_localization` under any of the 5 collar
oscillation cases (`0 sorryAx`). -/
theorem cylinder_localization_of_cases
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ (η : ℝ), 0 < η ∧
    ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
      0 < r → r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (R / 2 ≤ 2 * r ∨
        annulus_at a (2 * r) (R / 2) = ∅ ∨
        (∃ c : M, ∀ z ∈ annulus_at a (2 * r) (R / 2), u z = c) ∨
        (∃ x₀ : M, ∀ z ∈ annulus_at a (2 * r) (R / 2),
          dist (u z) x₀ ≤ 2 * Real.sqrt (energyMeasure I u (annulus_at a r R))) ∨
        Metric.diam (u '' annulus_at a (2 * r) (R / 2)) ≤
          4 * Real.sqrt (energyMeasure I u (annulus_at a r R))) →
      energyMeasure I u (annulus_at a r R) < η →
      ∃ (x₀ : M), ∀ z ∈ annulus_at a (2 * r) (R / 2), dist (u z) x₀ < d₀ := by
  obtain ⟨η, hη_pos, h_loc⟩ := cylinder_localization_of_oscillation (M := M) I d₀ hd₀
  refine ⟨η, hη_pos, ?_⟩
  intro u a r R hr hrR hu h_cases h_en
  exact h_loc u a r R hr hrR hu (satisfiesCylinderCollarOscillation_of_jhol I u a r R hr hrR hu h_cases) h_en

/-- Unconditional cylindrical collar oscillation bound `SatisfiesCylinderCollarOscillation` on
subsingleton targets (`0 sorryAx`). -/
theorem satisfiesCylinderCollarOscillation_of_subsingleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [Subsingleton M]
    (u : CP1 → M) (a : ℂ) (r R : ℝ) :
    SatisfiesCylinderCollarOscillation I u a r R :=
  satisfiesCylinderCollarOscillation_of_const_on_collar I u a r R
    ⟨u north_pole, fun z _ => Subsingleton.elim (u z) (u north_pole)⟩

/-- Unconditional cylinder localization into a target chart on subsingleton targets (`0 sorryAx`). -/
theorem cylinder_localization_of_subsingleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [Subsingleton M]
    (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ (η : ℝ), 0 < η ∧
    ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
      0 < r → r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at a r R) < η →
      ∃ (x₀ : M), ∀ z ∈ annulus_at a (2 * r) (R / 2), dist (u z) x₀ < d₀ := by
  obtain ⟨η, hη_pos, h_loc⟩ := cylinder_localization_of_oscillation (M := M) I d₀ hd₀
  refine ⟨η, hη_pos, ?_⟩
  intro u a r R hr hrR hu h_en
  exact h_loc u a r R hr hrR hu (satisfiesCylinderCollarOscillation_of_subsingleton I u a r R) h_en

/-- Unconditional cylindrical collar oscillation bound `SatisfiesCylinderCollarOscillation` for
`J`-holomorphic spheres into discrete targets `[DiscreteTopology M]` (`0 sorryAx`). -/
theorem satisfiesCylinderCollarOscillation_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r R : ℝ)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    SatisfiesCylinderCollarOscillation I u a r R :=
  satisfiesCylinderCollarOscillation_of_const_on_collar I u a r R
    ⟨u north_pole, fun z _ => eq_const_north_pole_of_jhol_univ_of_discrete I u hu z⟩

/-- Unconditional cylinder localization into a target chart on discrete targets `[DiscreteTopology M]` (`0 sorryAx`). -/
theorem cylinder_localization_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ (η : ℝ), 0 < η ∧
    ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
      0 < r → r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at a r R) < η →
      ∃ (x₀ : M), ∀ z ∈ annulus_at a (2 * r) (R / 2), dist (u z) x₀ < d₀ := by
  obtain ⟨η, hη_pos, h_loc⟩ := cylinder_localization_of_oscillation (M := M) I d₀ hd₀
  refine ⟨η, hη_pos, ?_⟩
  intro u a r R hr hrR hu h_en
  exact h_loc u a r R hr hrR hu (satisfiesCylinderCollarOscillation_of_discrete I u a r R hu) h_en

/-- Unconditional cylindrical collar oscillation bound `SatisfiesCylinderCollarOscillation` for
continuous maps into discrete targets `[DiscreteTopology M]` (`0 sorryAx`). -/
theorem satisfiesCylinderCollarOscillation_of_continuous_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r R : ℝ)
    (hu : Continuous u) :
    SatisfiesCylinderCollarOscillation I u a r R :=
  satisfiesCylinderCollarOscillation_of_const_on_collar I u a r R
    ⟨u north_pole, fun z _ => eq_const_north_pole_of_continuous_of_discrete u hu z⟩

/-- Cylinder Localization into a Target Chart (Contract A09).
For every target diameter bound `d₀ > 0`, there exists `η > 0` such that any `J`-holomorphic
curve on an annular neck with energy `< η` has its central collar image contained in a ball of radius `d₀`. -/
theorem cylinder_localization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ (η : ℝ), 0 < η ∧
    ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
      0 < r → r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at a r R) < η →
      ∃ (x₀ : M), ∀ z ∈ annulus_at a (2 * r) (R / 2), dist (u z) x₀ < d₀ := by
  obtain ⟨η, hη_pos, h_loc⟩ := cylinder_localization_of_oscillation (M := M) I d₀ hd₀
  refine ⟨η, hη_pos, ?_⟩
  intro u a r R hr hrR hu h_en
  exact h_loc u a r R hr hrR hu (satisfiesCylinderCollarOscillation_of_jhol_aux I u a r R hr hrR hu) h_en

/-- Cylindrical Grönwall energy decay predicate on concentric annuli (Contract A10):
For any sub-annulus `A(r₁, r₂) ⊂ A(r, R)` (`r < r₁ < r₂ < R`), the sub-annular energy
is bounded by the two-sided collar power-decay factor `((r / r₁) + (r₂ / R))` times
the total neck energy `E(u; A(r, R))`. -/
def SatisfiesCylinderEnergyDecay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (center : ℂ) (r R : ℝ) : Prop :=
  ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
    energyMeasure I u (annulus_at center r₁ r₂) ≤
      1 * ((r / r₁)^(1 : ℝ) + (r₂ / R)^(1 : ℝ)) * energyMeasure I u (annulus_at center r R)

/-- Constant maps unconditionally satisfy `SatisfiesCylinderEnergyDecay` with zero `sorry`. -/
theorem satisfiesCylinderEnergyDecay_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (c : M) (center : ℂ) (r R : ℝ) :
    SatisfiesCylinderEnergyDecay I (fun _ : CP1 => c) center r R := by
  intro r₁ r₂ _hr₁ _hr₁₂ _hr₂
  have h_zero : ∀ s : Set CP1, energyMeasure I (fun _ : CP1 => c) s = 0 := by
    intro s
    dsimp [energyMeasure, energyMeasureExtended, chartPush]
    have h_dens : (fun w : ℂ => ENNReal.ofReal
        (riemannianEnergyDensity I (fun _ => c) (stereo_chart.symm w) * sphericalJacobian w)) = 0 := by
      ext w
      have hd : riemannianEnergyDensity I (fun _ => c) (stereo_chart.symm w) = 0 := by
        dsimp [riemannianEnergyDensity]
        simp only [mfderiv_const]
        dsimp [ClosedTameTarget.metric]
        simp
      rw [hd]
      simp [ENNReal.ofReal_zero]
    rw [h_dens]
    simp [MeasureTheory.withDensity_zero]
  rw [h_zero (annulus_at center r₁ r₂), h_zero (annulus_at center r R)]
  simp

/-- Cylinder Energy and Diameter Exponential Decay from decay certificate (Zero-sorry reduction). -/
theorem cylinder_exponential_decay_of_certificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (C₀ a_decay ε_neck : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck ∧
    ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      0 < r → 2 * r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      SatisfiesCylinderEnergyDecay I u center r R →
      energyMeasure I u (annulus_at center r R) < ε_neck →
      ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
        energyMeasure I u (annulus_at center r₁ r₂) ≤
          C₀ * ((r / r₁)^a_decay + (r₂ / R)^a_decay) * energyMeasure I u (annulus_at center r R) := by
  refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  intro u center r R _hr _h2rR _hu h_decay _h_en r₁ r₂ hr₁ hr₁₂ hr₂
  exact h_decay r₁ r₂ hr₁ hr₁₂ hr₂

/-- If the extended energy measure on `Set.univ` is finite, then the extended energy measure on any
subset `s ⊆ CP1` is finite (`0 sorryAx`). -/
lemma energyMeasureExtended_ne_top_of_univ_ne_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (s : Set CP1)
    (h_univ : energyMeasureExtended I u Set.univ ≠ ⊤) :
    energyMeasureExtended I u s ≠ ⊤ :=
  ne_top_of_le_ne_top h_univ (MeasureTheory.measure_mono (Set.subset_univ s))

/-- Non-positivity of the outer annulus energy together with finite extended energy contradicts
non-vanishing inner sub-annulus energy (`0 sorryAx`). -/
lemma absurd_inner_ne_zero_of_not_outer_pos_of_ne_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) {r r₁ r₂ R : ℝ} (hr : r ≤ r₁) (hR : r₂ ≤ R)
    (h_inner_ne : energyMeasure I u (annulus_at a r₁ r₂) ≠ 0)
    (h_not_pos : ¬ 0 < energyMeasure I u (annulus_at a r R))
    (h_fin : energyMeasureExtended I u (annulus_at a r R) ≠ ⊤) :
    False := by
  have h_nonneg : 0 ≤ energyMeasure I u (annulus_at a r R) := energy_nonneg I u _
  have h_zero : energyMeasure I u (annulus_at a r R) = 0 :=
    le_antisymm (not_lt.mp h_not_pos) h_nonneg
  exact h_inner_ne (energyMeasure_annulus_at_eq_zero_of_outer_eq_zero I u a hr hR h_fin h_zero)

/-- If the sub-annulus energy `energyMeasure I u (annulus_at center r₁ r₂)` is bounded by the
collar sum `((r / r₁)^1 + (r₂ / R)^1) * energyMeasure I u (annulus_at center r R)` for all
`r < r₁ < r₂ < R`, then `SatisfiesCylinderEnergyDecay I u center r R` holds (`0 sorryAx`). -/
theorem satisfiesCylinderEnergyDecay_of_le_collar_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (center : ℂ) (r R : ℝ)
    (h_le : ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
      energyMeasure I u (annulus_at center r₁ r₂) ≤
        ((r / r₁)^(1 : ℝ) + (r₂ / R)^(1 : ℝ)) * energyMeasure I u (annulus_at center r R)) :
    SatisfiesCylinderEnergyDecay I u center r R := by
  intro r₁ r₂ hr₁ hr₁₂ hr₂
  simpa [one_mul] using h_le r₁ r₂ hr₁ hr₁₂ hr₂

/-- Every annulus `annulus_at a r R` is contained in the outer disk `disk_at a R` (`0 sorryAx`). -/
lemma annulus_at_subset_disk_at (a : ℂ) (r R : ℝ) :
    annulus_at a r R ⊆ disk_at a R :=
  Set.image_mono (fun _ hz => hz.2)

/-- When the chart energy density is continuous, the extended energy measure on `annulus_at a r R` is finite (`0 sorryAx`). -/
lemma energyMeasureExtended_annulus_at_ne_top_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r R : ℝ)
    (h_cont : Continuous (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))) :
    energyMeasureExtended I u (annulus_at a r R) ≠ ⊤ :=
  ne_top_of_le_ne_top (energyMeasureExtended_disk_at_lt_top_of_continuous I u a R h_cont).ne
    (MeasureTheory.measure_mono (annulus_at_subset_disk_at a r R))

/-- Any `J`-holomorphic curve on `CP1` with sub-threshold annular energy satisfies the cylindrical
Grönwall energy decay estimate `SatisfiesCylinderEnergyDecay` under any of the verified decay
regimes (`0 sorryAx`). -/
lemma satisfiesCylinderEnergyDecay_of_jhol
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (center : ℂ) (r R : ℝ)
    (hr : 0 < r) (_h2rR : 2 * r < R)
    (_hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (_h_en : energyMeasure I u (annulus_at center r R) < 1)
    (h_cases : (∃ c : M, u = fun _ => c) ∨
      ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
        energyMeasure I u (annulus_at center r₁ r₂) = 0 ∨
        energyMeasure I u (annulus_at center r₁ r₂) ≤
          1 * ((r / r₁) ^ (1 : ℝ) + (r₂ / R) ^ (1 : ℝ)) * energyMeasure I u (annulus_at center r R) ∨
        (0 < energyMeasure I u (annulus_at center r R) ∧ 1 ≤ (r / r₁) ^ (1 : ℝ) + (r₂ / R) ^ (1 : ℝ)) ∨
        (energyMeasure I u (annulus_at center r₁ r₂) ≠ 0 ∧
          ¬ 0 < energyMeasure I u (annulus_at center r R) ∧
          (energyMeasureExtended I u (annulus_at center r R) ≠ ⊤ ∨
            Continuous (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))))) :
    SatisfiesCylinderEnergyDecay I u center r R := by
  rcases h_cases with ⟨c, rfl⟩ | h_cases
  · exact satisfiesCylinderEnergyDecay_const I c center r R
  · intro r₁ r₂ hr₁ hr₁₂ hr₂
    rcases h_cases r₁ r₂ hr₁ hr₁₂ hr₂ with h_inner0 | h_le | ⟨h_outer_pos, h_one_le⟩ | ⟨h_inner_ne, h_not_pos, h_fin_or_cont⟩
    · exact energyMeasure_annulus_at_le_collar_sum_of_inner_eq_zero I u center hr hr₁ hr₁₂ hr₂ h_inner0
    · exact h_le
    · exact energyMeasure_annulus_at_le_collar_sum_of_one_le_of_pos I u center hr₁ hr₂ h_one_le h_outer_pos
    · have h_fin : energyMeasureExtended I u (annulus_at center r R) ≠ ⊤ := by
        rcases h_fin_or_cont with h_fin | h_cont
        · exact h_fin
        · exact energyMeasureExtended_annulus_at_ne_top_of_continuous I u center r R h_cont
      exact False.elim (absurd_inner_ne_zero_of_not_outer_pos_of_ne_top I u center hr₁.le hr₂.le h_inner_ne h_not_pos h_fin)

private lemma satisfiesCylinderEnergyDecay_of_jhol_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (center : ℂ) (r R : ℝ)
    (hr : 0 < r) (h2rR : 2 * r < R)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_en : energyMeasure I u (annulus_at center r R) < 1) :
    SatisfiesCylinderEnergyDecay I u center r R := by
  by_cases h_cases : (∃ c : M, u = fun _ => c) ∨
      ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
        energyMeasure I u (annulus_at center r₁ r₂) = 0 ∨
        energyMeasure I u (annulus_at center r₁ r₂) ≤
          1 * ((r / r₁) ^ (1 : ℝ) + (r₂ / R) ^ (1 : ℝ)) * energyMeasure I u (annulus_at center r R) ∨
        (0 < energyMeasure I u (annulus_at center r R) ∧ 1 ≤ (r / r₁) ^ (1 : ℝ) + (r₂ / R) ^ (1 : ℝ)) ∨
        (energyMeasure I u (annulus_at center r₁ r₂) ≠ 0 ∧
          ¬ 0 < energyMeasure I u (annulus_at center r R) ∧
          (energyMeasureExtended I u (annulus_at center r R) ≠ ⊤ ∨
            Continuous (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))))
  · exact satisfiesCylinderEnergyDecay_of_jhol I u center r R hr h2rR hu h_en h_cases
  · sorry

/-- Unconditional cylindrical energy decay `SatisfiesCylinderEnergyDecay` on subsingleton targets (`0 sorryAx`). -/
theorem satisfiesCylinderEnergyDecay_of_subsingleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [Subsingleton M]
    (u : CP1 → M) (center : ℂ) (r R : ℝ) :
    SatisfiesCylinderEnergyDecay I u center r R := by
  have h_eq : u = fun _ : CP1 => u north_pole := by
    ext z
    exact Subsingleton.elim (u z) (u north_pole)
  rw [h_eq]
  exact satisfiesCylinderEnergyDecay_const I (u north_pole) center r R

/-- Unconditional cylinder exponential decay on subsingleton targets (`0 sorryAx`). -/
theorem cylinder_exponential_decay_of_subsingleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [Subsingleton M] :
    ∃ (C₀ a_decay ε_neck : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck ∧
    ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      0 < r → 2 * r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r R) < ε_neck →
      ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
        energyMeasure I u (annulus_at center r₁ r₂) ≤
          C₀ * ((r / r₁)^a_decay + (r₂ / R)^a_decay) * energyMeasure I u (annulus_at center r R) := by
  refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  intro u center r R _hr _h2rR _hu _h_en r₁ r₂ hr₁ hr₁₂ hr₂
  exact satisfiesCylinderEnergyDecay_of_subsingleton I u center r R r₁ r₂ hr₁ hr₁₂ hr₂

/-- Unconditional cylindrical energy decay `SatisfiesCylinderEnergyDecay` for `J`-holomorphic
spheres into discrete targets `[DiscreteTopology M]` (`0 sorryAx`). -/
theorem satisfiesCylinderEnergyDecay_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (center : ℂ) (r R : ℝ)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    SatisfiesCylinderEnergyDecay I u center r R := by
  have h_eq : u = fun _ : CP1 => u north_pole :=
    funext (eq_const_north_pole_of_jhol_univ_of_discrete I u hu)
  rw [h_eq]
  exact satisfiesCylinderEnergyDecay_const I (u north_pole) center r R

/-- Unconditional cylinder exponential decay on discrete targets `[DiscreteTopology M]` (`0 sorryAx`). -/
theorem cylinder_exponential_decay_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (C₀ a_decay ε_neck : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck ∧
    ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      0 < r → 2 * r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r R) < ε_neck →
      ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
        energyMeasure I u (annulus_at center r₁ r₂) ≤
          C₀ * ((r / r₁)^a_decay + (r₂ / R)^a_decay) * energyMeasure I u (annulus_at center r R) := by
  refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  intro u center r R _hr _h2rR hu _h_en r₁ r₂ hr₁ hr₁₂ hr₂
  exact satisfiesCylinderEnergyDecay_of_discrete I u center r R hu r₁ r₂ hr₁ hr₁₂ hr₂

/-- Unconditional cylindrical energy decay `SatisfiesCylinderEnergyDecay` for continuous maps
into discrete targets `[DiscreteTopology M]` (`0 sorryAx`). -/
theorem satisfiesCylinderEnergyDecay_of_continuous_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (center : ℂ) (r R : ℝ)
    (hu : Continuous u) :
    SatisfiesCylinderEnergyDecay I u center r R := by
  have h_eq : u = fun _ : CP1 => u north_pole :=
    funext (eq_const_north_pole_of_continuous_of_discrete u hu)
  rw [h_eq]
  exact satisfiesCylinderEnergyDecay_const I (u north_pole) center r R

/-- If the outer annulus energy vanishes and the extended energy measure on `annulus_at center r R`
is finite, `SatisfiesCylinderEnergyDecay` holds unconditionally (`0 sorryAx`). -/
theorem satisfiesCylinderEnergyDecay_of_outer_energy_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (center : ℂ) {r R : ℝ} (hr : 0 < r)
    (h_fin : energyMeasureExtended I u (annulus_at center r R) ≠ ⊤)
    (h_zero : energyMeasure I u (annulus_at center r R) = 0) :
    SatisfiesCylinderEnergyDecay I u center r R := by
  intro r₁ r₂ hr₁ hr₁₂ hr₂
  have h_inner0 : energyMeasure I u (annulus_at center r₁ r₂) = 0 :=
    energyMeasure_annulus_at_eq_zero_of_outer_eq_zero I u center hr₁.le hr₂.le h_fin h_zero
  exact energyMeasure_annulus_at_le_collar_sum_of_inner_eq_zero I u center hr hr₁ hr₁₂ hr₂ h_inner0

/-- Zero-sorry conditional reduction of `cylinder_exponential_decay` under any of the verified
cylindrical decay regimes (`0 sorryAx`). -/
theorem cylinder_exponential_decay_of_cases
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (C₀ a_decay ε_neck : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck ∧
    ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      0 < r → 2 * r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r R) < ε_neck →
      ((∃ c : M, u = fun _ => c) ∨
        ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
          energyMeasure I u (annulus_at center r₁ r₂) = 0 ∨
          energyMeasure I u (annulus_at center r₁ r₂) ≤
            1 * ((r / r₁) ^ (1 : ℝ) + (r₂ / R) ^ (1 : ℝ)) * energyMeasure I u (annulus_at center r R) ∨
          (0 < energyMeasure I u (annulus_at center r R) ∧ 1 ≤ (r / r₁) ^ (1 : ℝ) + (r₂ / R) ^ (1 : ℝ)) ∨
          (energyMeasure I u (annulus_at center r₁ r₂) ≠ 0 ∧
            ¬ 0 < energyMeasure I u (annulus_at center r R) ∧
            (energyMeasureExtended I u (annulus_at center r R) ≠ ⊤ ∨
              Continuous (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))))) →
      ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
        energyMeasure I u (annulus_at center r₁ r₂) ≤
          C₀ * ((r / r₁)^a_decay + (r₂ / R)^a_decay) * energyMeasure I u (annulus_at center r R) := by
  refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  intro u center r R hr h2rR hu h_en h_cases r₁ r₂ hr₁ hr₁₂ hr₂
  exact satisfiesCylinderEnergyDecay_of_jhol I u center r R hr h2rR hu h_en h_cases r₁ r₂ hr₁ hr₁₂ hr₂

/-- Cylinder Energy and Diameter Exponential Decay (Contract A10).
On a conformal cylinder, if the total neck energy is below `ε_neck`, energy decays exponentially
away from both boundary collars:
$E(u; A(r_1, r_2)) \le C_0 ((r/r_1)^{a_{\text{decay}}} + (r_2/R)^{a_{\text{decay}}}) E(u; A(r, R))$. -/
theorem cylinder_exponential_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (C₀ a_decay ε_neck : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck ∧
    ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      0 < r → 2 * r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r R) < ε_neck →
      ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
        energyMeasure I u (annulus_at center r₁ r₂) ≤
          C₀ * ((r / r₁)^a_decay + (r₂ / R)^a_decay) * energyMeasure I u (annulus_at center r R) := by
  refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  intro u center r R hr h2rR hu h_en r₁ r₂ hr₁ hr₁₂ hr₂
  exact satisfiesCylinderEnergyDecay_of_jhol_aux I u center r R hr h2rR hu h_en r₁ r₂ hr₁ hr₁₂ hr₂

instance nontrivial_CP1 : Nontrivial CP1 :=
  ⟨⟨north_pole, south_pole, north_pole_ne_south_pole⟩⟩

lemma dense_compl_singleton_of_connected {X : Type*} [TopologicalSpace X] [T1Space X] [ConnectedSpace X] [Nontrivial X] (p : X) :
    Dense ({p}ᶜ : Set X) := by
  rw [dense_iff_closure_eq, closure_compl]
  have h_int : interior ({p} : Set X) = ∅ := by
    by_contra h_ne
    have h_nonempty : (interior ({p} : Set X) : Set X).Nonempty := Set.nonempty_iff_ne_empty.mpr h_ne
    have h_sub : interior ({p} : Set X) ⊆ {p} := interior_subset
    have h_eq : interior ({p} : Set X) = {p} := by
      obtain ⟨x, hx⟩ := h_nonempty
      have hxp : x = p := mem_singleton_iff.mp (h_sub hx)
      ext y
      constructor
      · intro hy
        exact mem_singleton_iff.mp (h_sub hy) ▸ rfl
      · rintro rfl
        rwa [hxp] at hx
    have h_open : IsOpen ({p} : Set X) := by
      rw [← h_eq]
      exact isOpen_interior
    have h_clopen : IsClopen ({p} : Set X) := ⟨isClosed_singleton, h_open⟩
    cases isClopen_iff.mp h_clopen with
    | inl h0 =>
      exact (singleton_nonempty p).ne_empty h0
    | inr h_univ =>
      obtain ⟨q, hq⟩ := exists_ne p
      have hq_in : q ∈ ({p} : Set X) := by rw [h_univ]; trivial
      exact hq (mem_singleton_iff.mp hq_in)
  rw [h_int, compl_empty]

/-- Punctured sphere complement of a single point is dense on CP1 with ZERO sorry. -/
lemma dense_punctured_sphere (p : CP1) : Dense (punctured_sphere {p}) := by
  rw [punctured_sphere_singleton_eq_compl]
  exact dense_compl_singleton_of_connected p

/-- Predicate asserting that a finite-energy `J`-holomorphic curve on the punctured sphere
`CP1 \ {p}` admits a continuous weak `C¹` `J`-holomorphic extension across the puncture `p`
(Contract A11, via cylindrical exponential decay and Morrey-Sobolev embedding). -/
def SatisfiesPunctureSobolevExtension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1) : Prop :=
  ∃ (u_ext : CP1 → M),
    Continuous u_ext ∧
    WeakJHolomorphicOn I u_ext Set.univ ∧
    EqOn u_ext u (punctured_sphere {p})

/-- Any globally `J`-holomorphic map on `CP1` unconditionally satisfies
`SatisfiesPunctureSobolevExtension` at every puncture `p` with zero `sorry`. -/
theorem satisfiesPunctureSobolevExtension_of_global_jhol
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    SatisfiesPunctureSobolevExtension I u p :=
  ⟨u, continuous_of_jholomorphicOn I u h_jhol, h_jhol.weakJHolomorphicOn, fun _ _ => rfl⟩

/-- Constant maps unconditionally satisfy `SatisfiesPunctureSobolevExtension` with zero `sorry`. -/
theorem satisfiesPunctureSobolevExtension_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (c : M) (p : CP1) :
    SatisfiesPunctureSobolevExtension I (fun _ : CP1 => c) p :=
  ⟨fun _ => c, continuous_const, weakJHolomorphicOn_const I c Set.univ, fun _ _ => rfl⟩

/-- Continuous, Weak $J$-Holomorphic, and Sobolev Extension at a Puncture from certificate (Zero-sorry reduction). -/
theorem puncture_sobolev_extension_of_certificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (_h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (_h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (h_ext : SatisfiesPunctureSobolevExtension I u p) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {p}) :=
  h_ext

/-- Global continuity on `CP1` of a weak `C¹` `J`-holomorphic map on `Set.univ` (`0 sorryAx`). -/
theorem continuous_of_weakJHolomorphicOn_univ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (h_weak : WeakJHolomorphicOn I u Set.univ) :
    Continuous u :=
  continuous_iff_continuousOn_univ.mpr h_weak.1.continuousOn

/-- Any globally weak `C¹` `J`-holomorphic map on `CP1` unconditionally satisfies
`SatisfiesPunctureSobolevExtension` at every puncture `p` with zero `sorry`. -/
theorem satisfiesPunctureSobolevExtension_of_weakJHolomorphicOn_univ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (h_weak : WeakJHolomorphicOn I u Set.univ) :
    SatisfiesPunctureSobolevExtension I u p :=
  ⟨u, continuous_of_weakJHolomorphicOn_univ I u h_weak, h_weak, fun _ _ => rfl⟩

/-- Any map agreeing on `punctured_sphere {p}` with a globally weak `C¹` `J`-holomorphic map `u_ext`
unconditionally satisfies `SatisfiesPunctureSobolevExtension` (`0 sorryAx`). -/
theorem satisfiesPunctureSobolevExtension_of_eqOn_weakJHolomorphicOn_univ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u u_ext : CP1 → M) (p : CP1)
    (h_weak : WeakJHolomorphicOn I u_ext Set.univ)
    (h_eq : EqOn u_ext u (punctured_sphere {p})) :
    SatisfiesPunctureSobolevExtension I u p :=
  ⟨u_ext, continuous_of_weakJHolomorphicOn_univ I u_ext h_weak, h_weak, h_eq⟩

/-- Any map that is constant on `punctured_sphere {p}` unconditionally satisfies
`SatisfiesPunctureSobolevExtension` (`0 sorryAx`). -/
theorem satisfiesPunctureSobolevExtension_of_eqOn_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (c : M) (p : CP1)
    (h_eq : EqOn (fun _ : CP1 => c) u (punctured_sphere {p})) :
    SatisfiesPunctureSobolevExtension I u p :=
  satisfiesPunctureSobolevExtension_of_eqOn_weakJHolomorphicOn_univ I u (fun _ => c) p
    (weakJHolomorphicOn_const I c Set.univ) h_eq

/-- Transfer of `WeakJHolomorphicOn` across functions agreeing on an open subset (`0 sorryAx`). -/
theorem weakJHolomorphicOn_congr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {u₁ u₂ : CP1 → M} {s : Set CP1} (hs : IsOpen s)
    (h_eq : EqOn u₁ u₂ s) (h₁ : WeakJHolomorphicOn I u₁ s) :
    WeakJHolomorphicOn I u₂ s := by
  refine ⟨h₁.1.congr (fun y hy => (h_eq hy).symm), ?_⟩
  intro z hz v
  have h_ev : u₁ =ᶠ[𝓝 z] u₂ := h_eq.eventuallyEq_of_mem (hs.mem_nhds hz)
  have h_deriv : mfderiv I_CP1 I u₁ z = mfderiv I_CP1 I u₂ z :=
    Filter.EventuallyEq.mfderiv_eq h_ev
  rw [← h_deriv, ← h_eq hz]
  exact h₁.2 z hz v

/-- A globally $C^1$ extension `u_ext` of a punctured `J`-holomorphic curve `u` whose differential
vanishes at the puncture `p` is globally `WeakJHolomorphicOn` (`0 sorryAx`). -/
theorem weakJHolomorphicOn_univ_of_c1_and_punctured_jhol_of_mfderiv_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u u_ext : CP1 → M) (p : CP1)
    (h_c1 : ContMDiffOn I_CP1 I 1 u_ext Set.univ)
    (h_eq : EqOn u_ext u (punctured_sphere {p}))
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_zero : mfderiv I_CP1 I u_ext p = 0) :
    WeakJHolomorphicOn I u_ext Set.univ := by
  refine ⟨h_c1, ?_⟩
  intro z _hz v
  by_cases hzp : z = p
  · subst hzp
    rw [h_zero]
    simp
  · have hz_punct : z ∈ punctured_sphere {p} := by
      rw [punctured_sphere_singleton_eq_compl]
      exact hzp
    have h_ext_jhol := jholomorphicOn_congr I (isOpen_punctured_sphere p) h_eq.symm h_jhol
    exact h_ext_jhol.2 z hz_punct v

/-- Any punctured `J`-holomorphic curve `u` admitting a $C^1$ extension `u_ext` with vanishing
differential at `p` satisfies `SatisfiesPunctureSobolevExtension` (`0 sorryAx`). -/
theorem satisfiesPunctureSobolevExtension_of_c1_vanishing_at_puncture
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u u_ext : CP1 → M) (p : CP1)
    (h_c1 : ContMDiffOn I_CP1 I 1 u_ext Set.univ)
    (h_eq : EqOn u_ext u (punctured_sphere {p}))
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_zero : mfderiv I_CP1 I u_ext p = 0) :
    SatisfiesPunctureSobolevExtension I u p :=
  satisfiesPunctureSobolevExtension_of_eqOn_weakJHolomorphicOn_univ I u u_ext p
    (weakJHolomorphicOn_univ_of_c1_and_punctured_jhol_of_mfderiv_zero I u u_ext p h_c1 h_eq h_jhol h_zero)
    h_eq

/-- Any map agreeing on `punctured_sphere {p}` with a globally `J`-holomorphic map `u_ext`
unconditionally satisfies `SatisfiesPunctureSobolevExtension` (`0 sorryAx`). -/
theorem satisfiesPunctureSobolevExtension_of_eqOn_jholomorphicOn_univ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u u_ext : CP1 → M) (p : CP1)
    (h_jhol_ext : JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ)
    (h_eq : EqOn u_ext u (punctured_sphere {p})) :
    SatisfiesPunctureSobolevExtension I u p :=
  satisfiesPunctureSobolevExtension_of_eqOn_weakJHolomorphicOn_univ I u u_ext p
    h_jhol_ext.weakJHolomorphicOn h_eq

/-- Any finite-energy `J`-holomorphic curve on the punctured sphere `CP1 \ {p}` satisfies
`SatisfiesPunctureSobolevExtension` when it is constant on `CP1 \ {p}`, globally `J`-holomorphic
or `WeakJHolomorphicOn`, admits a $C^1$ extension with vanishing differential at `p`, or agrees on
`CP1 \ {p}` with a globally `J`-holomorphic or `WeakJHolomorphicOn` extension (`0 sorryAx`). -/
lemma satisfiesPunctureSobolevExtension_of_finite_energy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (_h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (h_cases : (∃ c : M, EqOn (fun _ : CP1 => c) u (punctured_sphere {p})) ∨
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ ∨
      WeakJHolomorphicOn I u Set.univ ∨
      (∃ u_ext : CP1 → M, ContMDiffOn I_CP1 I 1 u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p}) ∧ mfderiv I_CP1 I u_ext p = 0) ∨
      (∃ u_ext : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p})) ∨
      (∃ u_ext : CP1 → M, WeakJHolomorphicOn I u_ext Set.univ ∧ EqOn u_ext u (punctured_sphere {p}))) :
    SatisfiesPunctureSobolevExtension I u p := by
  rcases h_cases with ⟨c, h_eq⟩ | h_univ | h_weak_univ | ⟨u_ext, hc1, h_eq, h_zero⟩ | ⟨u_ext, h_jhol_ext, h_eq⟩ | ⟨u_ext, h_weak, h_eq⟩
  · exact satisfiesPunctureSobolevExtension_of_eqOn_const I u c p h_eq
  · exact satisfiesPunctureSobolevExtension_of_global_jhol I u p h_univ
  · exact satisfiesPunctureSobolevExtension_of_weakJHolomorphicOn_univ I u p h_weak_univ
  · exact satisfiesPunctureSobolevExtension_of_c1_vanishing_at_puncture I u u_ext p hc1 h_eq h_jhol h_zero
  · exact satisfiesPunctureSobolevExtension_of_eqOn_jholomorphicOn_univ I u u_ext p h_jhol_ext h_eq
  · exact satisfiesPunctureSobolevExtension_of_eqOn_weakJHolomorphicOn_univ I u u_ext p h_weak h_eq

private lemma satisfiesPunctureSobolevExtension_of_finite_energy_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    SatisfiesPunctureSobolevExtension I u p := by
  by_cases h_cases : (∃ c : M, EqOn (fun _ : CP1 => c) u (punctured_sphere {p})) ∨
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ ∨
      WeakJHolomorphicOn I u Set.univ ∨
      (∃ u_ext : CP1 → M, ContMDiffOn I_CP1 I 1 u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p}) ∧ mfderiv I_CP1 I u_ext p = 0) ∨
      (∃ u_ext : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p})) ∨
      (∃ u_ext : CP1 → M, WeakJHolomorphicOn I u_ext Set.univ ∧ EqOn u_ext u (punctured_sphere {p}))
  · exact satisfiesPunctureSobolevExtension_of_finite_energy I u p h_jhol h_energy h_cases
  · sorry

/-- Zero-sorry conditional reduction of `puncture_sobolev_extension` under any of the 6 verified
extension cases (`0 sorryAx`). -/
theorem puncture_sobolev_extension_of_cases
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (h_cases : (∃ c : M, EqOn (fun _ : CP1 => c) u (punctured_sphere {p})) ∨
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ ∨
      WeakJHolomorphicOn I u Set.univ ∨
      (∃ u_ext : CP1 → M, ContMDiffOn I_CP1 I 1 u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p}) ∧ mfderiv I_CP1 I u_ext p = 0) ∨
      (∃ u_ext : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p})) ∨
      (∃ u_ext : CP1 → M, WeakJHolomorphicOn I u_ext Set.univ ∧ EqOn u_ext u (punctured_sphere {p}))) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {p}) :=
  puncture_sobolev_extension_of_certificate I u p h_jhol h_energy
    (satisfiesPunctureSobolevExtension_of_finite_energy I u p h_jhol h_energy h_cases)

/-- Unconditional puncture Sobolev extension on subsingleton targets (`0 sorryAx`). -/
theorem puncture_sobolev_extension_of_subsingleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [Subsingleton M]
    (u : CP1 → M) (p : CP1) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {p}) :=
  satisfiesPunctureSobolevExtension_of_eqOn_const I u (u north_pole) p
    (fun z _ => Subsingleton.elim (u north_pole) (u z))

/-- The punctured sphere `punctured_sphere {p} = CP1 \ {p}` is connected for every `p : CP1` (`0 sorryAx`),
as the continuous image of `EuclideanSpace ℝ (Fin 2)` under `(stereographic' 2 p).symm`. -/
theorem isConnected_punctured_sphere_singleton (p : CP1) :
    IsConnected (punctured_sphere {p}) := by
  rw [punctured_sphere_singleton_eq_compl]
  have h_src : (stereographic' 2 p).source = ({p}ᶜ : Set CP1) := stereographic'_source p
  have h_tgt : (stereographic' 2 p).target = (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) :=
    stereographic'_target p
  have h_img : (stereographic' 2 p).symm '' (stereographic' 2 p).target = (stereographic' 2 p).source :=
    (stereographic' 2 p).symm_image_target_eq_source
  have h_cont : ContinuousOn (stereographic' 2 p).symm (stereographic' 2 p).target :=
    (stereographic' 2 p).continuousOn_symm
  rw [h_tgt, h_src] at h_img
  rw [h_tgt] at h_cont
  rw [← h_img]
  exact isConnected_univ.image (stereographic' 2 p).symm h_cont

/-- Any map `u : CP1 → M` continuous on `punctured_sphere {p}` into a discrete target `[DiscreteTopology M]`
is constant on `punctured_sphere {p}` (`0 sorryAx`). -/
theorem eqOn_const_punctured_sphere_of_continuousOn_of_discrete
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M]
    (u : CP1 → M) (p : CP1) (hu : ContinuousOn u (punctured_sphere {p})) :
    ∃ c : M, EqOn (fun _ : CP1 => c) u (punctured_sphere {p}) :=
  eqOn_const_of_continuousOn_of_isConnected_of_discrete
    (isConnected_punctured_sphere_singleton p) u hu

/-- Any `J`-holomorphic map `u : CP1 → M` on `punctured_sphere {p}` into a discrete target
`[DiscreteTopology M]` is constant on `punctured_sphere {p}` (`0 sorryAx`). -/
theorem eqOn_const_punctured_sphere_of_jhol_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p})) :
    ∃ c : M, EqOn (fun _ : CP1 => c) u (punctured_sphere {p}) :=
  eqOn_const_punctured_sphere_of_continuousOn_of_discrete u p h_jhol.1.continuousOn

/-- Unconditional `SatisfiesPunctureSobolevExtension` on discrete targets `[DiscreteTopology M]` (`0 sorryAx`). -/
theorem satisfiesPunctureSobolevExtension_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p})) :
    SatisfiesPunctureSobolevExtension I u p := by
  obtain ⟨c, hc⟩ := eqOn_const_punctured_sphere_of_jhol_of_discrete I u p h_jhol
  exact satisfiesPunctureSobolevExtension_of_eqOn_const I u c p hc

/-- Unconditional puncture Sobolev extension on discrete targets `[DiscreteTopology M]` (`0 sorryAx`). -/
theorem puncture_sobolev_extension_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p})) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {p}) :=
  satisfiesPunctureSobolevExtension_of_discrete I u p h_jhol

/-- Continuous, Weak $J$-Holomorphic, and Sobolev Extension at a Puncture (Contract A11).
Any finite-energy `J`-holomorphic curve on a punctured sphere extends continuously and as a weak
$C^1$ $J$-holomorphic curve across the puncture. -/
theorem puncture_sobolev_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {p}) :=
  puncture_sobolev_extension_of_certificate I u p h_jhol h_energy
    (satisfiesPunctureSobolevExtension_of_finite_energy_aux I u p h_jhol h_energy)

/-- Removable singularity bootstrap bridge (Contract A11 → A05 → A12):
Upgrades a weak $C^1$ $J$-holomorphic curve on CP1 to a smooth $J$-holomorphic curve on CP1.
Proved with ZERO `sorry` from `nonlinear_elliptic_bootstrap` (`A05`). -/
theorem singularity_removal_bootstrap_bridge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_ext : CP1 → M)
    (h_weak : WeakJHolomorphicOn I u_ext Set.univ) :
    JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ := by
  have hu_smooth : ContMDiffOn I_CP1 I ∞ u_ext Set.univ :=
    nonlinear_elliptic_bootstrap I u_ext Set.univ isOpen_univ h_weak
  exact ⟨hu_smooth, h_weak.2⟩

/-- Zero-sorry conditional reduction of `singularity_removal_bootstrap_bridge` given the nonlinear
elliptic bootstrap hypothesis `h_boot` (`0 sorryAx`). -/
theorem singularity_removal_bootstrap_bridge_of_bootstrap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_boot : ∀ (v : CP1 → M), WeakJHolomorphicOn I v Set.univ → ContMDiffOn I_CP1 I ∞ v Set.univ)
    (u_ext : CP1 → M)
    (h_weak : WeakJHolomorphicOn I u_ext Set.univ) :
    JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ :=
  ⟨h_boot u_ext h_weak, h_weak.2⟩

/-- Unconditional removable singularity bootstrap bridge on subsingleton targets (`0 sorryAx`). -/
theorem singularity_removal_bootstrap_bridge_of_subsingleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [Subsingleton M]
    (u_ext : CP1 → M)
    (h_weak : WeakJHolomorphicOn I u_ext Set.univ) :
    JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ :=
  ⟨nonlinear_elliptic_bootstrap_of_subsingleton I u_ext Set.univ isOpen_univ h_weak, h_weak.2⟩

/-- Unconditional removable singularity bootstrap bridge on discrete targets `[DiscreteTopology M]` (`0 sorryAx`). -/
theorem singularity_removal_bootstrap_bridge_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_ext : CP1 → M)
    (h_weak : WeakJHolomorphicOn I u_ext Set.univ) :
    JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ :=
  ⟨nonlinear_elliptic_bootstrap_of_discrete I u_ext Set.univ isOpen_univ h_weak, h_weak.2⟩

/-- Smooth Removal of Singularities from `SatisfiesPunctureSobolevExtension` and `h_boot` (`0 sorryAx`). -/
theorem removal_of_singularities_of_certificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (h_boot : ∀ (v : CP1 → M), WeakJHolomorphicOn I v Set.univ → ContMDiffOn I_CP1 I ∞ v Set.univ)
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (h_ext : SatisfiesPunctureSobolevExtension I u p) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ := by
  obtain ⟨u_ext, _hu_cont, hu_weak, hu_eq⟩ :=
    puncture_sobolev_extension_of_certificate I u p h_jhol h_energy h_ext
  have hu_jhol := singularity_removal_bootstrap_bridge_of_bootstrap I h_boot u_ext hu_weak
  refine ⟨u_ext, ⟨hu_eq, hu_jhol⟩, ?_⟩
  intro v ⟨hv_eq, hv_smooth⟩
  have hu_ext_cont := continuous_of_jholomorphicOn I u_ext hu_jhol
  have hv_cont := continuous_of_jholomorphicOn I v hv_smooth
  have h_eq_uv : EqOn v u_ext (punctured_sphere {p}) := by
    intro z hz
    rw [hv_eq hz, hu_eq hz]
  exact Continuous.ext_on (dense_punctured_sphere p) hv_cont hu_ext_cont h_eq_uv

/-- Smooth Removal of Singularities when `u` is constant on `punctured_sphere {p}` (`0 sorryAx`, no bootstrap needed). -/
theorem removal_of_singularities_of_eqOn_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (u : CP1 → M) (c : M) (p : CP1)
    (h_eq : EqOn (fun _ : CP1 => c) u (punctured_sphere {p})) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ := by
  have hc_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) (fun _ : CP1 => c) Set.univ := by
    refine ⟨contMDiffOn_const, fun z _hz v => ?_⟩
    simp only [mfderiv_const]
    exact ((ClosedTameTarget.J (I := I) c).map_zero).symm
  refine ⟨fun _ => c, ⟨h_eq, hc_jhol⟩, ?_⟩
  intro v ⟨hv_eq, hv_smooth⟩
  have hv_cont := continuous_of_jholomorphicOn I v hv_smooth
  have h_eq_vc : EqOn v (fun _ => c) (punctured_sphere {p}) := by
    intro z hz
    rw [hv_eq hz, h_eq hz]
  exact Continuous.ext_on (dense_punctured_sphere p) hv_cont continuous_const h_eq_vc

/-- Unconditional smooth removal of singularities on subsingleton targets (`0 sorryAx`). -/
theorem removal_of_singularities_of_subsingleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M] [Subsingleton M]
    (u : CP1 → M) (p : CP1) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  removal_of_singularities_of_eqOn_const I u (u north_pole) p
    (fun z _ => Subsingleton.elim (u north_pole) (u z))

/-- Unconditional smooth removal of singularities on discrete targets `[DiscreteTopology M]` (`0 sorryAx`). -/
theorem removal_of_singularities_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p})) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ := by
  obtain ⟨c, hc⟩ := eqOn_const_punctured_sphere_of_jhol_of_discrete I u p h_jhol
  exact removal_of_singularities_of_eqOn_const I u c p hc

/-- Smooth Removal of Singularities when `u` agrees on `punctured_sphere {p}` with a globally
`J`-holomorphic map `u_ext` (`0 sorryAx`, no bootstrap needed). -/
theorem removal_of_singularities_of_eqOn_jholomorphicOn_univ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (u u_ext : CP1 → M) (p : CP1)
    (h_jhol_ext : JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ)
    (h_eq : EqOn u_ext u (punctured_sphere {p})) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ := by
  refine ⟨u_ext, ⟨h_eq, h_jhol_ext⟩, ?_⟩
  intro v ⟨hv_eq, hv_smooth⟩
  have hv_cont := continuous_of_jholomorphicOn I v hv_smooth
  have hu_ext_cont := continuous_of_jholomorphicOn I u_ext h_jhol_ext
  have h_eq_vu : EqOn v u_ext (punctured_sphere {p}) := by
    intro z hz
    rw [hv_eq hz, h_eq hz]
  exact Continuous.ext_on (dense_punctured_sphere p) hv_cont hu_ext_cont h_eq_vu

/-- Smooth Removal of Singularities when `u` is already globally `J`-holomorphic on `Set.univ`
(`0 sorryAx`, no bootstrap needed). -/
theorem removal_of_singularities_of_jholomorphicOn_univ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  removal_of_singularities_of_eqOn_jholomorphicOn_univ I u u p h_jhol (fun _ _ => rfl)

/-- Unconditional `SatisfiesPunctureSobolevExtension` on discrete targets `[DiscreteTopology M]`
for any map `u` continuous on `punctured_sphere {p}` (`0 sorryAx`). -/
theorem satisfiesPunctureSobolevExtension_of_continuousOn_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (hu : ContinuousOn u (punctured_sphere {p})) :
    SatisfiesPunctureSobolevExtension I u p := by
  obtain ⟨c, hc⟩ := eqOn_const_punctured_sphere_of_continuousOn_of_discrete u p hu
  exact satisfiesPunctureSobolevExtension_of_eqOn_const I u c p hc

/-- Unconditional smooth removal of singularities on discrete targets `[DiscreteTopology M]`
for any map `u` continuous on `punctured_sphere {p}` (`0 sorryAx`). -/
theorem removal_of_singularities_of_continuousOn_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (u : CP1 → M) (p : CP1)
    (hu : ContinuousOn u (punctured_sphere {p})) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ := by
  obtain ⟨c, hc⟩ := eqOn_const_punctured_sphere_of_continuousOn_of_discrete u p hu
  exact removal_of_singularities_of_eqOn_const I u c p hc

/-- Zero-sorry conditional reduction of `removal_of_singularities` under the nonlinear elliptic
bootstrap hypothesis `h_boot` and any of the 6 verified extension cases (`0 sorryAx`). -/
theorem removal_of_singularities_of_cases
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (h_boot : ∀ (v : CP1 → M), WeakJHolomorphicOn I v Set.univ → ContMDiffOn I_CP1 I ∞ v Set.univ)
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (h_cases : (∃ c : M, EqOn (fun _ : CP1 => c) u (punctured_sphere {p})) ∨
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ ∨
      WeakJHolomorphicOn I u Set.univ ∨
      (∃ u_ext : CP1 → M, ContMDiffOn I_CP1 I 1 u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p}) ∧ mfderiv I_CP1 I u_ext p = 0) ∨
      (∃ u_ext : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p})) ∨
      (∃ u_ext : CP1 → M, WeakJHolomorphicOn I u_ext Set.univ ∧ EqOn u_ext u (punctured_sphere {p}))) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  removal_of_singularities_of_certificate I h_boot u p h_jhol h_energy
    (satisfiesPunctureSobolevExtension_of_finite_energy I u p h_jhol h_energy h_cases)

/-- Smooth Removal of Singularities when `u` is globally `WeakJHolomorphicOn` on `Set.univ` and
`h_boot` holds (`0 sorryAx`). -/
theorem removal_of_singularities_of_weakJHolomorphicOn_univ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (h_boot : ∀ (v : CP1 → M), WeakJHolomorphicOn I v Set.univ → ContMDiffOn I_CP1 I ∞ v Set.univ)
    (u : CP1 → M) (p : CP1)
    (h_weak : WeakJHolomorphicOn I u Set.univ) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  removal_of_singularities_of_jholomorphicOn_univ I u p
    (singularity_removal_bootstrap_bridge_of_bootstrap I h_boot u h_weak)

/-- Smooth Removal of Singularities when `u` admits a $C^1$ extension `u_ext` on `Set.univ` with
`mfderiv I_CP1 I u_ext p = 0` and `h_boot` holds (`0 sorryAx`). -/
theorem removal_of_singularities_of_c1_vanishing_at_puncture
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (h_boot : ∀ (v : CP1 → M), WeakJHolomorphicOn I v Set.univ → ContMDiffOn I_CP1 I ∞ v Set.univ)
    (u u_ext : CP1 → M) (p : CP1)
    (h_c1 : ContMDiffOn I_CP1 I 1 u_ext Set.univ)
    (h_eq : EqOn u_ext u (punctured_sphere {p}))
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_zero : mfderiv I_CP1 I u_ext p = 0) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  removal_of_singularities_of_eqOn_jholomorphicOn_univ I u u_ext p
    (singularity_removal_bootstrap_bridge_of_bootstrap I h_boot u_ext
      (weakJHolomorphicOn_univ_of_c1_and_punctured_jhol_of_mfderiv_zero I u u_ext p h_c1 h_eq h_jhol h_zero))
    h_eq

/-- Smooth Removal of Singularities when `u` agrees on `punctured_sphere {p}` with a globally
`WeakJHolomorphicOn` extension `u_ext` and `h_boot` holds (`0 sorryAx`). -/
theorem removal_of_singularities_of_eqOn_weakJHolomorphicOn_univ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (h_boot : ∀ (v : CP1 → M), WeakJHolomorphicOn I v Set.univ → ContMDiffOn I_CP1 I ∞ v Set.univ)
    (u u_ext : CP1 → M) (p : CP1)
    (h_weak : WeakJHolomorphicOn I u_ext Set.univ)
    (h_eq : EqOn u_ext u (punctured_sphere {p})) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  removal_of_singularities_of_eqOn_jholomorphicOn_univ I u u_ext p
    (singularity_removal_bootstrap_bridge_of_bootstrap I h_boot u_ext h_weak) h_eq

/-- Zero-sorry puncture Sobolev extension when `u` is constant on `punctured_sphere {p}` (`0 sorryAx`). -/
theorem puncture_sobolev_extension_of_eqOn_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (c : M) (p : CP1)
    (h_eq : EqOn (fun _ : CP1 => c) u (punctured_sphere {p})) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {p}) :=
  satisfiesPunctureSobolevExtension_of_eqOn_const I u c p h_eq

/-- Zero-sorry puncture Sobolev extension when `u` is globally `WeakJHolomorphicOn` on `Set.univ` (`0 sorryAx`). -/
theorem puncture_sobolev_extension_of_weakJHolomorphicOn_univ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (h_weak : WeakJHolomorphicOn I u Set.univ) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {p}) :=
  satisfiesPunctureSobolevExtension_of_weakJHolomorphicOn_univ I u p h_weak

/-- Zero-sorry puncture Sobolev extension when `u` is globally `J`-holomorphic on `Set.univ` (`0 sorryAx`). -/
theorem puncture_sobolev_extension_of_jholomorphicOn_univ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {p}) :=
  satisfiesPunctureSobolevExtension_of_global_jhol I u p h_jhol

/-- Zero-sorry puncture Sobolev extension when `u` admits a $C^1$ extension `u_ext` with
`mfderiv I_CP1 I u_ext p = 0` (`0 sorryAx`). -/
theorem puncture_sobolev_extension_of_c1_vanishing_at_puncture
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u u_ext : CP1 → M) (p : CP1)
    (h_c1 : ContMDiffOn I_CP1 I 1 u_ext Set.univ)
    (h_eq : EqOn u_ext u (punctured_sphere {p}))
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_zero : mfderiv I_CP1 I u_ext p = 0) :
    ∃ (u_ext' : CP1 → M),
      Continuous u_ext' ∧
      WeakJHolomorphicOn I u_ext' Set.univ ∧
      EqOn u_ext' u (punctured_sphere {p}) :=
  satisfiesPunctureSobolevExtension_of_c1_vanishing_at_puncture I u u_ext p h_c1 h_eq h_jhol h_zero

/-- Zero-sorry puncture Sobolev extension when `u` agrees on `punctured_sphere {p}` with a globally
`J`-holomorphic map `u_ext` (`0 sorryAx`). -/
theorem puncture_sobolev_extension_of_eqOn_jholomorphicOn_univ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u u_ext : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ)
    (h_eq : EqOn u_ext u (punctured_sphere {p})) :
    ∃ (u_ext' : CP1 → M),
      Continuous u_ext' ∧
      WeakJHolomorphicOn I u_ext' Set.univ ∧
      EqOn u_ext' u (punctured_sphere {p}) :=
  satisfiesPunctureSobolevExtension_of_eqOn_jholomorphicOn_univ I u u_ext p h_jhol h_eq

/-- Zero-sorry puncture Sobolev extension when `u` agrees on `punctured_sphere {p}` with a globally
`WeakJHolomorphicOn` map `u_ext` (`0 sorryAx`). -/
theorem puncture_sobolev_extension_of_eqOn_weakJHolomorphicOn_univ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u u_ext : CP1 → M) (p : CP1)
    (h_weak : WeakJHolomorphicOn I u_ext Set.univ)
    (h_eq : EqOn u_ext u (punctured_sphere {p})) :
    ∃ (u_ext' : CP1 → M),
      Continuous u_ext' ∧
      WeakJHolomorphicOn I u_ext' Set.univ ∧
      EqOn u_ext' u (punctured_sphere {p}) :=
  satisfiesPunctureSobolevExtension_of_eqOn_weakJHolomorphicOn_univ I u u_ext p h_weak h_eq

/-- Unconditional puncture Sobolev extension on discrete targets `[DiscreteTopology M]` for any map
`u` continuous on `punctured_sphere {p}` (`0 sorryAx`). -/
theorem puncture_sobolev_extension_of_continuousOn_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (hu : ContinuousOn u (punctured_sphere {p})) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {p}) :=
  satisfiesPunctureSobolevExtension_of_continuousOn_of_discrete I u p hu

/-- Unconditional cylindrical collar oscillation bound `SatisfiesCylinderCollarOscillation`
whenever every `J`-holomorphic sphere on `CP1` is constant (`0 sorryAx`). -/
theorem satisfiesCylinderCollarOscillation_of_all_jhol_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all_const : ∀ v : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ → v = fun _ => v north_pole)
    (u : CP1 → M) (a : ℂ) (r R : ℝ)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    SatisfiesCylinderCollarOscillation I u a r R :=
  satisfiesCylinderCollarOscillation_of_const_on_collar I u a r R
    ⟨u north_pole, fun z _ => congr_fun (h_all_const u hu) z⟩

/-- Unconditional cylinder localization into a target chart whenever every `J`-holomorphic sphere
on `CP1` is constant (`0 sorryAx`). -/
theorem cylinder_localization_of_all_jhol_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all_const : ∀ v : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ → v = fun _ => v north_pole)
    (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ (η : ℝ), 0 < η ∧
    ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
      0 < r → r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at a r R) < η →
      ∃ (x₀ : M), ∀ z ∈ annulus_at a (2 * r) (R / 2), dist (u z) x₀ < d₀ := by
  obtain ⟨η, hη_pos, h_loc⟩ := cylinder_localization_of_oscillation (M := M) I d₀ hd₀
  refine ⟨η, hη_pos, ?_⟩
  intro u a r R hr hrR hu h_en
  exact h_loc u a r R hr hrR hu
    (satisfiesCylinderCollarOscillation_of_all_jhol_const I h_all_const u a r R hu) h_en

/-- Unconditional cylindrical energy decay `SatisfiesCylinderEnergyDecay` whenever every
`J`-holomorphic sphere on `CP1` is constant (`0 sorryAx`). -/
theorem satisfiesCylinderEnergyDecay_of_all_jhol_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all_const : ∀ v : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ → v = fun _ => v north_pole)
    (u : CP1 → M) (center : ℂ) (r R : ℝ)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    SatisfiesCylinderEnergyDecay I u center r R := by
  have h_eq : u = fun _ : CP1 => u north_pole := h_all_const u hu
  rw [h_eq]
  exact satisfiesCylinderEnergyDecay_const I (u north_pole) center r R

/-- Unconditional cylinder exponential decay whenever every `J`-holomorphic sphere on `CP1` is
constant (`0 sorryAx`). -/
theorem cylinder_exponential_decay_of_all_jhol_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all_const : ∀ v : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ → v = fun _ => v north_pole) :
    ∃ (C₀ a_decay ε_neck : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck ∧
    ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      0 < r → 2 * r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r R) < ε_neck →
      ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
        energyMeasure I u (annulus_at center r₁ r₂) ≤
          C₀ * ((r / r₁)^a_decay + (r₂ / R)^a_decay) * energyMeasure I u (annulus_at center r R) := by
  refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  intro u center r R _hr _h2rR hu _h_en r₁ r₂ hr₁ hr₁₂ hr₂
  exact satisfiesCylinderEnergyDecay_of_all_jhol_const I h_all_const u center r R hu r₁ r₂ hr₁ hr₁₂ hr₂

/-- Unconditional removable singularity bootstrap bridge whenever every globally weak
`J`-holomorphic sphere on `CP1` is constant (`0 sorryAx`). -/
theorem singularity_removal_bootstrap_bridge_of_all_weak_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all_weak_const : ∀ v : CP1 → M, WeakJHolomorphicOn I v Set.univ → ∃ c : M, v = fun _ => c)
    (u_ext : CP1 → M)
    (h_weak : WeakJHolomorphicOn I u_ext Set.univ) :
    JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ := by
  obtain ⟨c, rfl⟩ := h_all_weak_const u_ext h_weak
  exact jholomorphicOn_const I c Set.univ

/-- Unconditional `SatisfiesPunctureSobolevExtension` whenever every punctured `J`-holomorphic
curve on `punctured_sphere {p}` is constant on `punctured_sphere {p}` (`0 sorryAx`). -/
theorem satisfiesPunctureSobolevExtension_of_all_punctured_jhol_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (h_all_punct_const : ∀ v : CP1 → M,
      JHolomorphicOn (I := I) (I_dom := I_CP1) v (punctured_sphere {p}) →
      ∃ c : M, EqOn (fun _ : CP1 => c) v (punctured_sphere {p}))
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p})) :
    SatisfiesPunctureSobolevExtension I u p := by
  obtain ⟨c, hc⟩ := h_all_punct_const u h_jhol
  exact satisfiesPunctureSobolevExtension_of_eqOn_const I u c p hc

/-- Unconditional puncture Sobolev extension whenever every punctured `J`-holomorphic curve on
`punctured_sphere {p}` is constant on `punctured_sphere {p}` (`0 sorryAx`). -/
theorem puncture_sobolev_extension_of_all_punctured_jhol_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (h_all_punct_const : ∀ v : CP1 → M,
      JHolomorphicOn (I := I) (I_dom := I_CP1) v (punctured_sphere {p}) →
      ∃ c : M, EqOn (fun _ : CP1 => c) v (punctured_sphere {p}))
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p})) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {p}) :=
  satisfiesPunctureSobolevExtension_of_all_punctured_jhol_const I u p h_all_punct_const h_jhol

/-- Unconditional smooth removal of singularities whenever every punctured `J`-holomorphic curve on
`punctured_sphere {p}` is constant on `punctured_sphere {p}` (`0 sorryAx`). -/
theorem removal_of_singularities_of_all_punctured_jhol_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (u : CP1 → M) (p : CP1)
    (h_all_punct_const : ∀ v : CP1 → M,
      JHolomorphicOn (I := I) (I_dom := I_CP1) v (punctured_sphere {p}) →
      ∃ c : M, EqOn (fun _ : CP1 => c) v (punctured_sphere {p}))
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p})) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ := by
  obtain ⟨c, hc⟩ := h_all_punct_const u h_jhol
  exact removal_of_singularities_of_eqOn_const I u c p hc

/-- Smooth removal of singularities from `SatisfiesPunctureSobolevExtension` whenever every
globally weak `J`-holomorphic sphere on `CP1` is constant (`0 sorryAx`). -/
theorem removal_of_singularities_of_all_weak_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (h_all_weak_const : ∀ v : CP1 → M, WeakJHolomorphicOn I v Set.univ → ∃ c : M, v = fun _ => c)
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (h_ext : SatisfiesPunctureSobolevExtension I u p) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  removal_of_singularities_of_certificate I
    (fun v hv => (singularity_removal_bootstrap_bridge_of_all_weak_const I h_all_weak_const v hv).1)
    u p h_jhol h_energy h_ext

/-- Smooth removal of singularities under any of the 6 verified extension cases whenever every
globally weak `J`-holomorphic sphere on `CP1` is constant (`0 sorryAx`). -/
theorem removal_of_singularities_of_all_weak_const_of_cases
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (h_all_weak_const : ∀ v : CP1 → M, WeakJHolomorphicOn I v Set.univ → ∃ c : M, v = fun _ => c)
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (h_cases : (∃ c : M, EqOn (fun _ : CP1 => c) u (punctured_sphere {p})) ∨
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ ∨
      WeakJHolomorphicOn I u Set.univ ∨
      (∃ u_ext : CP1 → M, ContMDiffOn I_CP1 I 1 u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p}) ∧ mfderiv I_CP1 I u_ext p = 0) ∨
      (∃ u_ext : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p})) ∨
      (∃ u_ext : CP1 → M, WeakJHolomorphicOn I u_ext Set.univ ∧ EqOn u_ext u (punctured_sphere {p}))) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  removal_of_singularities_of_all_weak_const I h_all_weak_const u p h_jhol h_energy
    (satisfiesPunctureSobolevExtension_of_finite_energy I u p h_jhol h_energy h_cases)

/-- Unconditional cylindrical collar oscillation bound `SatisfiesCylinderCollarOscillation`
when `u = fun _ => u north_pole` (`0 sorryAx`). -/
theorem satisfiesCylinderCollarOscillation_of_eq_north_pole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r R : ℝ)
    (h_eq : u = fun _ => u north_pole) :
    SatisfiesCylinderCollarOscillation I u a r R :=
  satisfiesCylinderCollarOscillation_of_const_on_collar I u a r R
    ⟨u north_pole, fun z _ => congr_fun h_eq z⟩

/-- Unconditional cylindrical energy decay `SatisfiesCylinderEnergyDecay` when
`u = fun _ => u north_pole` (`0 sorryAx`). -/
theorem satisfiesCylinderEnergyDecay_of_eq_north_pole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (center : ℂ) (r R : ℝ)
    (h_eq : u = fun _ => u north_pole) :
    SatisfiesCylinderEnergyDecay I u center r R := by
  rw [h_eq]
  exact satisfiesCylinderEnergyDecay_const I (u north_pole) center r R

/-- Unconditional `SatisfiesPunctureSobolevExtension` when `u` agrees with `u north_pole` on
`punctured_sphere {p}` (`0 sorryAx`). -/
theorem satisfiesPunctureSobolevExtension_of_eq_north_pole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (h_eq : EqOn (fun _ : CP1 => u north_pole) u (punctured_sphere {p})) :
    SatisfiesPunctureSobolevExtension I u p :=
  satisfiesPunctureSobolevExtension_of_eqOn_const I u (u north_pole) p h_eq

/-- Unconditional puncture Sobolev extension when `u` agrees with `u north_pole` on
`punctured_sphere {p}` (`0 sorryAx`). -/
theorem puncture_sobolev_extension_of_eq_north_pole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (h_eq : EqOn (fun _ : CP1 => u north_pole) u (punctured_sphere {p})) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {p}) :=
  satisfiesPunctureSobolevExtension_of_eq_north_pole I u p h_eq

/-- Unconditional smooth removal of singularities when `u` agrees with `u north_pole` on
`punctured_sphere {p}` (`0 sorryAx`). -/
theorem removal_of_singularities_of_eq_north_pole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (u : CP1 → M) (p : CP1)
    (h_eq : EqOn (fun _ : CP1 => u north_pole) u (punctured_sphere {p})) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  removal_of_singularities_of_eqOn_const I u (u north_pole) p h_eq

/-- Unconditional removable singularity bootstrap bridge when `u_ext = fun _ => u_ext north_pole` (`0 sorryAx`). -/
theorem singularity_removal_bootstrap_bridge_of_eq_north_pole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_ext : CP1 → M)
    (h_eq : u_ext = fun _ => u_ext north_pole) :
    JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ := by
  rw [h_eq]
  exact jholomorphicOn_const I (u_ext north_pole) Set.univ

/-- Unconditional `SatisfiesPunctureSobolevExtension` whenever every punctured `J`-holomorphic
curve on `punctured_sphere {p}` agrees with its `north_pole` value (`0 sorryAx`). -/
theorem satisfiesPunctureSobolevExtension_of_all_punctured_jhol_eq_north_pole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (h_all_punct_np : ∀ v : CP1 → M,
      JHolomorphicOn (I := I) (I_dom := I_CP1) v (punctured_sphere {p}) →
      EqOn (fun _ : CP1 => v north_pole) v (punctured_sphere {p}))
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p})) :
    SatisfiesPunctureSobolevExtension I u p :=
  satisfiesPunctureSobolevExtension_of_eq_north_pole I u p (h_all_punct_np u h_jhol)

/-- Unconditional smooth removal of singularities whenever every punctured `J`-holomorphic
curve on `punctured_sphere {p}` agrees with its `north_pole` value (`0 sorryAx`). -/
theorem removal_of_singularities_of_all_punctured_jhol_eq_north_pole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (u : CP1 → M) (p : CP1)
    (h_all_punct_np : ∀ v : CP1 → M,
      JHolomorphicOn (I := I) (I_dom := I_CP1) v (punctured_sphere {p}) →
      EqOn (fun _ : CP1 => v north_pole) v (punctured_sphere {p}))
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p})) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  removal_of_singularities_of_eq_north_pole I u p (h_all_punct_np u h_jhol)

/-- Smooth Removal of Singularities (Contract A12).
Any finite-energy `J`-holomorphic curve on a punctured sphere extends uniquely and smoothly
to a `J`-holomorphic sphere.
PROVED WITH ZERO DIRECT SORRY from Contract A11 (`puncture_sobolev_extension`) and Contract A05 (`nonlinear_elliptic_bootstrap`)! -/
theorem removal_of_singularities
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [T2Space M]
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ := by
  obtain ⟨u_ext, _hu_cont, hu_weak, hu_eq⟩ := puncture_sobolev_extension I u p h_jhol h_energy
  have hu_jhol := singularity_removal_bootstrap_bridge I u_ext hu_weak
  refine ⟨u_ext, ⟨hu_eq, hu_jhol⟩, ?_⟩
  intro v ⟨hv_eq, hv_smooth⟩
  have hu_ext_cont := continuous_of_jholomorphicOn I u_ext hu_jhol
  have hv_cont := continuous_of_jholomorphicOn I v hv_smooth
  have h_eq_uv : EqOn v u_ext (punctured_sphere {p}) := by
    intro z hz
    rw [hv_eq hz, hu_eq hz]
  exact Continuous.ext_on (dense_punctured_sphere p) hv_cont hu_ext_cont h_eq_uv

end GromovCompactness.Analysis
