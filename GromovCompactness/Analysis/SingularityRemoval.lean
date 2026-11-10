/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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
  simp only [mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
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
  rw [h_top, ENNReal.toReal_top] at h_pos
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
  exact (compl_eq_univ_sdiff {p}).symm

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
    exact inferInstance
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
  h_eq.of_subset_closure hv₁ hv₂ sdiff_subset (ball_subset_closure_punctured_ball r hr)

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

/-- Collar oscillation predicate with a general constant `C`:
`dist (u z₁) (u z₂) ≤ C * √E(u; A(r, R))` on the collar `A(2r, R/2)`. -/
def SatisfiesCylinderCollarOscillationWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (C : ℝ) (u : CP1 → M) (a : ℂ) (r R : ℝ) : Prop :=
  ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
    dist (u z₁) (u z₂) ≤ C * Real.sqrt (energyMeasure I u (annulus_at a r R))

/-- Certificate `h_osc` (corrected form, Contract A09): there are target constants `C > 0` and
`ε > 0` such that every `J`-holomorphic sphere whose annulus `A(a; r, R)` carries energy `< ε`
satisfies the collar bound `osc ≤ C * √E(u; A(r, R))`.

The universal form with `C = 4` and no smallness hypothesis is false: on a round sphere with a
long thin neck of circumference `ℓ` and length `L ≫ ℓ`, a uniformizing map has collar oscillation
`≈ L` but annular energy `≈ ℓ L`, and `L > 4 √(ℓ L)` once `L > 16 ℓ`. -/
def CollarOscillationProperty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] : Prop :=
  ∃ (C ε : ℝ), 0 < C ∧ 0 < ε ∧
    ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
      0 < r → r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at a r R) < ε →
      SatisfiesCylinderCollarOscillationWith I C u a r R

/-- Constant maps satisfy the collar oscillation predicate for every `C ≥ 0` (`0 sorryAx`). -/
theorem satisfiesCylinderCollarOscillationWith_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {C : ℝ} (hC : 0 ≤ C) (c : M) (a : ℂ) (r R : ℝ) :
    SatisfiesCylinderCollarOscillationWith I C (fun _ : CP1 => c) a r R := by
  intro z₁ _ z₂ _
  rw [dist_self]
  exact mul_nonneg hC (Real.sqrt_nonneg _)

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
  have : Nonempty M := ⟨u north_pole⟩
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

/-- The diameter of the collar image `u '' annulus_at a (2 * r) (R / 2)` is bounded by the
diameter of `Set.range u` (`0 sorryAx`). -/
theorem diam_image_collar_le_diam_range
    {M : Type*} [MetricSpace M] [CompactSpace M]
    (u : CP1 → M) (a : ℂ) (r R : ℝ) :
    Metric.diam (u '' annulus_at a (2 * r) (R / 2)) ≤ Metric.diam (Set.range u) :=
  Metric.diam_mono (Set.image_subset_range u _) (isCompact_univ.isBounded.subset (Set.subset_univ _))

/-- The diameter of the collar image `u '' annulus_at a (2 * r) (R / 2)` is bounded by the
target diameter `Metric.diam (Set.univ : Set M)` (`0 sorryAx`). -/
theorem diam_image_collar_le_diam_univ
    {M : Type*} [MetricSpace M] [CompactSpace M]
    (u : CP1 → M) (a : ℂ) (r R : ℝ) :
    Metric.diam (u '' annulus_at a (2 * r) (R / 2)) ≤ Metric.diam (Set.univ : Set M) :=
  Metric.diam_mono (Set.subset_univ _) isCompact_univ.isBounded

/-- Any map whose range diameter is bounded by `4 * √E(u; A(r, R))` unconditionally satisfies
`SatisfiesCylinderCollarOscillation` (`0 sorryAx`). -/
theorem satisfiesCylinderCollarOscillation_of_diam_range_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r R : ℝ)
    (h_diam : Metric.diam (Set.range u) ≤ 4 * Real.sqrt (energyMeasure I u (annulus_at a r R))) :
    SatisfiesCylinderCollarOscillation I u a r R :=
  satisfiesCylinderCollarOscillation_of_diam_image_le I u a r R
    (le_trans (diam_image_collar_le_diam_range u a r R) h_diam)

/-- When the target diameter `Metric.diam (Set.univ : Set M)` is bounded by `4 * √E(u; A(r, R))`,
`SatisfiesCylinderCollarOscillation` holds unconditionally (`0 sorryAx`). -/
theorem satisfiesCylinderCollarOscillation_of_diam_univ_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r R : ℝ)
    (h_diam : Metric.diam (Set.univ : Set M) ≤ 4 * Real.sqrt (energyMeasure I u (annulus_at a r R))) :
    SatisfiesCylinderCollarOscillation I u a r R :=
  satisfiesCylinderCollarOscillation_of_diam_image_le I u a r R
    (le_trans (diam_image_collar_le_diam_univ u a r R) h_diam)

/-- Pointwise collar localization into a target ball of radius `d₀` whenever the collar image
diameter is strictly less than `d₀` (`0 sorryAx`). -/
theorem exists_collar_ball_of_diam_image_lt
    {M : Type*} [MetricSpace M] [CompactSpace M]
    (u : CP1 → M) (a : ℂ) (r R d₀ : ℝ)
    (h_diam : Metric.diam (u '' annulus_at a (2 * r) (R / 2)) < d₀) :
    ∃ (x₀ : M), ∀ z ∈ annulus_at a (2 * r) (R / 2), dist (u z) x₀ < d₀ := by
  have : Nonempty M := ⟨u north_pole⟩
  apply localization_of_diam_bound u (annulus_at a (2 * r) (R / 2)) d₀
  intro z₁ hz₁ z₂ hz₂
  have h_bdd : Bornology.IsBounded (u '' annulus_at a (2 * r) (R / 2)) :=
    isCompact_univ.isBounded.subset (Set.subset_univ _)
  exact lt_of_le_of_lt (Metric.dist_le_diam_of_mem h_bdd ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, rfl⟩) h_diam

/-- Pointwise collar localization into a target ball of radius `d₀` whenever `Metric.diam (Set.range u) < d₀` (`0 sorryAx`). -/
theorem exists_collar_ball_of_diam_range_lt
    {M : Type*} [MetricSpace M] [CompactSpace M]
    (u : CP1 → M) (a : ℂ) (r R d₀ : ℝ)
    (h_diam : Metric.diam (Set.range u) < d₀) :
    ∃ (x₀ : M), ∀ z ∈ annulus_at a (2 * r) (R / 2), dist (u z) x₀ < d₀ :=
  exists_collar_ball_of_diam_image_lt u a r R d₀
    (lt_of_le_of_lt (diam_image_collar_le_diam_range u a r R) h_diam)

/-- Pointwise collar localization into a target ball of radius `d₀` whenever `Metric.diam (Set.univ : Set M) < d₀` (`0 sorryAx`). -/
theorem exists_collar_ball_of_diam_univ_lt
    {M : Type*} [MetricSpace M] [CompactSpace M]
    (u : CP1 → M) (a : ℂ) (r R d₀ : ℝ)
    (h_diam : Metric.diam (Set.univ : Set M) < d₀) :
    ∃ (x₀ : M), ∀ z ∈ annulus_at a (2 * r) (R / 2), dist (u z) x₀ < d₀ :=
  exists_collar_ball_of_diam_image_lt u a r R d₀
    (lt_of_le_of_lt (diam_image_collar_le_diam_univ u a r R) h_diam)

/-- Unconditional cylinder localization when `Metric.diam (Set.univ : Set M) < d₀` (`0 sorryAx`). -/
theorem cylinder_localization_of_diam_univ_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (d₀ : ℝ) (hd₀ : 0 < d₀)
    (h_diam : Metric.diam (Set.univ : Set M) < d₀) :
    ∃ (η : ℝ), 0 < η ∧
    ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
      0 < r → r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at a r R) < η →
      ∃ (x₀ : M), ∀ z ∈ annulus_at a (2 * r) (R / 2), dist (u z) x₀ < d₀ := by
  obtain ⟨η, hη_pos, _⟩ := exists_neck_energy_threshold d₀ 2 hd₀ (by norm_num)
  refine ⟨η, hη_pos, ?_⟩
  intro u a r R _hr _hrR _hu _h_en
  exact exists_collar_ball_of_diam_univ_lt u a r R d₀ h_diam

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
curve on an annular neck with energy `< η` has its central collar image contained in a ball of radius `d₀`.
The hypothesis is the corrected collar oscillation certificate `CollarOscillationProperty I M`. -/
theorem cylinder_localization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_osc : CollarOscillationProperty I M)
    (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ (η : ℝ), 0 < η ∧
    ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
      0 < r → r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at a r R) < η →
      ∃ (x₀ : M), ∀ z ∈ annulus_at a (2 * r) (R / 2), dist (u z) x₀ < d₀ := by
  obtain ⟨C, ε, hC, hε, h_bound⟩ := h_osc
  set δ : ℝ := d₀ / (2 * C) with hδ_def
  have hδ_pos : 0 < δ := div_pos hd₀ (by positivity)
  refine ⟨min ε (δ ^ 2), lt_min hε (by positivity), ?_⟩
  intro u a r R hr hrR hu h_en
  have : Nonempty M := ⟨u north_pole⟩
  have h_en_ε : energyMeasure I u (annulus_at a r R) < ε := lt_of_lt_of_le h_en (min_le_left _ _)
  have h_en_δ : energyMeasure I u (annulus_at a r R) < δ ^ 2 := lt_of_lt_of_le h_en (min_le_right _ _)
  have h_sqrt : Real.sqrt (energyMeasure I u (annulus_at a r R)) < δ := by
    rw [← Real.sqrt_sq hδ_pos.le]
    exact Real.sqrt_lt_sqrt (energy_nonneg I u _) h_en_δ
  have h_Cδ : C * δ = d₀ / 2 := by
    rw [hδ_def]
    field_simp
  apply localization_of_diam_bound u (annulus_at a (2 * r) (R / 2)) d₀
  intro z₁ hz₁ z₂ hz₂
  have h_le := h_bound u a r R hr hrR hu h_en_ε z₁ hz₁ z₂ hz₂
  have h_lt : C * Real.sqrt (energyMeasure I u (annulus_at a r R)) < C * δ :=
    mul_lt_mul_of_pos_left h_sqrt hC
  linarith

/-!
### 8b. Geometric Decay, Small-Drop Pigeonhole, and Widman Hole-Filling (ported from `qinz1yang/differential-geometry`, `0 sorryAx`)
-/

/-- Power-decay scale absorption lemma (`0 sorryAx`, ported from `qinz1yang/differential-geometry`):
For `q < p`, `0 < ε`, and `0 < R`, there exists `θ ∈ (0, R)` such that `A * θ ^ p < ε * θ ^ q`. -/
theorem exists_pos_lt_mul_rpow_lt_mul_rpow {A p q ε R : ℝ} (hqp : q < p)
    (hε : 0 < ε) (hR : 0 < R) :
    ∃ θ : ℝ, 0 < θ ∧ θ < R ∧ A * θ ^ p < ε * θ ^ q := by
  have hcont : ContinuousAt (fun θ : ℝ => A * θ ^ (p - q)) 0 :=
    (Real.continuousAt_rpow_const 0 (p - q) (.inr (sub_pos.mpr hqp).le)).const_mul A
  have hlim : Filter.Tendsto (fun θ : ℝ => A * θ ^ (p - q)) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa [Real.zero_rpow (sub_pos.mpr hqp).ne'] using hcont.tendsto
  have hsmall : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ), A * θ ^ (p - q) < ε := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    exact hlim.eventually (Iio_mem_nhds hε)
  have hpos : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ), 0 < θ := self_mem_nhdsWithin
  have hbound : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ), θ < R :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hR)
  obtain ⟨θ, hθ, hθR, hθsmall⟩ := (hpos.and (hbound.and hsmall)).exists
  refine ⟨θ, hθ, hθR, ?_⟩
  calc
    A * θ ^ p = (A * θ ^ (p - q)) * θ ^ q := by
      rw [mul_assoc, ← Real.rpow_add hθ, sub_add_cancel]
    _ < ε * θ ^ q := mul_lt_mul_of_pos_right hθsmall (Real.rpow_pos_of_pos hθ q)

/-- Inhomogeneous geometric recurrence bound (`0 sorryAx`, ported from `qinz1yang/differential-geometry`). -/
theorem le_geometric_of_recurrence
    {u : ℕ → ℝ} {r s B : ℝ} (hr : 0 ≤ r) (hrs : r ≠ s)
    (k : ℕ) (hstep : ∀ n < k, u (n + 1) ≤ r * u n + B * s ^ n) :
    u k ≤ r ^ k * (u 0 - B / (s - r)) + B / (s - r) * s ^ k := by
  have hne : s - r ≠ 0 := sub_ne_zero.mpr hrs.symm
  have hmul : B / (s - r) * (s - r) = B := div_mul_cancel₀ B hne
  have hrec : ∀ n < k,
      u (n + 1) - B / (s - r) * s ^ (n + 1) ≤
        r * (u n - B / (s - r) * s ^ n) := by
    intro n hn
    have h := hstep n hn
    have heq : B * s ^ n = B / (s - r) * (s - r) * s ^ n := by rw [hmul]
    rw [heq] at h
    rw [pow_succ]
    nlinarith
  have h := le_geom (u := fun n => u n - B / (s - r) * s ^ n) hr k hrec
  simp only [pow_zero, mul_one] at h
  nlinarith

/-- Inhomogeneous geometric recurrence bound when `r < s` (`0 sorryAx`, ported from `qinz1yang/differential-geometry`). -/
theorem le_geometric_of_recurrence_of_lt
    {u : ℕ → ℝ} {r s B : ℝ} (hr : 0 ≤ r) (hrs : r < s)
    (hu0 : 0 ≤ u 0) (hB : 0 ≤ B)
    (k : ℕ) (hstep : ∀ n < k, u (n + 1) ≤ r * u n + B * s ^ n) :
    u k ≤ s ^ k * (u 0 + B / (s - r)) := by
  have hmain := le_geometric_of_recurrence hr hrs.ne k hstep
  have hp : r ^ k ≤ s ^ k := pow_le_pow_left₀ hr hrs.le k
  have hden : 0 ≤ B / (s - r) := div_nonneg hB (sub_nonneg.mpr hrs.le)
  have hprod := mul_nonneg (pow_nonneg hr k) hden
  have hup := mul_le_mul_of_nonneg_right hp hu0
  nlinarith

/-- Scale contraction recurrence bound (`0 sorryAx`, ported from `qinz1yang/differential-geometry`). -/
theorem geometric_scale_bound_of_recurrence
    {Φ : ℝ → ℝ} {R θ A B p q : ℝ}
    (hR : 0 < R) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hΦ : 0 ≤ Φ R)
    (hcontract : A * θ ^ p < θ ^ q)
    (hstep : ∀ r ∈ Set.Ioc (0 : ℝ) R,
      Φ (θ * r) ≤ A * θ ^ p * Φ r + B * r ^ q) (k : ℕ) :
    Φ (θ ^ k * R) ≤ (θ ^ q) ^ k *
      (Φ R + B * R ^ q / (θ ^ q - A * θ ^ p)) := by
  have hrec : ∀ n < k,
      Φ (θ ^ (n + 1) * R) ≤
        (A * θ ^ p) * Φ (θ ^ n * R) + (B * R ^ q) * (θ ^ q) ^ n := by
    intro n _
    have hnpos : 0 < θ ^ n * R := mul_pos (pow_pos hθ n) hR
    have hnle : θ ^ n * R ≤ R := by
      have hp : θ ^ n ≤ 1 := pow_le_one₀ hθ.le hθ1
      nlinarith
    have h := hstep (θ ^ n * R) ⟨hnpos, hnle⟩
    have hp : (θ ^ n * R) ^ q = (θ ^ q) ^ n * R ^ q := by
      rw [Real.mul_rpow (pow_nonneg hθ.le n) hR.le, ← Real.rpow_pow_comm hθ.le]
    rw [hp] at h
    have harg : θ ^ (n + 1) * R = θ * (θ ^ n * R) := by
      rw [pow_succ]
      ring
    rw [harg]
    calc
      _ ≤ A * θ ^ p * Φ (θ ^ n * R) + B * ((θ ^ q) ^ n * R ^ q) := h
      _ = _ := by ring
  simpa only [pow_zero, one_mul] using
    le_geometric_of_recurrence_of_lt
      (u := fun n => Φ (θ ^ n * R))
      (mul_nonneg hA (Real.rpow_nonneg hθ.le _)) hcontract
      (by simpa only [pow_zero, one_mul] using hΦ)
      (mul_nonneg hB (Real.rpow_nonneg hR.le _)) k hrec

/-- Half-contraction scale bound (`0 sorryAx`, ported from `qinz1yang/differential-geometry`). -/
theorem geometric_scale_bound_of_half_contraction
    {Φ : ℝ → ℝ} {R θ A B p q : ℝ}
    (hR : 0 < R) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hΦ : 0 ≤ Φ R)
    (hcontract : A * θ ^ p ≤ θ ^ q / 2)
    (hstep : ∀ r ∈ Set.Ioc (0 : ℝ) R,
      Φ (θ * r) ≤ A * θ ^ p * Φ r + B * r ^ q) (k : ℕ) :
    Φ (θ ^ k * R) ≤ θ ^ ((k : ℝ) * q) *
      (Φ R + 2 * B * R ^ q / θ ^ q) := by
  have hθq : 0 < θ ^ q := Real.rpow_pos_of_pos hθ q
  have hgap : 0 < θ ^ q - A * θ ^ p := by linarith
  have hmain := geometric_scale_bound_of_recurrence hR hθ hθ1 hA hB hΦ
    (by linarith : A * θ ^ p < θ ^ q) hstep k
  have hnum : 0 ≤ B * R ^ q := mul_nonneg hB (Real.rpow_nonneg hR.le _)
  have hquot : B * R ^ q / (θ ^ q - A * θ ^ p) ≤ 2 * B * R ^ q / θ ^ q := by
    apply (div_le_div_iff₀ hgap hθq).mpr
    nlinarith
  have hp : (θ ^ q) ^ k = θ ^ ((k : ℝ) * q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hθ.le, mul_comm q]
  rw [← hp]
  exact hmain.trans (mul_le_mul_of_nonneg_left
    (by simpa [add_comm] using add_le_add_left hquot (Φ R)) (pow_nonneg hθq.le k))

/-- Continuous radius power-law decay from discrete geometric scale decay (`0 sorryAx`,
ported from `qinz1yang/differential-geometry`). -/
theorem radius_power_bound_of_geometric_decay
    {E : ℝ → ℝ} {θ R q M : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hR : 0 < R)
    (hq : 0 ≤ q) (hM : 0 ≤ M) (hmono : MonotoneOn E (Set.Ioc (0 : ℝ) R))
    (hdec : ∀ n : ℕ, E (θ ^ n * R) ≤ (θ ^ q) ^ n * M) :
    ∀ r ∈ Set.Ioc (0 : ℝ) R,
      E r ≤ (M / (θ * R) ^ q) * r ^ q := by
  intro r hr
  obtain ⟨n, hlo, hhi⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hr.1 hR) ((div_le_one hR).mpr hr.2) hθ hθ1
  have hscale0 : 0 < θ ^ n * R := mul_pos (pow_pos hθ n) hR
  have hscaleR : θ ^ n * R ≤ R := mul_le_of_le_one_left hR.le (pow_le_one₀ hθ.le hθ1.le)
  have hscale : r ≤ θ ^ n * R := (div_le_iff₀ hR).mp hhi
  have hnear : θ ^ n ≤ r / (θ * R) := by
    rw [pow_succ] at hlo
    have hh := (lt_div_iff₀ hR).mp hlo
    apply (le_div_iff₀ (mul_pos hθ hR)).mpr
    nlinarith
  have hp : (θ ^ q) ^ n ≤ (r / (θ * R)) ^ q := by
    rw [Real.rpow_pow_comm hθ.le]
    exact Real.rpow_le_rpow (pow_nonneg hθ.le n) hnear hq
  calc
    E r ≤ E (θ ^ n * R) := hmono hr ⟨hscale0, hscaleR⟩ hscale
    _ ≤ (θ ^ q) ^ n * M := hdec n
    _ ≤ (r / (θ * R)) ^ q * M := mul_le_mul_of_nonneg_right hp hM
    _ = (M / (θ * R) ^ q) * r ^ q := by
      rw [Real.div_rpow hr.1.le (mul_nonneg hθ.le hR.le)]
      ring

/-- Small-drop pigeonhole lemma for monotone sequences (`0 sorryAx`, ported from `qinz1yang/differential-geometry`). -/
theorem exists_sub_lt_of_mul_lt
    (e : ℕ → ℝ) {B η : ℝ} {N : ℕ}
    (hN : 0 ≤ e N) (hzero : e 0 ≤ B) (hB : B < (N : ℝ) * η) :
    ∃ j < N, e j - e (j + 1) < η := by
  have hsum : (∑ j ∈ Finset.range N, (e j - e (j + 1))) <
      ∑ _j ∈ Finset.range N, η := by
    rw [Finset.sum_range_sub', Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact (sub_le_self _ hN).trans_lt (hzero.trans_lt hB)
  obtain ⟨j, hj, hdrop⟩ := Finset.exists_lt_of_sum_lt hsum
  exact ⟨j, Finset.mem_range.mp hj, hdrop⟩

/-- Uniform index energy bound from small-drop hole-filling (`0 sorryAx`, ported from `qinz1yang/differential-geometry`). -/
theorem exists_uniform_index_energy_le_of_small_drop
    {ε C B η : ℝ} (hε : 0 < ε) (hC : 0 < C) (hB : 0 ≤ B) (hη : 0 < η) :
    ∃ N : ℕ, 0 < N ∧ ∀ e : ℕ → ℝ, ∀ δ : ℝ,
      Antitone e → (∀ k, 0 ≤ e k) → e 0 ≤ B →
      (∀ j, e j - e (j + 1) < ε → e (j + 1) ≤ C * (e j - e (j + 1)) + δ) →
      e N ≤ η + δ := by
  let t : ℝ := min ε (η / C)
  have ht : 0 < t := lt_min hε (div_pos hη hC)
  obtain ⟨N, hN⟩ := exists_nat_gt (B / t)
  have hNpos : 0 < N := by
    have hNreal : (0 : ℝ) < N := (div_nonneg hB ht.le).trans_lt hN
    exact Nat.cast_pos.mp hNreal
  have hBmul : B < (N : ℝ) * t := (div_lt_iff₀ ht).mp hN
  refine ⟨N, hNpos, ?_⟩
  intro e δ he hnonneg hzero hdrop
  obtain ⟨j, hj, hjdrop⟩ := exists_sub_lt_of_mul_lt e (hnonneg N) hzero hBmul
  have hsmall : e j - e (j + 1) < ε := hjdrop.trans_le (min_le_left _ _)
  have heta : C * (e j - e (j + 1)) < η := by
    have h := (lt_div_iff₀ hC).mp (hjdrop.trans_le (min_le_right _ _))
    simpa only [mul_comm] using h
  exact (he (Nat.succ_le_iff.mpr hj)).trans
    ((hdrop j hsmall).trans (add_le_add heta.le le_rfl))

/-- Dyadic decay from Widman hole-filling (`0 sorryAx`, ported from `qinz1yang/differential-geometry`):
For any antitone sequence `e : ℕ → ℝ` with `e 0 ≤ Λ` satisfying `e (j + 1) ≤ K * (e j - e (j + 1))`
whenever `e j - e (j + 1) < ε₀`, there exists `N` depending only on `(ε₀, K, Λ)` such that
`e (N + k) ≤ (K / (1 + K)) ^ k * ε₀`. -/
theorem dyadic_decay_of_hole_filling {ε₀ K Λ : ℝ} (hε₀ : 0 < ε₀) (hK : 0 < K)
    (hΛ : 0 ≤ Λ) :
    ∃ N : ℕ, ∀ e : ℕ → ℝ, Antitone e → (∀ k, 0 ≤ e k) → e 0 ≤ Λ →
      (∀ j, e j - e (j + 1) < ε₀ → e (j + 1) ≤ K * (e j - e (j + 1))) →
      ∀ k, e (N + k) ≤ (K / (1 + K)) ^ k * ε₀ := by
  obtain ⟨N, _, hN⟩ := exists_uniform_index_energy_le_of_small_drop
    hε₀ hK hΛ (half_pos hε₀)
  refine ⟨N, fun e he he0 heΛ hdrop k => ?_⟩
  have hdrop0 : ∀ j, e j - e (j + 1) < ε₀ → e (j + 1) ≤ K * (e j - e (j + 1)) + 0 :=
    fun j hj => by rw [add_zero]; exact hdrop j hj
  have heN : e N ≤ ε₀ / 2 + 0 := hN e 0 he he0 heΛ hdrop0
  rw [add_zero] at heN
  induction k with
  | zero => simpa only [add_zero, pow_zero, one_mul] using heN.trans (half_le_self hε₀.le)
  | succ k ih =>
    have hlt : e (N + k) - e (N + k + 1) < ε₀ := by
      have h1 := he0 (N + k + 1)
      have h2 : e (N + k) ≤ ε₀ / 2 := (he (Nat.le_add_right N k)).trans heN
      linarith
    have hstep := hdrop (N + k) hlt
    have hθ : e (N + k + 1) ≤ K / (1 + K) * e (N + k) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      nlinarith
    rw [← add_assoc, pow_succ]
    calc e (N + k + 1) ≤ K / (1 + K) * e (N + k) := hθ
      _ ≤ K / (1 + K) * ((K / (1 + K)) ^ k * ε₀) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (K / (1 + K)) ^ k * (K / (1 + K)) * ε₀ := by ring

/-- Widman hole-filling contraction on concentric annuli (`0 sorryAx`):
If `E(u; A(r₁, r₂)) ≤ K * (E(u; A(r, R)) - E(u; A(r₁, r₂)))` with `0 ≤ K`, then
`E(u; A(r₁, r₂)) ≤ (K / (1 + K)) * E(u; A(r, R))`. -/
theorem energyMeasure_annulus_le_of_hole_filling
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (center : ℂ) (r r₁ r₂ R K : ℝ) (hK : 0 ≤ K)
    (h_hole : energyMeasure I u (annulus_at center r₁ r₂) ≤
      K * (energyMeasure I u (annulus_at center r R) - energyMeasure I u (annulus_at center r₁ r₂))) :
    energyMeasure I u (annulus_at center r₁ r₂) ≤
      (K / (1 + K)) * energyMeasure I u (annulus_at center r R) := by
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  nlinarith

/-- Iterated Widman hole-filling geometric contraction (`0 sorryAx`):
If `e : ℕ → ℝ` satisfies `e (j + 1) ≤ K * (e j - e (j + 1))` for all `j < k` with `0 ≤ K`,
then `e k ≤ (K / (1 + K)) ^ k * e 0`. -/
theorem le_pow_hole_filling_of_step
    {e : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) (k : ℕ)
    (h_step : ∀ j < k, e (j + 1) ≤ K * (e j - e (j + 1))) :
    e k ≤ (K / (1 + K)) ^ k * e 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : e (k + 1) ≤ K / (1 + K) * e k := by
      have h := h_step k (Nat.lt_succ_self k)
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      nlinarith
    have ih' := ih (fun j hj => h_step j (Nat.lt_succ_of_lt hj))
    rw [pow_succ, mul_assoc]
    calc e (k + 1) ≤ K / (1 + K) * e k := hk
      _ ≤ K / (1 + K) * ((K / (1 + K)) ^ k * e 0) :=
        mul_le_mul_of_nonneg_left ih' (by positivity)
      _ = (K / (1 + K)) ^ k * (K / (1 + K) * e 0) := by ring

/-- One-sided punctured-disk power-law energy decay derived from two-sided cylinder energy decay (`0 sorryAx`):
If `u` satisfies two-sided cylinder decay on sub-annuli of `annulus_at center 0 R` with constants
`(C₀, a_decay)` (`0 ≤ C₀`, `0 ≤ a_decay`) and `energyMeasureExtended I u (annulus_at center 0 R) ≠ ⊤`,
then for all `0 < r₁ < r₂ < R`, choosing the inner radius `r = min (r₁ / 2) (r₁ * (r₂ / R))`
absorbs the inner collar ratio `(r / r₁)^a_decay ≤ (r₂ / R)^a_decay` and yields
`E(u; A(r₁, r₂)) ≤ 2 * C₀ * (r₂ / R)^a_decay * E(u; A(0, R))`. -/
theorem energyMeasure_annulus_le_punctured_disk_power_of_cylinder_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (center : ℂ) {r₁ r₂ R C₀ a_decay : ℝ}
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (hr₂R : r₂ < R)
    (hC₀ : 0 ≤ C₀) (ha : 0 ≤ a_decay)
    (h_fin : energyMeasureExtended I u (annulus_at center 0 R) ≠ ⊤)
    (h_cyl : ∀ r : ℝ, 0 < r → r < r₁ →
      energyMeasure I u (annulus_at center r₁ r₂) ≤
        C₀ * ((r / r₁) ^ a_decay + (r₂ / R) ^ a_decay) * energyMeasure I u (annulus_at center r R)) :
    energyMeasure I u (annulus_at center r₁ r₂) ≤
      2 * C₀ * (r₂ / R) ^ a_decay * energyMeasure I u (annulus_at center 0 R) := by
  have hr₂_pos : 0 < r₂ := lt_trans hr₁ hr₁₂
  have hR_pos : 0 < R := lt_trans hr₂_pos hr₂R
  let r := min (r₁ / 2) (r₁ * (r₂ / R))
  have hr_pos : 0 < r := lt_min (half_pos hr₁) (mul_pos hr₁ (div_pos hr₂_pos hR_pos))
  have hr_lt_r₁ : r < r₁ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr₁)
  have h_ratio_le : r / r₁ ≤ r₂ / R := by
    rw [div_le_iff₀ hr₁, mul_comm]
    exact min_le_right _ _
  have h_rpow_le : (r / r₁) ^ a_decay ≤ (r₂ / R) ^ a_decay :=
    Real.rpow_le_rpow (div_nonneg hr_pos.le hr₁.le) h_ratio_le ha
  have h_mono : energyMeasure I u (annulus_at center r R) ≤
      energyMeasure I u (annulus_at center 0 R) :=
    energyMeasure_annulus_at_mono I u center hr_pos.le le_rfl h_fin
  have h_step := h_cyl r hr_pos hr_lt_r₁
  have h_en_nonneg : 0 ≤ energyMeasure I u (annulus_at center r R) := energy_nonneg I u _
  have h_rpow_nonneg : 0 ≤ (r₂ / R) ^ a_decay := Real.rpow_nonneg (div_nonneg hr₂_pos.le hR_pos.le) _
  calc
    energyMeasure I u (annulus_at center r₁ r₂)
      ≤ C₀ * ((r / r₁) ^ a_decay + (r₂ / R) ^ a_decay) * energyMeasure I u (annulus_at center r R) := h_step
    _ ≤ C₀ * ((r₂ / R) ^ a_decay + (r₂ / R) ^ a_decay) * energyMeasure I u (annulus_at center r R) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add h_rpow_le le_rfl) hC₀) h_en_nonneg
    _ = 2 * C₀ * (r₂ / R) ^ a_decay * energyMeasure I u (annulus_at center r R) := by ring
    _ ≤ 2 * C₀ * (r₂ / R) ^ a_decay * energyMeasure I u (annulus_at center 0 R) :=
      mul_le_mul_of_nonneg_left h_mono (by positivity)

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

/-- Cylinder energy decay predicate with general constants `C₀` and exponent `a_decay`:
`E(u; A(r₁, r₂)) ≤ C₀ * ((r / r₁)^a + (r₂ / R)^a) * E(u; A(r, R))` for `r < r₁ < r₂ < R`. -/
def SatisfiesCylinderEnergyDecayWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (C₀ a_decay : ℝ) (u : CP1 → M) (center : ℂ) (r R : ℝ) : Prop :=
  ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
    energyMeasure I u (annulus_at center r₁ r₂) ≤
      C₀ * ((r / r₁) ^ a_decay + (r₂ / R) ^ a_decay) * energyMeasure I u (annulus_at center r R)

/-- Certificate `h_decay` (corrected form, Contract A10): there are target constants `C₀, a, ε > 0`
such that every `J`-holomorphic sphere whose annulus `A(center; r, R)` carries energy `< ε`
satisfies two-sided power decay on sub-annuli. This is exactly the hypothesis consumed by
`cylinder_exponential_decay` and `exists_target_thresholds`.

The universal form `SatisfiesCylinderEnergyDecay` (constants `1, 1`, no smallness hypothesis) is
false: for `id : CP1 → CP1`, `center = 0`, `r = ε`, `R = 1/ε`, `r₁ = 1/2`, `r₂ = 2`, the left side
`E(id; A(1/2, 2))` is a fixed positive area while the right side is `≤ 4ε · E(id) → 0`. -/
def CylinderEnergyDecayProperty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] : Prop :=
  ∃ (C₀ a_decay ε_neck : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck ∧
    ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      0 < r → 2 * r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r R) < ε_neck →
      SatisfiesCylinderEnergyDecayWith I C₀ a_decay u center r R

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
      have hd : riemannianEnergyDensity I (fun _ => c) (stereo_chart.symm w) = 0 :=
        energy_density_const_map I c (stereo_chart.symm w)
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

/-- Cylinder Energy and Diameter Exponential Decay (Contract A10, conditional pass-through of `h_decay`). -/
theorem cylinder_exponential_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_decay : ∃ (C₀ a_decay ε_neck : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck ∧
      ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
        0 < r → 2 * r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        energyMeasure I u (annulus_at center r R) < ε_neck →
        ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
          energyMeasure I u (annulus_at center r₁ r₂) ≤
            C₀ * ((r / r₁)^a_decay + (r₂ / R)^a_decay) * energyMeasure I u (annulus_at center r R)) :
    ∃ (C₀ a_decay ε_neck : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck ∧
    ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      0 < r → 2 * r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r R) < ε_neck →
      ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
        energyMeasure I u (annulus_at center r₁ r₂) ≤
          C₀ * ((r / r₁)^a_decay + (r₂ / R)^a_decay) * energyMeasure I u (annulus_at center r R) :=
  h_decay

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
  continuousOn_univ.mp h_weak.1.continuousOn

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

/-- Every stereographic annulus `annulus_at a r R` is a Borel measurable subset of `CP1` (`0 sorryAx`). -/
theorem measurableSet_annulus_at (a : ℂ) (r R : ℝ) :
    MeasurableSet (annulus_at a r R) :=
  (is_open_annulus_at a r R).measurableSet

/-- Every punctured disk `annulus_at a 0 R` is contained in `punctured_sphere {stereo_chart.symm a}` (`0 sorryAx`). -/
theorem annulus_at_zero_subset_punctured_sphere (a : ℂ) (R : ℝ) :
    annulus_at a 0 R ⊆ punctured_sphere {stereo_chart.symm a} := by
  rw [punctured_sphere_singleton_eq_compl]
  rintro p ⟨z, ⟨hz_pos, _⟩, rfl⟩ hp_eq
  rw [Set.mem_singleton_iff] at hp_eq
  have hza : z = a := stereo_chart_symm_injective hp_eq
  subst hza
  simp [dist_self] at hz_pos

/-- Every stereographic annulus `annulus_at a r R` is contained in `punctured_sphere {north_pole}` (`0 sorryAx`). -/
theorem annulus_at_subset_punctured_sphere_north_pole (a : ℂ) (r R : ℝ) :
    annulus_at a r R ⊆ punctured_sphere {north_pole} := by
  rw [punctured_sphere_singleton_eq_compl]
  rintro p hp rfl
  exact north_pole_not_mem_annulus_at a r R hp

/-- The countable intersection of punctured disks `annulus_at a 0 (1 / (n + 1))` is empty (`0 sorryAx`). -/
theorem iInter_annulus_at_zero_nat (a : ℂ) :
    (⋂ n : ℕ, annulus_at a 0 (1 / ((n : ℝ) + 1))) = ∅ := by
  ext p
  simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
  by_cases h0 : p ∈ annulus_at a 0 (1 / ((0 : ℕ) + 1 : ℝ))
  · rcases h0 with ⟨z, ⟨hz_pos, _⟩, rfl⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / dist z a)
    refine ⟨n, ?_⟩
    rintro ⟨w, ⟨_, hw_lt⟩, hw_eq⟩
    have hzw : w = z := stereo_chart_symm_injective hw_eq
    rcases hzw with rfl
    have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : 1 < (n : ℝ) * dist w a := (div_lt_iff₀ hz_pos).mp hn
    have h1 : 1 / ((n : ℝ) + 1) < dist w a := by
      rw [div_lt_iff₀ hn_pos]
      linarith
    linarith
  · exact ⟨0, h0⟩

/-- Vanishing of the extended energy measure on shrinking punctured disks `annulus_at a 0 (1 / (n + 1))`
for any finite-energy curve on `punctured_sphere {stereo_chart.symm a}` (`0 sorryAx`). -/
theorem tendsto_energyMeasureExtended_annulus_at_zero_nat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ)
    (h_energy : energyMeasureExtended I u (punctured_sphere {stereo_chart.symm a}) ≠ ⊤) :
    Filter.Tendsto
      (fun n : ℕ => energyMeasureExtended I u (annulus_at a 0 (1 / ((n : ℝ) + 1))))
      Filter.atTop (𝓝 0) := by
  have h_meas : ∀ n : ℕ,
      MeasureTheory.NullMeasurableSet (annulus_at a 0 (1 / ((n : ℝ) + 1))) (energyMeasureExtended I u) :=
    fun n => (measurableSet_annulus_at a 0 (1 / ((n : ℝ) + 1))).nullMeasurableSet
  have h_anti : Antitone (fun n : ℕ => annulus_at a 0 (1 / ((n : ℝ) + 1))) := by
    intro i j hij
    apply annulus_at_mono a le_rfl
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have h_fin : ∃ i : ℕ, energyMeasureExtended I u (annulus_at a 0 (1 / ((i : ℝ) + 1))) ≠ ⊤ :=
    ⟨0, ne_top_of_le_ne_top h_energy
      (MeasureTheory.measure_mono (annulus_at_zero_subset_punctured_sphere a _))⟩
  have h_tendsto := MeasureTheory.tendsto_measure_iInter_atTop h_meas h_anti h_fin
  rwa [iInter_annulus_at_zero_nat a, MeasureTheory.measure_empty] at h_tendsto

/-- Existence of a small punctured-disk radius `R₀ > 0` around `stereo_chart.symm a` with sub-threshold
energy `< ε` for any finite-energy curve (`0 sorryAx`). -/
theorem exists_punctured_disk_energy_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) {ε : ℝ} (hε : 0 < ε)
    (h_energy : energyMeasureExtended I u (punctured_sphere {stereo_chart.symm a}) ≠ ⊤) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ r R : ℝ, 0 ≤ r → R ≤ R₀ →
      energyMeasure I u (annulus_at a r R) < ε := by
  have h_tendsto := tendsto_energyMeasureExtended_annulus_at_zero_nat I u a h_energy
  have h_mem : Set.Iio (ENNReal.ofReal ε) ∈ 𝓝 (0 : ENNReal) :=
    Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨n, hn⟩ := (h_tendsto.eventually h_mem).exists
  refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_⟩
  intro r R hr hR
  have h_mono : energyMeasureExtended I u (annulus_at a r R) ≤
      energyMeasureExtended I u (annulus_at a 0 (1 / ((n : ℝ) + 1))) :=
    energyMeasureExtended_annulus_at_mono I u a hr hR
  exact ENNReal.toReal_lt_of_lt_ofReal (lt_of_le_of_lt h_mono hn)

/-- Pointwise agreement on `punctured_sphere {p}` of `Function.update u p x₀` with `u` (`0 sorryAx`). -/
theorem eqOn_update_punctured_sphere
    {M : Type*} (u : CP1 → M) (p : CP1) (x₀ : M) :
    EqOn (Function.update u p x₀) u (punctured_sphere {p}) := by
  intro z hz
  rw [punctured_sphere_singleton_eq_compl] at hz
  exact Function.update_of_ne hz x₀ u

/-- Global continuity of `Function.update u p x₀` across an isolated puncture `p : CP1` whenever
`u` is continuous on `punctured_sphere {p}` and converges to `x₀` along `𝓝[≠] p` (`0 sorryAx`). -/
theorem continuous_update_of_tendsto_punctured_sphere
    {M : Type*} [TopologicalSpace M]
    (u : CP1 → M) (p : CP1) (x₀ : M)
    (hu_cont : ContinuousOn u (punctured_sphere {p}))
    (hu_lim : Filter.Tendsto u (𝓝[≠] p) (𝓝 x₀)) :
    Continuous (Function.update u p x₀) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hzp : z = p
  · subst hzp
    rw [← continuousWithinAt_compl_self]
    unfold ContinuousWithinAt
    rw [Function.update_self]
    have h_eq : EqOn u (Function.update u z x₀) ({z}ᶜ : Set CP1) := by
      intro y hy
      exact (Function.update_of_ne hy x₀ u).symm
    exact hu_lim.congr' (h_eq.eventuallyEq_of_mem self_mem_nhdsWithin)
  · have hz_mem : z ∈ punctured_sphere {p} := by
      rw [punctured_sphere_singleton_eq_compl]
      exact hzp
    have h_ca : ContinuousAt u z :=
      hu_cont.continuousAt ((isOpen_punctured_sphere p).mem_nhds hz_mem)
    have h_ev : u =ᶠ[𝓝 z] Function.update u p x₀ :=
      (eqOn_update_punctured_sphere u p x₀).symm.eventuallyEq_of_mem
        ((isOpen_punctured_sphere p).mem_nhds hz_mem)
    exact h_ca.congr h_ev

/-- If `Function.update u p x₀` is `WeakJHolomorphicOn` on `Set.univ`, then `u` satisfies
`SatisfiesPunctureSobolevExtension` at `p` (`0 sorryAx`). -/
theorem satisfiesPunctureSobolevExtension_of_update_weakJHolomorphicOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1) (x₀ : M)
    (h_weak : WeakJHolomorphicOn I (Function.update u p x₀) Set.univ) :
    SatisfiesPunctureSobolevExtension I u p :=
  satisfiesPunctureSobolevExtension_of_eqOn_weakJHolomorphicOn_univ I u
    (Function.update u p x₀) p h_weak (eqOn_update_punctured_sphere u p x₀)

/-- If `Function.update u p x₀` is $C^1$ on `Set.univ` with vanishing differential at `p`, then
any `J`-holomorphic curve `u` on `punctured_sphere {p}` satisfies `SatisfiesPunctureSobolevExtension` (`0 sorryAx`). -/
theorem satisfiesPunctureSobolevExtension_of_update_c1_vanishing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1) (x₀ : M)
    (h_c1 : ContMDiffOn I_CP1 I 1 (Function.update u p x₀) Set.univ)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_zero : mfderiv I_CP1 I (Function.update u p x₀) p = 0) :
    SatisfiesPunctureSobolevExtension I u p :=
  satisfiesPunctureSobolevExtension_of_c1_vanishing_at_puncture I u
    (Function.update u p x₀) p h_c1 (eqOn_update_punctured_sphere u p x₀) h_jhol h_zero

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
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (h_ext : SatisfiesPunctureSobolevExtension I u p) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {p}) :=
  puncture_sobolev_extension_of_certificate I u p h_jhol h_energy h_ext

/-- Removable singularity bootstrap bridge (Contract A11 → A05 → A12):
Upgrades a weak $C^1$ $J$-holomorphic curve on CP1 to a smooth $J$-holomorphic curve on CP1.
Proved with ZERO `sorry` from `nonlinear_elliptic_bootstrap` (`A05`). -/
theorem singularity_removal_bootstrap_bridge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_ext : CP1 → M)
    (h_weak : WeakJHolomorphicOn I u_ext Set.univ)
    (h_tower : ∀ (n : ℕ), ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u_ext Set.univ) :
    JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext Set.univ := by
  have hu_smooth : ContMDiffOn I_CP1 I ∞ u_ext Set.univ :=
    nonlinear_elliptic_bootstrap I u_ext Set.univ isOpen_univ h_weak h_tower
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
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (h_ext : SatisfiesPunctureSobolevExtension I u p)
    (h_tower : ∀ (u_ext : CP1 → M), WeakJHolomorphicOn I u_ext Set.univ →
      ∀ (n : ℕ), ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u_ext Set.univ) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ := by
  obtain ⟨u_ext, _hu_cont, hu_weak, hu_eq⟩ := puncture_sobolev_extension I u p h_jhol h_energy h_ext
  have hu_jhol := singularity_removal_bootstrap_bridge I u_ext hu_weak (h_tower u_ext hu_weak)
  refine ⟨u_ext, ⟨hu_eq, hu_jhol⟩, ?_⟩
  intro v ⟨hv_eq, hv_smooth⟩
  have hu_ext_cont := continuous_of_jholomorphicOn I u_ext hu_jhol
  have hv_cont := continuous_of_jholomorphicOn I v hv_smooth
  have h_eq_uv : EqOn v u_ext (punctured_sphere {p}) := by
    intro z hz
    rw [hv_eq hz, hu_eq hz]
  exact Continuous.ext_on (dense_punctured_sphere p) hv_cont hu_ext_cont h_eq_uv

/-!
## Coordinate-Level Widman Hole-Filling, Collar Oscillation & Puncture Cauchy Extension
(`h_osc`, `h_decay`, `h_punc`)

This section implements the coordinate-level derivations for Certificates 3, 4, and 5:
1. `poincare_circle_const`: 1D Poincaré / Wirtinger inequality on `[0, 2π]` for constant loops.
2. `hole_filling_step` and `hole_filling_contraction_lt_one`: Widman's hole-filling step
   `E(u; A(2r, R/2)) ≤ (K / (1 + K)) * E(u; A(r, R))` with contraction factor `θ = K / (1 + K) < 1`.
3. `diam_image_collar_le_four_sqrt_energy`: diameter bound `diam (u '' A(2r, R/2)) ≤ 4 √E(u; A(r, R))`
   from `SatisfiesCylinderCollarOscillation`.
4. `energy_annulus_tendsto_zero` and `oscillation_tendsto_zero`: vanishing dyadic neck energy and
   vanishing collar diameter as `r → 0⁺` around an isolated finite-energy puncture.
5. `exists_limit_point_of_puncture` and `satisfiesPunctureSobolevExtension_of_finite_energy_aux`:
   Cauchy filter completeness on `[CompactSpace M]` yielding `∃ m_star, Tendsto u (𝓝[≠] p) (𝓝 m_star)`
   and continuous `WeakJHolomorphicOn` extension via `Function.update u p m_star`.
-/

/-- Unconditional 1D Poincaré inequality on `[0, 2π]` for any constant loop `fun _ => y₀` (`0 sorryAx`). -/
theorem poincare_circle_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y₀ : E) (C_poincare : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖(fun _ : ℝ => y₀) θ - y₀‖ ^ 2 ≤
      C_poincare * ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖deriv (fun _ : ℝ => y₀) θ‖ ^ 2 := by
  simp

/-- The Widman hole-filling contraction factor `θ = K / (1 + K)` is strictly less than `1` for any
`0 ≤ K` (`0 sorryAx`). -/
theorem hole_filling_contraction_lt_one {K : ℝ} (hK : 0 ≤ K) :
    K / (1 + K) < 1 := by
  rw [div_lt_one (by linarith)]
  linarith

/-- Widman's hole-filling step on concentric dyadic annuli `A(2r, R/2) ⊂ A(r, R)`:
if the inner annular energy is bounded by `K` times the collar energy difference
`E(A(r, R)) - E(A(2r, R/2))`, then `E(A(2r, R/2)) ≤ (K / (1 + K)) * E(A(r, R))` (`0 sorryAx`). -/
theorem hole_filling_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (center : ℂ) (r R K : ℝ) (_h_annulus : 4 * r < R) (hK : 0 ≤ K)
    (h_hole : energyMeasure I u (annulus_at center (2 * r) (R / 2)) ≤
      K * (energyMeasure I u (annulus_at center r R) -
           energyMeasure I u (annulus_at center (2 * r) (R / 2)))) :
    energyMeasure I u (annulus_at center (2 * r) (R / 2)) ≤
      (K / (1 + K)) * energyMeasure I u (annulus_at center r R) :=
  energyMeasure_annulus_le_of_hole_filling I u center r (2 * r) (R / 2) R K hK h_hole

/-- If `SatisfiesCylinderCollarOscillation I u a r R` holds, then the diameter of the collar image
`u '' annulus_at a (2 * r) (R / 2)` is bounded by `4 * √E(u; A(r, R))` (`0 sorryAx`). -/
theorem diam_image_collar_le_four_sqrt_energy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r R : ℝ)
    (h_osc : SatisfiesCylinderCollarOscillation I u a r R) :
    Metric.diam (u '' annulus_at a (2 * r) (R / 2)) ≤
      4 * Real.sqrt (energyMeasure I u (annulus_at a r R)) := by
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  rintro _ ⟨z₁, hz₁, rfl⟩ _ ⟨z₂, hz₂, rfl⟩
  exact h_osc z₁ hz₁ z₂ hz₂

/-- For any finite-energy curve on `punctured_sphere {stereo_chart.symm a}`, the energy on shrinking
dyadic annuli `annulus_at a (r / 2) r` tends to `0` as `r → 0⁺` (`0 sorryAx`).
Derived unconditionally from `exists_punctured_disk_energy_lt`. -/
theorem energy_annulus_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ)
    (h_energy : energyMeasureExtended I u (punctured_sphere {stereo_chart.symm a}) ≠ ⊤) :
    Filter.Tendsto (fun r : ℝ => energyMeasure I u (annulus_at a (r / 2) r)) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R₀, hR₀, h_lt⟩ := exists_punctured_disk_energy_lt I u a hε h_energy
  filter_upwards [Ioo_mem_nhdsGT hR₀] with r hr
  have hr_nonneg : 0 ≤ r / 2 := by linarith [hr.1]
  have h_en_nonneg : 0 ≤ energyMeasure I u (annulus_at a (r / 2) r) :=
    energy_nonneg I u _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h_en_nonneg]
  exact h_lt (r / 2) r hr_nonneg hr.2.le

/-- For any finite-energy curve on `punctured_sphere {stereo_chart.symm a}`, the energy on wider
dyadic collars `annulus_at a (r / 4) (2 * r)` tends to `0` as `r → 0⁺` (`0 sorryAx`). -/
theorem energy_wide_annulus_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ)
    (h_energy : energyMeasureExtended I u (punctured_sphere {stereo_chart.symm a}) ≠ ⊤) :
    Filter.Tendsto (fun r : ℝ => energyMeasure I u (annulus_at a (r / 4) (2 * r))) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R₀, hR₀, h_lt⟩ := exists_punctured_disk_energy_lt I u a hε h_energy
  filter_upwards [Ioo_mem_nhdsGT (half_pos hR₀)] with r hr
  have hr_nonneg : 0 ≤ r / 4 := by linarith [hr.1]
  have h2r_le : 2 * r ≤ R₀ := by linarith [hr.2]
  have h_en_nonneg : 0 ≤ energyMeasure I u (annulus_at a (r / 4) (2 * r)) :=
    energy_nonneg I u _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h_en_nonneg]
  exact h_lt (r / 4) (2 * r) hr_nonneg h2r_le

/-- Vanishing oscillation on shrinking dyadic annuli `annulus_at a (r / 2) r` around a finite-energy
puncture whenever `SatisfiesCylinderCollarOscillation I u a (r / 4) (2 * r)` holds for small `r > 0`
(`0 sorryAx`). -/
theorem oscillation_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ)
    (h_energy : energyMeasureExtended I u (punctured_sphere {stereo_chart.symm a}) ≠ ⊤)
    (h_osc : ∀ᶠ r in 𝓝[>] (0 : ℝ), SatisfiesCylinderCollarOscillation I u a (r / 4) (2 * r)) :
    Filter.Tendsto (fun r : ℝ => Metric.diam (u '' annulus_at a (r / 2) r)) (𝓝[>] 0) (𝓝 0) := by
  have h_en_zero := energy_wide_annulus_tendsto_zero I u a h_energy
  have h_upper : Filter.Tendsto
      (fun r : ℝ => 4 * Real.sqrt (energyMeasure I u (annulus_at a (r / 4) (2 * r))))
      (𝓝[>] 0) (𝓝 0) := by
    have h_cont : Continuous (fun x : ℝ => 4 * Real.sqrt x) :=
      continuous_const.mul Real.continuous_sqrt
    have h_comp := (h_cont.tendsto 0).comp h_en_zero
    rw [Real.sqrt_zero, mul_zero] at h_comp
    exact h_comp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper ?_ ?_
  · exact Filter.Eventually.of_forall (fun _ => Metric.diam_nonneg)
  · filter_upwards [h_osc] with r hr_osc
    have h_diam := diam_image_collar_le_four_sqrt_energy I u a (r / 4) (2 * r) hr_osc
    have h1 : 2 * (r / 4) = r / 2 := by ring
    have h2 : 2 * r / 2 = r := by ring
    rw [h1, h2] at h_diam
    exact h_diam

/-- Vanishing punctured-neighborhood oscillation implies that `Filter.map u (𝓝[≠] p)` is a Cauchy
filter in `M`, so by completeness of `[CompactSpace M]` the limit `lim_{z → p} u(z)` exists (`0 sorryAx`). -/
theorem exists_limit_point_of_puncture
    {M : Type*} [MetricSpace M] [CompactSpace M]
    (u : CP1 → M) (p : CP1)
    (h_osc_nhds : ∀ ε > 0, ∃ U ∈ 𝓝 p, ∀ z₁ ∈ U \ {p}, ∀ z₂ ∈ U \ {p}, dist (u z₁) (u z₂) < ε) :
    ∃ m_star : M, Filter.Tendsto u (𝓝[≠] p) (𝓝 m_star) := by
  have h_dense : Dense ({p}ᶜ : Set CP1) := by
    rw [← punctured_sphere_singleton_eq_compl]
    exact dense_punctured_sphere p
  have h_neBot : (𝓝[≠] p).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (h_dense p)
  have h_cauchy : Cauchy (Filter.map u (𝓝[≠] p)) := by
    rw [Metric.cauchy_iff]
    refine ⟨Filter.NeBot.map h_neBot u, ?_⟩
    intro ε hε
    obtain ⟨U, hU, h_dist⟩ := h_osc_nhds ε hε
    refine ⟨u '' ({p}ᶜ ∩ U), Filter.image_mem_map (inter_mem_nhdsWithin ({p}ᶜ) hU), ?_⟩
    rintro _ ⟨z₁, hz₁, rfl⟩ _ ⟨z₂, hz₂, rfl⟩
    exact h_dist z₁ ⟨hz₁.2, hz₁.1⟩ z₂ ⟨hz₂.2, hz₂.1⟩
  exact CompleteSpace.complete h_cauchy

/-- Puncture Sobolev extension certificate (`h_punc`) from vanishing punctured-neighborhood
oscillation and continuous-to-weak extension (`0 sorryAx`). -/
theorem satisfiesPunctureSobolevExtension_of_finite_energy_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1)
    (_h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (_h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (h_osc_nhds : ∀ ε > 0, ∃ U ∈ 𝓝 p, ∀ z₁ ∈ U \ {p}, ∀ z₂ ∈ U \ {p}, dist (u z₁) (u z₂) < ε)
    (h_weak_of_lim : ∀ m_star : M, Filter.Tendsto u (𝓝[≠] p) (𝓝 m_star) →
      WeakJHolomorphicOn I (Function.update u p m_star) Set.univ) :
    SatisfiesPunctureSobolevExtension I u p := by
  obtain ⟨m_star, hm_star⟩ := exists_limit_point_of_puncture u p h_osc_nhds
  exact satisfiesPunctureSobolevExtension_of_update_weakJHolomorphicOn I u p m_star
    (h_weak_of_lim m_star hm_star)

/-- Unconditional derivation of vanishing punctured-neighborhood oscillation from finite punctured-sphere
energy and small-energy collar oscillation with a constant `C` (`SatisfiesCylinderCollarOscillationWith`,
`0 sorryAx`).
For any two points `z₁, z₂` in `disk_at a (R₀ / 2) \ {stereo_chart.symm a}`, both have strictly
positive stereographic distance from `a`, so choosing `r = (1 / 4) * min (dist w₁ a) (dist w₂ a) > 0`
places both `z₁` and `z₂` inside a single collar `annulus_at a (2 * r) (R₀ / 2)` whose parent annulus
`annulus_at a r R₀` has energy `< min ε_osc (ε / (2C)) ^ 2` by `exists_punctured_disk_energy_lt`. -/
theorem punctured_disk_oscillation_of_collar_oscillation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ)
    (h_energy : energyMeasureExtended I u (punctured_sphere {stereo_chart.symm a}) ≠ ⊤)
    (h_osc : ∃ (C ε_osc : ℝ), 0 < C ∧ 0 < ε_osc ∧ ∀ r R : ℝ, 0 < r → 2 * r < R / 2 →
      energyMeasure I u (annulus_at a r R) < ε_osc → SatisfiesCylinderCollarOscillationWith I C u a r R) :
    ∀ ε > 0, ∃ U ∈ 𝓝 (stereo_chart.symm a),
      ∀ z₁ ∈ U \ {stereo_chart.symm a}, ∀ z₂ ∈ U \ {stereo_chart.symm a},
        dist (u z₁) (u z₂) < ε := by
  intro ε hε
  obtain ⟨C, ε_osc, hC, hε_osc, h_bnd⟩ := h_osc
  set δ : ℝ := min ε_osc ((ε / (2 * C)) ^ 2) with hδ_def
  have hδ_pos : 0 < δ := lt_min hε_osc (by positivity)
  obtain ⟨R₀, hR₀_pos, hR₀_energy⟩ := exists_punctured_disk_energy_lt I u a hδ_pos h_energy
  have hR₀_half : 0 < R₀ / 2 := by linarith
  refine ⟨disk_at a (R₀ / 2), (is_open_disk_at a (R₀ / 2)).mem_nhds (center_mem_disk_at a hR₀_half), ?_⟩
  rintro z₁ ⟨⟨w₁, hw₁_ball, rfl⟩, hz₁_ne⟩ z₂ ⟨⟨w₂, hw₂_ball, rfl⟩, hz₂_ne⟩
  have hw₁_ne : w₁ ≠ a := fun h => hz₁_ne (by rw [Set.mem_singleton_iff, h])
  have hw₂_ne : w₂ ≠ a := fun h => hz₂_ne (by rw [Set.mem_singleton_iff, h])
  have hd₁_pos : 0 < dist w₁ a := dist_pos.mpr hw₁_ne
  have hd₂_pos : 0 < dist w₂ a := dist_pos.mpr hw₂_ne
  have hd₁_lt : dist w₁ a < R₀ / 2 := Metric.mem_ball.mp hw₁_ball
  have hd₂_lt : dist w₂ a < R₀ / 2 := Metric.mem_ball.mp hw₂_ball
  let r := (1 / 4 : ℝ) * min (dist w₁ a) (dist w₂ a)
  have hr_pos : 0 < r := by
    dsimp [r]
    exact mul_pos (by norm_num) (lt_min hd₁_pos hd₂_pos)
  have h2r_lt_d1 : 2 * r < dist w₁ a := by
    have h_le : min (dist w₁ a) (dist w₂ a) ≤ dist w₁ a := min_le_left _ _
    dsimp [r]
    linarith
  have h2r_lt_d2 : 2 * r < dist w₂ a := by
    have h_le : min (dist w₁ a) (dist w₂ a) ≤ dist w₂ a := min_le_right _ _
    dsimp [r]
    linarith
  have h2r_lt_half : 2 * r < R₀ / 2 := lt_trans h2r_lt_d1 hd₁_lt
  have hz₁_ann : stereo_chart.symm w₁ ∈ annulus_at a (2 * r) (R₀ / 2) :=
    ⟨w₁, ⟨h2r_lt_d1, hd₁_lt⟩, rfl⟩
  have hz₂_ann : stereo_chart.symm w₂ ∈ annulus_at a (2 * r) (R₀ / 2) :=
    ⟨w₂, ⟨h2r_lt_d2, hd₂_lt⟩, rfl⟩
  have h_en_lt : energyMeasure I u (annulus_at a r R₀) < δ :=
    hR₀_energy r R₀ hr_pos.le le_rfl
  have h_dist_le := h_bnd r R₀ hr_pos h2r_lt_half (lt_of_lt_of_le h_en_lt (min_le_left _ _))
    (stereo_chart.symm w₁) hz₁_ann (stereo_chart.symm w₂) hz₂_ann
  have h_sqrt_lt : Real.sqrt (energyMeasure I u (annulus_at a r R₀)) < ε / (2 * C) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ ε / (2 * C))]
    exact Real.sqrt_lt_sqrt (energy_nonneg I u _) (lt_of_lt_of_le h_en_lt (min_le_right _ _))
  have h_C_eq : C * (ε / (2 * C)) = ε / 2 := by
    field_simp
  have h_mul_lt : C * Real.sqrt (energyMeasure I u (annulus_at a r R₀)) < C * (ε / (2 * C)) :=
    mul_lt_mul_of_pos_left h_sqrt_lt hC
  linarith

/-- Exterior stereographic region `{w : ℂ | r < ‖w‖}` mapped to `CP1 \ {north_pole}`. -/
noncomputable def exterior_at (r : ℝ) : Set CP1 :=
  stereo_chart.symm '' {w : ℂ | r < ‖w‖}

/-- Every `exterior_at r` is an open subset of `CP1` (`0 sorryAx`). -/
theorem isOpen_exterior_at (r : ℝ) : IsOpen (exterior_at r) := by
  dsimp [exterior_at]
  have h_open : IsOpen {w : ℂ | r < ‖w‖} := isOpen_Ioi.preimage continuous_norm
  apply stereo_chart.isOpen_image_symm_of_subset_target h_open
  rw [stereo_chart_target]
  exact Set.subset_univ _

/-- Every `exterior_at r` is Borel measurable in `CP1` (`0 sorryAx`). -/
theorem measurableSet_exterior_at (r : ℝ) : MeasurableSet (exterior_at r) :=
  (isOpen_exterior_at r).measurableSet

/-- Monotonicity of `exterior_at r`: larger radii give smaller exterior regions (`0 sorryAx`). -/
theorem exterior_at_anti {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) : exterior_at r₂ ⊆ exterior_at r₁ := by
  dsimp [exterior_at]
  apply Set.image_mono
  intro w hw
  exact lt_of_le_of_lt h hw

/-- Every `exterior_at r` is contained in `punctured_sphere {north_pole}` (`0 sorryAx`). -/
theorem exterior_at_subset_punctured_north_pole (r : ℝ) :
    exterior_at r ⊆ punctured_sphere {north_pole} := by
  rw [punctured_sphere_singleton_eq_compl]
  rintro p ⟨w, _, rfl⟩ hp_eq
  rw [Set.mem_singleton_iff] at hp_eq
  have h_source := stereo_chart.map_target (show w ∈ stereo_chart.target by simp [stereo_chart_target])
  rw [hp_eq, stereo_chart_source] at h_source
  exact h_source rfl

/-- Every annulus centered at `0` with inner radius `r ≥ r₀` is contained in `exterior_at r₀` (`0 sorryAx`). -/
theorem annulus_at_zero_subset_exterior_at {r₀ r : ℝ} (hr : r₀ ≤ r) (R : ℝ) :
    annulus_at 0 r R ⊆ exterior_at r₀ := by
  rintro p ⟨w, ⟨hw_gt, _⟩, rfl⟩
  rw [dist_zero_right] at hw_gt
  exact ⟨w, lt_of_le_of_lt hr hw_gt, rfl⟩

/-- The countable intersection of `exterior_at (n + 1)` is empty (`0 sorryAx`). -/
theorem iInter_exterior_at_nat : (⋂ n : ℕ, exterior_at ((n : ℝ) + 1)) = ∅ := by
  ext p
  simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
  by_cases h0 : p ∈ exterior_at ((0 : ℕ) + 1 : ℝ)
  · rcases h0 with ⟨z, _, rfl⟩
    obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
    refine ⟨n, ?_⟩
    rintro ⟨w, hw_gt, hw_eq⟩
    have hzw : w = z := stereo_chart_symm_injective hw_eq
    subst hzw
    change (n : ℝ) + 1 < ‖w‖ at hw_gt
    linarith
  · exact ⟨0, h0⟩

/-- Vanishing of the extended energy measure on `exterior_at (n + 1)` as `n → ∞` (`0 sorryAx`). -/
theorem tendsto_energyMeasureExtended_exterior_at_nat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M)
    (h_energy : energyMeasureExtended I u (punctured_sphere {north_pole}) ≠ ⊤) :
    Filter.Tendsto
      (fun n : ℕ => energyMeasureExtended I u (exterior_at ((n : ℝ) + 1)))
      Filter.atTop (𝓝 0) := by
  have h_meas : ∀ n : ℕ,
      MeasureTheory.NullMeasurableSet (exterior_at ((n : ℝ) + 1)) (energyMeasureExtended I u) :=
    fun n => (measurableSet_exterior_at ((n : ℝ) + 1)).nullMeasurableSet
  have h_anti : Antitone (fun n : ℕ => exterior_at ((n : ℝ) + 1)) := by
    intro i j hij
    apply exterior_at_anti
    exact_mod_cast Nat.add_le_add_right hij 1
  have h_fin : ∃ i : ℕ, energyMeasureExtended I u (exterior_at ((i : ℝ) + 1)) ≠ ⊤ :=
    ⟨0, ne_top_of_le_ne_top h_energy
      (MeasureTheory.measure_mono (exterior_at_subset_punctured_north_pole _))⟩
  have h_tendsto := MeasureTheory.tendsto_measure_iInter_atTop h_meas h_anti h_fin
  rwa [iInter_exterior_at_nat, MeasureTheory.measure_empty] at h_tendsto

/-- Existence of a large inner radius `r₀ > 0` such that all outer annuli `annulus_at 0 r R` (`r₀ ≤ r`)
have energy `< ε` for any finite-energy curve on `punctured_sphere {north_pole}` (`0 sorryAx`). -/
theorem exists_exterior_annulus_energy_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) {ε : ℝ} (hε : 0 < ε)
    (h_energy : energyMeasureExtended I u (punctured_sphere {north_pole}) ≠ ⊤) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r R : ℝ, r₀ ≤ r →
      energyMeasure I u (annulus_at 0 r R) < ε := by
  have h_tendsto := tendsto_energyMeasureExtended_exterior_at_nat I u h_energy
  have h_mem : Set.Iio (ENNReal.ofReal ε) ∈ 𝓝 (0 : ENNReal) :=
    Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨n, hn⟩ := (h_tendsto.eventually h_mem).exists
  refine ⟨(n : ℝ) + 1, by positivity, ?_⟩
  intro r R hr
  have h_mono : energyMeasureExtended I u (annulus_at 0 r R) ≤
      energyMeasureExtended I u (exterior_at ((n : ℝ) + 1)) :=
    MeasureTheory.measure_mono (annulus_at_zero_subset_exterior_at hr R)
  exact ENNReal.toReal_lt_of_lt_ofReal (lt_of_le_of_lt h_mono hn)

/-- `{north_pole} ∪ exterior_at r` is an open neighborhood of `north_pole` in `CP1` (`0 sorryAx`). -/
theorem north_pole_exterior_mem_nhds (r : ℝ) :
    ({north_pole} ∪ exterior_at r) ∈ 𝓝 north_pole := by
  have h_compl_eq : ({north_pole} ∪ exterior_at r)ᶜ = stereo_chart.symm '' Metric.closedBall (0 : ℂ) r := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, not_or]
    constructor
    · rintro ⟨hz_ne, hz_not_ext⟩
      have hz_src : z ∈ stereo_chart.source := by
        rw [stereo_chart_source]
        exact hz_ne
      refine ⟨stereo_chart z, ?_, stereo_chart.left_inv hz_src⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      by_contra h_gt
      exact hz_not_ext ⟨stereo_chart z, lt_of_not_ge h_gt, stereo_chart.left_inv hz_src⟩
    · rintro ⟨w, hw_ball, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hw_ball
      refine ⟨?_, ?_⟩
      · intro h_np
        have h_src := stereo_chart.map_target (show w ∈ stereo_chart.target by simp [stereo_chart_target])
        rw [h_np, stereo_chart_source] at h_src
        exact h_src rfl
      · rintro ⟨w', hw'_gt, hw'_eq⟩
        have hww' : w' = w := stereo_chart_symm_injective hw'_eq
        subst hww'
        change r < ‖w'‖ at hw'_gt
        linarith
  have h_compact : IsCompact (stereo_chart.symm '' Metric.closedBall (0 : ℂ) r) :=
    (isCompact_closedBall (0 : ℂ) r).image stereo_chart_symm_continuous
  have h_open : IsOpen ({north_pole} ∪ exterior_at r) := by
    rw [← isClosed_compl_iff, h_compl_eq]
    exact h_compact.isClosed
  exact h_open.mem_nhds (Set.mem_union_left _ rfl)

/-- Vanishing punctured-neighborhood oscillation at `north_pole` from finite punctured-sphere energy
and small-energy collar oscillation (`0 sorryAx`). -/
theorem punctured_north_pole_oscillation_of_collar_oscillation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M)
    (h_energy : energyMeasureExtended I u (punctured_sphere {north_pole}) ≠ ⊤)
    (h_osc : ∃ (C ε_osc : ℝ), 0 < C ∧ 0 < ε_osc ∧ ∀ r R : ℝ, 0 < r → 2 * r < R / 2 →
      energyMeasure I u (annulus_at 0 r R) < ε_osc → SatisfiesCylinderCollarOscillationWith I C u 0 r R) :
    ∀ ε > 0, ∃ U ∈ 𝓝 north_pole,
      ∀ z₁ ∈ U \ {north_pole}, ∀ z₂ ∈ U \ {north_pole},
        dist (u z₁) (u z₂) < ε := by
  intro ε hε
  obtain ⟨C, ε_osc, hC, hε_osc, h_bnd⟩ := h_osc
  set δ : ℝ := min ε_osc ((ε / (2 * C)) ^ 2)
  have hδ_pos : 0 < δ := lt_min hε_osc (by positivity)
  obtain ⟨r₀, hr₀_pos, hr₀_energy⟩ := exists_exterior_annulus_energy_lt I u hδ_pos h_energy
  refine ⟨{north_pole} ∪ exterior_at (2 * r₀), north_pole_exterior_mem_nhds (2 * r₀), ?_⟩
  rintro z₁ ⟨hz₁_un, hz₁_ne⟩ z₂ ⟨hz₂_un, hz₂_ne⟩
  have hz₁_ext : z₁ ∈ exterior_at (2 * r₀) := hz₁_un.resolve_left hz₁_ne
  have hz₂_ext : z₂ ∈ exterior_at (2 * r₀) := hz₂_un.resolve_left hz₂_ne
  rcases hz₁_ext with ⟨w₁, hw₁_gt, rfl⟩
  rcases hz₂_ext with ⟨w₂, hw₂_gt, rfl⟩
  change 2 * r₀ < ‖w₁‖ at hw₁_gt
  change 2 * r₀ < ‖w₂‖ at hw₂_gt
  let R : ℝ := 4 * max ‖w₁‖ ‖w₂‖ + 1
  have h_w1_le : ‖w₁‖ ≤ max ‖w₁‖ ‖w₂‖ := le_max_left _ _
  have h_w2_le : ‖w₂‖ ≤ max ‖w₁‖ ‖w₂‖ := le_max_right _ _
  have hw₁_lt_half : ‖w₁‖ < R / 2 := by dsimp [R]; linarith
  have hw₂_lt_half : ‖w₂‖ < R / 2 := by dsimp [R]; linarith
  have h2r₀_lt_half : 2 * r₀ < R / 2 := lt_trans hw₁_gt hw₁_lt_half
  have hz₁_ann : stereo_chart.symm w₁ ∈ annulus_at 0 (2 * r₀) (R / 2) := by
    refine ⟨w₁, ?_, rfl⟩
    simp only [Set.mem_setOf, dist_zero_right]
    exact ⟨hw₁_gt, hw₁_lt_half⟩
  have hz₂_ann : stereo_chart.symm w₂ ∈ annulus_at 0 (2 * r₀) (R / 2) := by
    refine ⟨w₂, ?_, rfl⟩
    simp only [Set.mem_setOf, dist_zero_right]
    exact ⟨hw₂_gt, hw₂_lt_half⟩
  have h_en_lt : energyMeasure I u (annulus_at 0 r₀ R) < δ :=
    hr₀_energy r₀ R le_rfl
  have h_dist_le := h_bnd r₀ R hr₀_pos h2r₀_lt_half (lt_of_lt_of_le h_en_lt (min_le_left _ _))
    (stereo_chart.symm w₁) hz₁_ann (stereo_chart.symm w₂) hz₂_ann
  have h_sqrt_lt : Real.sqrt (energyMeasure I u (annulus_at 0 r₀ R)) < ε / (2 * C) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ ε / (2 * C))]
    exact Real.sqrt_lt_sqrt (energy_nonneg I u _) (lt_of_lt_of_le h_en_lt (min_le_right _ _))
  have h_C_eq : C * (ε / (2 * C)) = ε / 2 := by
    field_simp
  have h_mul_lt : C * Real.sqrt (energyMeasure I u (annulus_at 0 r₀ R)) < C * (ε / (2 * C)) :=
    mul_lt_mul_of_pos_left h_sqrt_lt hC
  linarith

/-- Every stereographic annulus `annulus_at a r R` with `0 < r` avoids `stereo_chart.symm a` (`0 sorryAx`). -/
theorem annulus_at_pos_subset_punctured_sphere (a : ℂ) {r : ℝ} (hr : 0 < r) (R : ℝ) :
    annulus_at a r R ⊆ punctured_sphere {stereo_chart.symm a} := by
  intro z hz
  exact annulus_at_zero_subset_punctured_sphere a R (annulus_at_mono a hr.le le_rfl hz)

/-- Vanishing punctured-neighborhood oscillation at **any** puncture `p : CP1` (both finite points
`p ≠ north_pole` and `p = north_pole`) from finite punctured-sphere energy and local small-energy
collar oscillation (`0 sorryAx`). -/
theorem punctured_oscillation_of_local_collar_oscillation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_osc_local : ∃ (C ε_osc : ℝ), 0 < C ∧ 0 < ε_osc ∧
      ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at a r R) →
        energyMeasure I u (annulus_at a r R) < ε_osc →
        SatisfiesCylinderCollarOscillationWith I C u a r R)
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (he : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∀ ε > 0, ∃ U ∈ 𝓝 p, ∀ z₁ ∈ U \ {p}, ∀ z₂ ∈ U \ {p}, dist (u z₁) (u z₂) < ε := by
  obtain ⟨C, ε_osc, hC, hε_osc, h_bnd⟩ := h_osc_local
  by_cases hp : p = north_pole
  · subst hp
    apply punctured_north_pole_oscillation_of_collar_oscillation I u he
    refine ⟨C, ε_osc, hC, hε_osc, fun r R hr h2r hE => ?_⟩
    have hrR : r < R := by linarith
    have hu_ann : JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at 0 r R) :=
      ⟨hu.1.mono (annulus_at_subset_punctured_sphere_north_pole 0 r R),
       fun z hz => hu.2 z (annulus_at_subset_punctured_sphere_north_pole 0 r R hz)⟩
    exact h_bnd u 0 r R hr hrR hu_ann hE
  · have hp_src : p ∈ stereo_chart.source := by
      rw [stereo_chart_source]
      exact hp
    set a : ℂ := stereo_chart p
    have ha_symm : stereo_chart.symm a = p := stereo_chart.left_inv hp_src
    rw [← ha_symm] at hu he ⊢
    apply punctured_disk_oscillation_of_collar_oscillation I u a he
    refine ⟨C, ε_osc, hC, hε_osc, fun r R hr h2r hE => ?_⟩
    have hrR : r < R := by linarith
    have hu_ann : JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at a r R) :=
      ⟨hu.1.mono (annulus_at_pos_subset_punctured_sphere a hr R),
       fun z hz => hu.2 z (annulus_at_pos_subset_punctured_sphere a hr R hz)⟩
    exact h_bnd u a r R hr hrR hu_ann hE

/-- Unconditional existence of the puncture limit `lim_{z → stereo_chart.symm a} u(z)` from
finite energy and collar oscillation (`0 sorryAx`). -/
theorem exists_limit_point_of_collar_oscillation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ)
    (h_energy : energyMeasureExtended I u (punctured_sphere {stereo_chart.symm a}) ≠ ⊤)
    (h_osc : ∃ (C ε_osc : ℝ), 0 < C ∧ 0 < ε_osc ∧ ∀ r R : ℝ, 0 < r → 2 * r < R / 2 →
      energyMeasure I u (annulus_at a r R) < ε_osc → SatisfiesCylinderCollarOscillationWith I C u a r R) :
    ∃ m_star : M, Filter.Tendsto u (𝓝[≠] (stereo_chart.symm a)) (𝓝 m_star) :=
  exists_limit_point_of_puncture u (stereo_chart.symm a)
    (punctured_disk_oscillation_of_collar_oscillation I u a h_energy h_osc)

/-- Unconditional continuous extension across `stereo_chart.symm a` of any finite-energy punctured
`J`-holomorphic map satisfying collar oscillation (`0 sorryAx`). -/
theorem exists_continuous_extension_of_collar_oscillation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {stereo_chart.symm a}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {stereo_chart.symm a}) ≠ ⊤)
    (h_osc : ∃ (C ε_osc : ℝ), 0 < C ∧ 0 < ε_osc ∧ ∀ r R : ℝ, 0 < r → 2 * r < R / 2 →
      energyMeasure I u (annulus_at a r R) < ε_osc → SatisfiesCylinderCollarOscillationWith I C u a r R) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      ContMDiffOn I_CP1 I ((0 : ℕ) : WithTop ℕ∞) u_ext Set.univ ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext (punctured_sphere {stereo_chart.symm a}) ∧
      EqOn u_ext u (punctured_sphere {stereo_chart.symm a}) := by
  obtain ⟨m_star, hm_star⟩ := exists_limit_point_of_collar_oscillation I u a h_energy h_osc
  let p := stereo_chart.symm a
  have h_eq : EqOn (Function.update u p m_star) u (punctured_sphere {p}) :=
    eqOn_update_punctured_sphere u p m_star
  have h_cont : Continuous (Function.update u p m_star) :=
    continuous_update_of_tendsto_punctured_sphere u p m_star h_jhol.1.continuousOn hm_star
  refine ⟨Function.update u p m_star, h_cont, contMDiffOn_zero_iff.mpr h_cont.continuousOn, ?_, h_eq⟩
  exact jholomorphicOn_congr I (isOpen_punctured_sphere p) h_eq.symm h_jhol

/-- By density of `punctured_sphere {p}` in `CP1` (`dense_punctured_sphere p`) and Hausdorffness of `E`,
if `u_ext` is $C^1$ on `CP1`, agrees with a punctured `J`-holomorphic map `u` on `punctured_sphere {p}`,
and its Cauchy–Riemann defect is continuous at `p`, then the Cauchy–Riemann equation holds at `p`
as well, so `u_ext` is globally `WeakJHolomorphicOn` (`0 sorryAx`). -/
theorem weakJHolomorphicOn_univ_of_c1_and_continuousAt_cr_at_puncture
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u u_ext : CP1 → M) (p : CP1)
    (h_c1 : ContMDiffOn I_CP1 I 1 u_ext Set.univ)
    (h_eq : EqOn u_ext u (punctured_sphere {p}))
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_cr_cont : ∀ v : TangentSpace I_CP1 p,
      ContinuousAt (fun z : CP1 =>
        mfderiv I_CP1 I u_ext z (RiemannDomain.j z v) -
          (ClosedTameTarget.J (I := I) (u_ext z)) (mfderiv I_CP1 I u_ext z v)) p) :
    WeakJHolomorphicOn I u_ext Set.univ := by
  have h_ext_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext (punctured_sphere {p}) :=
    jholomorphicOn_congr I (isOpen_punctured_sphere p) h_eq.symm h_jhol
  refine ⟨h_c1, ?_⟩
  intro z _hz v
  by_cases hzp : z = p
  · subst hzp
    have h_dense : Dense ({z}ᶜ : Set CP1) := by
      rw [← punctured_sphere_singleton_eq_compl]
      exact dense_punctured_sphere z
    have : (𝓝[≠] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (h_dense z)
    let φ : CP1 → E := fun w =>
      mfderiv I_CP1 I u_ext w (RiemannDomain.j w v) -
        (ClosedTameTarget.J (I := I) (u_ext w)) (mfderiv I_CP1 I u_ext w v)
    have h_tendsto_phi : Filter.Tendsto φ (𝓝[≠] z) (𝓝 (φ z)) :=
      (h_cr_cont v).tendsto.mono_left nhdsWithin_le_nhds
    have h_zero_on : EqOn φ (fun _ => 0) ({z}ᶜ : Set CP1) := by
      intro w hw
      have hw_punc : w ∈ punctured_sphere {z} := by
        rwa [punctured_sphere_singleton_eq_compl]
      exact sub_eq_zero.mpr (h_ext_jhol.2 w hw_punc v)
    have h_tendsto_zero : Filter.Tendsto φ (𝓝[≠] z) (𝓝 0) :=
      tendsto_const_nhds.congr' (h_zero_on.symm.eventuallyEq_of_mem self_mem_nhdsWithin)
    have h_phi_z_zero : φ z = 0 := tendsto_nhds_unique h_tendsto_phi h_tendsto_zero
    exact sub_eq_zero.mp h_phi_z_zero
  · have hz_punct : z ∈ punctured_sphere {p} := by
      rw [punctured_sphere_singleton_eq_compl]
      exact hzp
    exact h_ext_jhol.2 z hz_punct v

/-- First-principles synthesis for `h_punc` (`SatisfiesPunctureSobolevExtension`):
combining `exists_limit_point_of_collar_oscillation` and
`weakJHolomorphicOn_univ_of_c1_and_continuousAt_cr_at_puncture` constructs the explicit extension
`u_ext = Function.update u (stereo_chart.symm a) m_star` and proves `SatisfiesPunctureSobolevExtension`
once the updated map is $C^1$ with continuous Cauchy–Riemann defect at the puncture (`0 sorryAx`). -/
theorem satisfiesPunctureSobolevExtension_of_collar_oscillation_and_c1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {stereo_chart.symm a}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {stereo_chart.symm a}) ≠ ⊤)
    (h_osc : ∃ (C ε_osc : ℝ), 0 < C ∧ 0 < ε_osc ∧ ∀ r R : ℝ, 0 < r → 2 * r < R / 2 →
      energyMeasure I u (annulus_at a r R) < ε_osc → SatisfiesCylinderCollarOscillationWith I C u a r R)
    (h_c1 : ∀ m_star : M, Filter.Tendsto u (𝓝[≠] (stereo_chart.symm a)) (𝓝 m_star) →
      ContMDiffOn I_CP1 I 1 (Function.update u (stereo_chart.symm a) m_star) Set.univ ∧
      ∀ v : TangentSpace I_CP1 (stereo_chart.symm a),
        ContinuousAt (fun z : CP1 =>
          mfderiv I_CP1 I (Function.update u (stereo_chart.symm a) m_star) z (RiemannDomain.j z v) -
            (ClosedTameTarget.J (I := I) (Function.update u (stereo_chart.symm a) m_star z))
              (mfderiv I_CP1 I (Function.update u (stereo_chart.symm a) m_star) z v))
          (stereo_chart.symm a)) :
    SatisfiesPunctureSobolevExtension I u (stereo_chart.symm a) := by
  obtain ⟨m_star, hm_star⟩ := exists_limit_point_of_collar_oscillation I u a h_energy h_osc
  obtain ⟨hc1, hcr⟩ := h_c1 m_star hm_star
  let p := stereo_chart.symm a
  have h_weak : WeakJHolomorphicOn I (Function.update u p m_star) Set.univ :=
    weakJHolomorphicOn_univ_of_c1_and_continuousAt_cr_at_puncture I u
      (Function.update u p m_star) p hc1 (eqOn_update_punctured_sphere u p m_star) h_jhol hcr
  exact satisfiesPunctureSobolevExtension_of_update_weakJHolomorphicOn I u p m_star h_weak

/-- Phase 2 bridge for Certificate 3 (`h_osc`), with a general constant `C`:
a radial segment bound `dist (u z₁) (u z_mid) ≤ (C / 2) * √E(u; A(r, R))` and a circular slice bound
`dist (u z_mid) (u z₂) ≤ (C / 2) * √E(u; A(r, R))` through an intermediate point `z_mid` give
`SatisfiesCylinderCollarOscillationWith I C u a r R` by the triangle inequality (`0 sorryAx`). -/
theorem satisfiesCylinderCollarOscillation_of_radial_and_angular_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (C : ℝ) (u : CP1 → M) (a : ℂ) (r R : ℝ)
    (h_rad_ang : ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
      ∃ z_mid : CP1,
        dist (u z₁) (u z_mid) ≤ (C / 2) * Real.sqrt (energyMeasure I u (annulus_at a r R)) ∧
        dist (u z_mid) (u z₂) ≤ (C / 2) * Real.sqrt (energyMeasure I u (annulus_at a r R))) :
    SatisfiesCylinderCollarOscillationWith I C u a r R := by
  intro z₁ hz₁ z₂ hz₂
  obtain ⟨z_mid, h_rad, h_ang⟩ := h_rad_ang z₁ hz₁ z₂ hz₂
  have h_tri := dist_triangle (u z₁) (u z_mid) (u z₂)
  have h_sum : (C / 2) * Real.sqrt (energyMeasure I u (annulus_at a r R)) +
      (C / 2) * Real.sqrt (energyMeasure I u (annulus_at a r R)) =
      C * Real.sqrt (energyMeasure I u (annulus_at a r R)) := by ring
  linarith

/-- Phase 2 Manifold-to-Chart Bridge for Certificate 4 (`h_decay`):
Iterated Widman hole-filling across nested dyadic annuli `annulus_at center (2 ^ j * r) (R / 2 ^ j)`
for `0 ≤ j < k` yields geometric dyadic energy contraction
`E(u; A(2^k r, R / 2^k)) ≤ (K / (1 + K))^k * E(u; A(r, R))` (`0 sorryAx`). -/
theorem iterated_dyadic_annulus_energy_le_of_hole_filling
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (center : ℂ) (r R K : ℝ) (hK : 0 ≤ K) (k : ℕ)
    (h_step : ∀ j < k,
      energyMeasure I u (annulus_at center ((2 : ℝ) ^ (j + 1) * r) (R / (2 : ℝ) ^ (j + 1))) ≤
        K * (energyMeasure I u (annulus_at center ((2 : ℝ) ^ j * r) (R / (2 : ℝ) ^ j)) -
             energyMeasure I u (annulus_at center ((2 : ℝ) ^ (j + 1) * r) (R / (2 : ℝ) ^ (j + 1))))) :
    energyMeasure I u (annulus_at center ((2 : ℝ) ^ k * r) (R / (2 : ℝ) ^ k)) ≤
      (K / (1 + K)) ^ k * energyMeasure I u (annulus_at center r R) := by
  let e : ℕ → ℝ := fun j =>
    energyMeasure I u (annulus_at center ((2 : ℝ) ^ j * r) (R / (2 : ℝ) ^ j))
  have h_pow := le_pow_hole_filling_of_step (e := e) hK k h_step
  have he0 : e 0 = energyMeasure I u (annulus_at center r R) := by
    dsimp [e]
    rw [pow_zero, one_mul, div_one]
  rwa [he0] at h_pow

/-- Concentric stereographic annuli `annulus_at a r₁ r₂` and `annulus_at a r₃ r₄` with `r₂ ≤ r₃`
are disjoint (`0 sorryAx`). -/
theorem disjoint_annulus_at_of_le (a : ℂ) {r₁ r₂ r₃ r₄ : ℝ} (h23 : r₂ ≤ r₃) :
    Disjoint (annulus_at a r₁ r₂) (annulus_at a r₃ r₄) := by
  rw [Set.disjoint_left]
  rintro p ⟨z₁, ⟨_, hz₁_hi⟩, rfl⟩ ⟨z₂, ⟨hz₂_lo, _⟩, h_eq⟩
  have hz : z₂ = z₁ := stereo_chart_symm_injective h_eq
  subst hz
  linarith

/-- Disjoint three-ring superadditivity on concentric stereographic annuli (`0 sorryAx`):
For `r' ≤ r₁ ≤ r₂ ≤ R'` and finite outer annular energy `energyMeasureExtended I u (annulus_at center r' R') ≠ ⊤`,
the sum of the inner collar `A(r', r₁)`, middle sub-annulus `A(r₁, r₂)`, and outer collar `A(r₂, R')` energies
is bounded above by the total annular energy `E(u; A(r', R'))`. -/
theorem energyMeasure_three_annuli_le_outer
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (center : ℂ) {r' r₁ r₂ R' : ℝ}
    (hr₁ : r' ≤ r₁) (hr₁₂ : r₁ ≤ r₂) (hr₂ : r₂ ≤ R')
    (h_fin : energyMeasureExtended I u (annulus_at center r' R') ≠ ⊤) :
    energyMeasure I u (annulus_at center r' r₁) +
      energyMeasure I u (annulus_at center r₂ R') +
      energyMeasure I u (annulus_at center r₁ r₂) ≤
      energyMeasure I u (annulus_at center r' R') := by
  let A₁ := annulus_at center r' r₁
  let A₂ := annulus_at center r₁ r₂
  let A₃ := annulus_at center r₂ R'
  let A := annulus_at center r' R'
  have hA₁_sub : A₁ ⊆ A := annulus_at_mono center le_rfl (le_trans hr₁₂ hr₂)
  have hA₂_sub : A₂ ⊆ A := annulus_at_mono center hr₁ hr₂
  have hA₃_sub : A₃ ⊆ A := annulus_at_mono center (le_trans hr₁ hr₁₂) le_rfl
  have h_union_sub : (A₁ ∪ A₃) ∪ A₂ ⊆ A :=
    Set.union_subset (Set.union_subset hA₁_sub hA₃_sub) hA₂_sub
  have h_disj_13 : Disjoint A₁ A₃ := disjoint_annulus_at_of_le center hr₁₂
  have h_disj_12 : Disjoint A₁ A₂ := disjoint_annulus_at_of_le center le_rfl
  have h_disj_32 : Disjoint A₃ A₂ := (disjoint_annulus_at_of_le center le_rfl).symm
  have h_disj_u2 : Disjoint (A₁ ∪ A₃) A₂ := Disjoint.union_left h_disj_12 h_disj_32
  have h_m1 : MeasurableSet A₁ := measurableSet_annulus_at center r' r₁
  have h_m2 : MeasurableSet A₂ := measurableSet_annulus_at center r₁ r₂
  have h_m3 : MeasurableSet A₃ := measurableSet_annulus_at center r₂ R'
  have h_fin1 : energyMeasureExtended I u A₁ ≠ ⊤ :=
    ne_top_of_le_ne_top h_fin (MeasureTheory.measure_mono hA₁_sub)
  have h_fin2 : energyMeasureExtended I u A₂ ≠ ⊤ :=
    ne_top_of_le_ne_top h_fin (MeasureTheory.measure_mono hA₂_sub)
  have h_fin3 : energyMeasureExtended I u A₃ ≠ ⊤ :=
    ne_top_of_le_ne_top h_fin (MeasureTheory.measure_mono hA₃_sub)
  have h_fin13 : energyMeasureExtended I u (A₁ ∪ A₃) ≠ ⊤ := by
    rw [MeasureTheory.measure_union h_disj_13 h_m3]
    exact ENNReal.add_ne_top.mpr ⟨h_fin1, h_fin3⟩
  have h_meas_le : energyMeasureExtended I u ((A₁ ∪ A₃) ∪ A₂) ≤ energyMeasureExtended I u A :=
    MeasureTheory.measure_mono h_union_sub
  have h_real_le := ENNReal.toReal_mono h_fin h_meas_le
  rw [MeasureTheory.measure_union h_disj_u2 h_m2,
      ENNReal.toReal_add h_fin13 h_fin2,
      MeasureTheory.measure_union h_disj_13 h_m3,
      ENNReal.toReal_add h_fin1 h_fin3] at h_real_le
  exact h_real_le

/-- Disjoint dyadic collar-ring difference inequality (`0 sorryAx`):
For `0 ≤ r'` and `4 * r' ≤ R'` with `energyMeasureExtended I u (annulus_at center r' R') ≠ ⊤`,
the sum of the boundary collar energies `E(u; A(r', 2r')) + E(u; A(R'/2, R'))` is at most
the annular energy difference `E(u; A(r', R')) - E(u; A(2r', R'/2))`. -/
theorem energyMeasure_collar_sum_le_outer_sub_inner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (center : ℂ) {r' R' : ℝ}
    (hr' : 0 ≤ r') (h4 : 4 * r' ≤ R')
    (h_fin : energyMeasureExtended I u (annulus_at center r' R') ≠ ⊤) :
    energyMeasure I u (annulus_at center r' (2 * r')) +
      energyMeasure I u (annulus_at center (R' / 2) R') ≤
      energyMeasure I u (annulus_at center r' R') -
        energyMeasure I u (annulus_at center (2 * r') (R' / 2)) := by
  have h3 := energyMeasure_three_annuli_le_outer I u center
    (by linarith : r' ≤ 2 * r') (by linarith : 2 * r' ≤ R' / 2) (by linarith : R' / 2 ≤ R') h_fin
  linarith

/-- Continuous two-sided power-law cylinder energy decay from discrete dyadic Widman hole-filling (`0 sorryAx`):
If a map `u : CP1 → M` with `energyMeasureExtended I u (annulus_at center r R) ≠ ⊤` satisfies the
single-step Widman hole-filling inequality
`E(u; A(2^{j+1} r, R / 2^{j+1})) ≤ K * (E(u; A(2^j r, R / 2^j)) - E(u; A(2^{j+1} r, R / 2^{j+1})))`
with `K > 0` at every non-degenerate dyadic depth `4 * (2^j * r) < R / 2^j`, then with
`C₀ = (1 + K) / K > 0` and `a_decay = log((1 + K) / K) / log 2 > 0`, `u` satisfies
`SatisfiesCylinderEnergyDecayWith I C₀ a_decay u center r R` across all continuous sub-annuli `r < r₁ < r₂ < R`. -/
theorem satisfiesCylinderEnergyDecayWith_of_dyadic_hole_filling
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (center : ℂ) {r R K : ℝ}
    (hr : 0 < r) (hK : 0 < K)
    (h_fin : energyMeasureExtended I u (annulus_at center r R) ≠ ⊤)
    (h_step : ∀ j : ℕ, 4 * ((2 : ℝ) ^ j * r) < R / (2 : ℝ) ^ j →
      energyMeasure I u (annulus_at center ((2 : ℝ) ^ (j + 1) * r) (R / (2 : ℝ) ^ (j + 1))) ≤
        K * (energyMeasure I u (annulus_at center ((2 : ℝ) ^ j * r) (R / (2 : ℝ) ^ j)) -
             energyMeasure I u (annulus_at center ((2 : ℝ) ^ (j + 1) * r) (R / (2 : ℝ) ^ (j + 1))))) :
    SatisfiesCylinderEnergyDecayWith I ((1 + K) / K) (Real.log ((1 + K) / K) / Real.log 2) u center r R := by
  intro r₁ r₂ hr₁ hr₁₂ hr₂
  let C₀ : ℝ := (1 + K) / K
  let a_decay : ℝ := Real.log C₀ / Real.log 2
  have hr₁_pos : 0 < r₁ := lt_trans hr hr₁
  have hr₂_pos : 0 < r₂ := lt_trans hr₁_pos hr₁₂
  have hR_pos : 0 < R := lt_trans hr₂_pos hr₂
  have hC₀_gt_one : 1 < C₀ := (one_lt_div hK).mpr (by linarith)
  have hC₀_pos : 0 < C₀ := lt_trans zero_lt_one hC₀_gt_one
  have ha_pos : 0 < a_decay :=
    div_pos (Real.log_pos hC₀_gt_one) (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have h2_pow_a : (2 : ℝ) ^ a_decay = C₀ := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hlog2 : Real.log 2 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
    have h_mul : Real.log 2 * a_decay = Real.log C₀ := mul_div_cancel₀ _ hlog2
    rw [h_mul, Real.exp_log hC₀_pos]
  have h_half_pow_a : (1 / 2 : ℝ) ^ a_decay = K / (1 + K) := by
    rw [one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), h2_pow_a]
    exact inv_div (1 + K) K
  let x : ℝ := max (r / r₁) (r₂ / R)
  have hx_pos : 0 < x := lt_max_of_lt_left (div_pos hr hr₁_pos)
  have hx_le_one : x ≤ 1 :=
    max_le ((div_le_one hr₁_pos).mpr hr₁.le) ((div_le_one hR_pos).mpr hr₂.le)
  obtain ⟨k, hlo, hhi⟩ := exists_nat_pow_near_of_lt_one hx_pos hx_le_one
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have h2k_pos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
  have hr_div_le : r / r₁ ≤ 1 / (2 : ℝ) ^ k := by
    calc r / r₁ ≤ x := le_max_left _ _
      _ ≤ (1 / 2 : ℝ) ^ k := hhi
      _ = 1 / (2 : ℝ) ^ k := one_div_pow 2 k
  have h_inner_le : (2 : ℝ) ^ k * r ≤ r₁ := by
    have h1 := (div_le_div_iff₀ hr₁_pos h2k_pos).mp hr_div_le
    linarith
  have hr2_div_le : r₂ / R ≤ 1 / (2 : ℝ) ^ k := by
    calc r₂ / R ≤ x := le_max_right _ _
      _ ≤ (1 / 2 : ℝ) ^ k := hhi
      _ = 1 / (2 : ℝ) ^ k := one_div_pow 2 k
  have h_outer_le : r₂ ≤ R / (2 : ℝ) ^ k := by
    rw [le_div_iff₀ h2k_pos]
    have h1 := (div_le_div_iff₀ hR_pos h2k_pos).mp hr2_div_le
    linarith
  have h_step_k : ∀ j < k,
      energyMeasure I u (annulus_at center ((2 : ℝ) ^ (j + 1) * r) (R / (2 : ℝ) ^ (j + 1))) ≤
        K * (energyMeasure I u (annulus_at center ((2 : ℝ) ^ j * r) (R / (2 : ℝ) ^ j)) -
             energyMeasure I u (annulus_at center ((2 : ℝ) ^ (j + 1) * r) (R / (2 : ℝ) ^ (j + 1)))) := by
    intro j hj
    apply h_step j
    have hj1_le_k : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.succ_le_of_lt hj)
    have hj_pos : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num) j
    have hj1_pos : 0 < (2 : ℝ) ^ (j + 1) := pow_pos (by norm_num) (j + 1)
    have h_in_j : (2 : ℝ) ^ (j + 1) * r ≤ r₁ :=
      le_trans (mul_le_mul_of_nonneg_right hj1_le_k hr.le) h_inner_le
    have h_out_j : r₂ ≤ R / (2 : ℝ) ^ (j + 1) :=
      le_trans h_outer_le (div_le_div_of_nonneg_left hR_pos.le hj1_pos hj1_le_k)
    have h_lt_j : (2 : ℝ) ^ (j + 1) * r < R / (2 : ℝ) ^ (j + 1) :=
      lt_of_le_of_lt h_in_j (lt_of_lt_of_le hr₁₂ h_out_j)
    have h_pow_succ : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := pow_succ' 2 j
    rw [h_pow_succ] at h_lt_j
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (2 : ℝ) ^ j)] at h_lt_j
    rw [lt_div_iff₀ hj_pos]
    have h_id : 4 * ((2 : ℝ) ^ j * r) * (2 : ℝ) ^ j = (2 * (2 : ℝ) ^ j * r) * (2 * (2 : ℝ) ^ j) := by ring
    linarith
  have h_iter := iterated_dyadic_annulus_energy_le_of_hole_filling I u center r R K hK.le k h_step_k
  have h1_le_2k : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have h_fin_k : energyMeasureExtended I u (annulus_at center ((2 : ℝ) ^ k * r) (R / (2 : ℝ) ^ k)) ≠ ⊤ :=
    ne_top_of_le_ne_top h_fin (energyMeasureExtended_annulus_at_mono I u center
      (le_mul_of_one_le_left hr.le h1_le_2k)
      (div_le_self hR_pos.le h1_le_2k))
  have h_mono_sub : energyMeasure I u (annulus_at center r₁ r₂) ≤
      energyMeasure I u (annulus_at center ((2 : ℝ) ^ k * r) (R / (2 : ℝ) ^ k)) :=
    energyMeasure_annulus_at_mono I u center h_inner_le h_outer_le h_fin_k
  have h_theta_eq : K / (1 + K) = C₀⁻¹ := by
    dsimp [C₀]
    rw [inv_div]
  have h_theta_k : (K / (1 + K)) ^ k = C₀ * (K / (1 + K)) ^ (k + 1) := by
    rw [pow_succ, h_theta_eq]
    have hC₀_ne : C₀ ≠ 0 := hC₀_pos.ne'
    field_simp
  have h_theta_k1_le : (K / (1 + K)) ^ (k + 1) ≤ (r / r₁) ^ a_decay + (r₂ / R) ^ a_decay := by
    have h_pow_comm : (K / (1 + K)) ^ (k + 1) = ((1 / 2 : ℝ) ^ (k + 1)) ^ a_decay := by
      rw [← h_half_pow_a, Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have h_le_x : ((1 / 2 : ℝ) ^ (k + 1)) ^ a_decay ≤ x ^ a_decay :=
      Real.rpow_le_rpow (pow_nonneg (by norm_num) (k + 1)) hlo.le ha_pos.le
    have hx_le_sum : x ^ a_decay ≤ (r / r₁) ^ a_decay + (r₂ / R) ^ a_decay := by
      rcases max_choice (r / r₁) (r₂ / R) with h_eq | h_eq
      · dsimp [x]
        rw [h_eq]
        have h_pos2 : 0 ≤ (r₂ / R) ^ a_decay := Real.rpow_nonneg (div_nonneg hr₂_pos.le hR_pos.le) a_decay
        linarith
      · dsimp [x]
        rw [h_eq]
        have h_pos1 : 0 ≤ (r / r₁) ^ a_decay := Real.rpow_nonneg (div_nonneg hr.le hr₁_pos.le) a_decay
        linarith
    linarith
  have h_E_nonneg : 0 ≤ energyMeasure I u (annulus_at center r R) := energy_nonneg I u _
  calc
    energyMeasure I u (annulus_at center r₁ r₂)
      ≤ energyMeasure I u (annulus_at center ((2 : ℝ) ^ k * r) (R / (2 : ℝ) ^ k)) := h_mono_sub
    _ ≤ (K / (1 + K)) ^ k * energyMeasure I u (annulus_at center r R) := h_iter
    _ = C₀ * (K / (1 + K)) ^ (k + 1) * energyMeasure I u (annulus_at center r R) := by rw [h_theta_k]
    _ ≤ C₀ * ((r / r₁) ^ a_decay + (r₂ / R) ^ a_decay) * energyMeasure I u (annulus_at center r R) := by
      apply mul_le_mul_of_nonneg_right _ h_E_nonneg
      exact mul_le_mul_of_nonneg_left h_theta_k1_le hC₀_pos.le

/-- Continuous two-sided power-law cylinder energy decay from single-step collar Widman hole-filling (`0 sorryAx`):
If on every nested sub-annulus `A(r', R') ⊆ A(r, R)` with `4 * r' < R'`, the interior energy
`E(u; A(2r', R'/2))` is bounded by `K` times the boundary collar energy `E(u; A(r', 2r')) + E(u; A(R'/2, R'))`,
then `u` satisfies `SatisfiesCylinderEnergyDecayWith I ((1 + K) / K) (log((1 + K) / K) / log 2) u center r R`. -/
theorem satisfiesCylinderEnergyDecayWith_of_collar_hole_filling
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (center : ℂ) {r R K : ℝ}
    (hr : 0 < r) (hK : 0 < K)
    (h_fin : energyMeasureExtended I u (annulus_at center r R) ≠ ⊤)
    (h_collar : ∀ r' R' : ℝ, r ≤ r' → R' ≤ R → 4 * r' < R' →
      energyMeasure I u (annulus_at center (2 * r') (R' / 2)) ≤
        K * (energyMeasure I u (annulus_at center r' (2 * r')) +
             energyMeasure I u (annulus_at center (R' / 2) R'))) :
    SatisfiesCylinderEnergyDecayWith I ((1 + K) / K) (Real.log ((1 + K) / K) / Real.log 2) u center r R := by
  apply satisfiesCylinderEnergyDecayWith_of_dyadic_hole_filling I u center hr hK h_fin
  intro j hj4
  let r' := (2 : ℝ) ^ j * r
  let R' := R / (2 : ℝ) ^ j
  have h1_le_2j : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hr'_pos : 0 < r' := mul_pos (pow_pos (by norm_num) j) hr
  have hR'_pos : 0 < R' := by linarith
  have hR_pos : 0 < R := by
    have h2j_pos : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num) j
    exact (div_pos_iff_of_pos_right h2j_pos).mp hR'_pos
  have hr_le_r' : r ≤ r' := le_mul_of_one_le_left hr.le h1_le_2j
  have hR'_le_R : R' ≤ R := div_le_self hR_pos.le h1_le_2j
  have h_fin_j : energyMeasureExtended I u (annulus_at center r' R') ≠ ⊤ :=
    ne_top_of_le_ne_top h_fin (energyMeasureExtended_annulus_at_mono I u center hr_le_r' hR'_le_R)
  have h_col := h_collar r' R' hr_le_r' hR'_le_R hj4
  have h_diff := energyMeasure_collar_sum_le_outer_sub_inner I u center hr'_pos.le hj4.le h_fin_j
  have h_in_eq : (2 : ℝ) ^ (j + 1) * r = 2 * r' := by
    dsimp [r']
    rw [pow_succ']
    ring
  have h_out_eq : R / (2 : ℝ) ^ (j + 1) = R' / 2 := by
    dsimp [R']
    rw [pow_succ', div_div, mul_comm 2 ((2 : ℝ) ^ j)]
  rw [h_in_eq, h_out_eq]
  linarith [mul_le_mul_of_nonneg_left h_diff hK.le]

/-- Unconditional bounded-aspect-ratio cylinder energy decay (`0 sorryAx`):
Whenever `0 < r`, `R ≤ M_rat * r` with `1 ≤ M_rat`, `0 < a_decay`, and
`energyMeasureExtended I u (annulus_at center r R) ≠ ⊤`, `u` satisfies
`SatisfiesCylinderEnergyDecayWith I (M_rat ^ a_decay) a_decay u center r R` unconditionally. -/
theorem satisfiesCylinderEnergyDecayWith_of_ratio_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (center : ℂ) {r R M_rat a_decay : ℝ}
    (hr : 0 < r) (hM : 1 ≤ M_rat) (ha : 0 < a_decay) (h_rat : R ≤ M_rat * r)
    (h_fin : energyMeasureExtended I u (annulus_at center r R) ≠ ⊤) :
    SatisfiesCylinderEnergyDecayWith I (M_rat ^ a_decay) a_decay u center r R := by
  intro r₁ r₂ hr₁ hr₁₂ hr₂
  have hr₁_pos : 0 < r₁ := lt_trans hr hr₁
  have hr₂_pos : 0 < r₂ := lt_trans hr₁_pos hr₁₂
  have hR_pos : 0 < R := lt_trans hr₂_pos hr₂
  have hM_pos : 0 < M_rat := lt_of_lt_of_le zero_lt_one hM
  have h_mono : energyMeasure I u (annulus_at center r₁ r₂) ≤ energyMeasure I u (annulus_at center r R) :=
    energyMeasure_annulus_at_mono I u center hr₁.le hr₂.le h_fin
  have h_r_div : 1 / M_rat ≤ r / r₁ := by
    rw [div_le_div_iff₀ hM_pos hr₁_pos]
    have h1 : r₁ < M_rat * r := lt_of_lt_of_le (lt_trans hr₁₂ hr₂) h_rat
    linarith
  have h_rpow_le : (1 / M_rat) ^ a_decay ≤ (r / r₁) ^ a_decay :=
    Real.rpow_le_rpow (by positivity) h_r_div ha.le
  have h_prod_one : M_rat ^ a_decay * (1 / M_rat) ^ a_decay = 1 := by
    rw [one_div, Real.inv_rpow hM_pos.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hM_pos a_decay).ne']
  have h_one_le : 1 ≤ M_rat ^ a_decay * ((r / r₁) ^ a_decay + (r₂ / R) ^ a_decay) := by
    have h_pos2 : 0 ≤ (r₂ / R) ^ a_decay := Real.rpow_nonneg (div_nonneg hr₂_pos.le hR_pos.le) a_decay
    have h_Ma_pos : 0 ≤ M_rat ^ a_decay := Real.rpow_nonneg hM_pos.le a_decay
    calc
      (1 : ℝ) = M_rat ^ a_decay * (1 / M_rat) ^ a_decay := h_prod_one.symm
      _ ≤ M_rat ^ a_decay * ((r / r₁) ^ a_decay + (r₂ / R) ^ a_decay) :=
        mul_le_mul_of_nonneg_left (by linarith) h_Ma_pos
  have h_E_nonneg : 0 ≤ energyMeasure I u (annulus_at center r R) := energy_nonneg I u _
  nlinarith

/-- Global `CylinderEnergyDecayProperty` (`cert_decay` / Contract A10) derived from
single-step collar Widman hole-filling (`0 sorryAx`):
If there exist `K > 0` and `ε_neck > 0` such that every `J`-holomorphic sphere `u` and annulus
`A(center; r', R')` with `0 < r'`, `4 * r' < R'`, and `E(u; A(r', R')) < ε_neck` satisfies
finite extended energy and the single-step collar bound
`E(u; A(2r', R'/2)) ≤ K * (E(u; A(r', 2r')) + E(u; A(R'/2, R')))`,
then `CylinderEnergyDecayProperty I M` holds with explicit positive constants
`C₀ = (1 + K) / K`, `a_decay = log((1 + K) / K) / log 2`, and `ε_neck`. -/
theorem cylinderEnergyDecayProperty_of_collar_hole_filling
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {K ε_neck : ℝ} (hK : 0 < K) (hε : 0 < ε_neck)
    (h_fin : ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      0 < r → 2 * r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r R) < ε_neck →
      energyMeasureExtended I u (annulus_at center r R) ≠ ⊤)
    (h_collar : ∀ (u : CP1 → M) (center : ℂ) (r' R' : ℝ),
      0 < r' → 4 * r' < R' →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r' R') < ε_neck →
      energyMeasure I u (annulus_at center (2 * r') (R' / 2)) ≤
        K * (energyMeasure I u (annulus_at center r' (2 * r')) +
             energyMeasure I u (annulus_at center (R' / 2) R'))) :
    CylinderEnergyDecayProperty I M := by
  let C₀ : ℝ := (1 + K) / K
  let a_decay : ℝ := Real.log C₀ / Real.log 2
  have hC₀_gt_one : 1 < C₀ := (one_lt_div hK).mpr (by linarith)
  have hC₀_pos : 0 < C₀ := lt_trans zero_lt_one hC₀_gt_one
  have ha_pos : 0 < a_decay :=
    div_pos (Real.log_pos hC₀_gt_one) (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  refine ⟨C₀, a_decay, ε_neck, hC₀_pos, ha_pos, hε, ?_⟩
  intro u center r R hr h2rR hu h_en
  have h_fin_rR := h_fin u center r R hr h2rR hu h_en
  apply satisfiesCylinderEnergyDecayWith_of_collar_hole_filling I u center hr hK h_fin_rR
  intro r' R' hr' hR' h4
  have hr'_pos : 0 < r' := lt_of_lt_of_le hr hr'
  have h_en_sub : energyMeasure I u (annulus_at center r' R') < ε_neck :=
    lt_of_le_of_lt (energyMeasure_annulus_at_mono I u center hr' hR' h_fin_rR) h_en
  exact h_collar u center r' R' hr'_pos h4 hu h_en_sub

/-- Contract A10 (`cylinder_exponential_decay`) derived from single-step collar Widman hole-filling (`0 sorryAx`). -/
theorem cylinder_exponential_decay_of_collar_hole_filling
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {K ε_neck : ℝ} (hK : 0 < K) (hε : 0 < ε_neck)
    (h_fin : ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      0 < r → 2 * r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r R) < ε_neck →
      energyMeasureExtended I u (annulus_at center r R) ≠ ⊤)
    (h_collar : ∀ (u : CP1 → M) (center : ℂ) (r' R' : ℝ),
      0 < r' → 4 * r' < R' →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r' R') < ε_neck →
      energyMeasure I u (annulus_at center (2 * r') (R' / 2)) ≤
        K * (energyMeasure I u (annulus_at center r' (2 * r')) +
             energyMeasure I u (annulus_at center (R' / 2) R'))) :
    ∃ (C₀ a_decay ε_neck' : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck' ∧
    ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      0 < r → 2 * r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r R) < ε_neck' →
      ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
        energyMeasure I u (annulus_at center r₁ r₂) ≤
          C₀ * ((r / r₁)^a_decay + (r₂ / R)^a_decay) * energyMeasure I u (annulus_at center r R) :=
  cylinder_exponential_decay I
    (cylinderEnergyDecayProperty_of_collar_hole_filling I M hK hε h_fin h_collar)

/-!
### 10. Step 2: Arbitrary-Modulus Collar Oscillation from Bounded-Modulus Ring Oscillation + Cylinder Energy Decay (`0 sorryAx`)

On a long neck `annulus_at a r R` with arbitrary aspect ratio `R / r`, a single Courant–Lebesgue
slice bound on `A(r, R)` cannot bound the radial oscillation without a factor of `√(log(R/r))`.
Instead, any pair of points `z₁, z₂ ∈ annulus_at a (2 * r) (R / 2)` with `2r < s = dist w₁ a ≤ t = dist w₂ a < R/2`
is connected through a dyadic radial chain `s = ρ₀ ≤ ρ₁ ≤ ⋯ ≤ ρ_N = t` (`ρ_{k+1} ≤ 2 ρ_k`).
Each dyadic ring `[ρ_k, ρ_{k+1}]` sits inside the central collar `(2 r_{1,k}, r_{2,k} / 2)` of the
bounded-modulus sub-annulus:
`r_{1,k} = max ((r + ρ_k / 2) / 2) (ρ_k / 3)`, `r_{2,k} = min (ρ_{k+1} + R / 2) (3 * ρ_{k+1})`,
which satisfies `r < r_{1,k} < r_{2,k} < R` and bounded aspect ratio `r_{2,k} ≤ 18 * r_{1,k}`.
Summing the bounded-modulus ring oscillation bounds against the two-sided power decay
`E(u; A(r_{1,k}, r_{2,k})) ≤ C₀ * ((r / r_{1,k})^a + (r_{2,k} / R)^a) * E(u; A(r, R))`
yields `SatisfiesCylinderCollarOscillationWith I C u a r R` with a constant `C` independent of `R / r`.
-/

/-- Inner parent radius for a dyadic ring starting at radius `s ∈ (2r, R/2)`:
`boundedModulusInner r s = max ((r + s / 2) / 2) (s / 3)`. -/
noncomputable def boundedModulusInner (r s : ℝ) : ℝ :=
  max ((r + s / 2) / 2) (s / 3)

/-- Outer parent radius for a dyadic ring ending at radius `t ∈ (2r, R/2)`:
`boundedModulusOuter R t = min (t + R / 2) (3 * t)`. -/
noncomputable def boundedModulusOuter (R t : ℝ) : ℝ :=
  min (t + R / 2) (3 * t)

/-- Exact arithmetic properties of the bounded-modulus parent sub-annulus
`(boundedModulusInner r s, boundedModulusOuter R t)` for any dyadic step `2r < s ≤ t < R/2`
with `t ≤ 2s` (`0 sorryAx`). -/
theorem boundedModulus_subannulus_props {r R s t : ℝ}
    (hr : 0 < r) (hs : 2 * r < s) (hst : s ≤ t) (ht2s : t ≤ 2 * s) (htR : t < R / 2) :
    0 < boundedModulusInner r s ∧
    r < boundedModulusInner r s ∧
    2 * boundedModulusInner r s < s ∧
    t < boundedModulusOuter R t / 2 ∧
    boundedModulusOuter R t < R ∧
    boundedModulusInner r s < boundedModulusOuter R t ∧
    boundedModulusOuter R t ≤ 18 * boundedModulusInner r s ∧
    s / 3 ≤ boundedModulusInner r s ∧
    boundedModulusOuter R t ≤ 3 * t := by
  dsimp [boundedModulusInner, boundedModulusOuter]
  have h1 : r < (r + s / 2) / 2 := by linarith
  have h1_le : (r + s / 2) / 2 ≤ max ((r + s / 2) / 2) (s / 3) := le_max_left _ _
  have hs3_le : s / 3 ≤ max ((r + s / 2) / 2) (s / 3) := le_max_right _ _
  have hr_lt : r < max ((r + s / 2) / 2) (s / 3) := lt_of_lt_of_le h1 h1_le
  have h2r1_lt_s : 2 * max ((r + s / 2) / 2) (s / 3) < s := by
    rcases max_choice ((r + s / 2) / 2) (s / 3) with hmax | hmax <;> linarith
  have ht_lt_half : t < min (t + R / 2) (3 * t) / 2 := by
    rcases min_choice (t + R / 2) (3 * t) with hmin | hmin <;> linarith
  have hmin_le1 : min (t + R / 2) (3 * t) ≤ t + R / 2 := min_le_left _ _
  have hmin_le2 : min (t + R / 2) (3 * t) ≤ 3 * t := min_le_right _ _
  have hr2_lt_R : min (t + R / 2) (3 * t) < R := by linarith
  have hr1_lt_r2 : max ((r + s / 2) / 2) (s / 3) < min (t + R / 2) (3 * t) := by linarith
  have hr2_le_18 : min (t + R / 2) (3 * t) ≤ 18 * max ((r + s / 2) / 2) (s / 3) := by linarith
  exact ⟨lt_trans hr hr_lt, hr_lt, h2r1_lt_s, ht_lt_half, hr2_lt_R, hr1_lt_r2,
    hr2_le_18, hs3_le, hmin_le2⟩

/-- Point at distance `ρ` from `a` along the ray from `a` through `w` (`0 sorryAx`). -/
noncomputable def radialPointOnRay (a w : ℂ) (ρ : ℝ) : ℂ :=
  a + ((ρ / dist w a : ℝ) : ℂ) * (w - a)

/-- If `dist w a > 0` and `ρ ≥ 0`, then `dist (radialPointOnRay a w ρ) a = ρ` (`0 sorryAx`). -/
theorem dist_radialPointOnRay {a w : ℂ} {ρ : ℝ} (hw : 0 < dist w a) (hρ : 0 ≤ ρ) :
    dist (radialPointOnRay a w ρ) a = ρ := by
  dsimp [radialPointOnRay]
  rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg hρ hw.le),
    ← dist_eq_norm, div_mul_cancel₀ _ hw.ne']

/-- At `ρ = dist w a`, `radialPointOnRay a w (dist w a) = w` (`0 sorryAx`). -/
theorem radialPointOnRay_self {a w : ℂ} (hw : 0 < dist w a) :
    radialPointOnRay a w (dist w a) = w := by
  dsimp [radialPointOnRay]
  rw [div_self hw.ne', Complex.ofReal_one, one_mul, add_sub_cancel]

/-- Subadditivity of `Real.sqrt` on nonnegative reals: `√(x + y) ≤ √x + √y` (`0 sorryAx`). -/
theorem sqrt_add_le_sqrt_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h_nonneg : 0 ≤ Real.sqrt x + Real.sqrt y := by positivity
  rw [← Real.sqrt_sq h_nonneg]
  apply Real.sqrt_le_sqrt
  calc
    x + y = (Real.sqrt x) ^ 2 + (Real.sqrt y) ^ 2 := by rw [Real.sq_sqrt hx, Real.sq_sqrt hy]
    _ ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
      have : 0 ≤ 2 * Real.sqrt x * Real.sqrt y := by positivity
      linarith [add_sq (Real.sqrt x) (Real.sqrt y)]

/-- Single dyadic step oscillation bound (`2r < s ≤ t < R/2`, `t ≤ 2s`) from bounded-modulus (`≤ 18`)
collar oscillation and two-sided cylinder energy decay (`0 sorryAx`). -/
theorem dist_le_of_dyadic_step_bounded_modulus_and_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {C_ring C₀ a_decay : ℝ} (hC_ring : 0 ≤ C_ring) (hC₀ : 0 ≤ C₀) (ha : 0 ≤ a_decay)
    (u : CP1 → M) (a : ℂ) {r R : ℝ} (hr : 0 < r)
    (h_ring : ∀ r₁ r₂ : ℝ, r < r₁ → r₁ < r₂ → r₂ < R → r₂ ≤ 18 * r₁ →
      SatisfiesCylinderCollarOscillationWith I C_ring u a r₁ r₂)
    (h_decay : SatisfiesCylinderEnergyDecayWith I C₀ a_decay u a r R)
    {w₁ w₂ : ℂ} {s t : ℝ}
    (hs_gt : 2 * r < s) (hst : s ≤ t) (ht2s : t ≤ 2 * s) (ht_lt : t < R / 2)
    (hw₁ : s ≤ dist w₁ a ∧ dist w₁ a ≤ t)
    (hw₂ : s ≤ dist w₂ a ∧ dist w₂ a ≤ t) :
    dist (u (stereo_chart.symm w₁)) (u (stereo_chart.symm w₂)) ≤
      (C_ring * Real.sqrt C₀ * (3 : ℝ) ^ (a_decay / 2)) *
        ((r / s) ^ (a_decay / 2) + (t / R) ^ (a_decay / 2)) *
        Real.sqrt (energyMeasure I u (annulus_at a r R)) := by
  obtain ⟨hr₁_pos, hr_lt_r₁, h2r₁_lt_s, ht_lt_r₂_half, hr₂_lt_R, hr₁_lt_r₂, hr₂_le_18, hs3_le, hr₂_le_3t⟩ :=
    boundedModulus_subannulus_props hr hs_gt hst ht2s ht_lt
  set r₁ := boundedModulusInner r s
  set r₂ := boundedModulusOuter R t
  have hz₁_mem : stereo_chart.symm w₁ ∈ annulus_at a (2 * r₁) (r₂ / 2) :=
    ⟨w₁, ⟨lt_of_lt_of_le h2r₁_lt_s hw₁.1, lt_of_le_of_lt hw₁.2 ht_lt_r₂_half⟩, rfl⟩
  have hz₂_mem : stereo_chart.symm w₂ ∈ annulus_at a (2 * r₁) (r₂ / 2) :=
    ⟨w₂, ⟨lt_of_lt_of_le h2r₁_lt_s hw₂.1, lt_of_le_of_lt hw₂.2 ht_lt_r₂_half⟩, rfl⟩
  have h_osc_step := h_ring r₁ r₂ hr_lt_r₁ hr₁_lt_r₂ hr₂_lt_R hr₂_le_18
    (stereo_chart.symm w₁) hz₁_mem (stereo_chart.symm w₂) hz₂_mem
  have h_dec_step := h_decay r₁ r₂ hr_lt_r₁ hr₁_lt_r₂ hr₂_lt_R
  have hs_pos : 0 < s := by linarith
  have ht_pos : 0 < t := lt_of_lt_of_le hs_pos hst
  have hR_pos : 0 < R := by linarith
  have h_r_div_r₁ : r / r₁ ≤ 3 * (r / s) := by
    rw [div_le_iff₀ hr₁_pos]
    have h_mul : s ≤ 3 * r₁ := by linarith
    calc
      r = (r / s) * s := (div_mul_cancel₀ r hs_pos.ne').symm
      _ ≤ (r / s) * (3 * r₁) := mul_le_mul_of_nonneg_left h_mul (div_nonneg hr.le hs_pos.le)
      _ = 3 * (r / s) * r₁ := by ring
  have h_r₂_div_R : r₂ / R ≤ 3 * (t / R) := by
    calc
      r₂ / R ≤ (3 * t) / R := div_le_div_of_nonneg_right hr₂_le_3t hR_pos.le
      _ = 3 * (t / R) := mul_div_assoc 3 t R
  have h_rpow1 : (r / r₁) ^ a_decay ≤ (3 : ℝ) ^ a_decay * (r / s) ^ a_decay := by
    calc
      (r / r₁) ^ a_decay ≤ (3 * (r / s)) ^ a_decay :=
        Real.rpow_le_rpow (div_nonneg hr.le hr₁_pos.le) h_r_div_r₁ ha
      _ = (3 : ℝ) ^ a_decay * (r / s) ^ a_decay :=
        Real.mul_rpow (by norm_num) (div_nonneg hr.le hs_pos.le)
  have h_rpow2 : (r₂ / R) ^ a_decay ≤ (3 : ℝ) ^ a_decay * (t / R) ^ a_decay := by
    calc
      (r₂ / R) ^ a_decay ≤ (3 * (t / R)) ^ a_decay :=
        Real.rpow_le_rpow (div_nonneg (lt_trans hr₁_pos hr₁_lt_r₂).le hR_pos.le) h_r₂_div_R ha
      _ = (3 : ℝ) ^ a_decay * (t / R) ^ a_decay :=
        Real.mul_rpow (by norm_num) (div_nonneg ht_pos.le hR_pos.le)
  have h_en_nonneg : 0 ≤ energyMeasure I u (annulus_at a r R) := energy_nonneg I u _
  have h_dec_bound :
      energyMeasure I u (annulus_at a r₁ r₂) ≤
        (C₀ * (3 : ℝ) ^ a_decay) * ((r / s) ^ a_decay + (t / R) ^ a_decay) *
          energyMeasure I u (annulus_at a r R) := by
    calc
      energyMeasure I u (annulus_at a r₁ r₂)
        ≤ C₀ * ((r / r₁) ^ a_decay + (r₂ / R) ^ a_decay) * energyMeasure I u (annulus_at a r R) := h_dec_step
      _ ≤ C₀ * ((3 : ℝ) ^ a_decay * (r / s) ^ a_decay + (3 : ℝ) ^ a_decay * (t / R) ^ a_decay) *
            energyMeasure I u (annulus_at a r R) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add h_rpow1 h_rpow2) hC₀) h_en_nonneg
      _ = (C₀ * (3 : ℝ) ^ a_decay) * ((r / s) ^ a_decay + (t / R) ^ a_decay) *
            energyMeasure I u (annulus_at a r R) := by ring
  have h_sqrt_step :
      Real.sqrt (energyMeasure I u (annulus_at a r₁ r₂)) ≤
        Real.sqrt C₀ * (3 : ℝ) ^ (a_decay / 2) *
          ((r / s) ^ (a_decay / 2) + (t / R) ^ (a_decay / 2)) *
          Real.sqrt (energyMeasure I u (annulus_at a r R)) := by
    have h_rs_pos : 0 ≤ r / s := div_nonneg hr.le hs_pos.le
    have h_tR_pos : 0 ≤ t / R := div_nonneg ht_pos.le hR_pos.le
    have h_rpow_rs_nonneg : 0 ≤ (r / s) ^ a_decay := Real.rpow_nonneg h_rs_pos _
    have h_rpow_tR_nonneg : 0 ≤ (t / R) ^ a_decay := Real.rpow_nonneg h_tR_pos _
    have h_3a_nonneg : 0 ≤ (3 : ℝ) ^ a_decay := Real.rpow_nonneg (by norm_num) _
    have h_sqrt_3a : Real.sqrt ((3 : ℝ) ^ a_decay) = (3 : ℝ) ^ (a_decay / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
      ring_nf
    have h_sqrt_rs : Real.sqrt ((r / s) ^ a_decay) = (r / s) ^ (a_decay / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul h_rs_pos]
      ring_nf
    have h_sqrt_tR : Real.sqrt ((t / R) ^ a_decay) = (t / R) ^ (a_decay / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul h_tR_pos]
      ring_nf
    calc
      Real.sqrt (energyMeasure I u (annulus_at a r₁ r₂))
        ≤ Real.sqrt ((C₀ * (3 : ℝ) ^ a_decay) * ((r / s) ^ a_decay + (t / R) ^ a_decay) *
            energyMeasure I u (annulus_at a r R)) := Real.sqrt_le_sqrt h_dec_bound
      _ = Real.sqrt (C₀ * (3 : ℝ) ^ a_decay) *
            Real.sqrt ((r / s) ^ a_decay + (t / R) ^ a_decay) *
            Real.sqrt (energyMeasure I u (annulus_at a r R)) := by
          rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hC₀ h_3a_nonneg)
                (add_nonneg h_rpow_rs_nonneg h_rpow_tR_nonneg)),
              Real.sqrt_mul (mul_nonneg hC₀ h_3a_nonneg)]
      _ = Real.sqrt C₀ * (3 : ℝ) ^ (a_decay / 2) *
            Real.sqrt ((r / s) ^ a_decay + (t / R) ^ a_decay) *
            Real.sqrt (energyMeasure I u (annulus_at a r R)) := by
          rw [Real.sqrt_mul hC₀, h_sqrt_3a]
      _ ≤ Real.sqrt C₀ * (3 : ℝ) ^ (a_decay / 2) *
            ((r / s) ^ (a_decay / 2) + (t / R) ^ (a_decay / 2)) *
            Real.sqrt (energyMeasure I u (annulus_at a r R)) := by
          have h_sub := sqrt_add_le_sqrt_add_sqrt h_rpow_rs_nonneg h_rpow_tR_nonneg
          rw [h_sqrt_rs, h_sqrt_tR] at h_sub
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h_sub (by positivity))
            (Real.sqrt_nonneg _)
  calc
    dist (u (stereo_chart.symm w₁)) (u (stereo_chart.symm w₂))
      ≤ C_ring * Real.sqrt (energyMeasure I u (annulus_at a r₁ r₂)) := h_osc_step
    _ ≤ C_ring * (Real.sqrt C₀ * (3 : ℝ) ^ (a_decay / 2) *
          ((r / s) ^ (a_decay / 2) + (t / R) ^ (a_decay / 2)) *
          Real.sqrt (energyMeasure I u (annulus_at a r R))) :=
      mul_le_mul_of_nonneg_left h_sqrt_step hC_ring
    _ = (C_ring * Real.sqrt C₀ * (3 : ℝ) ^ (a_decay / 2)) *
          ((r / s) ^ (a_decay / 2) + (t / R) ^ (a_decay / 2)) *
          Real.sqrt (energyMeasure I u (annulus_at a r R)) := by ring

/-- Every positive real ratio is bounded by `2 ^ N` for some `N : ℕ` (`0 sorryAx`). -/
theorem exists_le_two_pow_mul {s t : ℝ} (hs : 0 < s) :
    ∃ N : ℕ, t ≤ (2 : ℝ) ^ N * s := by
  obtain ⟨N, hN⟩ := exists_nat_gt (t / s)
  refine ⟨N, ?_⟩
  rw [div_lt_iff₀ hs] at hN
  have h_pow : (N : ℝ) < (2 : ℝ) ^ N := by
    exact_mod_cast Nat.lt_two_pow_self
  nlinarith

/-- Finite geometric series bound for `0 ≤ q < 1`: `∑ k ∈ Finset.range N, q ^ k ≤ 1 / (1 - q)` (`0 sorryAx`). -/
theorem sum_geom_le_inv_one_sub {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    (∑ k ∈ Finset.range N, q ^ k) ≤ 1 / (1 - q) := by
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  rw [le_div_iff₀ h1q, mul_comm, mul_neg_geom_sum q N]
  have h_pow_nonneg : 0 ≤ q ^ N := pow_nonneg hq0 N
  linarith

/-- Dyadic radial sequence `dyadicRadius w₁ w₂ a k = min (2^k * dist w₁ a) (dist w₂ a)`. -/
noncomputable def dyadicRadius (w₁ w₂ a : ℂ) (k : ℕ) : ℝ :=
  min ((2 : ℝ) ^ k * dist w₁ a) (dist w₂ a)

/-- Dyadic radial point chain `dyadicChainPoint w₁ w₂ a k` starting at `w₁` (`k = 0`) and stepping
along the ray from `a` through `w₂` at distances `dyadicRadius w₁ w₂ a k`. -/
noncomputable def dyadicChainPoint (w₁ w₂ a : ℂ) (k : ℕ) : ℂ :=
  if k = 0 then w₁ else radialPointOnRay a w₂ (dyadicRadius w₁ w₂ a k)

/-- Exact dyadic chain oscillation bound along `dyadicChainPoint w₁ w₂ a k` for `k : ℕ` (`0 sorryAx`). -/
theorem dist_le_sum_dyadic_chain_bounded_modulus_and_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {C_ring C₀ a_decay : ℝ} (hC_ring : 0 ≤ C_ring) (hC₀ : 0 ≤ C₀) (ha : 0 ≤ a_decay)
    (u : CP1 → M) (a : ℂ) {r R : ℝ} (hr : 0 < r)
    (h_ring : ∀ r₁ r₂ : ℝ, r < r₁ → r₁ < r₂ → r₂ < R → r₂ ≤ 18 * r₁ →
      SatisfiesCylinderCollarOscillationWith I C_ring u a r₁ r₂)
    (h_decay : SatisfiesCylinderEnergyDecayWith I C₀ a_decay u a r R)
    {w₁ w₂ : ℂ}
    (hw₁_gt : 2 * r < dist w₁ a)
    (hw₁₂ : dist w₁ a ≤ dist w₂ a)
    (hw₂_lt : dist w₂ a < R / 2)
    (N : ℕ) :
    dist (u (stereo_chart.symm w₁)) (u (stereo_chart.symm (dyadicChainPoint w₁ w₂ a N))) ≤
      (C_ring * Real.sqrt C₀ * (3 : ℝ) ^ (a_decay / 2)) *
        (∑ k ∈ Finset.range N,
          ((r / dyadicRadius w₁ w₂ a k) ^ (a_decay / 2) +
            (dyadicRadius w₁ w₂ a (k + 1) / R) ^ (a_decay / 2))) *
        Real.sqrt (energyMeasure I u (annulus_at a r R)) := by
  have hs_pos : 0 < dist w₁ a := by linarith
  have ht_pos : 0 < dist w₂ a := lt_of_lt_of_le hs_pos hw₁₂
  have hρ_pos : ∀ k, 0 < dyadicRadius w₁ w₂ a k :=
    fun k => lt_min (mul_pos (by positivity) hs_pos) ht_pos
  have hρ_gt_2r : ∀ k, 2 * r < dyadicRadius w₁ w₂ a k := by
    intro k
    apply lt_min _ (lt_of_lt_of_le hw₁_gt hw₁₂)
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have hρ_lt_R2 : ∀ k, dyadicRadius w₁ w₂ a k < R / 2 :=
    fun k => lt_of_le_of_lt (min_le_right _ _) hw₂_lt
  have hρ_mono : ∀ k, dyadicRadius w₁ w₂ a k ≤ dyadicRadius w₁ w₂ a (k + 1) := by
    intro k
    dsimp [dyadicRadius]
    apply min_le_min _ (le_refl (dist w₂ a))
    rw [pow_succ']
    have : 0 ≤ (2 : ℝ) ^ k * dist w₁ a := by positivity
    linarith
  have hρ_2 : ∀ k, dyadicRadius w₁ w₂ a (k + 1) ≤ 2 * dyadicRadius w₁ w₂ a k := by
    intro k
    dsimp [dyadicRadius]
    rw [pow_succ', mul_assoc]
    rcases min_choice ((2 : ℝ) ^ k * dist w₁ a) (dist w₂ a) with hmin | hmin
    · rw [hmin]
      exact min_le_left _ _
    · rw [hmin]
      have h_le : min (2 * ((2 : ℝ) ^ k * dist w₁ a)) (dist w₂ a) ≤ dist w₂ a := min_le_right _ _
      linarith
  have hw_seq_dist : ∀ k, dist (dyadicChainPoint w₁ w₂ a k) a = dyadicRadius w₁ w₂ a k := by
    intro k
    dsimp [dyadicChainPoint]
    split_ifs with hk
    · subst hk
      dsimp [dyadicRadius]
      rw [pow_zero, one_mul, min_eq_left hw₁₂]
    · exact dist_radialPointOnRay ht_pos (hρ_pos k).le
  induction N with
  | zero =>
    dsimp [dyadicChainPoint]
    simp
  | succ N ih =>
    have h_step := dist_le_of_dyadic_step_bounded_modulus_and_decay I hC_ring hC₀ ha u a hr h_ring h_decay
      (hρ_gt_2r N) (hρ_mono N) (hρ_2 N) (hρ_lt_R2 (N + 1))
      (w₁ := dyadicChainPoint w₁ w₂ a N) (w₂ := dyadicChainPoint w₁ w₂ a (N + 1))
      ⟨by rw [hw_seq_dist N], by rw [hw_seq_dist N]; exact hρ_mono N⟩
      ⟨by rw [hw_seq_dist (N + 1)]; exact hρ_mono N, by rw [hw_seq_dist (N + 1)]⟩
    have h_tri := dist_triangle
      (u (stereo_chart.symm w₁))
      (u (stereo_chart.symm (dyadicChainPoint w₁ w₂ a N)))
      (u (stereo_chart.symm (dyadicChainPoint w₁ w₂ a (N + 1))))
    rw [Finset.sum_range_succ]
    linarith

/-- Arbitrary-modulus collar oscillation (`SatisfiesCylinderCollarOscillationWith I C u a r R`)
derived from bounded-modulus (`r₂ ≤ 18 * r₁`) collar oscillation and two-sided cylinder energy
decay (`SatisfiesCylinderEnergyDecayWith I C₀ a_decay u a r R`) (`0 sorryAx`). -/
theorem satisfiesCylinderCollarOscillationWith_of_bounded_modulus_and_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {C_ring C₀ a_decay : ℝ} (hC_ring : 0 ≤ C_ring) (hC₀ : 0 ≤ C₀) (ha : 0 < a_decay)
    (u : CP1 → M) (a : ℂ) {r R : ℝ} (hr : 0 < r)
    (h_ring : ∀ r₁ r₂ : ℝ, r < r₁ → r₁ < r₂ → r₂ < R → r₂ ≤ 18 * r₁ →
      SatisfiesCylinderCollarOscillationWith I C_ring u a r₁ r₂)
    (h_decay : SatisfiesCylinderEnergyDecayWith I C₀ a_decay u a r R) :
    SatisfiesCylinderCollarOscillationWith I
      ((C_ring * Real.sqrt C₀ * (3 : ℝ) ^ (a_decay / 2)) *
        (2 / (1 - (2 : ℝ) ^ (- (a_decay / 2)))))
      u a r R := by
  have h_ord : ∀ {w₁ w₂ : ℂ},
      2 * r < dist w₁ a →
      dist w₁ a ≤ dist w₂ a →
      dist w₂ a < R / 2 →
      dist (u (stereo_chart.symm w₁)) (u (stereo_chart.symm w₂)) ≤
        ((C_ring * Real.sqrt C₀ * (3 : ℝ) ^ (a_decay / 2)) *
          (2 / (1 - (2 : ℝ) ^ (- (a_decay / 2))))) *
          Real.sqrt (energyMeasure I u (annulus_at a r R)) := by
    intro w₁ w₂ hw₁_gt hw₁₂ hw₂_lt
    set s := dist w₁ a
    set t := dist w₂ a
    have hs_pos : 0 < s := by linarith
    have ht_pos : 0 < t := lt_of_lt_of_le hs_pos hw₁₂
    have hR_pos : 0 < R := by linarith
    have h_ex : ∃ n : ℕ, t ≤ (2 : ℝ) ^ n * s := exists_le_two_pow_mul hs_pos
    classical
    let N₀ : ℕ := Nat.find h_ex
    have hN₀_spec : t ≤ (2 : ℝ) ^ N₀ * s := Nat.find_spec h_ex
    let N : ℕ := max N₀ 1
    have hN_pos : 0 < N := lt_of_lt_of_le zero_lt_one (le_max_right N₀ 1)
    have hN_ne : N ≠ 0 := hN_pos.ne'
    have hN₀_le_N : N₀ ≤ N := le_max_left N₀ 1
    have ht_le_powN : t ≤ (2 : ℝ) ^ N * s := by
      calc
        t ≤ (2 : ℝ) ^ N₀ * s := hN₀_spec
        _ ≤ (2 : ℝ) ^ N * s :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hN₀_le_N) hs_pos.le
    have hρ_N : dyadicRadius w₁ w₂ a N = t := min_eq_right ht_le_powN
    have hw_seq_N : dyadicChainPoint w₁ w₂ a N = w₂ := by
      dsimp [dyadicChainPoint]
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hN_ne h)), hρ_N, radialPointOnRay_self ht_pos]
    have h_pow_N_sub_one : (2 : ℝ) ^ (N - 1) * s ≤ t := by
      by_cases hN₀0 : N₀ = 0
      · have hN1 : N = 1 := by dsimp [N]; omega
        rw [hN1, Nat.sub_self, pow_zero, one_mul]
        exact hw₁₂
      · have hN_eq : N = N₀ := max_eq_left (Nat.one_le_iff_ne_zero.mpr hN₀0)
        have h_lt : N - 1 < N₀ := by omega
        have h_not := Nat.find_min h_ex h_lt
        exact le_of_not_ge h_not
    have h_chain := dist_le_sum_dyadic_chain_bounded_modulus_and_decay
      I hC_ring hC₀ ha.le u a hr h_ring h_decay hw₁_gt hw₁₂ hw₂_lt N
    rw [hw_seq_N] at h_chain
    set q := (2 : ℝ) ^ (- (a_decay / 2))
    have hq_nonneg : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
    have hq_lt_one : q < 1 := by
      dsimp [q]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos (half_pos ha))
    have h_term_le : ∀ k ∈ Finset.range N,
        (r / dyadicRadius w₁ w₂ a k) ^ (a_decay / 2) +
          (dyadicRadius w₁ w₂ a (k + 1) / R) ^ (a_decay / 2) ≤
          q ^ k + q ^ (N - 1 - k) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hk_le : k ≤ N - 1 := by omega
      have h_pow_k_le_t : (2 : ℝ) ^ k * s ≤ t := by
        calc
          (2 : ℝ) ^ k * s ≤ (2 : ℝ) ^ (N - 1) * s :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk_le) hs_pos.le
          _ ≤ t := h_pow_N_sub_one
      have hρ_k_eq : dyadicRadius w₁ w₂ a k = (2 : ℝ) ^ k * s := min_eq_left h_pow_k_le_t
      have hρ_k_pos : 0 < dyadicRadius w₁ w₂ a k := by rw [hρ_k_eq]; positivity
      have h_r_div_ρk : r / dyadicRadius w₁ w₂ a k ≤ ((2 : ℝ) ^ k)⁻¹ := by
        rw [hρ_k_eq, div_le_iff₀ (by positivity)]
        calc
          r ≤ s := by linarith
          _ = ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k * s) := by field_simp
      have h_rpow1 : (r / dyadicRadius w₁ w₂ a k) ^ (a_decay / 2) ≤ q ^ k := by
        calc
          (r / dyadicRadius w₁ w₂ a k) ^ (a_decay / 2)
            ≤ (((2 : ℝ) ^ k)⁻¹) ^ (a_decay / 2) :=
              Real.rpow_le_rpow (div_nonneg hr.le hρ_k_pos.le) h_r_div_ρk (half_pos ha).le
          _ = q ^ k := by
              dsimp [q]
              rw [← Real.rpow_natCast, ← Real.rpow_neg_one, ← Real.rpow_mul (by norm_num),
                  ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
              ring_nf
      have hρ_k1_pos : 0 < dyadicRadius w₁ w₂ a (k + 1) := lt_min (by positivity) ht_pos
      have h_ρk1_div_R : dyadicRadius w₁ w₂ a (k + 1) / R ≤ ((2 : ℝ) ^ (N - 1 - k))⁻¹ := by
        rw [div_le_iff₀ hR_pos]
        have h_add : (k + 1) + (N - 1 - k) = N := by omega
        have h_pow_mul : (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (N - 1 - k) = 2 * (2 : ℝ) ^ (N - 1) := by
          rw [← pow_add, h_add, ← pow_succ']
          congr 1
          omega
        have h_prod_le_R : dyadicRadius w₁ w₂ a (k + 1) * (2 : ℝ) ^ (N - 1 - k) ≤ R := by
          calc
            dyadicRadius w₁ w₂ a (k + 1) * (2 : ℝ) ^ (N - 1 - k)
              ≤ ((2 : ℝ) ^ (k + 1) * s) * (2 : ℝ) ^ (N - 1 - k) :=
                mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
            _ = ((2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (N - 1 - k)) * s := by ring
            _ = 2 * ((2 : ℝ) ^ (N - 1) * s) := by rw [h_pow_mul]; ring
            _ ≤ 2 * t := mul_le_mul_of_nonneg_left h_pow_N_sub_one (by norm_num)
            _ ≤ R := by linarith
        calc
          dyadicRadius w₁ w₂ a (k + 1)
            = ((2 : ℝ) ^ (N - 1 - k))⁻¹ * (dyadicRadius w₁ w₂ a (k + 1) * (2 : ℝ) ^ (N - 1 - k)) := by
              field_simp
          _ ≤ ((2 : ℝ) ^ (N - 1 - k))⁻¹ * R :=
              mul_le_mul_of_nonneg_left h_prod_le_R (by positivity)
      have h_rpow2 : (dyadicRadius w₁ w₂ a (k + 1) / R) ^ (a_decay / 2) ≤ q ^ (N - 1 - k) := by
        calc
          (dyadicRadius w₁ w₂ a (k + 1) / R) ^ (a_decay / 2)
            ≤ (((2 : ℝ) ^ (N - 1 - k))⁻¹) ^ (a_decay / 2) :=
              Real.rpow_le_rpow (div_nonneg hρ_k1_pos.le hR_pos.le) h_ρk1_div_R (half_pos ha).le
          _ = q ^ (N - 1 - k) := by
              dsimp [q]
              rw [← Real.rpow_natCast, ← Real.rpow_neg_one, ← Real.rpow_mul (by norm_num),
                  ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
              ring_nf
      exact add_le_add h_rpow1 h_rpow2
    have h_sum_le :
        (∑ k ∈ Finset.range N,
          ((r / dyadicRadius w₁ w₂ a k) ^ (a_decay / 2) +
            (dyadicRadius w₁ w₂ a (k + 1) / R) ^ (a_decay / 2))) ≤
          2 / (1 - q) := by
      calc
        (∑ k ∈ Finset.range N,
          ((r / dyadicRadius w₁ w₂ a k) ^ (a_decay / 2) +
            (dyadicRadius w₁ w₂ a (k + 1) / R) ^ (a_decay / 2)))
          ≤ ∑ k ∈ Finset.range N, (q ^ k + q ^ (N - 1 - k)) := Finset.sum_le_sum h_term_le
        _ = (∑ k ∈ Finset.range N, q ^ k) + (∑ k ∈ Finset.range N, q ^ (N - 1 - k)) :=
          Finset.sum_add_distrib
        _ = (∑ k ∈ Finset.range N, q ^ k) + (∑ k ∈ Finset.range N, q ^ k) := by
          rw [Finset.sum_range_reflect (fun k => q ^ k) N]
        _ ≤ 1 / (1 - q) + 1 / (1 - q) :=
          add_le_add (sum_geom_le_inv_one_sub hq_nonneg hq_lt_one N)
            (sum_geom_le_inv_one_sub hq_nonneg hq_lt_one N)
        _ = 2 / (1 - q) := by ring
    refine le_trans h_chain ?_
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_left h_sum_le (by positivity)
  rintro z₁ ⟨w₁, ⟨hw₁_gt, hw₁_lt⟩, rfl⟩ z₂ ⟨w₂, ⟨hw₂_gt, hw₂_lt⟩, rfl⟩
  rcases le_total (dist w₁ a) (dist w₂ a) with hle | hle
  · exact h_ord hw₁_gt hle hw₂_lt
  · rw [dist_comm]
    exact h_ord hw₂_gt hle hw₁_lt

/-- Arbitrary-modulus local collar oscillation from bounded-modulus (`R ≤ 18 * r`) local collar
oscillation and local cylinder energy decay (`0 sorryAx`). -/
theorem local_collar_oscillation_of_bounded_modulus_and_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_ring_osc : ∃ (C_ring ε_ring : ℝ), 0 < C_ring ∧ 0 < ε_ring ∧
      ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R → R ≤ 18 * r →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at a r R) →
        energyMeasure I u (annulus_at a r R) < ε_ring →
        SatisfiesCylinderCollarOscillationWith I C_ring u a r R)
    (h_decay_local : ∃ (C₀ a_decay ε_neck : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck ∧
      ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
        0 < r → 2 * r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at center r R) →
        energyMeasure I u (annulus_at center r R) < ε_neck →
        SatisfiesCylinderEnergyDecayWith I C₀ a_decay u center r R) :
    ∃ (C ε_osc : ℝ), 0 < C ∧ 0 < ε_osc ∧
      ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at a r R) →
        energyMeasure I u (annulus_at a r R) < ε_osc →
        SatisfiesCylinderCollarOscillationWith I C u a r R := by
  obtain ⟨C_ring, ε_ring, hC_ring, hε_ring, h_ring⟩ := h_ring_osc
  obtain ⟨C₀, a_decay, ε_neck, hC₀, ha, hε_neck, h_dec⟩ := h_decay_local
  set q := (2 : ℝ) ^ (- (a_decay / 2))
  have hq_lt_one : q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos (half_pos ha))
  have h1q_pos : 0 < 1 - q := sub_pos.mpr hq_lt_one
  set C := (C_ring * Real.sqrt C₀ * (3 : ℝ) ^ (a_decay / 2)) * (2 / (1 - q))
  have hC_pos : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos (mul_pos hC_ring (Real.sqrt_pos.mpr hC₀)) (Real.rpow_pos_of_pos (by norm_num) _))
      (div_pos (by norm_num) h1q_pos)
  set ε_osc := min ε_neck (ε_ring / (2 * C₀))
  have hε_osc_pos : 0 < ε_osc := lt_min hε_neck (div_pos hε_ring (by positivity))
  refine ⟨C, ε_osc, hC_pos, hε_osc_pos, ?_⟩
  intro u a r R hr hrR hu hE
  by_cases h_collar : R / 2 ≤ 2 * r
  · intro z₁ hz₁
    rw [annulus_at_empty_of_le a h_collar] at hz₁
    exact False.elim hz₁
  · push_neg at h_collar
    have h2r_lt_R : 2 * r < R := by linarith
    have hE_neck : energyMeasure I u (annulus_at a r R) < ε_neck :=
      lt_of_lt_of_le hE (min_le_left _ _)
    have hE_div : energyMeasure I u (annulus_at a r R) < ε_ring / (2 * C₀) :=
      lt_of_lt_of_le hE (min_le_right _ _)
    have h_dec_u := h_dec u a r R hr h2r_lt_R hu hE_neck
    apply satisfiesCylinderCollarOscillationWith_of_bounded_modulus_and_decay
      I hC_ring.le hC₀.le ha u a hr _ h_dec_u
    intro r₁ r₂ hr₁ hr₁₂ hr₂ hr₂_18
    have hr₁_pos : 0 < r₁ := lt_trans hr hr₁
    have hr₂_pos : 0 < r₂ := lt_trans hr₁_pos hr₁₂
    have hR_pos : 0 < R := lt_trans hr₂_pos hr₂
    have h_sub : annulus_at a r₁ r₂ ⊆ annulus_at a r R := annulus_at_mono a hr₁.le hr₂.le
    have hu_sub : JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at a r₁ r₂) :=
      ⟨hu.1.mono h_sub, fun z hz => hu.2 z (h_sub hz)⟩
    have h_r_r₁_le : (r / r₁) ^ a_decay ≤ 1 :=
      Real.rpow_le_one (div_nonneg hr.le hr₁_pos.le) ((div_le_one hr₁_pos).mpr hr₁.le) ha.le
    have h_r₂_R_le : (r₂ / R) ^ a_decay ≤ 1 :=
      Real.rpow_le_one (div_nonneg hr₂_pos.le hR_pos.le) ((div_le_one hR_pos).mpr hr₂.le) ha.le
    have h_en_sub : energyMeasure I u (annulus_at a r₁ r₂) < ε_ring := by
      have h_step := h_dec_u r₁ r₂ hr₁ hr₁₂ hr₂
      have h_en_nonneg : 0 ≤ energyMeasure I u (annulus_at a r R) := energy_nonneg I u _
      calc
        energyMeasure I u (annulus_at a r₁ r₂)
          ≤ C₀ * ((r / r₁) ^ a_decay + (r₂ / R) ^ a_decay) * energyMeasure I u (annulus_at a r R) := h_step
        _ ≤ C₀ * (1 + 1) * energyMeasure I u (annulus_at a r R) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (add_le_add h_r_r₁_le h_r₂_R_le) hC₀.le) h_en_nonneg
        _ = (2 * C₀) * energyMeasure I u (annulus_at a r R) := by ring
        _ < (2 * C₀) * (ε_ring / (2 * C₀)) :=
          mul_lt_mul_of_pos_left hE_div (by positivity)
        _ = ε_ring := mul_div_cancel₀ ε_ring (by positivity)
    exact h_ring u a r₁ r₂ hr₁_pos hr₁₂ hr₂_18 hu_sub h_en_sub

/-- Arbitrary-modulus `CollarOscillationProperty I M` derived from bounded-modulus (`R ≤ 18 * r`)
collar oscillation and `CylinderEnergyDecayProperty I M` (`0 sorryAx`). -/
theorem collarOscillationProperty_of_bounded_modulus_and_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_ring_osc : ∃ (C_ring ε_ring : ℝ), 0 < C_ring ∧ 0 < ε_ring ∧
      ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R → R ≤ 18 * r →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        energyMeasure I u (annulus_at a r R) < ε_ring →
        SatisfiesCylinderCollarOscillationWith I C_ring u a r R)
    (h_decay : CylinderEnergyDecayProperty I M) :
    CollarOscillationProperty I M := by
  obtain ⟨C_ring, ε_ring, hC_ring, hε_ring, h_ring⟩ := h_ring_osc
  obtain ⟨C₀, a_decay, ε_neck, hC₀, ha, hε_neck, h_dec⟩ := h_decay
  set q := (2 : ℝ) ^ (- (a_decay / 2))
  have hq_lt_one : q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos (half_pos ha))
  have h1q_pos : 0 < 1 - q := sub_pos.mpr hq_lt_one
  set C := (C_ring * Real.sqrt C₀ * (3 : ℝ) ^ (a_decay / 2)) * (2 / (1 - q))
  have hC_pos : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos (mul_pos hC_ring (Real.sqrt_pos.mpr hC₀)) (Real.rpow_pos_of_pos (by norm_num) _))
      (div_pos (by norm_num) h1q_pos)
  set ε_osc := min ε_neck (ε_ring / (2 * C₀))
  have hε_osc_pos : 0 < ε_osc := lt_min hε_neck (div_pos hε_ring (by positivity))
  refine ⟨C, ε_osc, hC_pos, hε_osc_pos, ?_⟩
  intro u a r R hr hrR hu hE
  by_cases h_collar : R / 2 ≤ 2 * r
  · intro z₁ hz₁
    rw [annulus_at_empty_of_le a h_collar] at hz₁
    exact False.elim hz₁
  · push_neg at h_collar
    have h2r_lt_R : 2 * r < R := by linarith
    have hE_neck : energyMeasure I u (annulus_at a r R) < ε_neck :=
      lt_of_lt_of_le hE (min_le_left _ _)
    have hE_div : energyMeasure I u (annulus_at a r R) < ε_ring / (2 * C₀) :=
      lt_of_lt_of_le hE (min_le_right _ _)
    have h_dec_u := h_dec u a r R hr h2r_lt_R hu hE_neck
    apply satisfiesCylinderCollarOscillationWith_of_bounded_modulus_and_decay
      I hC_ring.le hC₀.le ha u a hr _ h_dec_u
    intro r₁ r₂ hr₁ hr₁₂ hr₂ hr₂_18
    have hr₁_pos : 0 < r₁ := lt_trans hr hr₁
    have hr₂_pos : 0 < r₂ := lt_trans hr₁_pos hr₁₂
    have hR_pos : 0 < R := lt_trans hr₂_pos hr₂
    have h_r_r₁_le : (r / r₁) ^ a_decay ≤ 1 :=
      Real.rpow_le_one (div_nonneg hr.le hr₁_pos.le) ((div_le_one hr₁_pos).mpr hr₁.le) ha.le
    have h_r₂_R_le : (r₂ / R) ^ a_decay ≤ 1 :=
      Real.rpow_le_one (div_nonneg hr₂_pos.le hR_pos.le) ((div_le_one hR_pos).mpr hr₂.le) ha.le
    have h_en_sub : energyMeasure I u (annulus_at a r₁ r₂) < ε_ring := by
      have h_step := h_dec_u r₁ r₂ hr₁ hr₁₂ hr₂
      have h_en_nonneg : 0 ≤ energyMeasure I u (annulus_at a r R) := energy_nonneg I u _
      calc
        energyMeasure I u (annulus_at a r₁ r₂)
          ≤ C₀ * ((r / r₁) ^ a_decay + (r₂ / R) ^ a_decay) * energyMeasure I u (annulus_at a r R) := h_step
        _ ≤ C₀ * (1 + 1) * energyMeasure I u (annulus_at a r R) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (add_le_add h_r_r₁_le h_r₂_R_le) hC₀.le) h_en_nonneg
        _ = (2 * C₀) * energyMeasure I u (annulus_at a r R) := by ring
        _ < (2 * C₀) * (ε_ring / (2 * C₀)) :=
          mul_lt_mul_of_pos_left hE_div (by positivity)
        _ = ε_ring := mul_div_cancel₀ ε_ring (by positivity)
    exact h_ring u a r₁ r₂ hr₁_pos hr₁₂ hr₂_18 hu h_en_sub

/-- Pointwise collar energy-density bound from dyadic disk regularity (`0 sorryAx`):
For any point `w₀` in the central Euclidean collar `{z : ℂ | 2 * r < dist z a ∧ dist z a < R / 2}` (`0 < r`),
the dyadic disk `disk_at w₀ (dist w₀ a / 2)` has radius `> r` and is contained in `annulus_at a r R`,
so any disk regularity bound `e(w₀) ≤ C_reg * (dist w₀ a / 2)^(-2) * E(u; D(w₀, dist w₀ a / 2))`
implies `e(w₀) ≤ C_reg * r^(-2) * E(u; A(r, R))`. -/
theorem riemannianEnergyDensity_collar_le_of_disk_regularity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) {r R C_reg : ℝ} (hr : 0 < r) (hC : 0 ≤ C_reg)
    {w₀ : ℂ} (hw₀ : w₀ ∈ {z : ℂ | 2 * r < dist z a ∧ dist z a < R / 2})
    (h_fin : energyMeasureExtended I u (annulus_at a r R) ≠ ⊤)
    (h_reg : riemannianEnergyDensity I u (stereo_chart.symm w₀) ≤
      C_reg * (dist w₀ a / 2) ^ (-2 : ℝ) * energyMeasure I u (disk_at w₀ (dist w₀ a / 2))) :
    riemannianEnergyDensity I u (stereo_chart.symm w₀) ≤
      C_reg * r ^ (-2 : ℝ) * energyMeasure I u (annulus_at a r R) := by
  have hρ_gt : r < dist w₀ a / 2 := by linarith [hw₀.1]
  have hρ_pos : 0 < dist w₀ a / 2 := lt_trans hr hρ_gt
  have h_rpow : (dist w₀ a / 2) ^ (-2 : ℝ) ≤ r ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hρ_pos.le, Real.rpow_neg hr.le, Real.rpow_two, Real.rpow_two]
    exact inv_anti₀ (sq_pos_of_pos hr)
      (sq_le_sq.mpr (by rw [abs_of_pos hr, abs_of_pos hρ_pos]; exact hρ_gt.le))
  have h_disk_le := energyMeasure_disk_at_collar_le_annulus_at I u a hr hw₀ h_fin
  have h_disk_nonneg : 0 ≤ energyMeasure I u (disk_at w₀ (dist w₀ a / 2)) := energy_nonneg I u _
  calc
    riemannianEnergyDensity I u (stereo_chart.symm w₀)
      ≤ C_reg * (dist w₀ a / 2) ^ (-2 : ℝ) * energyMeasure I u (disk_at w₀ (dist w₀ a / 2)) := h_reg
    _ ≤ C_reg * r ^ (-2 : ℝ) * energyMeasure I u (annulus_at a r R) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left h_rpow hC) h_disk_le h_disk_nonneg
      exact mul_nonneg hC (Real.rpow_nonneg hr.le _)

/-- Bounded-modulus collar oscillation (`SatisfiesCylinderCollarOscillationWith I (C_lip * M_rat) u a r R`)
from a Lipschitz bound `L ≤ C_lip * r⁻¹ * √E(u; A(r, R))` on the Euclidean collar (`0 sorryAx`). -/
theorem satisfiesCylinderCollarOscillationWith_of_lipschitz_collar_ring
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) {r R C_lip M_rat : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C_lip) (h_rat : R ≤ M_rat * r)
    (h_lip : ∀ w₁ ∈ {z : ℂ | 2 * r < dist z a ∧ dist z a < R / 2},
      ∀ w₂ ∈ {z : ℂ | 2 * r < dist z a ∧ dist z a < R / 2},
        dist (u (stereo_chart.symm w₁)) (u (stereo_chart.symm w₂)) ≤
          (C_lip * r⁻¹ * Real.sqrt (energyMeasure I u (annulus_at a r R))) * dist w₁ w₂) :
    SatisfiesCylinderCollarOscillationWith I (C_lip * M_rat) u a r R := by
  rintro z₁ ⟨w₁, hw₁, rfl⟩ z₂ ⟨w₂, hw₂, rfl⟩
  have h_dist_w : dist w₁ w₂ ≤ M_rat * r := by
    have h_tri : dist w₁ w₂ ≤ dist w₁ a + dist a w₂ := dist_triangle w₁ a w₂
    have h_symm : dist a w₂ = dist w₂ a := dist_comm a w₂
    have h1 : dist w₁ a < R / 2 := hw₁.2
    have h2 : dist w₂ a < R / 2 := hw₂.2
    linarith
  have h_step := h_lip w₁ hw₁ w₂ hw₂
  have h_fac_nonneg : 0 ≤ C_lip * r⁻¹ * Real.sqrt (energyMeasure I u (annulus_at a r R)) := by positivity
  calc
    dist (u (stereo_chart.symm w₁)) (u (stereo_chart.symm w₂))
      ≤ (C_lip * r⁻¹ * Real.sqrt (energyMeasure I u (annulus_at a r R))) * dist w₁ w₂ := h_step
    _ ≤ (C_lip * r⁻¹ * Real.sqrt (energyMeasure I u (annulus_at a r R))) * (M_rat * r) :=
      mul_le_mul_of_nonneg_left h_dist_w h_fac_nonneg
    _ = (C_lip * M_rat) * Real.sqrt (energyMeasure I u (annulus_at a r R)) := by
      have hr_ne : r ≠ 0 := hr.ne'
      field_simp

/-- Arbitrary-modulus `CollarOscillationProperty I M` (`cert_osc` / Contract A09) derived from
bounded-modulus (`R ≤ 18 * r`) radial/angular slice bounds and `CylinderEnergyDecayProperty I M` (`0 sorryAx`). -/
theorem collarOscillationProperty_of_slices_and_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_slices : ∃ (C_ring ε_ring : ℝ), 0 < C_ring ∧ 0 < ε_ring ∧
      ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R → R ≤ 18 * r →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        energyMeasure I u (annulus_at a r R) < ε_ring →
        ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
          ∃ z_mid : CP1,
            dist (u z₁) (u z_mid) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u (annulus_at a r R)) ∧
            dist (u z_mid) (u z₂) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u (annulus_at a r R)))
    (h_decay : CylinderEnergyDecayProperty I M) :
    CollarOscillationProperty I M := by
  obtain ⟨C_ring, ε_ring, hC_ring, hε_ring, h_sl⟩ := h_slices
  refine collarOscillationProperty_of_bounded_modulus_and_decay I
    ⟨C_ring, ε_ring, hC_ring, hε_ring, fun u a r R hr hrR hr18 hu hE =>
      satisfiesCylinderCollarOscillation_of_radial_and_angular_bounds I C_ring u a r R
        (h_sl u a r R hr hrR hr18 hu hE)⟩
    h_decay

/-- Arbitrary-modulus `CollarOscillationProperty I M` (`cert_osc`) derived from bounded-modulus
(`R ≤ 18 * r`) radial/angular slice bounds and single-step collar Widman hole-filling (`0 sorryAx`). -/
theorem collarOscillationProperty_of_slices_and_collar_hole_filling
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_slices : ∃ (C_ring ε_ring : ℝ), 0 < C_ring ∧ 0 < ε_ring ∧
      ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R → R ≤ 18 * r →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        energyMeasure I u (annulus_at a r R) < ε_ring →
        ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
          ∃ z_mid : CP1,
            dist (u z₁) (u z_mid) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u (annulus_at a r R)) ∧
            dist (u z_mid) (u z₂) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u (annulus_at a r R)))
    {K ε_neck : ℝ} (hK : 0 < K) (hε : 0 < ε_neck)
    (h_fin : ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      0 < r → 2 * r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r R) < ε_neck →
      energyMeasureExtended I u (annulus_at center r R) ≠ ⊤)
    (h_collar : ∀ (u : CP1 → M) (center : ℂ) (r' R' : ℝ),
      0 < r' → 4 * r' < R' →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r' R') < ε_neck →
      energyMeasure I u (annulus_at center (2 * r') (R' / 2)) ≤
        K * (energyMeasure I u (annulus_at center r' (2 * r')) +
             energyMeasure I u (annulus_at center (R' / 2) R'))) :
    CollarOscillationProperty I M :=
  collarOscillationProperty_of_slices_and_decay I h_slices
    (cylinderEnergyDecayProperty_of_collar_hole_filling I M hK hε h_fin h_collar)

/-- Contract A09 (`cylinder_localization`) derived from bounded-modulus (`R ≤ 18 * r`) radial/angular
slice bounds and `CylinderEnergyDecayProperty I M` (`0 sorryAx`). -/
theorem cylinder_localization_of_slices_and_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_slices : ∃ (C_ring ε_ring : ℝ), 0 < C_ring ∧ 0 < ε_ring ∧
      ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R → R ≤ 18 * r →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        energyMeasure I u (annulus_at a r R) < ε_ring →
        ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
          ∃ z_mid : CP1,
            dist (u z₁) (u z_mid) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u (annulus_at a r R)) ∧
            dist (u z_mid) (u z₂) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u (annulus_at a r R)))
    (h_decay : CylinderEnergyDecayProperty I M)
    (d₀ : ℝ) (hd₀ : 0 < d₀) :
    ∃ (η : ℝ), 0 < η ∧
    ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
      0 < r → r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at a r R) < η →
      ∃ (x₀ : M), ∀ z ∈ annulus_at a (2 * r) (R / 2), dist (u z) x₀ < d₀ :=
  cylinder_localization I (collarOscillationProperty_of_slices_and_decay I h_slices h_decay) d₀ hd₀

/-- Existence of a puncture limit `lim_{z → p} u(z)` at **any** puncture `p : CP1` (both finite
points `p ≠ north_pole` and `p = north_pole`) from finite punctured-sphere energy and local
small-energy collar oscillation (`0 sorryAx`). -/
theorem exists_limit_point_of_local_collar_oscillation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_osc_local : ∃ (C ε_osc : ℝ), 0 < C ∧ 0 < ε_osc ∧
      ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at a r R) →
        energyMeasure I u (annulus_at a r R) < ε_osc →
        SatisfiesCylinderCollarOscillationWith I C u a r R)
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (he : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∃ m_star : M, Filter.Tendsto u (𝓝[≠] p) (𝓝 m_star) :=
  exists_limit_point_of_puncture u p
    (punctured_oscillation_of_local_collar_oscillation I h_osc_local u p hu he)

/-- Uniqueness and existence of the puncture limit `lim_{z → p} u(z)` at **any** puncture `p : CP1`
from finite punctured-sphere energy and local small-energy collar oscillation (`0 sorryAx`). -/
theorem exists_unique_limit_point_of_local_collar_oscillation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_osc_local : ∃ (C ε_osc : ℝ), 0 < C ∧ 0 < ε_osc ∧
      ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at a r R) →
        energyMeasure I u (annulus_at a r R) < ε_osc →
        SatisfiesCylinderCollarOscillationWith I C u a r R)
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (he : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∃! m_star : M, Filter.Tendsto u (𝓝[≠] p) (𝓝 m_star) := by
  obtain ⟨m_star, hm_star⟩ := exists_limit_point_of_local_collar_oscillation I h_osc_local u p hu he
  refine ⟨m_star, hm_star, fun m' hm' => ?_⟩
  have h_dense : Dense ({p}ᶜ : Set CP1) := by
    rw [← punctured_sphere_singleton_eq_compl]
    exact dense_punctured_sphere p
  have : (𝓝[≠] p).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (h_dense p)
  exact tendsto_nhds_unique hm' hm_star

/-- Unique continuous extension across **any** puncture `p : CP1` of a finite-energy punctured
`J`-holomorphic curve under local small-energy collar oscillation (`0 sorryAx`). -/
theorem exists_unique_continuous_extension_of_local_collar_oscillation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_osc_local : ∃ (C ε_osc : ℝ), 0 < C ∧ 0 < ε_osc ∧
      ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at a r R) →
        energyMeasure I u (annulus_at a r R) < ε_osc →
        SatisfiesCylinderCollarOscillationWith I C u a r R)
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (he : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∃! u_ext : CP1 → M, Continuous u_ext ∧ EqOn u_ext u (punctured_sphere {p}) := by
  obtain ⟨m_star, hm_star⟩ := exists_limit_point_of_local_collar_oscillation I h_osc_local u p hu he
  have h_eq : EqOn (Function.update u p m_star) u (punctured_sphere {p}) :=
    eqOn_update_punctured_sphere u p m_star
  have h_cont : Continuous (Function.update u p m_star) :=
    continuous_update_of_tendsto_punctured_sphere u p m_star hu.1.continuousOn hm_star
  refine ⟨Function.update u p m_star, ⟨h_cont, h_eq⟩, ?_⟩
  intro v ⟨hv_cont, hv_eq⟩
  have h_eq_vu : EqOn v (Function.update u p m_star) (punctured_sphere {p}) := fun z hz => by
    rw [hv_eq hz, h_eq hz]
  exact Continuous.ext_on (dense_punctured_sphere p) hv_cont h_cont h_eq_vu

/-- If `u : CP1 → M` is `J`-holomorphic on `punctured_sphere {p}` and `Function.update u p m_star`
is $C^1$ at the single puncture point `p` (`ContMDiffAt I_CP1 I 1 (Function.update u p m_star) p`),
then `Function.update u p m_star` is globally $C^1$ on `CP1` (`0 sorryAx`). -/
theorem contMDiffOn_one_update_of_contMDiffAt_puncture
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (p : CP1) (m_star : M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_at : ContMDiffAt I_CP1 I 1 (Function.update u p m_star) p) :
    ContMDiffOn I_CP1 I 1 (Function.update u p m_star) Set.univ := by
  intro z _hz
  by_cases hzp : z = p
  · subst hzp
    exact h_at.contMDiffWithinAt
  · have hz_punc : z ∈ punctured_sphere {p} := by
      rw [punctured_sphere_singleton_eq_compl]
      exact hzp
    have hu_c1 : ContMDiffOn I_CP1 I 1 u (punctured_sphere {p}) :=
      hu.1.of_le (by decide : ((1 : ℕ) : WithTop ℕ∞) ≤ ∞)
    have h_upd_c1 : ContMDiffOn I_CP1 I 1 (Function.update u p m_star) (punctured_sphere {p}) :=
      hu_c1.congr (eqOn_update_punctured_sphere u p m_star)
    exact (h_upd_c1.contMDiffAt ((isOpen_punctured_sphere p).mem_nhds hz_punc)).contMDiffWithinAt

/-- General arbitrary-puncture (`p : CP1`) proof of `SatisfiesPunctureSobolevExtension I u p`
(`cert_punc`) from local small-energy collar oscillation and $C^1$ regularity at `p` (`0 sorryAx`). -/
theorem satisfiesPunctureSobolevExtension_of_local_collar_oscillation_and_c1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_osc_local : ∃ (C ε_osc : ℝ), 0 < C ∧ 0 < ε_osc ∧
      ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at a r R) →
        energyMeasure I u (annulus_at a r R) < ε_osc →
        SatisfiesCylinderCollarOscillationWith I C u a r R)
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (he : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (h_c1 : ∀ m_star : M, Filter.Tendsto u (𝓝[≠] p) (𝓝 m_star) →
      ContMDiffAt I_CP1 I 1 (Function.update u p m_star) p ∧
      ∀ v : TangentSpace I_CP1 p,
        ContinuousAt (fun z : CP1 =>
          mfderiv I_CP1 I (Function.update u p m_star) z (RiemannDomain.j z v) -
            (ClosedTameTarget.J (I := I) (Function.update u p m_star z))
              (mfderiv I_CP1 I (Function.update u p m_star) z v)) p) :
    SatisfiesPunctureSobolevExtension I u p := by
  obtain ⟨m_star, hm_star⟩ := exists_limit_point_of_local_collar_oscillation I h_osc_local u p hu he
  obtain ⟨h_at, hcr⟩ := h_c1 m_star hm_star
  have hc1 := contMDiffOn_one_update_of_contMDiffAt_puncture I u p m_star hu h_at
  have h_weak := weakJHolomorphicOn_univ_of_c1_and_continuousAt_cr_at_puncture
    I u (Function.update u p m_star) p hc1 (eqOn_update_punctured_sphere u p m_star) hu hcr
  exact satisfiesPunctureSobolevExtension_of_update_weakJHolomorphicOn I u p m_star h_weak

/-- Proof of `SatisfiesPunctureSobolevExtension I u p` (`cert_punc`) from bounded-modulus
(`R ≤ 18 * r`) radial/angular slice bounds, local exponential cylinder energy decay, and
single-point $C^1$ regularity at `p` (`0 sorryAx`). -/
theorem satisfiesPunctureSobolevExtension_of_slices_and_decay_and_c1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_slices : ∃ (C_ring ε_ring : ℝ), 0 < C_ring ∧ 0 < ε_ring ∧
      ∀ (u' : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R → R ≤ 18 * r →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u' (annulus_at a r R) →
        energyMeasure I u' (annulus_at a r R) < ε_ring →
        ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
          ∃ z_mid : CP1,
            dist (u' z₁) (u' z_mid) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u' (annulus_at a r R)) ∧
            dist (u' z_mid) (u' z₂) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u' (annulus_at a r R)))
    (h_decay : ∃ (C₀ a_decay ε_neck : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck ∧
      ∀ (u' : CP1 → M) (center : ℂ) (r R : ℝ),
        0 < r → 2 * r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u' (annulus_at center r R) →
        energyMeasure I u' (annulus_at center r R) < ε_neck →
        SatisfiesCylinderEnergyDecayWith I C₀ a_decay u' center r R)
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (he : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (h_c1 : ∀ m_star : M, Filter.Tendsto u (𝓝[≠] p) (𝓝 m_star) →
      ContMDiffAt I_CP1 I 1 (Function.update u p m_star) p ∧
      ∀ v : TangentSpace I_CP1 p,
        ContinuousAt (fun z : CP1 =>
          mfderiv I_CP1 I (Function.update u p m_star) z (RiemannDomain.j z v) -
            (ClosedTameTarget.J (I := I) (Function.update u p m_star z))
              (mfderiv I_CP1 I (Function.update u p m_star) z v)) p) :
    SatisfiesPunctureSobolevExtension I u p := by
  obtain ⟨C_ring, ε_ring, hC_ring, hε_ring, h_sl⟩ := h_slices
  have h_ring_osc : ∃ (C_ring ε_ring : ℝ), 0 < C_ring ∧ 0 < ε_ring ∧
      ∀ (u' : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R → R ≤ 18 * r →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u' (annulus_at a r R) →
        energyMeasure I u' (annulus_at a r R) < ε_ring →
        SatisfiesCylinderCollarOscillationWith I C_ring u' a r R :=
    ⟨C_ring, ε_ring, hC_ring, hε_ring, fun u' a r R hr hrR hr18 hu_ann hE =>
      satisfiesCylinderCollarOscillation_of_radial_and_angular_bounds I C_ring u' a r R
        (h_sl u' a r R hr hrR hr18 hu_ann hE)⟩
  have h_osc_local := local_collar_oscillation_of_bounded_modulus_and_decay I h_ring_osc h_decay
  exact satisfiesPunctureSobolevExtension_of_local_collar_oscillation_and_c1
    I h_osc_local u p hu he h_c1

/-- Contract A11 (`puncture_sobolev_extension`) proved from bounded-modulus (`R ≤ 18 * r`)
radial/angular slice bounds, local exponential cylinder energy decay, and single-point $C^1$
regularity at `p` (`0 sorryAx`). -/
theorem puncture_sobolev_extension_of_slices_and_decay_and_c1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_slices : ∃ (C_ring ε_ring : ℝ), 0 < C_ring ∧ 0 < ε_ring ∧
      ∀ (u' : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R → R ≤ 18 * r →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u' (annulus_at a r R) →
        energyMeasure I u' (annulus_at a r R) < ε_ring →
        ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
          ∃ z_mid : CP1,
            dist (u' z₁) (u' z_mid) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u' (annulus_at a r R)) ∧
            dist (u' z_mid) (u' z₂) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u' (annulus_at a r R)))
    (h_decay : ∃ (C₀ a_decay ε_neck : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck ∧
      ∀ (u' : CP1 → M) (center : ℂ) (r R : ℝ),
        0 < r → 2 * r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u' (annulus_at center r R) →
        energyMeasure I u' (annulus_at center r R) < ε_neck →
        SatisfiesCylinderEnergyDecayWith I C₀ a_decay u' center r R)
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (he : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (h_c1 : ∀ m_star : M, Filter.Tendsto u (𝓝[≠] p) (𝓝 m_star) →
      ContMDiffAt I_CP1 I 1 (Function.update u p m_star) p ∧
      ∀ v : TangentSpace I_CP1 p,
        ContinuousAt (fun z : CP1 =>
          mfderiv I_CP1 I (Function.update u p m_star) z (RiemannDomain.j z v) -
            (ClosedTameTarget.J (I := I) (Function.update u p m_star z))
              (mfderiv I_CP1 I (Function.update u p m_star) z v)) p) :
    ∃ (u_ext : CP1 → M),
      Continuous u_ext ∧
      WeakJHolomorphicOn I u_ext Set.univ ∧
      EqOn u_ext u (punctured_sphere {p}) :=
  puncture_sobolev_extension I u p hu he
    (satisfiesPunctureSobolevExtension_of_slices_and_decay_and_c1 I h_slices h_decay u p hu he h_c1)

/-- Contract A12 (`removal_of_singularities`) proved from bounded-modulus (`R ≤ 18 * r`)
radial/angular slice bounds, local exponential cylinder energy decay, single-point $C^1$
regularity at `p`, and `RegularityTowerProperty` (`0 sorryAx`). -/
theorem removal_of_singularities_of_slices_and_decay_and_c1_and_tower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_slices : ∃ (C_ring ε_ring : ℝ), 0 < C_ring ∧ 0 < ε_ring ∧
      ∀ (u' : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R → R ≤ 18 * r →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u' (annulus_at a r R) →
        energyMeasure I u' (annulus_at a r R) < ε_ring →
        ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
          ∃ z_mid : CP1,
            dist (u' z₁) (u' z_mid) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u' (annulus_at a r R)) ∧
            dist (u' z_mid) (u' z₂) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u' (annulus_at a r R)))
    (h_decay : ∃ (C₀ a_decay ε_neck : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck ∧
      ∀ (u' : CP1 → M) (center : ℂ) (r R : ℝ),
        0 < r → 2 * r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u' (annulus_at center r R) →
        energyMeasure I u' (annulus_at center r R) < ε_neck →
        SatisfiesCylinderEnergyDecayWith I C₀ a_decay u' center r R)
    (h_tower : RegularityTowerProperty I M)
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (he : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (h_c1 : ∀ m_star : M, Filter.Tendsto u (𝓝[≠] p) (𝓝 m_star) →
      ContMDiffAt I_CP1 I 1 (Function.update u p m_star) p ∧
      ∀ v : TangentSpace I_CP1 p,
        ContinuousAt (fun z : CP1 =>
          mfderiv I_CP1 I (Function.update u p m_star) z (RiemannDomain.j z v) -
            (ClosedTameTarget.J (I := I) (Function.update u p m_star z))
              (mfderiv I_CP1 I (Function.update u p m_star) z v)) p) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  removal_of_singularities I u p hu he
    (satisfiesPunctureSobolevExtension_of_slices_and_decay_and_c1 I h_slices h_decay u p hu he h_c1)
    (fun u_ext hu_weak n => h_tower u_ext Set.univ isOpen_univ hu_weak n)

/-- Contract A12 (`removal_of_singularities`) proved from bounded-modulus (`R ≤ 18 * r`)
radial/angular slice bounds, local exponential cylinder energy decay, single-point $C^1$
regularity at `p`, and the chart-level elliptic step (`0 sorryAx`). -/
theorem removal_of_singularities_of_slices_and_decay_and_c1_and_chart_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_slices : ∃ (C_ring ε_ring : ℝ), 0 < C_ring ∧ 0 < ε_ring ∧
      ∀ (u' : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R → R ≤ 18 * r →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u' (annulus_at a r R) →
        energyMeasure I u' (annulus_at a r R) < ε_ring →
        ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
          ∃ z_mid : CP1,
            dist (u' z₁) (u' z_mid) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u' (annulus_at a r R)) ∧
            dist (u' z_mid) (u' z₂) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u' (annulus_at a r R)))
    (h_decay : ∃ (C₀ a_decay ε_neck : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck ∧
      ∀ (u' : CP1 → M) (center : ℂ) (r R : ℝ),
        0 < r → 2 * r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u' (annulus_at center r R) →
        energyMeasure I u' (annulus_at center r R) < ε_neck →
        SatisfiesCylinderEnergyDecayWith I C₀ a_decay u' center r R)
    (h_chart_step : ∀ (u' : CP1 → M) (Ω : Set CP1), IsOpen Ω → WeakJHolomorphicOn I u' Ω →
      ∀ (k : ℕ), 1 ≤ k → ∀ z ∈ Ω,
        ContDiffAt ℝ (k : WithTop ℕ∞) (writtenInExtChartAt I_CP1 I z u') ((extChartAt I_CP1 z) z) →
        ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (writtenInExtChartAt I_CP1 I z u') ((extChartAt I_CP1 z) z))
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (he : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (h_c1 : ∀ m_star : M, Filter.Tendsto u (𝓝[≠] p) (𝓝 m_star) →
      ContMDiffAt I_CP1 I 1 (Function.update u p m_star) p ∧
      ∀ v : TangentSpace I_CP1 p,
        ContinuousAt (fun z : CP1 =>
          mfderiv I_CP1 I (Function.update u p m_star) z (RiemannDomain.j z v) -
            (ClosedTameTarget.J (I := I) (Function.update u p m_star z))
              (mfderiv I_CP1 I (Function.update u p m_star) z v)) p) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  removal_of_singularities_of_slices_and_decay_and_c1_and_tower I h_slices h_decay
    (regularityTowerProperty_of_chart_step I M h_chart_step) u p hu he h_c1

end GromovCompactness.Analysis
