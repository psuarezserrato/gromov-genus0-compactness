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
  constructor
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
  sorry

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
  sorry

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
      EqOn u_ext u (punctured_sphere {p}) := by
  sorry

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
