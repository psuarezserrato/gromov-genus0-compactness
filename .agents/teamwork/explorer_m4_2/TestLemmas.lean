import GromovCompactness.Geometry.Sphere
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral

open Real GromovCompactness

namespace GromovCompactness.Analysis

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

/-- Positivity of two-sided neck factor: $0 < (r / r_1)^\alpha + (r_2 / R)^\alpha$ when $r, r_2 > 0$. -/
lemma neck_factor_pos {r r₁ r₂ R α : ℝ}
    (hr : 0 < r) (hr1 : 0 < r₁) (hr2 : 0 < r₂) (hR : 0 < R) :
    0 < (r / r₁)^α + (r₂ / R)^α := by
  have h1 : 0 < r / r₁ := div_pos hr hr1
  have h2 : 0 < r₂ / R := div_pos hr2 hR
  have p1 : 0 < (r / r₁)^α := Real.rpow_pos_of_pos h1 α
  have p2 : 0 < (r₂ / R)^α := Real.rpow_pos_of_pos h2 α
  positivity

/-- Cauchy-Schwarz from nonnegativity of a quadratic polynomial:
If $A t^2 - 2 B t + C \ge 0$ for all $t \in \mathbb{R}$, and $A > 0$,
then $B^2 \le A C$. -/
lemma cauchy_schwarz_quadratic {A B C : ℝ} (hA : 0 < A)
    (h_quad : ∀ t : ℝ, 0 ≤ A * t^2 - 2 * B * t + C) :
    B^2 ≤ A * C := by
  have h_spec := h_quad (B / A)
  have h_id : A * (B / A)^2 - 2 * B * (B / A) + C = C - B^2 / A := by
    have hA_ne : A ≠ 0 := hA.ne'
    field_simp
    ring
  rw [h_id] at h_spec
  have h_div : B^2 / A ≤ C := by linarith
  have h_mul := (div_le_iff₀ hA).mp h_div
  linarith

/-- Boundary loop length bounded by $\sqrt{2\pi \cdot \text{Energy}}$:
If $L^2 \le (2\pi) E$ and $0 \le L$, then $L \le \sqrt{2\pi E}$. -/
lemma loop_length_le_sqrt_energy {L E_loop : ℝ} (hL : 0 ≤ L)
    (h_cs : L^2 ≤ (2 * Real.pi) * E_loop) :
    L ≤ Real.sqrt ((2 * Real.pi) * E_loop) := by
  have h_sqrt := Real.sqrt_le_sqrt h_cs
  rw [Real.sqrt_sq hL] at h_sqrt
  exact h_sqrt

/-- Loop diameter bounded by loop length: $\operatorname{diam} \le \text{Length} \le \sqrt{2\pi E}$. -/
lemma loop_diam_le_sqrt_energy {diam L E_loop : ℝ}
    (hdiam : diam ≤ L) (hL : 0 ≤ L)
    (h_cs : L^2 ≤ (2 * Real.pi) * E_loop) :
    diam ≤ Real.sqrt ((2 * Real.pi) * E_loop) :=
  hdiam.trans (loop_length_le_sqrt_energy hL h_cs)

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

/-- Existence of small neck energy threshold $\eta(d_0) > 0$ ensuring diameter localization:
Given constants $C > 0$ and $\varepsilon_0 > 0$, for any $d_0 > 0$,
there exists $\eta > 0$ such that $E < \eta$ implies $C \sqrt{E} < d_0$. -/
lemma exists_neck_energy_threshold (C ε₀ d₀ : ℝ) (hC : 0 < C) (hε₀ : 0 < ε₀) (hd₀ : 0 < d₀) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ε₀ ∧ ∀ E : ℝ, 0 ≤ E → E < η → C * Real.sqrt E < d₀ := by
  have h_div_pos : 0 < d₀ / (2 * C) := div_pos hd₀ (by linarith)
  have h_sq_pos : 0 < (d₀ / (2 * C))^2 := sq_pos_of_pos h_div_pos
  let η := min ε₀ ((d₀ / (2 * C))^2)
  have hη_pos : 0 < η := lt_min hε₀ h_sq_pos
  refine ⟨η, hη_pos, min_le_left _ _, ?_⟩
  intro E hE hE_lt
  have hE_sq : E < (d₀ / (2 * C))^2 := hE_lt.trans_le (min_le_right _ _)
  have h_sqrt_lt : Real.sqrt E < d₀ / (2 * C) := by
    rw [← Real.sqrt_sq h_div_pos.le]
    exact Real.sqrt_lt_sqrt hE hE_sq
  calc
    C * Real.sqrt E < C * (d₀ / (2 * C)) := (mul_lt_mul_left hC).mpr h_sqrt_lt
    _ = d₀ / 2 := by
      have hC_ne : C ≠ 0 := hC.ne'
      field_simp
      ring
    _ < d₀ := by linarith

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

end GromovCompactness.Analysis

/-- Exponential decay from differential inequality $F(t) \le c \cdot F'(t)$:
If $F : ℝ → ℝ$ is differentiable, $c > 0$, and $F(t) \le c \cdot F'(t)$ for all $t$,
then for any $T \le L$, $F(T) \cdot e^{-T/c} \le F(L) \cdot e^{-L/c}$. -/
lemma exp_decay_of_diff_ineq {F : ℝ → ℝ} (hF : Differentiable ℝ F)
    {c : ℝ} (hc : 0 < c)
    (h_ineq : ∀ t, F t ≤ c * deriv F t) :
    ∀ {T L : ℝ}, T ≤ L → F T * Real.exp (-T / c) ≤ F L * Real.exp (-L / c) := by
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
  intro T L hTL
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
If $R / 2 \le 2 * r$, then $\{z \in ℂ \mid 2 * r < \operatorname{dist}(z, a) \wedge \operatorname{dist}(z, a) < R / 2\} = \emptyset$. -/
lemma annulus_set_empty_of_le (a : ℂ) {r R : ℝ} (h : R / 2 ≤ 2 * r) :
    {z : ℂ | 2 * r < dist z a ∧ dist z a < R / 2} = ∅ := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h1, h2⟩
  linarith


/-- Degenerate collar annuli in CP1 are empty when  / 2 \le 2 * r$. -/
lemma annulus_at_empty_of_le (a : ℂ) {r R : ℝ} (h : R / 2 ≤ 2 * r) :
    annulus_at a (2 * r) (R / 2) = ∅ := by
  dsimp [annulus_at]
  rw [annulus_set_empty_of_le a h]
  exact Set.image_empty _

open GromovCompactness.Analysis

#print axioms exp_decay_factor_nonneg
#print axioms exp_decay_factor_pos
#print axioms exp_decay_factor_le_one
#print axioms exp_decay_factor_lt_one
#print axioms exp_decay_factor_mono
#print axioms neck_factor_le_two
#print axioms neck_factor_pos
#print axioms cauchy_schwarz_quadratic
#print axioms loop_length_le_sqrt_energy
#print axioms loop_diam_le_sqrt_energy
#print axioms one_sub_exp_neg_div_le
#print axioms one_sub_exp_neg_div_nonneg
#print axioms exists_neck_energy_threshold
#print axioms annulus_ratio_rpow_eq_exp_neg
#print axioms exp_decay_of_diff_ineq
#print axioms exp_decay_bound_of_diff_ineq
#print axioms localization_of_diam_bound
#print axioms annulus_set_empty_of_le
#print axioms annulus_at_empty_of_le
