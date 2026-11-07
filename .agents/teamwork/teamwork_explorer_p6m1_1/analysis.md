# Technical Analysis: Contract A01 (`scalar_mean_value_inequality`)

**Target Contract**: `A01` (`scalar_mean_value_inequality`, Item #1 in `COMPLETION_PLAN.md` §3.1)  
**File Location**: `GromovCompactness/Analysis/Monotonicity.lean` (lines 78–96)  
**Primary Mathematical References**:
- Mikhail Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Math. 82 (1985), §1.2 & §1.3.
- Dusa McDuff & Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology* (2012), Lemma 4.3.2 & Prop 4.4.1.
- Sergei Ivashkovich & Vsevolod Shevchishin, *Complex Curves in Almost-Complex Manifolds and Meromorphic Hulls*, arXiv:math/9912046 (1999), Lemma 2.1.1 & §2.1.
- Specification: `gromov_compactness.pdf` §4.1 (Contract A01).

---

## 1. Codebase Location, Current Type Signature, and Proof Status

### Location
Contract A01 is defined in:
`GromovCompactness/Analysis/Monotonicity.lean` (lines 78–96).  
(Note: There is no standalone `MeanValueInequality.lean`; it resides in `Monotonicity.lean` alongside topological lemmas for `target_monotonicity`.)

### Current Lean 4 Type Signature
```lean
theorem scalar_mean_value_inequality
    (b : ℝ) (hb : 0 ≤ b) (c : ℝ := 0) (hc : 0 ≤ c := by norm_num) :
    ∃ (η C : ℝ), 0 < η ∧ 0 < C ∧
    ∀ (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ),
      (∀ z, 0 ≤ e z) →
      ContinuousOn e (Metric.closedBall 0 r) →
      ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r) →
      (∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 - c * (e z) ≤ laplacian2D e z) →
      (∫ w in Metric.ball (0 : ℂ) r, e w) < η →
      (∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2), e z ≤ C * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w))
```

### Current Proof Status
The proof in `Monotonicity.lean` (lines 88–96) currently stands as:
```lean
  use 1, 16
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro r hr e he_nonneg he_cont he_diff he_subharm he_int z hz
  by_cases h_zero : (∫ w in Metric.ball (0 : ℂ) r, e w) = 0
  · have he_z_zero := mvi_branch_zero r hr e he_nonneg he_cont h_zero z hz
    rw [he_z_zero, h_zero]
    simp
  · sorry
```

**Key Observations**:
1. **Direct `sorry` on line 95**: While the vanishing-energy base case `h_zero` is cleanly proved via `mvi_branch_zero` (lines 46–72), the core non-zero energy branch is an open `sorry`.
2. **Hardcoded dummy constants**: The candidate instantiation `use 1, 16` is mathematically invalid for general $b, c$. As $b \to \infty$ or $c \to \infty$, the threshold $\eta$ must scale inversely with $b$ and $c$ (specifically, $\eta \sim \frac{\pi}{16(b+1)(c+1)}$). Since $\eta$ and $C$ are existentially quantified *after* $(b, hb, c, hc)$, $\eta(b, c)$ and $C(b, c)$ can and must depend on $b$ and $c$.

---

## 2. Handling of P0-4: Differential Inequality & Linear Absorption

### Context in `COMPLETION_PLAN.md`
Row **P0-4** states:
> *"`scalar_mean_value_inequality` assumes `-b e² ≤ Δe`, but `bochner_differential_inequality` provides `-b e² - c e ≤ Δe`. The two cannot be composed for `epsilon_regularity`.*  
> *Required fix: Generalize A01 to `Δe ≥ -b e² - c e` (standard: absorb via `r ≤ 1`), or strengthen A02 to drop `c`. Acceptance: A03 is provable from A01 + A02 by statement inspection."*

### Current Implementation Assessment
In the Phase 5 Milestone 3 remediation, Option 1 was adopted:
1. `scalar_mean_value_inequality` was augmented with optional default arguments:  
   `(c : ℝ := 0) (hc : 0 ≤ c := by norm_num)`.
2. The subharmonic hypothesis was generalized to:  
   `∀ z ∈ Metric.ball 0 r, -b * (e z)^2 - c * (e z) ≤ laplacian2D e z`.
3. Downstream calls in `EpsilonRegularity.lean:77-78` directly compose:
   ```lean
   obtain ⟨b, c, hb, hc, h_boch⟩ := bochner_differential_inequality (M := M) I
   obtain ⟨η, C, hη, hC, h_smv⟩ := scalar_mean_value_inequality b hb c hc
   ```
4. Backward compatibility is completely preserved: regression tests `test_scalar_mean_value_inequality_default_args` in `ChallengeMilestone3Phase5.lean:232` and `ChallengePhase2ModelA.lean:55` invoke `scalar_mean_value_inequality b hb` where $c = 0$ is inferred by default.

### Mathematical Mechanism of Linear Absorption
In Heinz's trick:
1. On the local ball $B_\rho(z_0)$ centered at the maximum of $(r - |z|)^2 e(z)$, $e(w) \le 4 e(z_0)$ for all $w \in B_\rho(z_0)$.
2. The differential inequality on $B_\rho(z_0)$ becomes:
   $$\Delta e(w) \ge -b (4 e_0)^2 - c (4 e_0) = - (16 b e_0^2 + 4 c e_0) =: -K.$$
3. Applying the subharmonic comparison with quadratic correction $v(w) = e(w) + \frac{K}{4} |w - z_0|^2$ on concentric disks of radius $t \le \rho$ yields:
   $$e_0 \le \frac{1}{\pi t^2} \int_{B_t(z_0)} e + \left(2 b e_0 + \frac{1}{2} c\right) e_0 t^2.$$
4. **Absorption**: If we set $\eta = \frac{\pi}{16(b+1)(c+1)}$, then:
   - When $c = 0$ (pure quadratic), if $(2 b e_0) \rho^2 > 1/2$, choosing $t = (4 b e_0)^{-1/2} < \rho$ forces $\int_{B_r} e \ge \frac{\pi}{8b} > \eta$, which contradicts $\int_{B_r} e < \eta$. Thus only Case A ($(2 b e_0) \rho^2 \le 1/2$) can occur, giving $(2\rho)^2 e_0 \le \frac{8}{\pi} \int_{B_r} e$ without any restriction on $r > 0$.
   - When $c > 0$, the linear term is similarly controlled because $e_0$ is forced to be small by $\eta$, preventing the quadratic coefficient from overcoming the mean value.

---

## 3. Inventory of Relevant Helper Lemmas

### Existing in `GromovCompactness`
- `laplacian2D (e : ℂ → ℝ) (z : ℂ)` (`Monotonicity.lean:41-42`):  
  Defined as `(iteratedFDeriv ℝ 2 e z) ![1, 1] + (iteratedFDeriv ℝ 2 e z) ![Complex.I, Complex.I]`.
- `mvi_branch_zero` (`Monotonicity.lean:46-72`):  
  Zero energy branch completely proved (`∫ e = 0 → e = 0` on `closedBall 0 (r/2)`).
- `laplacian2D_zero_of_not_diff`, `laplacian2D_of_iterated_one_zero`, `laplacian2D_const` (`Bochner.lean:46-77`).
- `laplacian2D_eq_trace_iteratedFDeriv`, `laplacian2D_continuousOn_of_contDiffOn` (`Bochner.lean:111-142`).
- `integral_translate_ball`, `ball_translate_to_closedBall` (`EpsilonRegularity.lean:42-59`).
- `TestA04Pieces.lean` (machine-verified zero-sorry polar/circle integral calculations).

### Relevant Mathlib v4.16 Modules
- `Mathlib.Topology.Order.Compact`:  
  - `isCompact_closedBall`: compact balls in metric spaces.
  - `IsCompact.exists_forall_ge` / `IsCompact.exists_isMaxOn`: extreme value theorem for continuous functions on compact spaces.
- `Mathlib.Analysis.SpecialFunctions.PolarCoord`:  
  - `Complex.integral_comp_polarCoord_symm`: polar coordinate change of variables on $\mathbb{C}$.
  - `polarCoord_target`, `polarCoord_source_ae_eq_univ`.
- `Mathlib.Analysis.Calculus.ContDiff`:  
  - `ContDiffOn ℝ 2`, `iteratedFDerivWithin_of_isOpen`.
- `Mathlib.MeasureTheory.Integral.SetIntegral`:  
  - `setIntegral_nonneg`, `setIntegral_mono`.

*(Note: `InnerProductSpace.HarmonicOnNhd` cited in informal notes does NOT exist in Mathlib v4.16; the subharmonic mean-value property must be formalized directly via quadratic potential comparison or circle averages).*

---

## 4. Model A Decomposition: 10 Fine-Grained Sub-Lemmas

To enable automated/assisted proof synthesis using local Gemma 9B (`gemma-lean4:latest`) and standard Lean tactics (`positivity`, `linarith`, `nlinarith`, `simp`, `ring`), we decompose Contract A01 into 10 modular lemmas:

### Sub-Lemma 1: `laplacian2D_sq_dist` (Quadratic Potential Laplacian)
```lean
/-- The Laplacian of the squared Euclidean distance to a fixed point in ℂ equals 4 everywhere. -/
lemma laplacian2D_sq_dist (z₀ : ℂ) (w : ℂ) :
    laplacian2D (fun z => ‖z - z₀‖^2) w = 4
```
*Tactic profile*: `simp [laplacian2D, norm_sq]`, `ring`. Gemma 9B leaf closure.

### Sub-Lemma 2: `laplacian2D_add` and `laplacian2D_smul` (Linearity)
```lean
/-- Linearity of laplacian2D under addition. -/
lemma laplacian2D_add (f g : ℂ → ℝ) (z : ℂ)
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    laplacian2D (fun w => f w + g w) z = laplacian2D f z + laplacian2D g z

/-- Scaling of laplacian2D by a constant factor. -/
lemma laplacian2D_smul (c : ℝ) (f : ℂ → ℝ) (z : ℂ)
    (hf : ContDiffAt ℝ 2 f z) :
    laplacian2D (fun w => c * f w) z = c * laplacian2D f z
```
*Tactic profile*: Follows from `iteratedFDeriv_add` and `iteratedFDeriv_smul`.

### Sub-Lemma 3: `subharmonic_mean_value_le` (Subharmonic Property on Disks)
```lean
/-- Sub-mean-value inequality for functions with non-negative Laplacian on a disk:
the central value is bounded by the spatial average. -/
lemma subharmonic_mean_value_le (z₀ : ℂ) (R : ℝ) (hR : 0 < R) (v : ℂ → ℝ)
    (hv_cont : ContinuousOn v (Metric.closedBall z₀ R))
    (hv_diff : ContDiffOn ℝ 2 v (Metric.ball z₀ R))
    (hv_subharm : ∀ w ∈ Metric.ball z₀ R, 0 ≤ laplacian2D v w) :
    v z₀ ≤ (π * R^2)⁻¹ * ∫ w in Metric.ball z₀ R, v w
```
*Proof route*: Circle average $A(s) = \frac{1}{2\pi} \int_0^{2\pi} v(z_0 + s e^{i\theta}) d\theta$ has $A'(s) = \frac{1}{2\pi s} \int_{B_s} \Delta v \ge 0$, so $v(z_0) = A(0) \le A(s)$, integrating $2\pi s ds$ yields the result.

### Sub-Lemma 4: `integral_sq_dist_ball` (Integral of Distance Potential)
```lean
/-- The integral of squared distance ‖w - z₀‖² over a disk of radius R equals π R⁴ / 2. -/
lemma integral_sq_dist_ball (z₀ : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    ∫ w in Metric.ball z₀ R, ‖w - z₀‖^2 = π * R^4 / 2
```
*Proof route*: Polar coordinates via `Complex.integral_comp_polarCoord_symm`: $\int_0^{2\pi} d\theta \int_0^R s^3 ds = 2\pi (R^4/4) = \pi R^4 / 2$.

### Sub-Lemma 5: `mean_value_le_of_laplacian_ge_neg_const` (Quadratic Potential Comparison)
```lean
/-- For a C² function with Δe ≥ -K on a disk, the central value is bounded by the
integral average plus K R² / 8. -/
lemma mean_value_le_of_laplacian_ge_neg_const
    (z₀ : ℂ) (R : ℝ) (hR : 0 < R) (e : ℂ → ℝ) (K : ℝ)
    (he_cont : ContinuousOn e (Metric.closedBall z₀ R))
    (he_diff : ContDiffOn ℝ 2 e (Metric.ball z₀ R))
    (he_lap : ∀ w ∈ Metric.ball z₀ R, -K ≤ laplacian2D e w) :
    e z₀ ≤ (π * R^2)⁻¹ * (∫ w in Metric.ball z₀ R, e w) + K * R^2 / 8
```
*Proof route*: Apply `subharmonic_mean_value_le` to $v(w) = e(w) + \frac{K}{4} \|w - z_0\|^2$. By Sub-lemmas 1 and 2, $\Delta v = \Delta e + K \ge 0$. Using Sub-lemma 4, $( \pi R^2 )^{-1} \int_{B_R} \frac{K}{4} \|w - z_0\|^2 = \frac{K R^2}{8}$.

### Sub-Lemma 6: `heinz_maximum_exists` (Attainment of Maximum)
```lean
/-- The weighted function w ↦ (r - ‖w‖)² e(w) attains its maximum on the closed ball of radius r. -/
lemma heinz_maximum_exists (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r)) :
    ∃ z₀ ∈ Metric.closedBall (0 : ℂ) r,
      ∀ w ∈ Metric.closedBall (0 : ℂ) r,
        (r - ‖w‖)^2 * e w ≤ (r - ‖z₀‖)^2 * e z₀
```
*Tactic profile*: Compactness of `closedBall 0 r` + `IsCompact.exists_forall_ge`.

### Sub-Lemma 7: `heinz_maximum_interior` (Maximum in Open Ball)
```lean
/-- If the integral of e is strictly positive, the maximum of (r - ‖w‖)² e(w) must occur
strictly in the interior Metric.ball 0 r, and its central value e(z₀) is strictly positive. -/
lemma heinz_maximum_interior (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (h_pos : 0 < ∫ w in Metric.ball (0 : ℂ) r, e w)
    (z₀ : ℂ) (hz₀ : z₀ ∈ Metric.closedBall 0 r)
    (h_max : ∀ w ∈ Metric.closedBall 0 r, (r - ‖w‖)^2 * e w ≤ (r - ‖z₀‖)^2 * e z₀) :
    z₀ ∈ Metric.ball (0 : ℂ) r ∧ 0 < e z₀
```
*Proof route*: On boundary $\|w\| = r$, $(r - \|w\|)^2 = 0$. If $e(z_0) = 0$ or $\|z_0\| = r$, maximum is 0, so $e \equiv 0$, contradicting $\int e > 0$.

### Sub-Lemma 8: `heinz_ball_subset_and_bound` (Heinz Local Neighborhood Control)
```lean
/-- On the ball B_ρ(z₀) of radius ρ = (r - ‖z₀‖)/2 centered at the Heinz maximum,
the ball is contained in B_r(0), and e is pointwise bounded by 4 * e(z₀). -/
lemma heinz_ball_subset_and_bound (r : ℝ) (z₀ : ℂ) (hz₀ : z₀ ∈ Metric.ball (0 : ℂ) r)
    (e : ℂ → ℝ) (he_nonneg : ∀ z, 0 ≤ e z)
    (h_max : ∀ w ∈ Metric.closedBall 0 r, (r - ‖w‖)^2 * e w ≤ (r - ‖z₀‖)^2 * e z₀) :
    let ρ := (r - ‖z₀‖) / 2
    Metric.closedBall z₀ ρ ⊆ Metric.ball 0 r ∧
    ∀ w ∈ Metric.closedBall z₀ ρ, e w ≤ 4 * e z₀
```
*Tactic profile*: Triangle inequality `‖w‖ ≤ ‖z₀‖ + ρ = (r + ‖z₀‖)/2 < r`, `r - ‖w‖ ≥ ρ`, $\rho^2 e(w) \le (r - \|w\|)^2 e(w) \le 4\rho^2 e(z_0)$, divide by $\rho^2 > 0$. Ideal for `linarith`, `nlinarith`, `positivity`.

### Sub-Lemma 9: `heinz_central_value_bound` (Real Variable Algebraic Optimization)
```lean
/-- Heinz algebraic optimization: from the quadratic differential bound on B_ρ(z₀)
and small total energy E < π / (16 (b + 1) (c + 1)), the maximum M = 4 ρ² e₀ is bounded by (8/π) E. -/
lemma heinz_central_value_bound (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (e₀ : ℝ) (he₀ : 0 < e₀) (ρ : ℝ) (hρ : 0 < ρ) (E : ℝ) (hE : 0 ≤ E)
    (h_smv : ∀ t ∈ Set.Ioc 0 ρ, e₀ ≤ (π * t^2)⁻¹ * E + (2 * b * e₀ + c / 2) * e₀ * t^2)
    (h_energy : E < π / (16 * (b + 1) * (c + 1))) :
    (2 * ρ)^2 * e₀ ≤ (8 / π) * E
```
*Proof route*: If $(2 b e_0 + c/2) \rho^2 \le 1/2$, test $t = \rho$. If $(2 b e_0 + c/2) \rho^2 > 1/2$, choose $t < \rho$ making the factor $1/2$; dividing by $e_0$ forces $E \ge \pi / (8(b+1))$, contradicting $h_{energy}$.

### Sub-Lemma 10: `heinz_transfer_to_half_ball` (Transfer to Target Half-Ball)
```lean
/-- Bounding e(z) on the concentric half-radius ball Metric.closedBall 0 (r/2)
from the Heinz maximum bound (r - ‖z₀‖)² e(z₀) ≤ (8/π) ∫_{B_r} e. -/
lemma heinz_transfer_to_half_ball (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z) (z₀ : ℂ) (hz₀ : z₀ ∈ Metric.closedBall 0 r)
    (h_max : ∀ w ∈ Metric.closedBall 0 r, (r - ‖w‖)^2 * e w ≤ (r - ‖z₀‖)^2 * e z₀)
    (M_bound : (r - ‖z₀‖)^2 * e z₀ ≤ (8 / π) * ∫ w in Metric.ball 0 r, e w) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
      e z ≤ (32 / π) * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w)
```
*Tactic profile*: For $z \in \overline{B_{r/2}}$, $r - \|z\| \ge r/2$, so $(r^2/4) e(z) \le (r - \|z\|)^2 e(z) \le M \le (8/\pi) E$, multiply by $4 r^{-2}$ to get $e(z) \le (32/\pi) r^{-2} E$. Pure `linarith`, `nlinarith`.

---

## 5. Master Theorem Assembly

Using Sub-lemmas 1–10, the proof of `scalar_mean_value_inequality` in `Monotonicity.lean` reduces to:
```lean
theorem scalar_mean_value_inequality
    (b : ℝ) (hb : 0 ≤ b) (c : ℝ := 0) (hc : 0 ≤ c := by norm_num) :
    ∃ (η C : ℝ), 0 < η ∧ 0 < C ∧
    ∀ (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ),
      (∀ z, 0 ≤ e z) →
      ContinuousOn e (Metric.closedBall 0 r) →
      ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r) →
      (∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 - c * (e z) ≤ laplacian2D e z) →
      (∫ w in Metric.ball (0 : ℂ) r, e w) < η →
      (∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2), e z ≤ C * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w)) := by
  let η := π / (16 * (b + 1) * (c + 1))
  let C := (32 : ℝ) / π
  use η, C
  refine ⟨by positivity, by positivity, ?_⟩
  intro r hr e he_nonneg he_cont he_diff he_subharm he_int z hz
  by_cases h_zero : (∫ w in Metric.ball (0 : ℂ) r, e w) = 0
  · have he_z_zero := mvi_branch_zero r hr e he_nonneg he_cont h_zero z hz
    rw [he_z_zero, h_zero]
    simp
  · have h_pos : 0 < ∫ w in Metric.ball (0 : ℂ) r, e w :=
      lt_of_le_of_ne (setIntegral_nonneg isOpen_ball.measurableSet (fun w _ => he_nonneg w)) (Ne.symm h_zero)
    rcases heinz_maximum_exists r hr e he_nonneg he_cont with ⟨z₀, hz₀_closed, h_max⟩
    have ⟨hz₀_ball, he₀_pos⟩ := heinz_maximum_interior r hr e he_nonneg he_cont h_pos z₀ hz₀_closed h_max
    let ρ := (r - ‖z₀‖) / 2
    have hρ_pos : 0 < ρ := by
      have : ‖z₀‖ < r := Metric.mem_ball.mp hz₀_ball
      linarith
    have ⟨h_sub, h_bound⟩ := heinz_ball_subset_and_bound r z₀ hz₀_ball e he_nonneg h_max
    have h_smv : ∀ t ∈ Set.Ioc 0 ρ, e z₀ ≤ (π * t^2)⁻¹ * (∫ w in Metric.ball (0 : ℂ) r, e w) + (2 * b * e z₀ + c / 2) * e z₀ * t^2 := by
      intro t ht
      have ht_pos : 0 < t := ht.1
      have ht_le : t ≤ ρ := ht.2
      have hBt_sub : Metric.ball z₀ t ⊆ Metric.ball 0 r := by
        intro w hw
        have hw_le : ‖w - z₀‖ < t := Metric.mem_ball.mp hw
        have hw_le' : ‖w - z₀‖ ≤ ρ := hw_le.le.trans ht_le
        exact h_sub (Metric.mem_closedBall.mpr hw_le')
      have hK_bound : ∀ w ∈ Metric.ball z₀ t, -(16 * b * (e z₀)^2 + 4 * c * (e z₀)) ≤ laplacian2D e w := by
        intro w hw
        have hw_in_sub : w ∈ Metric.ball 0 r := hBt_sub hw
        have hw_le_4e0 : e w ≤ 4 * e z₀ := h_bound w (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hw).le.trans ht_le)
        have h_subh := he_subharm w hw_in_sub
        have he_w_nonneg : 0 ≤ e w := he_nonneg w
        nlinarith
      have he_t_cont : ContinuousOn e (Metric.closedBall z₀ t) := by
        apply he_cont.mono
        intro w hw
        have : w ∈ Metric.ball 0 r := by
          have hw_le : ‖w - z₀‖ ≤ t := Metric.mem_closedBall.mp hw
          have : ‖w - z₀‖ ≤ ρ := hw_le.trans ht_le
          exact h_sub (Metric.mem_closedBall.mpr this)
        exact Metric.ball_subset_closedBall this
      have he_t_diff : ContDiffOn ℝ 2 e (Metric.ball z₀ t) := he_diff.mono hBt_sub
      have h_smv_t := mean_value_le_of_laplacian_ge_neg_const z₀ t ht_pos e (16 * b * (e z₀)^2 + 4 * c * (e z₀)) he_t_cont he_t_diff hK_bound
      have h_int_mono : ∫ w in Metric.ball z₀ t, e w ≤ ∫ w in Metric.ball 0 r, e w :=
        setIntegral_mono_set (he_cont.integrableOn_compact (isCompact_closedBall 0 r)).integrableOn hBt_sub (Filter.Eventually.of_forall (fun w => he_nonneg w))
      nlinarith
    have h_M := heinz_central_value_bound b c hb hc (e z₀) he₀_pos ρ hρ_pos (∫ w in Metric.ball 0 r, e w) (h_pos.le) h_smv he_int
    exact heinz_transfer_to_half_ball r hr e he_nonneg z₀ hz₀_closed h_max h_M z hz
```

---

## 6. Recommendations for Worker Execution in Phase 6 Milestone 1

1. **Keep `Monotonicity.lean` clean**: Implement Sub-lemmas 1–10 directly in `GromovCompactness/Analysis/Monotonicity.lean` right before `scalar_mean_value_inequality`.
2. **Local Prover Utilization**: Sub-lemmas 1 (`laplacian2D_sq_dist`), 4 (`integral_sq_dist_ball`), 6 (`heinz_maximum_exists`), 7 (`heinz_maximum_interior`), 8 (`heinz_ball_subset_and_bound`), and 10 (`heinz_transfer_to_half_ball`) are purely metric and algebraic and should be closed directly by Gemma 9B with `linarith`, `nlinarith`, `ring`, `positivity`.
3. **Core Analysis Effort**: Focus worker proving attention on Sub-lemma 3 (`subharmonic_mean_value_le`) and Sub-lemma 9 (`heinz_central_value_bound`).
4. **Zero-`sorryAx` Census Verification**: Once proved, verify that `GromovCompactness.Analysis.scalar_mean_value_inequality` depends strictly on standard Lean 4 axioms (`[propext, Classical.choice, Quot.sound]`).
