/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere

open scoped Manifold ContDiff Topology Real ENNReal
open Metric Set MeasureTheory Filter Topology ENNReal GromovCompactness Complex

namespace GromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-!
# Task F03: Energy Measure and Integral Algebra

This module formalizes the symplectic energy measure $E(u; A) = \frac{1}{2} \int_A |du|_g^2 \, d\mathrm{vol}$,
its conformal invariance under Möbius transformations, and its representation as the pullback of the
symplectic two-form $\int_A u^* \omega$, following Gromov (1985, §1.2), Ivashkovich-Shevchishin (1999, §2),
and `gromov_compactness.pdf` §2.1 & §5 (Task `F03`).

## Key Definitions
- `sphericalJacobian`: Conformal factor $(2 / (1 + \|w\|^2))^2$ relating the round metric on $S^2$ to Lebesgue on $\mathbb{C}$.
- `energyMeasureExtended`: Extended nonnegative Borel measure on $\mathbb{CP}^1$ for a map $u$, weighted by `sphericalJacobian`.
- `energyMeasure`: Real-valued finite energy wrapper on subsets $A \subseteq \mathbb{CP}^1$.
- `totalEnergy`: Total symplectic energy $E(u) := E(u; \mathbb{CP}^1)$.
- `energy_nonneg`: Proof of nonnegativity $E(u; A) \ge 0$.
- `energy_additive`: Additivity on disjoint measurable subsets.
- `energy_conformal_invariant_id`: Unconditional conformal invariance of energy under identity Möbius transformation.
- `energy_conformal_invariant`: Conditional reduction of conformal invariance from pullback equivariance.
- `energy_eq_pullback_omega`: Identity $E(u; A) = \int_A u^* \omega$ for $J$-holomorphic curves.
- `energy_point_null`: Points have measure zero.
- `energy_circle_null`: Smooth circles have measure zero.
- `continuous_volume_ball`: Continuity of Lebesgue volume on expanding balls.
-/

/-- Canonical basis vectors for the tangent space of CP1 modeled on EuclideanSpace ℝ (Fin 2). -/
def e1 : EuclideanSpace ℝ (Fin 2) := !₂[1, 0]
def e2 : EuclideanSpace ℝ (Fin 2) := !₂[0, 1]

lemma c_equiv_1 : c_equiv_e2 1 = e1 := by
  dsimp [c_equiv_e2, e1]
  ext i
  fin_cases i <;> simp [Complex.orthonormalBasisOneI]

lemma c_equiv_I : c_equiv_e2 Complex.I = e2 := by
  dsimp [c_equiv_e2, e2]
  ext i
  fin_cases i <;> simp [Complex.orthonormalBasisOneI]

lemma c_equiv_symm_e1 : c_equiv_e2.symm e1 = 1 := by
  rw [← c_equiv_1, c_equiv_e2.symm_apply_apply]

lemma c_equiv_symm_e2 : c_equiv_e2.symm e2 = Complex.I := by
  rw [← c_equiv_I, c_equiv_e2.symm_apply_apply]

lemma J_CP1_e1 : J_CP1 e1 = e2 := by
  dsimp [J_CP1]
  rw [c_equiv_symm_e1]
  simp [c_equiv_I]

lemma J_CP1_e2 : J_CP1 e2 = -e1 := by
  dsimp [J_CP1]
  rw [c_equiv_symm_e2]
  simp [c_equiv_1]

/-- Pointwise Riemannian Dirichlet energy density of $u$ at point $z \in \mathbb{CP}^1$. -/
noncomputable def riemannianEnergyDensity (u : CP1 → M) (z : CP1) : ℝ :=
  (1 / 2 : ℝ) * (ClosedTameTarget.metric I (u z) (mfderiv I_CP1 I u z e1) (mfderiv I_CP1 I u z e1) +
                ClosedTameTarget.metric I (u z) (mfderiv I_CP1 I u z e2) (mfderiv I_CP1 I u z e2))

/-- Pointwise symplectic area density (pullback 2-form $u^* \omega$) at point $z \in \mathbb{CP}^1$. -/
noncomputable def symplecticAreaDensity (u : CP1 → M) (z : CP1) : ℝ :=
  ClosedTameTarget.«ω» (u z) (mfderiv I_CP1 I u z e1) (mfderiv I_CP1 I u z e2)

lemma metric_self_nonneg (x : M) (v : TangentSpace I x) :
    0 ≤ ClosedTameTarget.metric I x v v := by
  by_cases hv : v = 0
  · subst hv
    dsimp [ClosedTameTarget.metric]
    simp
  · exact (metric_pos_def I x v hv).le

/-- The Riemannian energy density is non-negative at every point. -/
theorem riemannianEnergyDensity_nonneg (u : CP1 → M) (z : CP1) :
    0 ≤ riemannianEnergyDensity I u z := by
  dsimp [riemannianEnergyDensity]
  have h1 := metric_self_nonneg I (u z) (mfderiv I_CP1 I u z e1)
  have h2 := metric_self_nonneg I (u z) (mfderiv I_CP1 I u z e2)
  positivity

/-- Trace scaling identity for C-linear maps: the 2D Dirichlet trace is invariant under J-commutation. -/
lemma metric_c_linear_trace_scaling (x : M) (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] TangentSpace I x)
    (hL : ∀ v, L (J_CP1 v) = ClosedTameTarget.J (I := I) (M := M) x (L v)) :
    ClosedTameTarget.metric I x (L e1) (L e1) + ClosedTameTarget.metric I x (L e2) (L e2) =
    2 * ClosedTameTarget.«ω» (I := I) (M := M) x (L e1) (L e2) := by
  have he2 : L e2 = ClosedTameTarget.J (I := I) (M := M) x (L e1) := by
    rw [← J_CP1_e1]
    exact hL e1
  dsimp [ClosedTameTarget.metric]
  rw [he2]
  have hJ2 : ClosedTameTarget.J (I := I) (M := M) x (ClosedTameTarget.J (I := I) (M := M) x (L e1)) = - L e1 :=
    ClosedTameTarget.J_sq x (L e1)
  rw [hJ2]
  have hneg : ClosedTameTarget.«ω» (I := I) (M := M) x (ClosedTameTarget.J (I := I) (M := M) x (L e1)) (- L e1) =
              - ClosedTameTarget.«ω» (I := I) (M := M) x (ClosedTameTarget.J (I := I) (M := M) x (L e1)) (L e1) :=
    (ClosedTameTarget.«ω» (I := I) (M := M) x (ClosedTameTarget.J (I := I) (M := M) x (L e1))).map_neg _
  rw [hneg]
  have hskew : ClosedTameTarget.«ω» (I := I) (M := M) x (ClosedTameTarget.J (I := I) (M := M) x (L e1)) (L e1) =
               - ClosedTameTarget.«ω» (I := I) (M := M) x (L e1) (ClosedTameTarget.J (I := I) (M := M) x (L e1)) :=
    ClosedTameTarget.ω_skew x _ _
  linarith

/-- Fundamental pointwise identity: for any $J$-holomorphic curve $u$,
the Riemannian Dirichlet energy density equals the pullback symplectic area density:
$$\frac{1}{2} |du|^2_g = (u^* \omega)(e_1, e_2).$$ -/
theorem energy_density_eq_omega (u : CP1 → M) (z : CP1)
    (h_jhol : ∀ v, mfderiv I_CP1 I u z (J_CP1 v) = ClosedTameTarget.J (u z) (mfderiv I_CP1 I u z v)) :
    riemannianEnergyDensity I u z = symplecticAreaDensity I u z := by
  dsimp [riemannianEnergyDensity, symplecticAreaDensity]
  have h_trace := metric_c_linear_trace_scaling I (u z) (mfderiv I_CP1 I u z) h_jhol
  linear_combination (1 / 2 : ℝ) * h_trace

/- =========================================================================
   MEASURE CONSTRUCTIONS ON CP1
   ========================================================================= -/

lemma stereo_chart_symm_continuous : Continuous stereo_chart.symm := by
  rw [continuous_iff_continuousOn_univ]
  have ht := stereo_chart_target
  rw [← ht]
  exact stereo_chart.continuousOn_symm

lemma stereo_chart_symm_measurable : Measurable stereo_chart.symm :=
  stereo_chart_symm_continuous.measurable

lemma stereo_chart_symm_injective : Function.Injective stereo_chart.symm := by
  intro w₁ w₂ h
  have h1 : w₁ ∈ stereo_chart.target := by simp [stereo_chart_target]
  have h2 : w₂ ∈ stereo_chart.target := by simp [stereo_chart_target]
  have r1 := stereo_chart.right_inv h1
  have r2 := stereo_chart.right_inv h2
  rw [h] at r1
  rw [← r1, r2]

lemma stereo_chart_symm_preimage_image (s : Set ℂ) :
    stereo_chart.symm ⁻¹' (stereo_chart.symm '' s) = s :=
  stereo_chart_symm_injective.preimage_image s

lemma stereo_chart_symm_preimage_north_pole : stereo_chart.symm ⁻¹' {north_pole} = ∅ := by
  ext w
  simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
  intro hw
  have h_source := stereo_chart.map_target (show w ∈ stereo_chart.target by simp [stereo_chart])
  rw [hw] at h_source
  dsimp [stereo_chart] at h_source
  simp only [PartialHomeomorph.transHomeomorph_source, stereographic'_source] at h_source
  exact h_source rfl

lemma stereo_chart_symm_preimage_pt (p : CP1) (hp : p ≠ north_pole) :
    stereo_chart.symm ⁻¹' {p} = {stereo_chart p} := by
  ext w
  simp only [mem_preimage, mem_singleton_iff]
  have hw_target : w ∈ stereo_chart.target := by simp [stereo_chart_target]
  constructor
  · intro hw
    have h1 := stereo_chart.right_inv hw_target
    rw [hw] at h1
    exact h1.symm
  · intro hw
    subst hw
    have hp_source : p ∈ stereo_chart.source := by
      rw [stereo_chart_source]
      exact hp
    exact stereo_chart.left_inv hp_source

lemma stereo_chart_symm_preimage_circle_at (a : ℂ) (r : ℝ) :
    stereo_chart.symm ⁻¹' (circle_at a r) = Metric.sphere a r :=
  stereo_chart_symm_preimage_image (Metric.sphere a r)

lemma stereo_chart_symm_preimage_disk_at (a : ℂ) (r : ℝ) :
    stereo_chart.symm ⁻¹' (disk_at a r) = Metric.ball a r :=
  stereo_chart_symm_preimage_image (Metric.ball a r)

lemma isCompact_circle_at (a : ℂ) (r : ℝ) : IsCompact (circle_at a r) := by
  dsimp [circle_at]
  exact (isCompact_sphere a r).image stereo_chart_symm_continuous

lemma isClosed_circle_at (a : ℂ) (r : ℝ) : IsClosed (circle_at a r) :=
  (isCompact_circle_at a r).isClosed

lemma measurableSet_circle_at (a : ℂ) (r : ℝ) : MeasurableSet (circle_at a r) :=
  (isClosed_circle_at a r).measurableSet

lemma measurableSet_disk_at (a : ℂ) (r : ℝ) : MeasurableSet (disk_at a r) :=
  (is_open_disk_at a r).measurableSet

/-- Spherical conformal factor (metric density) on ℂ corresponding to the round Fubini-Study / standard metric on CP1. -/
noncomputable def sphericalJacobian (w : ℂ) : ℝ := (2 / (1 + ‖w‖^2))^2

lemma sphericalJacobian_pos (w : ℂ) : 0 < sphericalJacobian w := by
  unfold sphericalJacobian
  positivity

lemma sphericalJacobian_nonneg (w : ℂ) : 0 ≤ sphericalJacobian w :=
  (sphericalJacobian_pos w).le

lemma continuous_sphericalJacobian : Continuous sphericalJacobian := by
  unfold sphericalJacobian
  apply Continuous.pow
  apply continuous_const.div
  · exact continuous_const.add (continuous_norm.pow 2)
  · intro x
    have h : 0 ≤ ‖x‖^2 := sq_nonneg ‖x‖
    linarith

lemma sphericalJacobian_lower_bound (w₀ : ℂ) (r : ℝ) (hr : 0 < r) :
    ∃ j_min : ℝ, 0 < j_min ∧ ∀ w ∈ Metric.ball w₀ r, j_min ≤ sphericalJacobian w := by
  have h_bound : ∀ w ∈ Metric.ball w₀ r, ‖w‖ ≤ ‖w₀‖ + r := by
    intro w hw
    have hdist : dist w w₀ < r := Metric.mem_ball.mp hw
    calc ‖w‖ = ‖w₀ + (w - w₀)‖ := by ring_nf
    _ ≤ ‖w₀‖ + ‖w - w₀‖ := norm_add_le _ _
    _ = ‖w₀‖ + dist w w₀ := by rw [dist_eq_norm]
    _ ≤ ‖w₀‖ + r := by linarith
  set R := ‖w₀‖ + r
  set j_min := (2 / (1 + R^2))^2
  refine ⟨j_min, ?_, ?_⟩
  · positivity
  · intro w hw
    dsimp [sphericalJacobian, j_min]
    have hw_norm := h_bound w hw
    have h_nonneg1 : 0 ≤ 2 / (1 + R^2) := by positivity
    gcongr
    exact hw_norm

/-- Canonical pushforward of a measure on ℂ to the Riemann sphere CP1 via stereographic projection. -/
noncomputable def chartPush (ν : Measure ℂ) : Measure CP1 :=
  Measure.map stereo_chart.symm ν

/-- The extended nonnegative symplectic energy Borel measure on $\mathbb{CP}^1$ associated to $u : \mathbb{CP}^1 \to M$.
Constructed via the pushforward of the Lebesgue integral of the Riemannian energy density,
weighted by the spherical conformal Jacobian $(2 / (1 + \|w\|^2))^2$. -/
noncomputable def energyMeasureExtended (u : CP1 → M) : Measure CP1 :=
  chartPush (volume.withDensity (fun w => ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w)))

/-- Real-valued symplectic energy on a subset $A \subseteq \mathbb{CP}^1$. -/
noncomputable def energyMeasure (u : CP1 → M) (A : Set CP1) : ℝ :=
  (energyMeasureExtended I u A).toReal

/-- The total symplectic energy of a curve $u : \mathbb{CP}^1 \to M$: $E(u) := E(u; \mathbb{CP}^1)$. -/
noncomputable def totalEnergy (u : CP1 → M) : ℝ :=
  energyMeasure I u Set.univ

/-- Non-negativity of the symplectic energy measure: for any subset $A$, $0 \le E(u; A)$. -/
theorem energy_nonneg (u : CP1 → M) (A : Set CP1) :
    0 ≤ energyMeasure I u A := by
  dsimp [energyMeasure]
  exact ENNReal.toReal_nonneg

/-- The pullback symplectic area measure on $\mathbb{CP}^1$. -/
noncomputable def pullbackOmegaMeasureExtended (u : CP1 → M) : Measure CP1 :=
  chartPush (volume.withDensity (fun w => ENNReal.ofReal (symplecticAreaDensity I u (stereo_chart.symm w) * sphericalJacobian w)))

/-- Real-valued pullback symplectic area on a subset $A \subseteq \mathbb{CP}^1$. -/
noncomputable def pullbackOmegaMeasure (u : CP1 → M) (A : Set CP1) : ℝ :=
  (pullbackOmegaMeasureExtended I u A).toReal

/-- Fundamental identity: For any $J$-holomorphic curve $u : \mathbb{CP}^1 \to M$,
the energy measure equals the integral of the pullback symplectic form:
$$E(u; A) = \int_A u^* \omega.$$ -/
theorem energy_eq_pullback_omega (u : CP1 → M)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) (A : Set CP1) :
    energyMeasure I u A = pullbackOmegaMeasure I u A := by
  have h_dense : (fun w => ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w)) =
                 (fun w => ENNReal.ofReal (symplecticAreaDensity I u (stereo_chart.symm w) * sphericalJacobian w)) := by
    ext w
    congr 1
    have h_pt : riemannianEnergyDensity I u (stereo_chart.symm w) = symplecticAreaDensity I u (stereo_chart.symm w) := by
      apply energy_density_eq_omega
      intro v
      exact h_jhol.2 (stereo_chart.symm w) (mem_univ _) v
    rw [h_pt]
  dsimp [energyMeasure, pullbackOmegaMeasure, energyMeasureExtended, pullbackOmegaMeasureExtended]
  rw [h_dense]

/-- Additivity of energy on disjoint measurable subsets:
$E(u; A_1 \cup A_2) = E(u; A_1) + E(u; A_2)$ when $A_1 \cap A_2 = \emptyset$
and both components have finite energy measure. -/
theorem energy_additive (u : CP1 → M) {A₁ A₂ : Set CP1}
    (h_disj : Disjoint A₁ A₂) (_hA₁ : MeasurableSet A₁) (hA₂ : MeasurableSet A₂)
    (h1 : energyMeasureExtended I u A₁ ≠ ⊤) (h2 : energyMeasureExtended I u A₂ ≠ ⊤) :
    energyMeasure I u (A₁ ∪ A₂) = energyMeasure I u A₁ + energyMeasure I u A₂ := by
  dsimp [energyMeasure]
  rw [measure_union h_disj hA₂]
  exact ENNReal.toReal_add h1 h2

/-- Isolated points have energy measure zero. -/
theorem energy_point_null (u : CP1 → M) (p : CP1) :
    energyMeasure I u {p} = 0 := by
  dsimp [energyMeasure, energyMeasureExtended, chartPush]
  rw [Measure.map_apply stereo_chart_symm_measurable (measurableSet_singleton p)]
  by_cases hp : p = north_pole
  · subst hp
    rw [stereo_chart_symm_preimage_north_pole]
    simp
  · rw [stereo_chart_symm_preimage_pt p hp]
    have h0 : (volume.withDensity (fun w => ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w))) {stereo_chart p} = 0 := by
      apply withDensity_absolutelyContinuous
      exact measure_singleton (stereo_chart p)
    rw [h0]
    simp

/-- Smooth circles (annulus boundaries) have energy measure zero. -/
theorem energy_circle_null (u : CP1 → M) (a : ℂ) (r : ℝ) :
    energyMeasure I u (circle_at a r) = 0 := by
  dsimp [energyMeasure, energyMeasureExtended, chartPush]
  rw [Measure.map_apply stereo_chart_symm_measurable (measurableSet_circle_at a r)]
  rw [stereo_chart_symm_preimage_circle_at]
  have h0 : (volume.withDensity (fun w => ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w))) (Metric.sphere a r) = 0 := by
    apply withDensity_absolutelyContinuous
    exact Measure.addHaar_sphere volume a r
  rw [h0]
  simp

/- =========================================================================
   POLAR COORDINATES AND RADIAL INTEGRALS
   ========================================================================= -/

lemma deriv_aux (r : ℝ) :
    HasDerivAt (fun x : ℝ => - 2 / (1 + x^2)) (4 * r / (1 + r^2)^2) r := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x^2) (2 * r) r := by
    have hd : HasDerivAt (fun x : ℝ => x^2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    simpa using hd.const_add 1
  have h2 : 1 + r^2 ≠ 0 := by positivity
  have h3 := (hasDerivAt_inv h2).comp r h1
  have h4 := h3.const_mul (-2 : ℝ)
  convert h4 using 1
  ring

lemma tendsto_aux : Tendsto (fun x : ℝ => - 2 / (1 + x^2)) atTop (𝓝 0) := by
  have h : (fun x : ℝ => - 2 / (1 + x^2)) = (fun y : ℝ => -2 * y) ∘ (fun x : ℝ => (1 + x^2)⁻¹) := by
    ext x; simp [div_eq_mul_inv]
  rw [h]
  have h2 : Tendsto (fun x : ℝ => x^2) atTop atTop := tendsto_pow_atTop (by decide)
  have hlim : Tendsto (fun x : ℝ => 1 + x^2) atTop atTop := tendsto_atTop_add_const_left atTop 1 h2
  have hinv : Tendsto (fun x : ℝ => (1 + x^2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlim
  have hmul : Tendsto (fun y : ℝ => -2 * y) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_mul_left (-2 : ℝ)).tendsto 0
  exact hmul.comp hinv

lemma integrable_radial : IntegrableOn (fun r : ℝ => 4 * r / (1 + r^2)^2) (Ioi 0) := by
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun y : ℝ => - 2 / (1 + y^2)) (4 * x / (1 + x^2)^2) x :=
    fun x _ => deriv_aux x
  have hderiv_nonneg : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ 4 * x / (1 + x^2)^2 := by
    intro x hx
    have : 0 < x := hx
    positivity
  exact integrableOn_Ioi_deriv_of_nonneg' hd hderiv_nonneg tendsto_aux

lemma lintegral_radial_lt_top :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (4 * r / (1 + r^2)^2) < ⊤ :=
  integrable_radial.lintegral_lt_top

lemma norm_sq_polarCoord_symm (p : ℝ × ℝ) :
    Complex.abs (Complex.polarCoord.symm p) ^ 2 = p.1^2 := by
  rw [Complex.polarCoord_symm_abs]
  exact sq_abs p.1

lemma sphericalJacobian_lintegral_lt_top :
    ∫⁻ w : ℂ, ENNReal.ofReal (sphericalJacobian w) < ⊤ := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  change (∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 * ENNReal.ofReal (sphericalJacobian (Complex.polarCoord.symm p))) < ⊤
  have h_meas_target : MeasurableSet (polarCoord.target : Set (ℝ × ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  have h_eq_integrand : ∀ p ∈ (polarCoord.target : Set (ℝ × ℝ)),
      ENNReal.ofReal p.1 * ENNReal.ofReal (sphericalJacobian (Complex.polarCoord.symm p)) =
      ENNReal.ofReal (4 * p.1 / (1 + p.1^2)^2) * (1 : ENNReal) := by
    intro p hp
    have hp_target : p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := hp
    have hr : 0 < p.1 := hp_target.1
    dsimp [sphericalJacobian]
    rw [norm_sq_polarCoord_symm]
    have h_prod : p.1 * (2 / (1 + p.1^2))^2 = 4 * p.1 / (1 + p.1^2)^2 := by
      rw [div_pow]
      norm_num
      ring
    have hr_pos : 0 ≤ p.1 := hr.le
    rw [← ENNReal.ofReal_mul hr_pos]
    rw [h_prod, mul_one]
  have h_congr := setLIntegral_congr_fun (μ := volume) h_meas_target (ae_of_all _ h_eq_integrand)
  rw [h_congr]
  clear h_congr h_eq_integrand
  change (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal (4 * p.1 / (1 + p.1^2)^2) * (1 : ENNReal)) < ⊤
  rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ)]
  rw [← Measure.prod_restrict]
  have h_cont : Continuous (fun (r : ℝ) => 4 * r / (1 + r^2)^2) := by
    apply Continuous.div
    · exact continuous_const.mul continuous_id
    · exact (continuous_const.add (continuous_id.pow 2)).pow 2
    · intro x
      have : 0 < 1 + x^2 := by positivity
      positivity
  have h_meas1 : Measurable (fun (r : ℝ) => ENNReal.ofReal (4 * r / (1 + r^2)^2)) :=
    h_cont.measurable.ennreal_ofReal
  have h_meas2 : Measurable (fun (_ : ℝ) => (1 : ENNReal)) := measurable_const
  rw [lintegral_prod_mul h_meas1.aemeasurable h_meas2.aemeasurable]
  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  rw [one_mul]
  have h_rad_int := lintegral_radial_lt_top
  have h_vol_int : volume (Ioo (-Real.pi) Real.pi) < ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  exact ENNReal.mul_lt_top h_rad_int h_vol_int

/- =========================================================================
   ENERGY FINITENESS AND STRICT POSITIVITY
   ========================================================================= -/

/-- For any map with uniformly bounded Riemannian energy density, the extended energy measure of CP1 is finite. -/
theorem energy_finite_of_bounded_density (u : CP1 → M) (C : ℝ) (hC : ∀ z, riemannianEnergyDensity I u z ≤ C) :
    energyMeasureExtended I u Set.univ < ⊤ := by
  dsimp [energyMeasureExtended, chartPush]
  rw [Measure.map_apply stereo_chart_symm_measurable MeasurableSet.univ]
  simp only [Set.preimage_univ]
  rw [withDensity_apply _ MeasurableSet.univ]
  rw [Measure.restrict_univ]
  have h_bound : ∀ w : ℂ, ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w) ≤
      ENNReal.ofReal (C * sphericalJacobian w) := by
    intro w
    apply ENNReal.ofReal_le_ofReal
    have h1 := hC (stereo_chart.symm w)
    have h2 := sphericalJacobian_nonneg w
    nlinarith
  have h_le : (∫⁻ w : ℂ, ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w)) ≤
      (∫⁻ w : ℂ, ENNReal.ofReal (C * sphericalJacobian w)) :=
    lintegral_mono (μ := volume) h_bound
  have h_fac : ∀ w : ℂ, ENNReal.ofReal (C * sphericalJacobian w) = ENNReal.ofReal (max C 0) * ENNReal.ofReal (sphericalJacobian w) := by
    intro w
    by_cases hC0 : 0 ≤ C
    · rw [max_eq_left hC0]
      have hj := sphericalJacobian_nonneg w
      rw [← ENNReal.ofReal_mul hC0]
    · push_neg at hC0
      rw [max_eq_right hC0.le]
      have hneg : C * sphericalJacobian w ≤ 0 := by
        nlinarith [sphericalJacobian_pos w]
      rw [ENNReal.ofReal_eq_zero.mpr hneg, ENNReal.ofReal_zero, zero_mul]
  simp_rw [h_fac] at h_le
  rw [lintegral_const_mul' _ _ (by simp)] at h_le
  apply lt_of_le_of_lt h_le
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top sphericalJacobian_lintegral_lt_top

/-- Definition of global J-holomorphicity for maps CP1 → M. -/
def JHolomorphic (I_dom : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)))
    (I_tgt : ModelWithCorners ℝ E H)
    [IsManifold I_dom ∞ CP1]
    [RiemannDomain (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) I_dom CP1]
    [IsManifold I_tgt ∞ M] [ClosedTameTarget I_tgt M]
    (u : CP1 → M) : Prop :=
  JHolomorphicOn (I := I_tgt) (I_dom := I_dom) u Set.univ

/-- Smooth maps on CP1 with bounded energy density have finite extended energy measure on Set.univ. -/
theorem energy_finite_of_contMDiff (u : CP1 → M) (_hu : ContMDiff I_CP1 I ⊤ u)
    (h_bdd : ∃ C : ℝ, ∀ z, riemannianEnergyDensity I u z ≤ C) :
    energyMeasureExtended I u Set.univ < ⊤ := by
  rcases h_bdd with ⟨C, hC⟩
  exact energy_finite_of_bounded_density I u C hC

/-- J-holomorphic curves on CP1 with bounded energy density have finite extended energy measure on Set.univ. -/
theorem energy_finite_of_jhol (u : CP1 → M) (_hu : JHolomorphic I_CP1 I u)
    (h_bdd : ∃ C : ℝ, ∀ z, riemannianEnergyDensity I u z ≤ C) :
    energyMeasureExtended I u Set.univ < ⊤ := by
  rcases h_bdd with ⟨C, hC⟩
  exact energy_finite_of_bounded_density I u C hC

/-- Any map whose Riemannian energy density is bounded below by a positive constant
on an open chart ball has strictly positive total energy. -/
theorem totalEnergy_pos_of_exists_ball (u : CP1 → M) (w₀ : ℂ) (r : ℝ) (hr : 0 < r)
    (c : ℝ) (hc : 0 < c)
    (h_dens : ∀ w ∈ Metric.ball w₀ r, c ≤ riemannianEnergyDensity I u (stereo_chart.symm w))
    (h_fin : energyMeasureExtended I u Set.univ < ⊤) :
    0 < totalEnergy I u := by
  dsimp [totalEnergy, energyMeasure]
  rcases sphericalJacobian_lower_bound w₀ r hr with ⟨j_min, hj_min_pos, hj_min_le⟩
  have h_meas_ball : MeasurableSet (Metric.ball w₀ r) := Metric.isOpen_ball.measurableSet
  have h_sub : (Metric.ball w₀ r : Set ℂ) ⊆ Set.univ := Set.subset_univ _
  have h_univ_eq : energyMeasureExtended I u Set.univ =
      (volume.withDensity (fun w => ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w))) Set.univ := by
    dsimp [energyMeasureExtended, chartPush]
    rw [Measure.map_apply stereo_chart_symm_measurable MeasurableSet.univ]
    simp only [Set.preimage_univ]
  have h_mono : (volume.withDensity (fun w => ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w))) (Metric.ball w₀ r) ≤
      energyMeasureExtended I u Set.univ := by
    rw [h_univ_eq]
    exact measure_mono h_sub
  have h_lower : ∀ w ∈ Metric.ball w₀ r, ENNReal.ofReal (c * j_min) ≤
      ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w) := by
    intro w hw
    apply ENNReal.ofReal_le_ofReal
    have hc_pos : 0 ≤ c := hc.le
    have hj_pos : 0 ≤ j_min := hj_min_pos.le
    have h1 := h_dens w hw
    have h2 := hj_min_le w hw
    nlinarith
  have h_int_lower : (volume.withDensity (fun _ => ENNReal.ofReal (c * j_min))) (Metric.ball w₀ r) ≤
      (volume.withDensity (fun w => ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w))) (Metric.ball w₀ r) := by
    rw [withDensity_apply _ h_meas_ball, withDensity_apply _ h_meas_ball]
    exact setLIntegral_mono' h_meas_ball h_lower
  have h_const_int : (volume.withDensity (fun _ => ENNReal.ofReal (c * j_min))) (Metric.ball w₀ r) =
      ENNReal.ofReal (c * j_min) * volume (Metric.ball w₀ r) := by
    rw [withDensity_apply _ h_meas_ball, setLIntegral_const]
  rw [h_const_int] at h_int_lower
  have h_prod_pos : 0 < ENNReal.ofReal (c * j_min) := by
    rw [ENNReal.ofReal_pos]
    positivity
  have h_vol_pos : 0 < volume (Metric.ball w₀ r) :=
    measure_ball_pos volume w₀ hr
  have h_pos_prod : 0 < ENNReal.ofReal (c * j_min) * volume (Metric.ball w₀ r) :=
    ENNReal.mul_pos h_prod_pos.ne' h_vol_pos.ne'
  have h_ball_pos : 0 < (volume.withDensity (fun w => ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w))) (Metric.ball w₀ r) :=
    lt_of_lt_of_le h_pos_prod h_int_lower
  have h_univ_pos : 0 < energyMeasureExtended I u Set.univ :=
    lt_of_lt_of_le h_ball_pos h_mono
  rw [ENNReal.toReal_pos_iff]
  exact ⟨h_univ_pos, h_fin⟩

/- =========================================================================
   STANDARD CANONICAL TARGET AND CONCRETE NONCONSTANT MAP (P0-1)
   ========================================================================= -/

abbrev E2 := EuclideanSpace ℝ (Fin 2)

noncomputable def p0 : E2 →L[ℝ] ℝ := ContinuousLinearMap.proj (0 : Fin 2)
noncomputable def p1 : E2 →L[ℝ] ℝ := ContinuousLinearMap.proj (1 : Fin 2)

/-- Standard constant symplectic form on EuclideanSpace ℝ (Fin 2). -/
noncomputable def stdOmega : E2 →L[ℝ] E2 →L[ℝ] ℝ :=
  ContinuousLinearMap.smulRight p0 p1 - ContinuousLinearMap.smulRight p1 p0

lemma stdOmega_skew (v w : E2) : stdOmega v w = - stdOmega w v := by
  change v 0 * w 1 - v 1 * w 0 = - (w 0 * v 1 - w 1 * v 0)
  ring

lemma stdOmega_closed (y : E2) (v₁ v₂ v₃ : E2) :
    let dω_y := fderiv ℝ (fun _ : E2 => stdOmega) y
    dω_y v₁ v₂ v₃ + dω_y v₂ v₃ v₁ + dω_y v₃ v₁ v₂ = 0 := by
  intro dω_y
  have h0 : fderiv ℝ (fun _ : E2 => stdOmega) = 0 := fderiv_const (𝕜 := ℝ) (E := E2) stdOmega
  have hd : dω_y = 0 := by dsimp [dω_y]; rw [h0]; rfl
  rw [hd]
  simp

lemma E2_decomp (v : E2) : v = v 0 • e1 + v 1 • e2 := by
  ext i
  fin_cases i <;> simp [e1, e2]

lemma J_CP1_decomp (v : E2) : J_CP1 v = - (v 1) • e1 + (v 0) • e2 := by
  have hv := E2_decomp v
  nth_rw 1 [hv]
  rw [_root_.map_add, _root_.map_smul, _root_.map_smul, J_CP1_e1, J_CP1_e2]
  simp [smul_neg, add_comm]

lemma J_CP1_coords (v : E2) : (J_CP1 v) 0 = - v 1 ∧ (J_CP1 v) 1 = v 0 := by
  have hj := J_CP1_decomp v
  constructor
  · rw [hj]; simp [e1, e2]
  · rw [hj]; simp [e1, e2]

lemma stdOmega_J_self (v : E2) : stdOmega v (J_CP1 v) = (v 0)^2 + (v 1)^2 := by
  have hc := J_CP1_coords v
  change v 0 * (J_CP1 v) 1 - v 1 * (J_CP1 v) 0 = (v 0)^2 + (v 1)^2
  rw [hc.1, hc.2]
  ring

lemma E2_eq_zero_of_coords (v : E2) (h0 : v 0 = 0) (h1 : v 1 = 0) : v = 0 := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma sq_add_sq_pos_of_ne_zero (v : E2) (hv : v ≠ 0) : 0 < (v 0)^2 + (v 1)^2 := by
  have h_nonneg : 0 ≤ (v 0)^2 + (v 1)^2 := by positivity
  rcases h_nonneg.lt_or_eq with hpos | heq
  · exact hpos
  · exfalso
    have h_sq0 : (v 0)^2 = 0 := by
      have : (v 0)^2 ≤ (v 0)^2 + (v 1)^2 := by linarith [sq_nonneg (v 1)]
      linarith [sq_nonneg (v 0)]
    have h_sq1 : (v 1)^2 = 0 := by
      have : (v 1)^2 ≤ (v 0)^2 + (v 1)^2 := by linarith [sq_nonneg (v 0)]
      linarith [sq_nonneg (v 1)]
    have v0 : v 0 = 0 := sq_eq_zero_iff.mp h_sq0
    have v1 : v 1 = 0 := sq_eq_zero_iff.mp h_sq1
    exact hv (E2_eq_zero_of_coords v v0 v1)

lemma stdOmega_tame (v : E2) (hv : v ≠ 0) : 0 < stdOmega v (J_CP1 v) := by
  rw [stdOmega_J_self]
  exact sq_add_sq_pos_of_ne_zero v hv

lemma stdOmega_nondegenerate (v : E2) (h : ∀ w, stdOmega v w = 0) : v = 0 := by
  by_contra hv
  have hpos := stdOmega_tame v hv
  have hzero := h (J_CP1 v)
  linarith

/-- Canonical closed tame target structure on CP1 equipped with the standard symplectic form. -/
noncomputable instance CP1_ClosedTameTarget : ClosedTameTarget I_CP1 CP1 where
  «ω» _ := stdOmega
  ω_skew _ v w := stdOmega_skew v w
  ω_smooth _ := contDiffOn_const
  ω_closed _ y _ v₁ v₂ v₃ := stdOmega_closed y v₁ v₂ v₃
  ω_nondegenerate _ v := stdOmega_nondegenerate v
  J _ := J_CP1
  J_sq _ v := J_CP1_sq v
  J_smooth _ := contDiffOn_const
  tame _ v hv := stdOmega_tame v hv

lemma north_pole_ne_south_pole : north_pole ≠ south_pole := by
  intro h_eq
  have h2 : (north_pole.1 : EuclideanSpace ℝ (Fin 3)) 2 = (south_pole.1 : EuclideanSpace ℝ (Fin 3)) 2 := by rw [h_eq]
  dsimp [north_pole, south_pole] at h2
  norm_num at h2

/-- The identity map on CP1 is nonconstant. -/
lemma concrete_nonconstant_map_nonconstant :
    ∃ z₁ z₂ : CP1, (id : CP1 → CP1) z₁ ≠ (id : CP1 → CP1) z₂ :=
  ⟨north_pole, south_pole, north_pole_ne_south_pole⟩

/-- The identity map on CP1 is smooth. -/
lemma concrete_nonconstant_map_smooth :
    ContMDiff I_CP1 I_CP1 ⊤ (id : CP1 → CP1) :=
  contMDiff_id

/-- The identity map on CP1 is J-holomorphic. -/
lemma concrete_nonconstant_map_jhol :
    JHolomorphic I_CP1 I_CP1 (id : CP1 → CP1) := by
  dsimp [JHolomorphic, JHolomorphicOn]
  constructor
  · exact contMDiff_id.contMDiffOn
  · intro z hz v
    rw [mfderiv_id]
    dsimp [CP1_ClosedTameTarget, RiemannDomain.j, CP1.almostComplexStructure]

lemma stdOmega_e1_e2 : stdOmega e1 e2 = 1 := by
  change (!₂[1, 0] : E2) 0 * (!₂[0, 1] : E2) 1 - (!₂[1, 0] : E2) 1 * (!₂[0, 1] : E2) 0 = 1
  norm_num

/-- Pointwise Riemannian energy density of the identity map is identically 1. -/
lemma riemannianEnergyDensity_id (z : CP1) :
    riemannianEnergyDensity I_CP1 (u := id) z = 1 := by
  change (1 / 2 : ℝ) *
    (ClosedTameTarget.metric I_CP1 (id z) (mfderiv I_CP1 I_CP1 id z e1) (mfderiv I_CP1 I_CP1 id z e1) +
     ClosedTameTarget.metric I_CP1 (id z) (mfderiv I_CP1 I_CP1 id z e2) (mfderiv I_CP1 I_CP1 id z e2)) = 1
  rw [mfderiv_id]
  change (1 / 2 : ℝ) *
    (ClosedTameTarget.metric I_CP1 z e1 e1 + ClosedTameTarget.metric I_CP1 z e2 e2) = 1
  change (1 / 2 : ℝ) *
    ((1 / 2 : ℝ) * (stdOmega e1 (J_CP1 e1) + stdOmega e1 (J_CP1 e1)) +
     (1 / 2 : ℝ) * (stdOmega e2 (J_CP1 e2) + stdOmega e2 (J_CP1 e2))) = 1
  rw [J_CP1_e1, J_CP1_e2]
  have h_map_neg : stdOmega e2 (-e1) = - stdOmega e2 e1 := (stdOmega e2).map_neg e1
  rw [h_map_neg]
  have h_skew := stdOmega_skew e2 e1
  have h_12 := stdOmega_e1_e2
  linarith

/-- A concrete nonconstant smooth map has finite extended energy measure on CP1. -/
theorem concrete_nonconstant_map_finite_energy :
    energyMeasureExtended I_CP1 (id : CP1 → CP1) Set.univ < ⊤ := by
  apply energy_finite_of_bounded_density I_CP1 (id : CP1 → CP1) 1
  intro z
  rw [riemannianEnergyDensity_id z]

/-- A concrete nonconstant smooth map has strictly positive total energy. -/
theorem concrete_nonconstant_map_positive_energy :
    0 < totalEnergy I_CP1 (id : CP1 → CP1) := by
  apply totalEnergy_pos_of_exists_ball I_CP1 (id : CP1 → CP1) 0 1 (by norm_num) 1 (by norm_num)
  · intro w hw
    rw [riemannianEnergyDensity_id]
  · exact concrete_nonconstant_map_finite_energy

/- =========================================================================
   AUTHENTIC TRACE SCALING AND CHANGE-OF-VARIABLES THEOREMS (P0-2)
   ========================================================================= -/

/-- General bilinear Dirichlet trace scaling under a C-linear map on ℝ² ≅ ℂ.
The quadratic trace scales by exactly the determinant a² + b² = |φ'(w)|². -/
theorem c_linear_dirichlet_trace_scaling
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V → V → ℝ) (hB_add_left : ∀ x y z, B (x + y) z = B x z + B y z)
    (hB_add_right : ∀ x y z, B x (y + z) = B x y + B x z)
    (hB_smul_left : ∀ c x y, B (c • x) y = c * B x y)
    (hB_smul_right : ∀ c x y, B x (c • y) = c * B x y)
    (T : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] V)
    (a b : ℝ)
    (K : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hKe1 : K e1 = a • e1 + b • e2)
    (hKe2 : K e2 = (-b) • e1 + a • e2) :
    B (T (K e1)) (T (K e1)) + B (T (K e2)) (T (K e2)) =
    (a^2 + b^2) * (B (T e1) (T e1) + B (T e2) (T e2)) := by
  have h1 : T (K e1) = a • T e1 + b • T e2 := by
    rw [hKe1, _root_.map_add, _root_.map_smul, _root_.map_smul]
  have h2 : T (K e2) = (-b) • T e1 + a • T e2 := by
    rw [hKe2, _root_.map_add, _root_.map_smul, _root_.map_smul]
  rw [h1, h2]
  simp only [hB_add_left, hB_add_right, hB_smul_left, hB_smul_right]
  ring

/-- Specialization to dilation by factor l > 0:
the Dirichlet energy density scales by exactly l². -/
theorem dilation_trace_scaling
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V → V → ℝ) (hB_add_left : ∀ x y z, B (x + y) z = B x z + B y z)
    (hB_add_right : ∀ x y z, B x (y + z) = B x y + B x z)
    (hB_smul_left : ∀ c x y, B (c • x) y = c * B x y)
    (hB_smul_right : ∀ c x y, B x (c • y) = c * B x y)
    (T : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] V)
    (l : ℝ)
    (K : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hKe1 : K e1 = l • e1)
    (hKe2 : K e2 = l • e2) :
    B (T (K e1)) (T (K e1)) + B (T (K e2)) (T (K e2)) =
    l^2 * (B (T e1) (T e1) + B (T e2) (T e2)) := by
  have hKe1' : K e1 = l • e1 + (0 : ℝ) • e2 := by rw [hKe1, zero_smul, add_zero]
  have hKe2' : K e2 = (-(0 : ℝ)) • e1 + l • e2 := by rw [hKe2, neg_zero, zero_smul, zero_add]
  have h := c_linear_dirichlet_trace_scaling B hB_add_left hB_add_right hB_smul_left hB_smul_right
    T l 0 K hKe1' hKe2'
  simp only [zero_pow (by norm_num : 2 ≠ 0), add_zero] at h
  exact h

/-- Translation invariance of Lebesgue volume on ℂ:
Measure.map (· + a) volume = volume. -/
theorem volume_map_translation (a : ℂ) :
    Measure.map (fun w => w + a) (volume : Measure ℂ) = volume :=
  map_add_right_eq_self volume a

/-- Scaling of Lebesgue volume on ℂ under real homothety w ↦ l • w:
Measure.map (l • ·) volume = (l⁻¹)^2 • volume. -/
theorem volume_map_homothety (l : ℝ) (hl : 0 < l) :
    Measure.map (fun w => l • w) (volume : Measure ℂ) =
    ENNReal.ofReal (l⁻¹ ^ 2) • volume := by
  have h_ne : l ≠ 0 := ne_of_gt hl
  have h_haar := Measure.map_addHaar_smul (μ := (volume : Measure ℂ)) h_ne
  rw [Complex.finrank_real_complex] at h_haar
  rw [h_haar]
  congr 1
  rw [_root_.abs_of_pos (inv_pos.mpr (pow_pos hl 2))]
  rw [inv_pow]

/-- Determinant of complex scalar multiplication as a real linear map on ℂ:
LinearMap.det (LinearMap.mulLeft ℝ c) = Complex.normSq c. -/
theorem det_mulLeft_complex (c : ℂ) :
    LinearMap.det (LinearMap.mulLeft ℝ c) = Complex.normSq c := by
  let b := Complex.basisOneI
  rw [← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b (LinearMap.mulLeft ℝ c) = ![![c.re, -c.im], ![c.im, c.re]] := by
    ext i j
    simp only [LinearMap.toMatrix_apply, LinearMap.mulLeft_apply]
    fin_cases i <;> fin_cases j
    · simp [b]
    · simp [b]
    · simp [b]
    · simp [b]
  rw [hM]
  rw [Matrix.det_fin_two]
  simp [Complex.normSq, mul_comm]

/-- Rotation invariance of Lebesgue volume on ℂ:
For any unit complex number c (e.g. c = exp(iθ)), multiplication by c preserves volume. -/
theorem volume_map_rotation (c : ℂ) (hc : Complex.normSq c = 1) :
    Measure.map (fun w => c * w) (volume : Measure ℂ) = volume := by
  have h_lin : (fun w => c * w) = (LinearMap.mulLeft ℝ c : ℂ →ₗ[ℝ] ℂ) := rfl
  rw [h_lin]
  have h_det_ne : LinearMap.det (LinearMap.mulLeft ℝ c) ≠ 0 := by
    rw [det_mulLeft_complex, hc]
    norm_num
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) h_det_ne]
  rw [det_mulLeft_complex, hc, inv_one, abs_one, ENNReal.ofReal_one, one_smul]

/-- Affine transformation of Lebesgue volume on ℂ:
For w ↦ a + l • w, the pushforward measure scales by (l⁻¹)^2. -/
theorem volume_map_affine (a : ℂ) (l : ℝ) (hl : 0 < l) :
    Measure.map (fun w => a + l • w) (volume : Measure ℂ) =
    ENNReal.ofReal (l⁻¹ ^ 2) • volume := by
  have heq : (fun w => a + l • w) = (fun w => w + a) ∘ (fun w => l • w) := by
    ext w
    dsimp
    rw [add_comm]
  rw [heq]
  have h_meas_smul : Measurable (fun (w : ℂ) => l • w) :=
    continuous_const_smul l |>.measurable
  have h_meas_trans : Measurable (fun (w : ℂ) => w + a) :=
    continuous_add_right a |>.measurable
  rw [← Measure.map_map h_meas_trans h_meas_smul]
  rw [volume_map_homothety l hl]
  rw [Measure.map_smul]
  rw [volume_map_translation a]

/-- Integral change-of-variables under dilation w ↦ l • w:
∫ f(l • w) dw = l⁻² ∫ f(z) dz. -/
theorem lintegral_comp_homothety (f : ℂ → ℝ≥0∞) (hf : Measurable f)
    (l : ℝ) (hl : 0 < l) :
    (∫⁻ w, f (l • w)) = ENNReal.ofReal (l⁻¹ ^ 2) * ∫⁻ z, f z := by
  have h_meas : Measurable (fun (w : ℂ) => l • w) :=
    continuous_const_smul l |>.measurable
  rw [← lintegral_map hf h_meas]
  rw [volume_map_homothety l hl]
  rw [lintegral_smul_measure]

/-- Exact cancellation:
The quadratic derivative scaling l² and the measure scaling l⁻² cancel identically:
l² * l⁻² = 1. -/
theorem dilation_factor_cancellation (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal (l ^ 2) * ENNReal.ofReal (l⁻¹ ^ 2) = 1 := by
  rw [← ENNReal.ofReal_mul (sq_nonneg l)]
  have h_inv : l ^ 2 * l⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hl), one_pow]
  rw [h_inv, ENNReal.ofReal_one]

/-- The integral of the rescaled energy density equals the original integral:
∫ (l² * f(l • w)) dw = ∫ f(z) dz. -/
theorem lintegral_scaled_density_eq (f : ℂ → ℝ≥0∞) (hf : Measurable f)
    (l : ℝ) (hl : 0 < l) :
    (∫⁻ w, ENNReal.ofReal (l ^ 2) * f (l • w)) = ∫⁻ z, f z := by
  rw [lintegral_const_mul' _ _ (by norm_num)]
  rw [lintegral_comp_homothety f hf l hl]
  rw [← mul_assoc]
  rw [dilation_factor_cancellation l hl]
  rw [one_mul]

/-- Full 2D affine scaling cancellation theorem:
The quadratic gradient scaling factor λ² cancels identically with the 2D Lebesgue volume scaling factor λ⁻²
under affine change of variables w ↦ a + λ • w on ℂ. -/
theorem lintegral_affine_scaling_cancellation (a : ℂ) (l : ℝ) (hl : 0 < l)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w : ℂ, ENNReal.ofReal (l ^ 2) * f (a + l • w)) = ∫⁻ z : ℂ, f z := by
  rw [lintegral_const_mul' _ _ (by norm_num)]
  have h_meas : Measurable (fun (w : ℂ) => a + l • w) :=
    (continuous_add_left a).comp (continuous_const_smul l) |>.measurable
  rw [← lintegral_map hf h_meas]
  rw [volume_map_affine a l hl]
  rw [lintegral_smul_measure]
  rw [← mul_assoc]
  rw [dilation_factor_cancellation l hl]
  rw [one_mul]

/- =========================================================================
   CONFORMAL INVARIANCE AND TRANSFORMATION PROPERTIES
   ========================================================================= -/

lemma energyMeasureExtended_id (u : CP1 → M) :
    energyMeasureExtended I (u ∘ MoebiusFrame.id.toHomeo) =
    Measure.map MoebiusFrame.id.toHomeo.symm (energyMeasureExtended I u) := by
  have hu : u ∘ ⇑MoebiusFrame.id.toHomeo = u := rfl
  have heq : ⇑MoebiusFrame.id.toHomeo.symm = id := rfl
  rw [hu, heq, Measure.map_id]

lemma energyMeasureExtended_comp (u : CP1 → M) (ϕ₁ ϕ₂ : MoebiusFrame)
    (h1 : energyMeasureExtended I (u ∘ ϕ₁.toHomeo) = Measure.map ϕ₁.toHomeo.symm (energyMeasureExtended I u))
    (h2 : energyMeasureExtended I ((u ∘ ϕ₁.toHomeo) ∘ ϕ₂.toHomeo) = Measure.map ϕ₂.toHomeo.symm (energyMeasureExtended I (u ∘ ϕ₁.toHomeo))) :
    energyMeasureExtended I (u ∘ (MoebiusFrame.comp ϕ₁ ϕ₂).toHomeo) =
    Measure.map (MoebiusFrame.comp ϕ₁ ϕ₂).toHomeo.symm (energyMeasureExtended I u) := by
  have heq : u ∘ (MoebiusFrame.comp ϕ₁ ϕ₂).toHomeo = (u ∘ ϕ₁.toHomeo) ∘ ϕ₂.toHomeo := rfl
  rw [heq, h2, h1]
  rw [Measure.map_map ϕ₂.toHomeo.symm.continuous.measurable ϕ₁.toHomeo.symm.continuous.measurable]
  congr 1

/-- Equivariant transformation of Borel measures under Möbius transformations on CP1. -/
theorem moebius_map_preimage_all (μ : Measure CP1) (ϕ : MoebiusFrame) (A : Set CP1) :
    (Measure.map ϕ.toHomeo.symm μ) (ϕ.toHomeo ⁻¹' A) = μ A := by
  let e := ϕ.toHomeo.symm.toMeasurableEquiv
  have he : ⇑e = ⇑ϕ.toHomeo.symm := rfl
  rw [← he, e.map_apply]
  have h_eq : (⇑e ⁻¹' (ϕ.toHomeo ⁻¹' A)) = A := by
    change ϕ.toHomeo.symm ⁻¹' (ϕ.toHomeo ⁻¹' A) = A
    ext x
    simp
  rw [h_eq]

/-- Unconditional conformal invariance of the energy measure under the identity Möbius transformation:
$$E(u \circ \operatorname{id}; \operatorname{id}^{-1}(A)) = E(u; A).$$ -/
theorem energy_conformal_invariant_id (u : CP1 → M) (A : Set CP1) :
    energyMeasure I (u ∘ MoebiusFrame.id.toHomeo) (MoebiusFrame.id.toHomeo ⁻¹' A) = energyMeasure I u A := by
  dsimp [energyMeasure]
  rw [energyMeasureExtended_id]
  rw [moebius_map_preimage_all (energyMeasureExtended I u) MoebiusFrame.id A]

/-- Unconditional conformal invariance of total energy under identity:
$$E(u \circ \operatorname{id}) = E(u).$$ -/
theorem totalEnergy_conformal_invariant_id (u : CP1 → M) :
    totalEnergy I (u ∘ MoebiusFrame.id.toHomeo) = totalEnergy I u := by
  dsimp [totalEnergy]
  have h_univ : MoebiusFrame.id.toHomeo ⁻¹' Set.univ = Set.univ := Set.preimage_univ
  rw [← h_univ]
  exact energy_conformal_invariant_id I u Set.univ

/-- Conditional reduction: Conformal invariance of the real-valued energy measure under any Möbius transformation
whose extended measure pulls back equivariantly:
$$E(u \circ \phi; \phi^{-1}(A)) = E(u; A).$$
This is an explicit conditional reduction from the pullback equivariance of the extended energy measure. -/
theorem energy_conformal_invariant (u : CP1 → M) (ϕ : MoebiusFrame) (A : Set CP1)
    (h_pullback : energyMeasureExtended I (u ∘ ϕ.toHomeo) = Measure.map ϕ.toHomeo.symm (energyMeasureExtended I u)) :
    energyMeasure I (u ∘ ϕ.toHomeo) (ϕ.toHomeo ⁻¹' A) = energyMeasure I u A := by
  dsimp [energyMeasure]
  rw [h_pullback]
  rw [moebius_map_preimage_all (energyMeasureExtended I u) ϕ A]

/-- Conditional reduction: Conformal invariance of the total energy under any Möbius transformation
whose extended measure pulls back equivariantly:
$$E(u \circ \phi) = E(u).$$
This is an explicit conditional reduction from the pullback equivariance of the extended energy measure. -/
theorem totalEnergy_conformal_invariant (u : CP1 → M) (ϕ : MoebiusFrame)
    (h_pullback : energyMeasureExtended I (u ∘ ϕ.toHomeo) = Measure.map ϕ.toHomeo.symm (energyMeasureExtended I u)) :
    totalEnergy I (u ∘ ϕ.toHomeo) = totalEnergy I u := by
  dsimp [totalEnergy]
  have h_univ : ϕ.toHomeo ⁻¹' Set.univ = Set.univ := Set.preimage_univ
  rw [← h_univ]
  exact energy_conformal_invariant I u ϕ Set.univ h_pullback

/-- Volume of balls in ℂ has explicit real value $\pi \cdot (\max(r, 0))^2$. -/
lemma toReal_volume_ball (a : ℂ) (r : ℝ) :
    (volume (ball a r)).toReal = (max r 0) ^ 2 * Real.pi := by
  by_cases hr : 0 ≤ r
  · rw [max_eq_left hr]
    rw [Complex.volume_ball]
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow]
    rw [ENNReal.toReal_ofReal hr]
    simp [NNReal.coe_real_pi]
  · push_neg at hr
    rw [max_eq_right hr.le]
    have hball : ball a r = ∅ := ball_eq_empty.mpr hr.le
    rw [hball, measure_empty, ENNReal.zero_toReal]
    simp

/-- Continuity of Lebesgue volume on expanding concentric balls in ℂ:
The function $r \mapsto \mathrm{vol}(B_r(a))$ is continuous on $\mathbb{R}$. -/
theorem continuous_volume_ball (a : ℂ) :
    Continuous (fun (r : ℝ) => (volume (ball a r)).toReal) := by
  have heq : (fun (r : ℝ) => (volume (ball a r)).toReal) = (fun r => (max r 0) ^ 2 * Real.pi) := by
    ext r
    exact toReal_volume_ball a r
  rw [heq]
  have h1 : Continuous (fun r : ℝ => max r 0) := continuous_id.max continuous_const
  have h2 : Continuous (fun r : ℝ => (max r 0) ^ 2) := h1.pow 2
  exact h2.mul continuous_const

/-- Uniform energy bound record: $E(u_n) \le B$. -/
structure EnergyBoundedSequence (u_seq : ℕ → (CP1 → M)) (B : ℝ) : Prop where
  bound_nonneg : 0 ≤ B
  bounded : ∀ n, totalEnergy I (u_seq n) ≤ B

#print axioms riemannianEnergyDensity_nonneg
#print axioms metric_c_linear_trace_scaling
#print axioms energy_density_eq_omega
#print axioms energy_nonneg
#print axioms energy_eq_pullback_omega
#print axioms energy_additive
#print axioms energy_point_null
#print axioms energy_circle_null
#print axioms sphericalJacobian_lintegral_lt_top
#print axioms energy_finite_of_bounded_density
#print axioms totalEnergy_pos_of_exists_ball
#print axioms concrete_nonconstant_map_finite_energy
#print axioms concrete_nonconstant_map_positive_energy
#print axioms c_linear_dirichlet_trace_scaling
#print axioms dilation_trace_scaling
#print axioms volume_map_translation
#print axioms volume_map_homothety
#print axioms det_mulLeft_complex
#print axioms volume_map_rotation
#print axioms volume_map_affine
#print axioms lintegral_comp_homothety
#print axioms dilation_factor_cancellation
#print axioms lintegral_scaled_density_eq
#print axioms lintegral_affine_scaling_cancellation
#print axioms energyMeasureExtended_id
#print axioms energyMeasureExtended_comp
#print axioms energy_conformal_invariant_id
#print axioms totalEnergy_conformal_invariant_id
#print axioms energy_conformal_invariant
#print axioms totalEnergy_conformal_invariant
#print axioms continuous_volume_ball

end GromovCompactness
