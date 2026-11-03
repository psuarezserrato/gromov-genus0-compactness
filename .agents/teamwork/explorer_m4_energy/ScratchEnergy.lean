/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Data.Complex.FiniteDimensional
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness

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

/-- Fundamental pointwise identity: for any $J$-holomorphic curve $u$,
the Riemannian Dirichlet energy density equals the pullback symplectic area density:
$$\frac{1}{2} |du|^2_g = (u^* \omega)(e_1, e_2).$$ -/
theorem energy_density_eq_omega (u : CP1 → M) (z : CP1)
    (h_jhol : ∀ v, mfderiv I_CP1 I u z (J_CP1 v) = ClosedTameTarget.J (u z) (mfderiv I_CP1 I u z v)) :
    riemannianEnergyDensity I u z = symplecticAreaDensity I u z := by
  have he2 : mfderiv I_CP1 I u z e2 = ClosedTameTarget.J (u z) (mfderiv I_CP1 I u z e1) := by
    rw [← J_CP1_e1]
    exact h_jhol e1
  dsimp [riemannianEnergyDensity, symplecticAreaDensity, ClosedTameTarget.metric]
  rw [he2]
  have hJ2 : ClosedTameTarget.J (u z) (ClosedTameTarget.J (u z) (mfderiv I_CP1 I u z e1)) = - mfderiv I_CP1 I u z e1 :=
    ClosedTameTarget.J_sq (u z) (mfderiv I_CP1 I u z e1)
  rw [hJ2]
  have hneg : ClosedTameTarget.«ω» (u z) (ClosedTameTarget.J (u z) (mfderiv I_CP1 I u z e1)) (- mfderiv I_CP1 I u z e1) =
              - ClosedTameTarget.«ω» (u z) (ClosedTameTarget.J (u z) (mfderiv I_CP1 I u z e1)) (mfderiv I_CP1 I u z e1) :=
    (ClosedTameTarget.«ω» (u z) (ClosedTameTarget.J (u z) (mfderiv I_CP1 I u z e1))).map_neg _
  rw [hneg]
  have hskew : ClosedTameTarget.«ω» (u z) (ClosedTameTarget.J (u z) (mfderiv I_CP1 I u z e1)) (mfderiv I_CP1 I u z e1) =
               - ClosedTameTarget.«ω» (u z) (mfderiv I_CP1 I u z e1) (ClosedTameTarget.J (u z) (mfderiv I_CP1 I u z e1)) :=
    ClosedTameTarget.ω_skew (u z) _ _
  linarith

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

/-- Canonical pushforward of a measure on ℂ to the Riemann sphere CP1 via stereographic projection. -/
noncomputable def chartPush (ν : Measure ℂ) : Measure CP1 :=
  Measure.map stereo_chart.symm ν

/-- The extended nonnegative symplectic energy Borel measure on $\mathbb{CP}^1$ associated to $u : \mathbb{CP}^1 \to M$.
Constructed via the pushforward of the Lebesgue integral of the Riemannian energy density. -/
noncomputable def energyMeasureExtended (u : CP1 → M) : Measure CP1 :=
  chartPush (volume.withDensity (fun w => ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w))))

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
  chartPush (volume.withDensity (fun w => ENNReal.ofReal (symplecticAreaDensity I u (stereo_chart.symm w))))

/-- Real-valued pullback symplectic area on a subset $A \subseteq \mathbb{CP}^1$. -/
noncomputable def pullbackOmegaMeasure (u : CP1 → M) (A : Set CP1) : ℝ :=
  (pullbackOmegaMeasureExtended I u A).toReal

/-- Fundamental identity: For any $J$-holomorphic curve $u : \mathbb{CP}^1 \to M$,
the energy measure equals the integral of the pullback symplectic form:
$$E(u; A) = \int_A u^* \omega.$$ -/
theorem energy_eq_pullback_omega (u : CP1 → M)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) (A : Set CP1) :
    energyMeasure I u A = pullbackOmegaMeasure I u A := by
  have h_dense : (fun w => ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w))) =
                 (fun w => ENNReal.ofReal (symplecticAreaDensity I u (stereo_chart.symm w))) := by
    ext w
    congr 1
    apply energy_density_eq_omega
    intro v
    exact h_jhol.2 (stereo_chart.symm w) (mem_univ _) v
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
    have h0 : (volume.withDensity (fun w => ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w)))) {stereo_chart p} = 0 := by
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
  have h0 : (volume.withDensity (fun w => ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w)))) (Metric.sphere a r) = 0 := by
    apply withDensity_absolutelyContinuous
    exact Measure.addHaar_sphere volume a r
  rw [h0]
  simp

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

/-- Conformal invariance of the symplectic energy measure:
For any Möbius frame $\phi \in \operatorname{PSL}(2, \mathbb{C})$ and measurable set $A \subseteq \mathbb{CP}^1$,
when the energy measure pulls back equivariantly under the conformal diffeomorphism $\phi$,
$$E(u \circ \phi; \phi^{-1}(A)) = E(u; A).$$ -/
theorem energy_conformal_invariant (u : CP1 → M) (ϕ : MoebiusFrame) (A : Set CP1)
    (h_conf : energyMeasureExtended I (u ∘ ϕ.toHomeo) = Measure.map ϕ.toHomeo.symm (energyMeasureExtended I u)) :
    energyMeasure I (u ∘ ϕ.toHomeo) (ϕ.toHomeo ⁻¹' A) = energyMeasure I u A := by
  dsimp [energyMeasure]
  rw [h_conf]
  rw [moebius_map_preimage_all (energyMeasureExtended I u) ϕ A]

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

end GromovCompactness
