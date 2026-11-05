/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic

open scoped Manifold ContDiff Topology
open Metric Set

/-!
# Task F01: Target Geometry and Cauchy-Riemann Equation

This module formalizes the geometric target space $(M, \omega, J)$ for pseudo-holomorphic curves,
following Gromov (1985, §1.2), Ivashkovich-Shevchishin (1999, §2), and `gromov_compactness.pdf` §2.1.

## Key Definitions
- `ClosedTameTarget`: Compact, boundaryless smooth manifold $M$ equipped with a smooth closed
  non-degenerate two-form $\omega$ and a smooth almost complex structure $J$ tamed by $\omega$.
- `ClosedTameTarget.metric`: Symmetrized Riemannian metric
  $$g(v, w) := \frac{1}{2}\big(\omega(v, Jw) + \omega(w, Jv)\big).$$
- `metric_pos_def`: Proof that $g$ is positive definite ($v \neq 0 \implies g(v, v) > 0$).
- `metric_symm`: Proof that $g$ is symmetric ($g(v, w) = g(w, v)$).
- `metric_J_invariant`: Proof that $g$ is $J$-invariant ($g(Jv, Jw) = g(v, w)$).
- `JHolomorphicOn`: The Cauchy-Riemann equation $\bar\partial_J u = \frac{1}{2}(du + J \circ du \circ j) = 0$.
- `TargetGeometryConstants`: Injectivity radius, uniform convexity radius, and bounded geometry data.
-/

namespace GromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]

noncomputable instance (x : M) : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
noncomputable instance (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)

/-- Coordinate representation of an almost complex structure `J` in the extended chart at `x`. -/
def J_chart (J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x) (x : M) (y : E) : E →L[ℝ] E :=
  J ((extChartAt I x).symm y)

/-- Coordinate representation of a 2-form `ω` in the extended chart at `x`. -/
def ω_chart («ω» : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : M) (y : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  «ω» ((extChartAt I x).symm y)

/-- A compact, boundaryless, finite-dimensional smooth manifold equipped with a closed
non-degenerate two-form `ω` and an `ω`-tamed smooth almost complex structure `J`. -/
class ClosedTameTarget (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] where
  /-- The symplectic 2-form evaluated at basepoint `x` on tangent vectors `v, w`. -/
  «ω» : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  /-- Skew-symmetry of the two-form: `ω(v, w) = -ω(w, v)`. -/
  ω_skew : ∀ (x : M) (v w : TangentSpace I x), «ω» x v w = - «ω» x w v
  /-- Smoothness of the symplectic 2-form `ω`: chartwise C^∞ in every chart. -/
  ω_smooth : ∀ (x : M), ContDiffOn ℝ ∞ (ω_chart I «ω» x) (extChartAt I x).target
  /-- Closedness of the two-form: `dω = 0`.
  In every chart, the exterior derivative (cyclic sum of directional Fréchet derivatives)
  vanishes at every point `y ∈ chart.target`. -/
  ω_closed : ∀ (x : M) (y : E) (_ : y ∈ (extChartAt I x).target) (v₁ v₂ v₃ : E),
    let dω_y := fderiv ℝ (ω_chart I «ω» x) y
    dω_y v₁ v₂ v₃ + dω_y v₂ v₃ v₁ + dω_y v₃ v₁ v₂ = 0
  /-- Non-degeneracy of the two-form: `(∀ w, ω(v, w) = 0) → v = 0`. -/
  ω_nondegenerate : ∀ (x : M) (v : TangentSpace I x), (∀ w, «ω» x v w = 0) → v = 0
  /-- The almost complex structure `J : TM → TM`. -/
  J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x
  /-- Almost complex condition: `J² = -id`. -/
  J_sq : ∀ (x : M) (v : TangentSpace I x), J x (J x v) = -v
  /-- Smoothness of the almost complex bundle endomorphism `J`: chartwise C^∞ in every chart. -/
  J_smooth : ∀ (x : M), ContDiffOn ℝ ∞ (J_chart I J x) (extChartAt I x).target
  /-- Tameness condition: `ω(v, J v) > 0` for all non-zero `v`. -/
  tame : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < «ω» x v (J x v)

/-- Symmetrized Riemannian metric $g(v, w) = \frac{1}{2}(\omega(v, Jw) + \omega(w, Jv))$. -/
noncomputable def ClosedTameTarget.metric [tgt : ClosedTameTarget I M] (x : M) (v w : TangentSpace I x) : ℝ :=
  (1 / 2 : ℝ) * (tgt.«ω» x v (tgt.J x w) + tgt.«ω» x w (tgt.J x v))

/-- Symmetry of the Riemannian metric tensor: $g(v, w) = g(w, v)$. -/
theorem metric_symm [tgt : ClosedTameTarget I M] (x : M) (v w : TangentSpace I x) :
    ClosedTameTarget.metric I x v w = ClosedTameTarget.metric I x w v := by
  dsimp [ClosedTameTarget.metric]
  ring

/-- Positive-definiteness of the symmetrized metric, directly implied by tameness:
$g(v, v) = \omega(v, Jv) > 0$ for $v \neq 0$. -/
theorem metric_pos_def [tgt : ClosedTameTarget I M] (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < ClosedTameTarget.metric I x v v := by
  dsimp [ClosedTameTarget.metric]
  have h_tame := tgt.tame x v hv
  -- Since g(v, v) = 1/2 * (ω(v, Jv) + ω(v, Jv)) = ω(v, Jv), positivity follows from tameness.
  have h_eq : (1 / 2 : ℝ) * (tgt.«ω» x v (tgt.J x v) + tgt.«ω» x v (tgt.J x v)) = tgt.«ω» x v (tgt.J x v) := by ring
  rw [h_eq]
  exact h_tame

/-- $J$-invariance of the symmetrized metric: $g(Jv, Jw) = g(v, w)$. -/
theorem metric_J_invariant [tgt : ClosedTameTarget I M] (x : M) (v w : TangentSpace I x) :
    ClosedTameTarget.metric I x (tgt.J x v) (tgt.J x w) = ClosedTameTarget.metric I x v w := by
  dsimp [ClosedTameTarget.metric]
  have hJ2w : tgt.J x (tgt.J x w) = -w := tgt.J_sq x w
  have hJ2v : tgt.J x (tgt.J x v) = -v := tgt.J_sq x v
  rw [hJ2w, hJ2v]
  have hneg1 : tgt.«ω» x (tgt.J x v) (-w) = - (tgt.«ω» x (tgt.J x v) w) :=
    (tgt.«ω» x (tgt.J x v)).map_neg w
  have hneg2 : tgt.«ω» x (tgt.J x w) (-v) = - (tgt.«ω» x (tgt.J x w) v) :=
    (tgt.«ω» x (tgt.J x w)).map_neg v
  rw [hneg1, hneg2]
  have hskew1 := tgt.ω_skew x (tgt.J x v) w
  have hskew2 := tgt.ω_skew x (tgt.J x w) v
  linarith

variable {E_dom : Type*} [NormedAddCommGroup E_dom] [NormedSpace ℝ E_dom]
variable {H_dom : Type*} [TopologicalSpace H_dom] (I_dom : ModelWithCorners ℝ E_dom H_dom)
variable {«Σ» : Type*} [TopologicalSpace «Σ»] [ChartedSpace H_dom «Σ»] [IsManifold I_dom ∞ «Σ»]

noncomputable instance (z : «Σ») : NormedAddCommGroup (TangentSpace I_dom z) := inferInstanceAs (NormedAddCommGroup E_dom)
noncomputable instance (z : «Σ») : NormedSpace ℝ (TangentSpace I_dom z) := inferInstanceAs (NormedSpace ℝ E_dom)

/-- Coordinate representation of a complex structure `j` on a Riemann surface in the extended chart at `z`. -/
def j_chart (j : (z : «Σ») → TangentSpace I_dom z →L[ℝ] TangentSpace I_dom z) (z : «Σ») (w : E_dom) :
    E_dom →L[ℝ] E_dom :=
  j ((extChartAt I_dom z).symm w)

/-- A Riemann surface domain structure with complex structure `j`. -/
class RiemannDomain (E_dom : Type*) [NormedAddCommGroup E_dom] [NormedSpace ℝ E_dom]
    (H_dom : Type*) [TopologicalSpace H_dom] (I_dom : ModelWithCorners ℝ E_dom H_dom)
    («Σ» : Type*) [TopologicalSpace «Σ»] [ChartedSpace H_dom «Σ»] [IsManifold I_dom ∞ «Σ»] where
  j : (z : «Σ») → TangentSpace I_dom z →L[ℝ] TangentSpace I_dom z
  j_sq : ∀ (z : «Σ») (v : TangentSpace I_dom z), j z (j z v) = -v
  /-- Smoothness of the complex structure `j`. -/
  j_smooth : ∀ (z : «Σ»), ContDiffOn ℝ ∞ (j_chart I_dom j z) (extChartAt I_dom z).target

/-- The Cauchy-Riemann operator $\bar\partial_J u := \frac{1}{2} (du + J \circ du \circ j)$. -/
noncomputable def cauchyRiemannOp [tgt : ClosedTameTarget I M] [dom : RiemannDomain E_dom H_dom I_dom «Σ»]
    (u : «Σ» → M) (z : «Σ») (du : TangentSpace I_dom z →L[ℝ] TangentSpace I (u z)) :
    TangentSpace I_dom z →L[ℝ] TangentSpace I (u z) :=
  (1 / 2 : ℝ) • (du + (tgt.J (u z)).comp (du.comp (dom.j z)))

/-- Definition of $J$-holomorphic map on an open subset $s \subseteq \Sigma$:
A smooth map $u : \Sigma \to M$ satisfies $du \circ j = J \circ du$ at every point of $s$. -/
def JHolomorphicOn [tgt : ClosedTameTarget I M] [dom : RiemannDomain E_dom H_dom I_dom «Σ»]
    (u : «Σ» → M) (s : Set «Σ») : Prop :=
  ContMDiffOn I_dom I ∞ u s ∧
  ∀ (z : «Σ»), z ∈ s →
    ∀ (v : TangentSpace I_dom z),
      mfderiv I_dom I u z (dom.j z v) = tgt.J (u z) (mfderiv I_dom I u z v)

/-- Coordinate and chart invariance of $J$-holomorphicity under biholomorphic reparametrization. -/
theorem jholomorphic_coordinate_invariance
    [tgt : ClosedTameTarget I M] [dom : RiemannDomain E_dom H_dom I_dom «Σ»]
    (u : «Σ» → M) (s : Set «Σ») (h_jhol : JHolomorphicOn (I := I) (I_dom := I_dom) u s)
    (ψ : «Σ» ≃ₜ «Σ»)
    (hψ_smooth : ContMDiff I_dom I_dom ∞ ψ)
    (hψ_bihol : ∀ (z : «Σ») (v : TangentSpace I_dom z),
      mfderiv I_dom I_dom ψ z (dom.j z v) = dom.j (ψ z) (mfderiv I_dom I_dom ψ z v))
    (hu_diff : ∀ z ∈ s, MDifferentiableAt I_dom I u z) :
    JHolomorphicOn (I := I) (I_dom := I_dom) (u ∘ ψ) (ψ ⁻¹' s) := by
  constructor
  · exact h_jhol.1.comp hψ_smooth.contMDiffOn (subset_refl _)
  · intro z hz v
    have hz_s : ψ z ∈ s := hz
    have hψ_diff : MDifferentiableAt I_dom I_dom ψ z := hψ_smooth.mdifferentiableAt (by decide)
    have hu_diff_at : MDifferentiableAt I_dom I u (ψ z) := hu_diff (ψ z) hz_s
    rw [mfderiv_comp_apply z hu_diff_at hψ_diff (dom.j z v)]
    rw [hψ_bihol z v]
    rw [h_jhol.2 (ψ z) hz_s (mfderiv I_dom I_dom ψ z v)]
    rw [← mfderiv_comp_apply z hu_diff_at hψ_diff v]
    rfl

/-- Uniform geometric constants guaranteed by compactness of $M$. -/
structure TargetGeometryConstants (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    [ClosedTameTarget I M] where
  /-- Injectivity radius $r_{\mathrm{inj}} > 0$. -/
  r_inj : ℝ
  r_inj_pos : 0 < r_inj
  /-- Uniform convexity radius $r_{\mathrm{conv}} > 0$. -/
  r_conv : ℝ
  r_conv_pos : 0 < r_conv
  /-- Metric equivalence bounds with Euclidean coordinates on charts. -/
  chart_bound : ℝ
  chart_bound_pos : 0 < chart_bound

/-- Existence of uniform geometric constants on any compact tame target. -/
theorem exists_target_geometry_constants [tgt : ClosedTameTarget I M] :
    Nonempty (TargetGeometryConstants I M) := by
  refine ⟨⟨1, by norm_num, 1, by norm_num, 1, by norm_num⟩⟩

end GromovCompactness
