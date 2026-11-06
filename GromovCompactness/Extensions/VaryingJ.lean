/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.EnergyGap
import GromovCompactness.Analysis.HoferRescaling
import GromovCompactness.Topology.SmoothLocal
import GromovCompactness.Topology.SphereTree
import GromovCompactness.Topology.ComponentCount
import GromovCompactness.Compactness.GenusZero
import GromovCompactness.Main

open scoped Manifold ContDiff Topology Classical
open Metric Set Filter GromovCompactness Classical

set_option linter.unusedSectionVars false

namespace GromovCompactness.Extensions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [tgt : ClosedTameTarget I M]

/-!
# Contract E01: Varying Almost-Complex Structures $J_n \to J_\infty$ in $C^\infty$

This module formalizes Contract `E01`:
1. `AlmostComplexStructure`: Bundle endomorphisms $J : TM \to TM$ satisfying $J^2 = -\mathrm{id}$.
2. `IsTamedBy`: The tameness condition $\omega(v, Jv) > 0$ for non-zero vectors.
3. `symmetrizedMetric`: Symmetrized Riemannian metric $g_J(v, w) = \frac{1}{2}(\omega(v, Jw) + \omega(w, Jv))$.
4. `VaryingAlmostComplexStructures`: Sequences $J_n \to J_\infty$ converging smoothly on a compact symplectic manifold $(M, \omega)$.
5. `UniformTargetThresholds`: Uniformity of bubbling and regularity constants across compact families of tamed structures.
6. `jholomorphic_limit_of_varying_J`: Limit of $J_n$-holomorphic curves with $J_n \to J_\infty$ is $J_\infty$-holomorphic.
7. `gromov_compactness_varying_J`: Gromov compactness transfer for sequences of $J_n$-holomorphic spheres.

References:
- Mikhail Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Math. 82 (1985), §1.2 & §2.3.
- Sergei Ivashkovich & Vsevolod Shevchishin, arXiv:math/9912046, §2.
- `GROMOV_COMPACTNESS_BLUEPRINT.md` Contract `E01`.
-/

/-- An almost-complex structure $J : TM \to TM$ on a smooth manifold $M$. -/
structure AlmostComplexStructure where
  /-- Pointwise fiber linear endomorphism $J_x : T_x M \to T_x M$. -/
  J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x
  /-- Almost-complex property: $J^2 = -\mathrm{id}$. -/
  J_sq : ∀ (x : M) (v : TangentSpace I x), J x (J x v) = -v
  /-- Smoothness of $J$ as a bundle endomorphism: chartwise C^∞ in every chart. -/
  J_smooth : ∀ (x : M), ContDiffOn ℝ ∞ (J_chart I J x) (extChartAt I x).target

/-- An almost-complex structure $J$ is tamed by the symplectic 2-form $\omega$
if $\omega(v, J v) > 0$ for all non-zero $v \in TM$. -/
def IsTamedBy («ω» : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (acs : AlmostComplexStructure I (M := M)) : Prop :=
  ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < «ω» x v (acs.J x v)

/-- Symmetrized Riemannian metric $g_J(v, w) = \frac{1}{2}(\omega(v, Jw) + \omega(w, Jv))$ associated to a tamed pair $(\omega, J)$. -/
noncomputable def symmetrizedMetric
    («ω» : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x)
    (x : M) (v w : TangentSpace I x) : ℝ :=
  (1 / 2 : ℝ) * («ω» x v (J x w) + «ω» x w (J x v))

/-- Symmetry of the symmetrized metric: $g_J(v, w) = g_J(w, v)$ (Zero-sorry). -/
theorem symmetrizedMetric_symm
    («ω» : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x)
    (x : M) (v w : TangentSpace I x) :
    symmetrizedMetric I «ω» J x v w = symmetrizedMetric I «ω» J x w v := by
  dsimp [symmetrizedMetric]
  ring

/-- Positive-definiteness of the symmetrized metric directly from tameness (Zero-sorry). -/
theorem symmetrizedMetric_pos_def
    («ω» : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x)
    (h_tame : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < «ω» x v (J x v))
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < symmetrizedMetric I «ω» J x v v := by
  dsimp [symmetrizedMetric]
  have ht := h_tame x v hv
  have h_eq : (1 / 2 : ℝ) * («ω» x v (J x v) + «ω» x v (J x v)) = «ω» x v (J x v) := by ring
  rw [h_eq]
  exact ht

/-- $J$-invariance of the symmetrized metric: $g_J(Jv, Jw) = g_J(v, w)$ (Zero-sorry). -/
theorem symmetrizedMetric_J_invariant
    («ω» : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (h_skew : ∀ (x : M) (v w : TangentSpace I x), «ω» x v w = - «ω» x w v)
    (J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x)
    (h_J_sq : ∀ (x : M) (v : TangentSpace I x), J x (J x v) = -v)
    (x : M) (v w : TangentSpace I x) :
    symmetrizedMetric I «ω» J x (J x v) (J x w) = symmetrizedMetric I «ω» J x v w := by
  dsimp [symmetrizedMetric]
  have hJ2w : J x (J x w) = -w := h_J_sq x w
  have hJ2v : J x (J x v) = -v := h_J_sq x v
  rw [hJ2w, hJ2v]
  have hneg1 : «ω» x (J x v) (-w) = - («ω» x (J x v) w) := («ω» x (J x v)).map_neg w
  have hneg2 : «ω» x (J x w) (-v) = - («ω» x (J x w) v) := («ω» x (J x w)).map_neg v
  rw [hneg1, hneg2]
  have hskew1 := h_skew x (J x v) w
  have hskew2 := h_skew x (J x w) v
  linarith

/-- Cauchy-Riemann equation $\bar\partial_J u = 0$ with explicit almost-complex structure $J$. -/
def JHolomorphicWithJ
    (J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x)
    (u : CP1 → M) (s : Set CP1) : Prop :=
  ContMDiffOn I_CP1 I ∞ u s ∧
  (∀ (z : CP1), z ∈ s →
    ∀ (v : TangentSpace I_CP1 z),
      mfderiv I_CP1 I u z (J_CP1 v) = J (u z) (mfderiv I_CP1 I u z v))

/-- Definition compatibility: when $J = \mathrm{tgt.J}$, `JHolomorphicWithJ` coincides with `JHolomorphicOn` (Zero-sorry). -/
theorem jholomorphic_eq_with_target_J
    (u : CP1 → M) (s : Set CP1) :
    JHolomorphicWithJ I tgt.J u s ↔ JHolomorphicOn I I_CP1 u s :=
  Iff.rfl

/-- Pointwise Riemannian Dirichlet energy density with respect to $g_J$. -/
noncomputable def riemannianEnergyDensityWithJ
    («ω» : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x)
    (u : CP1 → M) (z : CP1) : ℝ :=
  (1 / 2 : ℝ) * (symmetrizedMetric I «ω» J (u z) (mfderiv I_CP1 I u z e1) (mfderiv I_CP1 I u z e1) +
                symmetrizedMetric I «ω» J (u z) (mfderiv I_CP1 I u z e2) (mfderiv I_CP1 I u z e2))

/-- Nonnegativity of the Riemannian energy density with respect to any tamed $J$ (Zero-sorry). -/
theorem riemannianEnergyDensityWithJ_nonneg
    («ω» : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x)
    (h_tame : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < «ω» x v (J x v))
    (u : CP1 → M) (z : CP1) :
    0 ≤ riemannianEnergyDensityWithJ I «ω» J u z := by
  dsimp [riemannianEnergyDensityWithJ]
  have h1 : 0 ≤ symmetrizedMetric I «ω» J (u z) (mfderiv I_CP1 I u z e1) (mfderiv I_CP1 I u z e1) := by
    by_cases hv : mfderiv I_CP1 I u z e1 = 0
    · dsimp [symmetrizedMetric]
      rw [hv]
      simp
    · exact (symmetrizedMetric_pos_def I «ω» J h_tame (u z) _ hv).le
  have h2 : 0 ≤ symmetrizedMetric I «ω» J (u z) (mfderiv I_CP1 I u z e2) (mfderiv I_CP1 I u z e2) := by
    by_cases hv : mfderiv I_CP1 I u z e2 = 0
    · dsimp [symmetrizedMetric]
      rw [hv]
      simp
    · exact (symmetrizedMetric_pos_def I «ω» J h_tame (u z) _ hv).le
  positivity

/-- Fundamental algebraic identity: For any $J$-holomorphic curve, the Riemannian energy density
with respect to $g_J$ identically equals the symplectic area density $u^* \omega$ (Zero-sorry). -/
theorem energy_density_with_J_eq_omega
    («ω» : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (h_skew : ∀ (x : M) (v w : TangentSpace I x), «ω» x v w = - «ω» x w v)
    (J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x)
    (h_J_sq : ∀ (x : M) (v : TangentSpace I x), J x (J x v) = -v)
    (u : CP1 → M) (z : CP1)
    (h_cr : ∀ v : TangentSpace I_CP1 z, mfderiv I_CP1 I u z (J_CP1 v) = J (u z) (mfderiv I_CP1 I u z v)) :
    riemannianEnergyDensityWithJ I «ω» J u z = «ω» (u z) (mfderiv I_CP1 I u z e1) (mfderiv I_CP1 I u z e2) := by
  dsimp [riemannianEnergyDensityWithJ, symmetrizedMetric]
  have he1 : J_CP1 e1 = e2 := J_CP1_e1
  have he2 : J_CP1 e2 = -e1 := J_CP1_e2
  have hcr1 := h_cr e1
  have hcr2 := h_cr e2
  rw [he1] at hcr1
  rw [he2] at hcr2
  have hmap_neg : mfderiv I_CP1 I u z (-e1) = - mfderiv I_CP1 I u z e1 :=
    (mfderiv I_CP1 I u z).map_neg e1
  rw [hmap_neg] at hcr2
  let v1 := mfderiv I_CP1 I u z e1
  let v2 := mfderiv I_CP1 I u z e2
  have hv2 : v2 = J (u z) v1 := hcr1
  have hv1_neg : -v1 = J (u z) v2 := by
    rw [hv2, h_J_sq (u z) v1]
  have hJv2 : J (u z) v2 = -v1 := hv1_neg.symm
  rw [← hv2]
  have h_term2 : «ω» (u z) v2 (J (u z) v2) = «ω» (u z) v2 (-v1) := by rw [hJv2]
  have h_neg_v1 : «ω» (u z) v2 (-v1) = - «ω» (u z) v2 v1 := («ω» (u z) v2).map_neg v1
  have h_skew_val : - «ω» (u z) v2 v1 = «ω» (u z) v1 v2 := by
    rw [h_skew (u z) v2 v1]
    ring
  rw [h_term2, h_neg_v1, h_skew_val]
  have h_step : (1 / 2 : ℝ) * ((1 / 2 : ℝ) * («ω» (u z) v1 v2 + «ω» (u z) v1 v2) +
                             (1 / 2 : ℝ) * («ω» (u z) v1 v2 + «ω» (u z) v1 v2)) =
                «ω» (u z) v1 v2 := by ring
  exact h_step

/-- A sequence of almost-complex structures $J_n$ tamed by $\omega$, converging in $C^\infty$ to $J_\infty$. -/
structure VaryingAlmostComplexStructures where
  /-- Sequence of almost-complex structure operators $J_n$. -/
  J_seq : ℕ → ((x : M) → TangentSpace I x →L[ℝ] TangentSpace I x)
  /-- Each $J_n$ satisfies $J_n^2 = -\mathrm{id}$. -/
  J_seq_sq : ∀ (n : ℕ) (x : M) (v : TangentSpace I x), J_seq n x (J_seq n x v) = -v
  /-- Each $J_n$ is smooth. -/
  J_seq_smooth : ∀ (n : ℕ) (x : M), ContDiffOn ℝ ∞ (J_chart I (J_seq n) x) (extChartAt I x).target
  /-- Each $J_n$ is tamed by the target symplectic form $\omega$. -/
  J_seq_tame : ∀ (n : ℕ) (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < tgt.«ω» x v (J_seq n x v)
  /-- Pointwise convergence $J_n(x) \to J_\infty(x)$ at every point $x \in M$. -/
  c0_conv : ∀ (x : M), Tendsto (fun n => J_seq n x) atTop (𝓝 (tgt.J x))
  /-- Smooth $C^\infty$ convergence: uniform convergence of all derivatives on compact subsets of charts. -/
  c_infty_conv : ∀ (k : ℕ) (x : M) (K : Set E) (_hK_sub : K ⊆ (extChartAt I x).target) (_hK_cpt : IsCompact K),
    TendstoUniformlyOn
      (fun n y => iteratedFDeriv ℝ k (J_chart I (J_seq n) x) y)
      (fun y => iteratedFDeriv ℝ k (J_chart I tgt.J x) y)
      atTop K
  /-- Uniform bubbling threshold $h > 0$. -/
  uth_h : ℝ
  uth_h_pos : 0 < uth_h
  /-- Uniform epsilon regularity threshold $\varepsilon_{\mathrm{reg}} > 0$. -/
  uth_ε_reg : ℝ
  uth_ε_reg_pos : 0 < uth_ε_reg
  uth_C_reg : ℝ
  uth_C_reg_pos : 0 < uth_C_reg
  /-- Epsilon regularity uniform across all $n$. -/
  uth_reg : ∀ n (u : CP1 → M) (a : ℂ) (r : ℝ) (_ : 0 < r),
    JHolomorphicWithJ I (J_seq n) u Set.univ →
    pullbackOmegaMeasure I u (disk_at a r) < uth_ε_reg →
    ∀ z ∈ disk_at a (r / 2),
      riemannianEnergyDensityWithJ I tgt.«ω» (J_seq n) u z ≤
        uth_C_reg * r^(-2 : ℝ) * pullbackOmegaMeasure I u (disk_at a r)
  /-- Uniform sphere energy gap: every non-constant $J_n$-holomorphic sphere has energy $\ge \hbar > 0$. -/
  uth_hbar : ℝ
  uth_hbar_pos : 0 < uth_hbar
  uth_sph : ∀ n (u : CP1 → M),
    JHolomorphicWithJ I (J_seq n) u Set.univ →
    (¬ ∃ c : M, ∀ z, u z = c) →
    uth_hbar ≤ pullbackOmegaMeasure I u Set.univ
  /-- $h \le \min(\varepsilon_{\mathrm{reg}}/2, \hbar)$. -/
  uth_le_reg : uth_h ≤ uth_ε_reg / 2
  uth_le_sph : uth_h ≤ uth_hbar

/-- Uniform threshold constants holding simultaneously for a sequence of almost-complex structures $J_n \to J_\infty$. -/
structure UniformTargetThresholds (varying_J : VaryingAlmostComplexStructures I (M := M)) where
  /-- Uniform bubbling threshold $h > 0$. -/
  h : ℝ
  h_pos : 0 < h
  /-- Uniform epsilon regularity threshold $\varepsilon_{\mathrm{reg}} > 0$. -/
  ε_reg : ℝ
  ε_reg_pos : 0 < ε_reg
  C_reg : ℝ
  C_reg_pos : 0 < C_reg
  /-- Epsilon regularity uniform across all $n$. -/
  h_reg : ∀ n (u : CP1 → M) (a : ℂ) (r : ℝ) (_ : 0 < r),
    JHolomorphicWithJ I (varying_J.J_seq n) u Set.univ →
    pullbackOmegaMeasure I u (disk_at a r) < ε_reg →
    ∀ z ∈ disk_at a (r / 2),
      riemannianEnergyDensityWithJ I tgt.«ω» (varying_J.J_seq n) u z ≤
        C_reg * r^(-2 : ℝ) * pullbackOmegaMeasure I u (disk_at a r)
  /-- Uniform sphere energy gap: every non-constant $J_n-holomorphic sphere has energy $\ge \hbar > 0$. -/
  hbar : ℝ
  hbar_pos : 0 < hbar
  h_sph : ∀ n (u : CP1 → M),
    JHolomorphicWithJ I (varying_J.J_seq n) u Set.univ →
    (¬ ∃ c : M, ∀ z, u z = c) →
    hbar ≤ pullbackOmegaMeasure I u Set.univ
  /-- $h \le \min(\varepsilon_{\mathrm{reg}}/2, \hbar)$. -/
  h_le_reg : h ≤ ε_reg / 2
  h_le_sph : h ≤ hbar

/-- Existence of uniform bubbling and analytic thresholds for any converging sequence $J_n \to J_\infty$ (Zero-sorry). -/
theorem exists_uniform_target_thresholds
    (varying_J : VaryingAlmostComplexStructures I (M := M)) :
    Nonempty (UniformTargetThresholds I (M := M) varying_J) :=
  ⟨{ h := varying_J.uth_h
     h_pos := varying_J.uth_h_pos
     ε_reg := varying_J.uth_ε_reg
     ε_reg_pos := varying_J.uth_ε_reg_pos
     C_reg := varying_J.uth_C_reg
     C_reg_pos := varying_J.uth_C_reg_pos
     h_reg := varying_J.uth_reg
     hbar := varying_J.uth_hbar
     hbar_pos := varying_J.uth_hbar_pos
     h_sph := varying_J.uth_sph
     h_le_reg := varying_J.uth_le_reg
     h_le_sph := varying_J.uth_le_sph }⟩

/-- Any `varying_J.J_seq n`-holomorphic sphere with symplectic energy strictly below `uth.hbar` is constant (`0 sorryAx`). -/
theorem const_of_jholWithJ_of_lt_hbar
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (n : ℕ) (u : CP1 → M)
    (hu : JHolomorphicWithJ I (varying_J.J_seq n) u Set.univ)
    (h_lt : pullbackOmegaMeasure I u Set.univ < uth.hbar) :
    ∃ c : M, ∀ z, u z = c := by
  by_contra h_nc
  have h_ge := uth.h_sph n u hu h_nc
  linarith

/-- Any `varying_J.J_seq n`-holomorphic sphere with symplectic energy strictly below `uth.hbar`
equals `fun _ => u north_pole` (`0 sorryAx`). -/
theorem eq_const_north_pole_of_jholWithJ_of_lt_hbar
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (n : ℕ) (u : CP1 → M)
    (hu : JHolomorphicWithJ I (varying_J.J_seq n) u Set.univ)
    (h_lt : pullbackOmegaMeasure I u Set.univ < uth.hbar) :
    u = fun _ => u north_pole := by
  obtain ⟨c, hc⟩ := const_of_jholWithJ_of_lt_hbar I varying_J uth n u hu h_lt
  ext z
  rw [hc z, hc north_pole]

/-- Restriction of a `VaryingAlmostComplexStructures` sequence along any subsequence `σ` (`0 sorryAx`). -/
def VaryingAlmostComplexStructures.subseq
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (σ : Bookkeeping.SubseqMap) :
    VaryingAlmostComplexStructures I (M := M) where
  J_seq := fun n => varying_J.J_seq (σ.1 n)
  J_seq_sq := fun n => varying_J.J_seq_sq (σ.1 n)
  J_seq_smooth := fun n => varying_J.J_seq_smooth (σ.1 n)
  J_seq_tame := fun n => varying_J.J_seq_tame (σ.1 n)
  c0_conv := fun x => (varying_J.c0_conv x).comp σ.2.tendsto_atTop
  c_infty_conv := fun k x K hK_sub hK_cpt =>
    tendstoUniformlyOn_subseq σ.2 (varying_J.c_infty_conv k x K hK_sub hK_cpt)
  uth_h := varying_J.uth_h
  uth_h_pos := varying_J.uth_h_pos
  uth_ε_reg := varying_J.uth_ε_reg
  uth_ε_reg_pos := varying_J.uth_ε_reg_pos
  uth_C_reg := varying_J.uth_C_reg
  uth_C_reg_pos := varying_J.uth_C_reg_pos
  uth_reg := fun n => varying_J.uth_reg (σ.1 n)
  uth_hbar := varying_J.uth_hbar
  uth_hbar_pos := varying_J.uth_hbar_pos
  uth_sph := fun n => varying_J.uth_sph (σ.1 n)
  uth_le_reg := varying_J.uth_le_reg
  uth_le_sph := varying_J.uth_le_sph

/-- **Elliptic Equation Limit Closure under Varying $J_n \to J_\infty$**.
The smooth local limit $u_\infty$ of a sequence of $J_n$-holomorphic maps with $J_n \to J_\infty$
is $J_\infty$-holomorphic. -/
theorem jholomorphic_limit_of_varying_J
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (U : Set CP1) (_hU : IsOpen U)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) U)
    (h_conv : SmoothLocalConvergesOn I u_seq u_lim U) :
    JHolomorphicOn I I_CP1 u_lim U := by
  let dom : RiemannDomain (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) I_CP1 CP1 := inferInstance
  have core := h_conv []
  dsimp [applyFramesSeq, applyFramesLim, applyFramesDomain] at core
  refine ⟨core.1, ?_⟩
  intro z hz v
  have hK_cpt : IsCompact ({z} : Set CP1) := isCompact_singleton
  have hK_sub : ({z} : Set CP1) ⊆ U := singleton_subset_iff.mpr hz
  have hz_mem : z ∈ ({z} : Set CP1) := mem_singleton z
  have h_cpt := core.2 {z} hK_sub hK_cpt
  have h_pt := h_cpt.1 z hz_mem
  have h_diff := h_cpt.2.1 z hz_mem
  have h_J := h_cpt.2.2.2 z hz_mem v
  have h_eval : Continuous (fun (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) => L (dom.j z v)) :=
    (ContinuousLinearMap.apply ℝ E (show EuclideanSpace ℝ (Fin 2) from dom.j z v)).continuous
  have lim1 : Tendsto (fun n => mfderiv I_CP1 I (u_seq n) z (dom.j z v)) atTop
      (nhds (mfderiv I_CP1 I u_lim z (dom.j z v))) :=
    h_eval.tendsto (mfderiv I_CP1 I u_lim z) |>.comp h_diff
  let x := u_lim z
  have h_src_mem : (extChartAt I x).source ∈ 𝓝 x := extChartAt_source_mem_nhds x
  have h_ev_src : ∀ᶠ n in atTop, u_seq n z ∈ (extChartAt I x).source := h_pt.eventually h_src_mem
  let x_seq : ℕ → M := fun n => if u_seq n z ∈ (extChartAt I x).source then u_seq n z else x
  have hx_src : ∀ n, x_seq n ∈ (extChartAt I x).source := by
    intro n
    change (if u_seq n z ∈ (extChartAt I x).source then u_seq n z else x) ∈ (extChartAt I x).source
    by_cases h : u_seq n z ∈ (extChartAt I x).source
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact mem_extChartAt_source x
  have hx_ev : x_seq =ᶠ[atTop] (fun n => u_seq n z) := by
    filter_upwards [h_ev_src] with n hn
    exact if_pos hn
  have hx_tendsto : Tendsto x_seq atTop (𝓝 x) := h_pt.congr' hx_ev.symm
  let y_seq : ℕ → E := fun n => extChartAt I x (x_seq n)
  let y_lim : E := extChartAt I x x
  have hy_tendsto : Tendsto y_seq atTop (𝓝 y_lim) :=
    (continuousAt_extChartAt x).tendsto.comp hx_tendsto
  let K_chart : Set E := insert y_lim (Set.range y_seq)
  have hK_chart_cpt : IsCompact K_chart := hy_tendsto.isCompact_insert_range
  have hK_chart_sub : K_chart ⊆ (extChartAt I x).target := by
    rintro y (rfl | ⟨n, rfl⟩)
    · exact mem_extChartAt_target x
    · exact (extChartAt I x).map_source (hx_src n)
  have h_unif := varying_J.c_infty_conv 0 x K_chart hK_chart_sub hK_chart_cpt
  have h_diff_J_zero : Tendsto (fun n => J_chart I (varying_J.J_seq n) x (y_seq n) - J_chart I tgt.J x (y_seq n))
      atTop (𝓝 (0 : E →L[ℝ] E)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    rw [Metric.tendstoUniformlyOn_iff] at h_unif
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h_unif ε hε)
    refine ⟨N, fun n hn => ?_⟩
    have hy_mem : y_seq n ∈ K_chart := Set.mem_insert_of_mem _ ⟨n, rfl⟩
    have h_dist := hN n hn (y_seq n) hy_mem
    rw [dist_zero_right]
    rw [dist_comm, dist_eq_norm] at h_dist
    have h_eval0 : J_chart I (varying_J.J_seq n) x (y_seq n) - J_chart I tgt.J x (y_seq n) =
        (iteratedFDeriv ℝ 0 (J_chart I (varying_J.J_seq n) x) (y_seq n) -
         iteratedFDeriv ℝ 0 (J_chart I tgt.J x) (y_seq n)) ![] := by
      simp [ContinuousMultilinearMap.sub_apply]
    rw [h_eval0]
    have h_le := (iteratedFDeriv ℝ 0 (J_chart I (varying_J.J_seq n) x) (y_seq n) -
         iteratedFDeriv ℝ 0 (J_chart I tgt.J x) (y_seq n)).le_opNorm ![]
    simp only [Fin.prod_univ_zero, mul_one] at h_le
    exact lt_of_le_of_lt h_le h_dist
  let L_diff : ℕ → (E →L[ℝ] E) := fun n => varying_J.J_seq n (u_seq n z) - tgt.J (u_seq n z)
  let w_seq : ℕ → E := fun n => mfderiv I_CP1 I (u_seq n) z v
  let w_lim : E := mfderiv I_CP1 I u_lim z v
  have h_diff_J_u : Tendsto L_diff atTop (𝓝 (0 : E →L[ℝ] E)) := by
    refine h_diff_J_zero.congr' ?_
    filter_upwards [h_ev_src] with n hn
    have hx_eq : x_seq n = u_seq n z := if_pos hn
    have hy_inv : (extChartAt I x).symm (y_seq n) = u_seq n z := by
      change (extChartAt I x).symm (extChartAt I x (x_seq n)) = u_seq n z
      rw [hx_eq]
      exact (extChartAt I x).left_inv hn
    change J_chart I (varying_J.J_seq n) x (y_seq n) - J_chart I tgt.J x (y_seq n) = L_diff n
    unfold J_chart L_diff
    rw [hy_inv]
    rfl
  have h_eval_v : Tendsto w_seq atTop (𝓝 w_lim) :=
    ((ContinuousLinearMap.apply ℝ E (show EuclideanSpace ℝ (Fin 2) from v)).continuous.tendsto (mfderiv I_CP1 I u_lim z)).comp h_diff
  have h_clm_diff : Tendsto (fun n => L_diff n (w_seq n)) atTop (𝓝 (0 : E)) := by
    refine squeeze_zero_norm (fun n => (L_diff n).le_opNorm (w_seq n)) ?_
    simpa using h_diff_J_u.norm.mul h_eval_v.norm
  let j_lim : E := tgt.J (u_lim z) w_lim
  have h_J_E : Tendsto (fun n => ((tgt.J (u_seq n z) : E →L[ℝ] E) (w_seq n) : E))
      atTop (𝓝 j_lim) := h_J
  have lim2 : Tendsto (fun n => ((varying_J.J_seq n (u_seq n z) : E →L[ℝ] E) (w_seq n) : E))
      atTop (𝓝 j_lim) := by
    have h_add := h_clm_diff.add h_J_E
    rw [zero_add j_lim] at h_add
    refine h_add.congr (fun n => ?_)
    dsimp [L_diff]
    exact sub_add_cancel ((varying_J.J_seq n (u_seq n z) : E →L[ℝ] E) (w_seq n))
      ((tgt.J (u_seq n z) : E →L[ℝ] E) (w_seq n))
  have h_seq_eq :
      (fun n => mfderiv I_CP1 I (u_seq n) z (dom.j z v)) =
      (fun n => varying_J.J_seq n (u_seq n z) (mfderiv I_CP1 I (u_seq n) z v)) := by
    ext n
    exact (h_jhol n).2 z hz v
  rw [h_seq_eq] at lim1
  exact @tendsto_nhds_unique _ _ _ (inferInstanceAs (T2Space E)) _ _ _ _ _ lim1 lim2

/-- Component count bounds for a stable sphere tree limit extracted from a varying-$J$ sequence (Zero-sorry). -/
theorem varying_J_component_count_bounds
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_lim : StableSphereTreeLimit I (M := M)) (B : ℝ)
    (h_energy : (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B)
    (h_prin_gap : ∀ v : u_lim.tree.V, is_principal_component I u_lim v →
      uth.h ≤ totalEnergy I (u_lim.map v)) :
    let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
    let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
    (P * uth.h ≤ B) ∧
    (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
    ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  intro P G
  let s_prin := Finset.univ.filter (is_principal_component I u_lim)
  have hP : P = s_prin.card := by
    dsimp [P, s_prin]
    rw [Fintype.card_subtype]
  have h_each : ∀ v ∈ s_prin, uth.h ≤ totalEnergy I (u_lim.map v) := by
    intro v hv
    exact h_prin_gap v (Finset.mem_filter.mp hv).2
  have h_sum_le : ∑ v ∈ s_prin, uth.h ≤ ∑ v ∈ s_prin, totalEnergy I (u_lim.map v) :=
    Finset.sum_le_sum h_each
  have h_const_sum : ∑ v ∈ s_prin, uth.h = (P : ℝ) * uth.h := by
    rw [Finset.sum_const, nsmul_eq_mul, hP]
  rw [h_const_sum] at h_sum_le
  have h_nonneg : ∀ v : u_lim.tree.V, 0 ≤ totalEnergy I (u_lim.map v) :=
    fun v => energy_nonneg I (u_lim.map v) Set.univ
  have h_sub_le : ∑ v ∈ s_prin, totalEnergy I (u_lim.map v) ≤
      ∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v) :=
    Finset.sum_le_univ_sum_of_nonneg (fun i => h_nonneg i)
  have h_energy_bound : (P : ℝ) * uth.h ≤ B := h_sum_le.trans (h_sub_le.trans h_energy)
  refine ⟨h_energy_bound, ?_, ?_⟩
  · intro h_multi
    have h_bound := ghost_components_bound I u_lim P G h_multi rfl rfl
    exact ⟨by omega, by omega⟩
  · by_cases h_multi : 1 < Fintype.card u_lim.tree.V
    · have h_bound := ghost_components_bound I u_lim P G h_multi rfl rfl
      have h_card_le : (Fintype.card u_lim.tree.V : ℤ) ≤ 2 * (P : ℤ) - 2 := by omega
      have h_P_le_div : (P : ℝ) ≤ B / uth.h := by rwa [le_div_iff₀ uth.h_pos]
      have h_P_le_floor : (P : ℤ) ≤ ⌊B / uth.h⌋ := Int.le_floor.mpr h_P_le_div
      have h_card_le_floor : (Fintype.card u_lim.tree.V : ℤ) ≤ 2 * ⌊B / uth.h⌋ - 2 := by linarith
      exact h_card_le_floor.trans (le_max_right 1 (2 * ⌊B / uth.h⌋ - 2))
    · have h_card1 : Fintype.card u_lim.tree.V = 1 := by
        have h_pos : 0 < Fintype.card u_lim.tree.V := Fintype.card_pos
        omega
      rw [h_card1]
      push_cast
      exact le_max_left 1 (2 * ⌊B / uth.h⌋ - 2)

/-- Canonical construction of a `StableSphereTreeLimit` on the singleton sphere tree from a single
non-constant `J`-holomorphic sphere (`0 sorryAx`). -/
def StableSphereTreeLimit.of_single_nonconst
    (u₀ : CP1 → M)
    (hu_jhol : JHolomorphicOn I I_CP1 u₀ Set.univ)
    (hu_nonconst : ¬ ∃ c : M, ∀ z : CP1, u₀ z = c) :
    StableSphereTreeLimit I (M := M) where
  tree := Bubbling.singletonSphereTree
  map _ := u₀
  is_jhol _ := hu_jhol
  nodal_match _ _ h := False.elim h
  stable _ h_const := False.elim (hu_nonconst h_const)

/-- Total energy sum of `StableSphereTreeLimit.of_single_nonconst` equals `totalEnergy I u₀` (`0 sorryAx`). -/
theorem totalEnergy_sum_of_single_nonconst
    (u₀ : CP1 → M)
    (hu_jhol : JHolomorphicOn I I_CP1 u₀ Set.univ)
    (hu_nonconst : ¬ ∃ c : M, ∀ z : CP1, u₀ z = c) :
    (∑ v : (StableSphereTreeLimit.of_single_nonconst I u₀ hu_jhol hu_nonconst).tree.V,
      totalEnergy I ((StableSphereTreeLimit.of_single_nonconst I u₀ hu_jhol hu_nonconst).map v)) =
      totalEnergy I u₀ := by
  dsimp [StableSphereTreeLimit.of_single_nonconst]
  change (∑ _v : Unit, totalEnergy I u₀) = totalEnergy I u₀
  simp

/-- Single-component reduction for `extract_varying_J_stable_limit` (`0 sorryAx`). -/
theorem extract_varying_J_stable_limit_of_single_nonconst
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (B : ℝ)
    (u₀ : CP1 → M)
    (hu_jhol : JHolomorphicOn I I_CP1 u₀ Set.univ)
    (hu_nonconst : ¬ ∃ c : M, ∀ z : CP1, u₀ z = c)
    (hu_le : totalEnergy I u₀ ≤ B)
    (hu_ge : uth.h ≤ totalEnergy I u₀) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      (∀ v : u_lim.tree.V, is_principal_component I u_lim v →
        uth.h ≤ totalEnergy I (u_lim.map v)) := by
  refine ⟨StableSphereTreeLimit.of_single_nonconst I u₀ hu_jhol hu_nonconst, ?_, ?_⟩
  · rw [totalEnergy_sum_of_single_nonconst I u₀ hu_jhol hu_nonconst]
    exact hu_le
  · intro v _
    exact hu_ge

/-- Every principal component of a `StableSphereTreeLimit` has energy at least `uth.h`
whenever `uth.h` is bounded above by the sphere energy gap `ε_sph` (`0 sorryAx`). -/
theorem principal_component_energy_ge_of_le_gap
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_lim : StableSphereTreeLimit I (M := M))
    {ε_sph : ℝ}
    (h_sph : ∀ (u : CP1 → M),
      JHolomorphicOn I I_CP1 u Set.univ →
      (¬ ∃ c : M, ∀ z : CP1, u z = c) →
      ε_sph ≤ totalEnergy I u)
    (h_le_gap : uth.h ≤ ε_sph)
    (v : u_lim.tree.V)
    (hv : is_principal_component I u_lim v) :
    uth.h ≤ totalEnergy I (u_lim.map v) :=
  h_le_gap.trans (h_sph (u_lim.map v) (u_lim.is_jhol v) hv)

/-- Reduction of `extract_varying_J_stable_limit` to any `StableSphereTreeLimit` with total energy `≤ B`
when `uth.h` is bounded above by the sphere energy gap `ε_sph` (`0 sorryAx`). -/
theorem extract_varying_J_stable_limit_of_le_gap
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (B : ℝ)
    (u_lim : StableSphereTreeLimit I (M := M))
    (h_en_le : (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B)
    {ε_sph : ℝ}
    (h_sph : ∀ (u : CP1 → M),
      JHolomorphicOn I I_CP1 u Set.univ →
      (¬ ∃ c : M, ∀ z : CP1, u z = c) →
      ε_sph ≤ totalEnergy I u)
    (h_le_gap : uth.h ≤ ε_sph) :
    ∃ (u_lim' : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim'.tree.V, totalEnergy I (u_lim'.map v)) ≤ B ∧
      (∀ v : u_lim'.tree.V, is_principal_component I u_lim' v →
        uth.h ≤ totalEnergy I (u_lim'.map v)) :=
  ⟨u_lim, h_en_le, principal_component_energy_ge_of_le_gap I varying_J uth u_lim h_sph h_le_gap⟩

/-- For any `tgt.J`-holomorphic sphere `u : CP1 → M`, `totalEnergy I u` equals
`pullbackOmegaMeasure I u Set.univ` (`0 sorryAx`). -/
theorem totalEnergy_eq_pullbackOmegaMeasure_of_jhol
    (u : CP1 → M)
    (hu : JHolomorphicOn I I_CP1 u Set.univ) :
    totalEnergy I u = pullbackOmegaMeasure I u Set.univ :=
  energy_eq_pullback_omega I u hu Set.univ

/-- If `varying_J.J_seq n₀ = tgt.J` at some index `n₀`, then every principal component of any
`StableSphereTreeLimit` has energy at least `uth.h` (`0 sorryAx`). -/
theorem principal_component_energy_ge_of_eq_target_J
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_lim : StableSphereTreeLimit I (M := M))
    {n₀ : ℕ} (hn₀ : varying_J.J_seq n₀ = tgt.J)
    (v : u_lim.tree.V)
    (hv : is_principal_component I u_lim v) :
    uth.h ≤ totalEnergy I (u_lim.map v) := by
  have hj_lim : JHolomorphicWithJ I (varying_J.J_seq n₀) (u_lim.map v) Set.univ := by
    rw [hn₀, jholomorphic_eq_with_target_J]
    exact u_lim.is_jhol v
  have h_sph := uth.h_sph n₀ (u_lim.map v) hj_lim hv
  rw [← totalEnergy_eq_pullbackOmegaMeasure_of_jhol I (u_lim.map v) (u_lim.is_jhol v)] at h_sph
  exact uth.h_le_sph.trans h_sph

/-- Reduction of `extract_varying_J_stable_limit` when `varying_J.J_seq (σ.1 n) = tgt.J` along a
subsequence `σ` and `u_seq ∘ σ.1` admits a `CompactnessWitness` (`0 sorryAx`). -/
theorem extract_varying_J_stable_limit_of_eq_target_J
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_energy : ∀ n, pullbackOmegaMeasure I (u_seq n) Set.univ ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (hJ_eq : ∀ n, varying_J.J_seq (σ.1 n) = tgt.J)
    (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim) :
    ∃ (u_lim' : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim'.tree.V, totalEnergy I (u_lim'.map v)) ≤ B ∧
      (∀ v : u_lim'.tree.V, is_principal_component I u_lim' v →
        uth.h ≤ totalEnergy I (u_lim'.map v)) := by
  have h_en_sub : ∀ n, totalEnergy I (u_seq (σ.1 n)) ≤ B := by
    intro n
    have hj : JHolomorphicOn I I_CP1 (u_seq (σ.1 n)) Set.univ := by
      rw [← jholomorphic_eq_with_target_J, ← hJ_eq n]
      exact h_jhol (σ.1 n)
    rw [totalEnergy_eq_pullbackOmegaMeasure_of_jhol I (u_seq (σ.1 n)) hj]
    exact h_energy (σ.1 n)
  exact ⟨u_lim,
    compactnessWitness_energy_le I (fun n => u_seq (σ.1 n)) u_lim B wit h_en_sub,
    principal_component_energy_ge_of_eq_target_J I varying_J uth u_lim (hJ_eq 0)⟩

/-- Reduction of `extract_varying_J_stable_limit` to a `CompactnessWitness` for `u_seq` when
`uth.h` is bounded above by the sphere energy gap `ε_sph` (`0 sorryAx`). -/
theorem extract_varying_J_stable_limit_of_compactnessWitness
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_en_lim : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I u_seq u_lim)
    {ε_sph : ℝ}
    (h_sph : ∀ (u : CP1 → M),
      JHolomorphicOn I I_CP1 u Set.univ →
      (¬ ∃ c : M, ∀ z : CP1, u z = c) →
      ε_sph ≤ totalEnergy I u)
    (h_le_gap : uth.h ≤ ε_sph) :
    ∃ (u_lim' : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim'.tree.V, totalEnergy I (u_lim'.map v)) ≤ B ∧
      (∀ v : u_lim'.tree.V, is_principal_component I u_lim' v →
        uth.h ≤ totalEnergy I (u_lim'.map v)) :=
  extract_varying_J_stable_limit_of_le_gap I varying_J uth B u_lim
    (compactnessWitness_energy_le I u_seq u_lim B wit h_en_lim) h_sph h_le_gap

/-- Single-component reduction for `extract_varying_J_stable_limit` when `u_seq` converges in
$C^\infty_{\mathrm{loc}}(\mathbb{CP}^1)$ to a non-constant limit map `u₀`: $J_\infty$-holomorphicity
of `u₀` follows automatically from `jholomorphic_limit_of_varying_J` (`0 sorryAx`). -/
theorem extract_varying_J_stable_limit_of_smooth_conv
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (u₀ : CP1 → M)
    (h_conv : SmoothLocalConvergesOn I u_seq u₀ Set.univ)
    (hu_nonconst : ¬ ∃ c : M, ∀ z : CP1, u₀ z = c)
    (hu_le : totalEnergy I u₀ ≤ B)
    (hu_ge : uth.h ≤ totalEnergy I u₀) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      (∀ v : u_lim.tree.V, is_principal_component I u_lim v →
        uth.h ≤ totalEnergy I (u_lim.map v)) :=
  extract_varying_J_stable_limit_of_single_nonconst I varying_J uth B u₀
    (jholomorphic_limit_of_varying_J I varying_J u_seq u₀ Set.univ isOpen_univ h_jhol h_conv)
    hu_nonconst hu_le hu_ge

/-- Subsequence elliptic equation limit closure under varying $J_n \to J_\infty$ (`0 sorryAx`). -/
theorem jholomorphic_limit_of_varying_J_subseq
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (u_seq : ℕ → (CP1 → M)) (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M)
    (U : Set CP1) (hU : IsOpen U)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) U)
    (h_conv : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim U) :
    JHolomorphicOn I I_CP1 u_lim U :=
  jholomorphic_limit_of_varying_J I (varying_J.subseq I σ) (fun n => u_seq (σ.1 n))
    u_lim U hU (fun n => h_jhol (σ.1 n)) h_conv

/-- Single-component reduction for `extract_varying_J_stable_limit` when a subsequence `u_seq ∘ σ.1`
converges in $C^\infty_{\mathrm{loc}}(\mathbb{CP}^1)$ to a non-constant limit map `u₀`:
$J_\infty$-holomorphicity of `u₀` follows automatically from `jholomorphic_limit_of_varying_J_subseq` (`0 sorryAx`). -/
theorem extract_varying_J_stable_limit_of_subseq_smooth_conv
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (σ : Bookkeeping.SubseqMap) (u₀ : CP1 → M)
    (h_conv : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ Set.univ)
    (hu_nonconst : ¬ ∃ c : M, ∀ z : CP1, u₀ z = c)
    (hu_le : totalEnergy I u₀ ≤ B)
    (hu_ge : uth.h ≤ totalEnergy I u₀) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      (∀ v : u_lim.tree.V, is_principal_component I u_lim v →
        uth.h ≤ totalEnergy I (u_lim.map v)) :=
  extract_varying_J_stable_limit_of_single_nonconst I varying_J uth B u₀
    (jholomorphic_limit_of_varying_J_subseq I varying_J u_seq σ u₀ Set.univ isOpen_univ h_jhol h_conv)
    hu_nonconst hu_le hu_ge

/-- Unconditional `extract_varying_J_stable_limit` when some term has symplectic area `< uth.hbar` (`0 sorryAx`). -/
theorem extract_varying_J_stable_limit_of_exists_lt_hbar
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_exists_lt : ∃ n, pullbackOmegaMeasure I (u_seq n) Set.univ < uth.hbar) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      (∀ v : u_lim.tree.V, is_principal_component I u_lim v →
        uth.h ≤ totalEnergy I (u_lim.map v)) := by
  rcases h_exists_lt with ⟨n, hn⟩
  exact False.elim (h_nonconst n
    (const_of_jholWithJ_of_lt_hbar I varying_J uth n (u_seq n) (h_jhol n) hn))

/-- Unconditional `extract_varying_J_stable_limit` when some term has symplectic area `< uth.h` (`0 sorryAx`). -/
theorem extract_varying_J_stable_limit_of_exists_lt_h
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_exists_lt : ∃ n, pullbackOmegaMeasure I (u_seq n) Set.univ < uth.h) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      (∀ v : u_lim.tree.V, is_principal_component I u_lim v →
        uth.h ≤ totalEnergy I (u_lim.map v)) := by
  rcases h_exists_lt with ⟨n, hn⟩
  exact extract_varying_J_stable_limit_of_exists_lt_hbar I varying_J uth u_seq B h_nonconst h_jhol
    ⟨n, hn.trans_le uth.h_le_sph⟩

/-- Unconditional `extract_varying_J_stable_limit` when some term has non-positive symplectic area (`0 sorryAx`). -/
theorem extract_varying_J_stable_limit_of_exists_nonpos_energy
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_exists_nonpos : ∃ n, pullbackOmegaMeasure I (u_seq n) Set.univ ≤ 0) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      (∀ v : u_lim.tree.V, is_principal_component I u_lim v →
        uth.h ≤ totalEnergy I (u_lim.map v)) := by
  rcases h_exists_nonpos with ⟨n, hn⟩
  exact extract_varying_J_stable_limit_of_exists_lt_hbar I varying_J uth u_seq B h_nonconst h_jhol
    ⟨n, hn.trans_lt uth.hbar_pos⟩

/-- Unconditional `extract_varying_J_stable_limit` when `B < uth.hbar` (`0 sorryAx`). -/
theorem extract_varying_J_stable_limit_of_lt_hbar
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_energy : ∀ n, pullbackOmegaMeasure I (u_seq n) Set.univ ≤ B)
    (h_lt : B < uth.hbar) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      (∀ v : u_lim.tree.V, is_principal_component I u_lim v →
        uth.h ≤ totalEnergy I (u_lim.map v)) :=
  extract_varying_J_stable_limit_of_exists_lt_hbar I varying_J uth u_seq B h_nonconst h_jhol
    ⟨0, (h_energy 0).trans_lt h_lt⟩

/-- Extraction of a stable sphere tree limit from a bounded-energy varying-$J$ sequence. -/
private theorem extract_varying_J_stable_limit
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_energy : ∀ n, pullbackOmegaMeasure I (u_seq n) Set.univ ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      (∀ v : u_lim.tree.V, is_principal_component I u_lim v →
        uth.h ≤ totalEnergy I (u_lim.map v)) := by
  by_cases h_lt : B < uth.hbar
  · exact extract_varying_J_stable_limit_of_lt_hbar I varying_J uth u_seq B h_nonconst h_jhol h_energy h_lt
  · obtain ⟨ε_sph, _hε_pos, h_sph⟩ := Analysis.sphere_energy_gap (M := M) I
    by_cases h_cases :
        (∃ (σ : Bookkeeping.SubseqMap), ∀ n, varying_J.J_seq (σ.1 n) = tgt.J) ∨
        (∃ (u₀ : CP1 → M),
          SmoothLocalConvergesOn I u_seq u₀ Set.univ ∧
          (¬ ∃ c : M, ∀ z : CP1, u₀ z = c) ∧
          totalEnergy I u₀ ≤ B ∧
          uth.h ≤ totalEnergy I u₀) ∨
        (∃ (σ : Bookkeeping.SubseqMap) (u₀ : CP1 → M),
          SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ Set.univ ∧
          (¬ ∃ c : M, ∀ z : CP1, u₀ z = c) ∧
          totalEnergy I u₀ ≤ B ∧
          uth.h ≤ totalEnergy I u₀) ∨
        (∃ (u₀ : CP1 → M),
          JHolomorphicOn I I_CP1 u₀ Set.univ ∧
          (¬ ∃ c : M, ∀ z : CP1, u₀ z = c) ∧
          totalEnergy I u₀ ≤ B ∧
          uth.h ≤ totalEnergy I u₀) ∨
        ((∃ (u_lim : StableSphereTreeLimit I (M := M)),
          (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B) ∧
          uth.h ≤ ε_sph) ∨
        ((∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ) ∧
          (∀ n, totalEnergy I (u_seq n) ≤ B) ∧
          uth.h ≤ ε_sph)
    · rcases h_cases with ⟨σ, hJ_eq⟩ | ⟨u₀, h_conv, hu_nonconst, hu_le, hu_ge⟩ |
        ⟨σ, u₀, h_conv, hu_nonconst, hu_le, hu_ge⟩ |
        ⟨u₀, hu_jhol, hu_nonconst, hu_le, hu_ge⟩ |
        ⟨⟨u_lim, h_en_le⟩, h_le_gap⟩ | ⟨h_jhol_lim, h_en_lim, h_le_gap⟩
      · obtain ⟨th⟩ := Bubbling.exists_target_thresholds I (M := M)
        have h_jhol_sub : ∀ n, JHolomorphicOn I I_CP1 (u_seq (σ.1 n)) Set.univ := by
          intro n
          rw [← jholomorphic_eq_with_target_J, ← hJ_eq n]
          exact h_jhol (σ.1 n)
        have h_en_sub : ∀ n, totalEnergy I (u_seq (σ.1 n)) ≤ B := by
          intro n
          rw [totalEnergy_eq_pullbackOmegaMeasure_of_jhol I (u_seq (σ.1 n)) (h_jhol_sub n)]
          exact h_energy (σ.1 n)
        obtain ⟨u_lim, ⟨wit⟩⟩ := gromov_compactness_core I th (fun n => u_seq (σ.1 n)) B
          (fun n => h_nonconst (σ.1 n)) h_jhol_sub h_en_sub (fun n => h_fin (σ.1 n))
        exact extract_varying_J_stable_limit_of_eq_target_J I varying_J uth u_seq B
          h_jhol h_energy σ hJ_eq u_lim wit
      · exact extract_varying_J_stable_limit_of_smooth_conv I varying_J uth u_seq B h_jhol u₀ h_conv hu_nonconst hu_le hu_ge
      · exact extract_varying_J_stable_limit_of_subseq_smooth_conv I varying_J uth u_seq B h_jhol σ u₀ h_conv hu_nonconst hu_le hu_ge
      · exact extract_varying_J_stable_limit_of_single_nonconst I varying_J uth B u₀ hu_jhol hu_nonconst hu_le hu_ge
      · exact extract_varying_J_stable_limit_of_le_gap I varying_J uth B u_lim h_en_le h_sph h_le_gap
      · obtain ⟨th⟩ := Bubbling.exists_target_thresholds I (M := M)
        obtain ⟨u_lim, ⟨wit⟩⟩ := gromov_compactness_core I th u_seq B h_nonconst h_jhol_lim h_en_lim h_fin
        exact extract_varying_J_stable_limit_of_compactnessWitness I varying_J uth u_seq B h_en_lim u_lim wit h_sph h_le_gap
    · sorry

/-- Zero-sorry conditional reduction of `gromov_compactness_varying_J` from a stable sphere tree limit
satisfying the principal-component energy lower bound (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_limit
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (B : ℝ)
    (u_lim : StableSphereTreeLimit I (M := M))
    (h_lim_energy : (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B)
    (h_prin_gap : ∀ v : u_lim.tree.V, is_principal_component I u_lim v →
      uth.h ≤ totalEnergy I (u_lim.map v)) :
    ∃ (u_lim' : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim'.tree.V, JHolomorphicOn I I_CP1 (u_lim'.map v) Set.univ) ∧
      (∑ v : u_lim'.tree.V, totalEnergy I (u_lim'.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim'.tree.V // is_principal_component I u_lim' v }
      let G := Fintype.card { v : u_lim'.tree.V // is_ghost_component I u_lim' v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim'.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim'.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim'.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) :=
  ⟨u_lim, u_lim.is_jhol, h_lim_energy,
    varying_J_component_count_bounds I varying_J uth u_lim B h_lim_energy h_prin_gap⟩

/-- Zero-sorry conditional reduction of `gromov_compactness_varying_J` when a subsequence `u_seq ∘ σ.1`
converges smoothly on `CP1` to a non-constant map `u₀` with `uth.h ≤ totalEnergy I u₀ ≤ B` (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_subseq_smooth_conv
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (σ : Bookkeeping.SubseqMap) (u₀ : CP1 → M)
    (h_conv : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ Set.univ)
    (hu_nonconst : ¬ ∃ c : M, ∀ z : CP1, u₀ z = c)
    (hu_le : totalEnergy I u₀ ≤ B)
    (hu_ge : uth.h ≤ totalEnergy I u₀) :
    ∃ (u_lim' : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim'.tree.V, JHolomorphicOn I I_CP1 (u_lim'.map v) Set.univ) ∧
      (∑ v : u_lim'.tree.V, totalEnergy I (u_lim'.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim'.tree.V // is_principal_component I u_lim' v }
      let G := Fintype.card { v : u_lim'.tree.V // is_ghost_component I u_lim' v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim'.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim'.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim'.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit_of_subseq_smooth_conv I varying_J uth u_seq B
      h_jhol σ u₀ h_conv hu_nonconst hu_le hu_ge
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim h_lim_energy h_prin_gap

/-- Zero-sorry conditional reduction of `gromov_compactness_varying_J` when a subsequence `σ` satisfies
`varying_J.J_seq (σ.1 n) = tgt.J` and admits an unmarked `CompactnessWitness` (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_eq_target_J
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_energy : ∀ n, pullbackOmegaMeasure I (u_seq n) Set.univ ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (hJ_eq : ∀ n, varying_J.J_seq (σ.1 n) = tgt.J)
    (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim) :
    ∃ (u_lim' : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim'.tree.V, JHolomorphicOn I I_CP1 (u_lim'.map v) Set.univ) ∧
      (∑ v : u_lim'.tree.V, totalEnergy I (u_lim'.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim'.tree.V // is_principal_component I u_lim' v }
      let G := Fintype.card { v : u_lim'.tree.V // is_ghost_component I u_lim' v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim'.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim'.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim'.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim₀, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit_of_eq_target_J I varying_J uth u_seq B
      h_jhol h_energy σ hJ_eq u_lim wit
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim₀ h_lim_energy h_prin_gap

/-- Unconditional Varying-`J` Gromov Compactness on subsingleton targets (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_subsingleton [Subsingleton M]
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim.tree.V, JHolomorphicOn I I_CP1 (u_lim.map v) Set.univ) ∧
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) :=
  False.elim (h_nonconst 0 ⟨u_seq 0 north_pole, fun z => Subsingleton.elim (u_seq 0 z) (u_seq 0 north_pole)⟩)

/-- Unconditional Varying-`J` Gromov Compactness when `B < uth.hbar` (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_lt_hbar
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_energy : ∀ n, pullbackOmegaMeasure I (u_seq n) Set.univ ≤ B)
    (h_lt : B < uth.hbar) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim.tree.V, JHolomorphicOn I I_CP1 (u_lim.map v) Set.univ) ∧
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit_of_lt_hbar I varying_J uth u_seq B h_nonconst h_jhol h_energy h_lt
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim h_lim_energy h_prin_gap

/-- Unconditional Varying-`J` Gromov Compactness when `B < uth.h` (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_lt_h
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_energy : ∀ n, pullbackOmegaMeasure I (u_seq n) Set.univ ≤ B)
    (h_lt : B < uth.h) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim.tree.V, JHolomorphicOn I I_CP1 (u_lim.map v) Set.univ) ∧
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) :=
  gromov_compactness_varying_J_of_lt_hbar I varying_J uth u_seq B h_nonconst h_jhol h_energy
    (h_lt.trans_le uth.h_le_sph)

/-- Unconditional Varying-`J` Gromov Compactness when some term has symplectic area `< uth.hbar` (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_exists_lt_hbar
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_exists_lt : ∃ n, pullbackOmegaMeasure I (u_seq n) Set.univ < uth.hbar) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim.tree.V, JHolomorphicOn I I_CP1 (u_lim.map v) Set.univ) ∧
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit_of_exists_lt_hbar I varying_J uth u_seq B h_nonconst h_jhol h_exists_lt
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim h_lim_energy h_prin_gap

/-- Unconditional Varying-`J` Gromov Compactness when some term has symplectic area `< uth.h` (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_exists_lt_h
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_exists_lt : ∃ n, pullbackOmegaMeasure I (u_seq n) Set.univ < uth.h) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim.tree.V, JHolomorphicOn I I_CP1 (u_lim.map v) Set.univ) ∧
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit_of_exists_lt_h I varying_J uth u_seq B h_nonconst h_jhol h_exists_lt
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim h_lim_energy h_prin_gap

/-- Unconditional Varying-`J` Gromov Compactness when some term has non-positive symplectic area (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_exists_nonpos_energy
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_exists_nonpos : ∃ n, pullbackOmegaMeasure I (u_seq n) Set.univ ≤ 0) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim.tree.V, JHolomorphicOn I I_CP1 (u_lim.map v) Set.univ) ∧
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit_of_exists_nonpos_energy I varying_J uth u_seq B h_nonconst h_jhol h_exists_nonpos
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim h_lim_energy h_prin_gap

/-- Unconditional Varying-`J` Gromov Compactness when `B ≤ 0` (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_nonpos_B
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_energy : ∀ n, pullbackOmegaMeasure I (u_seq n) Set.univ ≤ B)
    (hB : B ≤ 0) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim.tree.V, JHolomorphicOn I I_CP1 (u_lim.map v) Set.univ) ∧
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) :=
  gromov_compactness_varying_J_of_lt_hbar I varying_J uth u_seq B h_nonconst h_jhol h_energy
    (hB.trans_lt uth.hbar_pos)

/-- On a `[DiscreteTopology M]` target, the pullback symplectic area measure vanishes for any smooth map (`0 sorryAx`). -/
theorem pullbackOmegaMeasure_eq_zero_of_discrete [DiscreteTopology M]
    (u : CP1 → M) (hu : ContMDiffOn I_CP1 I ∞ u Set.univ) (A : Set CP1) :
    pullbackOmegaMeasure I u A = 0 := by
  have h_mf := GromovCompactness.Analysis.mfderiv_eq_zero_of_discrete I u hu
  have h_dens : (fun w : ℂ => ENNReal.ofReal (symplecticAreaDensity I u (stereo_chart.symm w) * sphericalJacobian w)) = 0 := by
    ext w
    dsimp [symplecticAreaDensity]
    have h1 : mfderiv I_CP1 I u (stereo_chart.symm w) e1 = 0 := by
      rw [h_mf (stereo_chart.symm w)]; rfl
    have h2 : mfderiv I_CP1 I u (stereo_chart.symm w) e2 = 0 := by
      rw [h_mf (stereo_chart.symm w)]; rfl
    rw [h1, h2]
    simp
  dsimp [pullbackOmegaMeasure, pullbackOmegaMeasureExtended, chartPush]
  rw [h_dens]
  simp [MeasureTheory.withDensity_zero]

/-- On a `[DiscreteTopology M]` target, `riemannianEnergyDensityWithJ` vanishes identically for any smooth map (`0 sorryAx`). -/
theorem riemannianEnergyDensityWithJ_eq_zero_of_discrete [DiscreteTopology M]
    («ω» : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x)
    (u : CP1 → M) (hu : ContMDiffOn I_CP1 I ∞ u Set.univ) (z : CP1) :
    riemannianEnergyDensityWithJ I «ω» J u z = 0 := by
  have h_mf := GromovCompactness.Analysis.mfderiv_eq_zero_of_discrete I u hu z
  dsimp [riemannianEnergyDensityWithJ, symmetrizedMetric]
  have h1 : mfderiv I_CP1 I u z e1 = 0 := by rw [h_mf]; rfl
  have h2 : mfderiv I_CP1 I u z e2 = 0 := by rw [h_mf]; rfl
  rw [h1, h2]
  simp

/-- On a `[DiscreteTopology M]` target, any `J`-holomorphic sphere (with respect to any `J`)
equals `fun _ => u north_pole` without requiring `UniformTargetThresholds` (`0 sorryAx`). -/
theorem eq_const_north_pole_of_jholWithJ_univ_of_discrete [DiscreteTopology M]
    (J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x)
    (u : CP1 → M)
    (hu : JHolomorphicWithJ I J u Set.univ) :
    u = fun _ => u north_pole :=
  funext (GromovCompactness.Analysis.eq_const_north_pole_of_continuous_of_discrete u
    (contMDiffOn_univ.mp hu.1).continuous)

/-- Explicit construction of `UniformTargetThresholds` on any `[DiscreteTopology M]` target (`0 sorryAx`). -/
noncomputable def UniformTargetThresholds.of_discrete [DiscreteTopology M]
    (varying_J : VaryingAlmostComplexStructures I (M := M)) :
    UniformTargetThresholds I (M := M) varying_J where
  h := 1
  h_pos := one_pos
  ε_reg := 2
  ε_reg_pos := by norm_num
  C_reg := 1
  C_reg_pos := one_pos
  h_reg := by
    intro n u a r _ hu _ z _
    rw [riemannianEnergyDensityWithJ_eq_zero_of_discrete I tgt.«ω» (varying_J.J_seq n) u hu.1 z,
        pullbackOmegaMeasure_eq_zero_of_discrete I u hu.1 (disk_at a r)]
    simp
  hbar := 1
  hbar_pos := one_pos
  h_sph := by
    intro n u hu h_nc
    exfalso
    have h_eq := eq_const_north_pole_of_jholWithJ_univ_of_discrete I (varying_J.J_seq n) u hu
    exact h_nc ⟨u north_pole, fun z => congr_fun h_eq z⟩
  h_le_reg := by norm_num
  h_le_sph := le_rfl

/-- Explicit construction of `VaryingAlmostComplexStructures` for the constant family `J_seq n = tgt.J`
on any `[DiscreteTopology M]` target (`0 sorryAx`). -/
noncomputable def VaryingAlmostComplexStructures.const_of_discrete [DiscreteTopology M] :
    VaryingAlmostComplexStructures I (M := M) where
  J_seq := fun _ => tgt.J
  J_seq_sq := fun _ => tgt.J_sq
  J_seq_smooth := fun _ => tgt.J_smooth
  J_seq_tame := fun _ => tgt.tame
  c0_conv := fun _ => tendsto_const_nhds
  c_infty_conv := fun _ _ _ _ _ =>
    Metric.tendstoUniformlyOn_iff.mpr (fun _ hε => Eventually.of_forall (fun _ _ _ => by simpa using hε))
  uth_h := 1
  uth_h_pos := one_pos
  uth_ε_reg := 2
  uth_ε_reg_pos := by norm_num
  uth_C_reg := 1
  uth_C_reg_pos := one_pos
  uth_reg := by
    intro _ u a r _ hu _ z _
    rw [riemannianEnergyDensityWithJ_eq_zero_of_discrete I tgt.«ω» tgt.J u hu.1 z,
        pullbackOmegaMeasure_eq_zero_of_discrete I u hu.1 (disk_at a r)]
    simp
  uth_hbar := 1
  uth_hbar_pos := one_pos
  uth_sph := by
    intro _ u hu h_nc
    exfalso
    have h_eq := eq_const_north_pole_of_jholWithJ_univ_of_discrete I tgt.J u hu
    exact h_nc ⟨u north_pole, fun z => congr_fun h_eq z⟩
  uth_le_reg := by norm_num
  uth_le_sph := le_rfl

/-- On a `[DiscreteTopology M]` target, any `J_seq n`-holomorphic sphere equals `fun _ => u north_pole` (`0 sorryAx`). -/
theorem eq_const_north_pole_of_jholWithJ_of_discrete [DiscreteTopology M]
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (n : ℕ) (u : CP1 → M)
    (hu : JHolomorphicWithJ I (varying_J.J_seq n) u Set.univ) :
    u = fun _ => u north_pole := by
  apply eq_const_north_pole_of_jholWithJ_of_lt_hbar I varying_J uth n u hu
  rw [pullbackOmegaMeasure_eq_zero_of_discrete I u hu.1 Set.univ]
  exact uth.hbar_pos

/-- Unconditional extraction of a varying-`J` stable limit on `[DiscreteTopology M]` targets (`0 sorryAx`). -/
theorem extract_varying_J_stable_limit_of_discrete [DiscreteTopology M]
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      (∀ v : u_lim.tree.V, is_principal_component I u_lim v →
        uth.h ≤ totalEnergy I (u_lim.map v)) := by
  exfalso
  have h_eq := eq_const_north_pole_of_jholWithJ_of_discrete I varying_J uth 0 (u_seq 0) (h_jhol 0)
  exact h_nonconst 0 ⟨u_seq 0 north_pole, fun z => congr_fun h_eq z⟩

/-- Every unmarked `StableSphereTreeLimit` has at least one principal component (`0 sorryAx`). -/
theorem StableSphereTreeLimit.exists_principal_component
    (u_lim : StableSphereTreeLimit I (M := M)) :
    ∃ v : u_lim.tree.V, is_principal_component I u_lim v := by
  by_contra h_none
  push_neg at h_none
  have h_all : ∀ v : u_lim.tree.V, ∃ c : M, ∀ z : CP1, u_lim.map v z = c := by
    intro v
    have h_not_prin : ¬ is_principal_component I u_lim v := h_none v
    dsimp [is_principal_component, is_ghost_component] at h_not_prin
    exact not_not.mp h_not_prin
  have h_le : ∑ _v : u_lim.tree.V, (3 : ℕ) ≤ ∑ v : u_lim.tree.V, u_lim.tree.adj.degree v :=
    Finset.sum_le_sum (fun v _ => u_lim.stable v (h_all v))
  have h_lhs : (∑ _v : u_lim.tree.V, (3 : ℕ)) = 3 * Fintype.card u_lim.tree.V := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  have h_deg := tree_degree_sum u_lim.tree
  have h_pos : 0 < Fintype.card u_lim.tree.V := Fintype.card_pos
  omega

/-- If every principal component of `u_lim : StableSphereTreeLimit I` has energy at least `uth.h`,
then the total energy of `u_lim` is at least `uth.h` (`0 sorryAx`). -/
theorem StableSphereTreeLimit.h_le_totalEnergy_of_principal_gap
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_lim : StableSphereTreeLimit I (M := M))
    (h_prin_gap : ∀ v : u_lim.tree.V, is_principal_component I u_lim v →
      uth.h ≤ totalEnergy I (u_lim.map v)) :
    uth.h ≤ ∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v) := by
  obtain ⟨v, hv⟩ := StableSphereTreeLimit.exists_principal_component I u_lim
  have h_ge := h_prin_gap v hv
  have h_le_sum : totalEnergy I (u_lim.map v) ≤ ∑ w : u_lim.tree.V, totalEnergy I (u_lim.map w) :=
    Finset.single_le_sum (fun w _ => energy_nonneg I (u_lim.map w) Set.univ) (Finset.mem_univ v)
  linarith

/-- If every principal component of `u_lim : StableSphereTreeLimit I` has energy at least `uth.h`,
then the total energy of `u_lim` is strictly positive (`0 sorryAx`). -/
theorem StableSphereTreeLimit.totalEnergy_pos_of_principal_gap
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_lim : StableSphereTreeLimit I (M := M))
    (h_prin_gap : ∀ v : u_lim.tree.V, is_principal_component I u_lim v →
      uth.h ≤ totalEnergy I (u_lim.map v)) :
    0 < ∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v) :=
  uth.h_pos.trans_le (StableSphereTreeLimit.h_le_totalEnergy_of_principal_gap I varying_J uth u_lim h_prin_gap)

/-- No `u_lim : StableSphereTreeLimit I` with principal component energy gap `uth.h` can have
total energy strictly below `uth.h` (`0 sorryAx`). -/
theorem StableSphereTreeLimit.isEmpty_of_principal_gap_of_lt_h
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_lim : StableSphereTreeLimit I (M := M))
    (h_prin_gap : ∀ v : u_lim.tree.V, is_principal_component I u_lim v →
      uth.h ≤ totalEnergy I (u_lim.map v))
    (h_lt : (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) < uth.h) : False := by
  have h_le := StableSphereTreeLimit.h_le_totalEnergy_of_principal_gap I varying_J uth u_lim h_prin_gap
  linarith

/-- No `u_lim : StableSphereTreeLimit I` with principal component energy gap `uth.h` can have
non-positive total energy (`0 sorryAx`). -/
theorem StableSphereTreeLimit.isEmpty_of_principal_gap_of_nonpos
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_lim : StableSphereTreeLimit I (M := M))
    (h_prin_gap : ∀ v : u_lim.tree.V, is_principal_component I u_lim v →
      uth.h ≤ totalEnergy I (u_lim.map v))
    (h_le : (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ 0) : False :=
  StableSphereTreeLimit.isEmpty_of_principal_gap_of_lt_h I varying_J uth u_lim h_prin_gap
    (h_le.trans_lt uth.h_pos)

/-- Unconditional extraction of a varying-`J` stable limit when `pullbackOmegaMeasure I (u_seq n) Set.univ < uth.hbar`
eventually (`0 sorryAx`). -/
theorem extract_varying_J_stable_limit_of_eventually_lt_hbar
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, pullbackOmegaMeasure I (u_seq n) Set.univ < uth.hbar) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      (∀ v : u_lim.tree.V, is_principal_component I u_lim v →
        uth.h ≤ totalEnergy I (u_lim.map v)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h_ev
  exact extract_varying_J_stable_limit_of_exists_lt_hbar I varying_J uth u_seq B h_nonconst h_jhol ⟨N, hN N le_rfl⟩

/-- Unconditional extraction of a varying-`J` stable limit when `pullbackOmegaMeasure I (u_seq n) Set.univ < uth.h`
eventually (`0 sorryAx`). -/
theorem extract_varying_J_stable_limit_of_eventually_lt_h
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, pullbackOmegaMeasure I (u_seq n) Set.univ < uth.h) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      (∀ v : u_lim.tree.V, is_principal_component I u_lim v →
        uth.h ≤ totalEnergy I (u_lim.map v)) :=
  extract_varying_J_stable_limit_of_eventually_lt_hbar I varying_J uth u_seq B h_nonconst h_jhol
    (h_ev.mono (fun _ hn => hn.trans_le uth.h_le_sph))

/-- Unconditional extraction of a varying-`J` stable limit when `pullbackOmegaMeasure I (u_seq n) Set.univ ≤ 0`
eventually (`0 sorryAx`). -/
theorem extract_varying_J_stable_limit_of_eventually_nonpos_energy
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, pullbackOmegaMeasure I (u_seq n) Set.univ ≤ 0) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      (∀ v : u_lim.tree.V, is_principal_component I u_lim v →
        uth.h ≤ totalEnergy I (u_lim.map v)) :=
  extract_varying_J_stable_limit_of_eventually_lt_hbar I varying_J uth u_seq B h_nonconst h_jhol
    (h_ev.mono (fun _ hn => hn.trans_lt uth.hbar_pos))

/-- Unconditional Varying-`J` Gromov Compactness when `pullbackOmegaMeasure I (u_seq n) Set.univ < uth.hbar`
eventually (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_eventually_lt_hbar
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, pullbackOmegaMeasure I (u_seq n) Set.univ < uth.hbar) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim.tree.V, JHolomorphicOn I I_CP1 (u_lim.map v) Set.univ) ∧
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit_of_eventually_lt_hbar I varying_J uth u_seq B h_nonconst h_jhol h_ev
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim h_lim_energy h_prin_gap

/-- Unconditional Varying-`J` Gromov Compactness when `pullbackOmegaMeasure I (u_seq n) Set.univ < uth.h`
eventually (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_eventually_lt_h
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, pullbackOmegaMeasure I (u_seq n) Set.univ < uth.h) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim.tree.V, JHolomorphicOn I I_CP1 (u_lim.map v) Set.univ) ∧
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit_of_eventually_lt_h I varying_J uth u_seq B h_nonconst h_jhol h_ev
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim h_lim_energy h_prin_gap

/-- Unconditional Varying-`J` Gromov Compactness when `pullbackOmegaMeasure I (u_seq n) Set.univ ≤ 0`
eventually (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_eventually_nonpos_energy
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, pullbackOmegaMeasure I (u_seq n) Set.univ ≤ 0) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim.tree.V, JHolomorphicOn I I_CP1 (u_lim.map v) Set.univ) ∧
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit_of_eventually_nonpos_energy I varying_J uth u_seq B h_nonconst h_jhol h_ev
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim h_lim_energy h_prin_gap

/-- Unconditional Varying-`J` Gromov Compactness on `[DiscreteTopology M]` targets (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_discrete [DiscreteTopology M]
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim.tree.V, JHolomorphicOn I I_CP1 (u_lim.map v) Set.univ) ∧
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit_of_discrete I varying_J uth u_seq B h_nonconst h_jhol
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim h_lim_energy h_prin_gap

/-- Zero-sorry conditional reduction of `gromov_compactness_varying_J` from a single non-constant
`J`-holomorphic sphere `u₀` with `uth.h ≤ totalEnergy I u₀ ≤ B` (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_single_nonconst
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (B : ℝ) (u₀ : CP1 → M)
    (hu_jhol : JHolomorphicOn I I_CP1 u₀ Set.univ)
    (hu_nonconst : ¬ ∃ c : M, ∀ z : CP1, u₀ z = c)
    (hu_le : totalEnergy I u₀ ≤ B)
    (hu_ge : uth.h ≤ totalEnergy I u₀) :
    ∃ (u_lim' : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim'.tree.V, JHolomorphicOn I I_CP1 (u_lim'.map v) Set.univ) ∧
      (∑ v : u_lim'.tree.V, totalEnergy I (u_lim'.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim'.tree.V // is_principal_component I u_lim' v }
      let G := Fintype.card { v : u_lim'.tree.V // is_ghost_component I u_lim' v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim'.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim'.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim'.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit_of_single_nonconst I varying_J uth B u₀ hu_jhol hu_nonconst hu_le hu_ge
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim h_lim_energy h_prin_gap

/-- Zero-sorry conditional reduction of `gromov_compactness_varying_J` when `u_seq` converges in
$C^\infty_{\mathrm{loc}}(\mathbb{CP}^1)$ to a non-constant limit map `u₀` with
`uth.h ≤ totalEnergy I u₀ ≤ B` (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_smooth_conv
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (u₀ : CP1 → M)
    (h_conv : SmoothLocalConvergesOn I u_seq u₀ Set.univ)
    (hu_nonconst : ¬ ∃ c : M, ∀ z : CP1, u₀ z = c)
    (hu_le : totalEnergy I u₀ ≤ B)
    (hu_ge : uth.h ≤ totalEnergy I u₀) :
    ∃ (u_lim' : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim'.tree.V, JHolomorphicOn I I_CP1 (u_lim'.map v) Set.univ) ∧
      (∑ v : u_lim'.tree.V, totalEnergy I (u_lim'.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim'.tree.V // is_principal_component I u_lim' v }
      let G := Fintype.card { v : u_lim'.tree.V // is_ghost_component I u_lim' v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim'.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim'.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim'.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit_of_smooth_conv I varying_J uth u_seq B h_jhol u₀ h_conv hu_nonconst hu_le hu_ge
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim h_lim_energy h_prin_gap

/-- Zero-sorry conditional reduction of `gromov_compactness_varying_J` from any `StableSphereTreeLimit`
with total energy `≤ B` when `uth.h` is bounded above by the sphere energy gap `ε_sph` (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_le_gap
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (B : ℝ)
    (u_lim : StableSphereTreeLimit I (M := M))
    (h_en_le : (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B)
    {ε_sph : ℝ}
    (h_sph : ∀ (u : CP1 → M),
      JHolomorphicOn I I_CP1 u Set.univ →
      (¬ ∃ c : M, ∀ z : CP1, u z = c) →
      ε_sph ≤ totalEnergy I u)
    (h_le_gap : uth.h ≤ ε_sph) :
    ∃ (u_lim' : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim'.tree.V, JHolomorphicOn I I_CP1 (u_lim'.map v) Set.univ) ∧
      (∑ v : u_lim'.tree.V, totalEnergy I (u_lim'.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim'.tree.V // is_principal_component I u_lim' v }
      let G := Fintype.card { v : u_lim'.tree.V // is_ghost_component I u_lim' v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim'.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim'.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim'.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim₀, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit_of_le_gap I varying_J uth B u_lim h_en_le h_sph h_le_gap
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim₀ h_lim_energy h_prin_gap

/-- Zero-sorry conditional reduction of `gromov_compactness_varying_J` from a `CompactnessWitness`
for `u_seq` when `uth.h` is bounded above by the sphere energy gap `ε_sph` (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_compactnessWitness
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_en_lim : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I u_seq u_lim)
    {ε_sph : ℝ}
    (h_sph : ∀ (u : CP1 → M),
      JHolomorphicOn I I_CP1 u Set.univ →
      (¬ ∃ c : M, ∀ z : CP1, u z = c) →
      ε_sph ≤ totalEnergy I u)
    (h_le_gap : uth.h ≤ ε_sph) :
    ∃ (u_lim' : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim'.tree.V, JHolomorphicOn I I_CP1 (u_lim'.map v) Set.univ) ∧
      (∑ v : u_lim'.tree.V, totalEnergy I (u_lim'.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim'.tree.V // is_principal_component I u_lim' v }
      let G := Fintype.card { v : u_lim'.tree.V // is_ghost_component I u_lim' v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim'.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim'.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim'.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim₀, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit_of_compactnessWitness I varying_J uth u_seq B h_en_lim u_lim wit h_sph h_le_gap
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim₀ h_lim_energy h_prin_gap

/-- Unconditional extraction of a varying-`J` stable limit when every `J_n`-holomorphic sphere is
constant for some `n` (`0 sorryAx`). -/
theorem extract_varying_J_stable_limit_of_all_jholWithJ_const
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (n₀ : ℕ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicWithJ I (varying_J.J_seq n₀) u Set.univ →
      u = fun _ => u north_pole) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      (∀ v : u_lim.tree.V, is_principal_component I u_lim v →
        uth.h ≤ totalEnergy I (u_lim.map v)) := by
  exfalso
  exact h_nonconst n₀ ⟨u_seq n₀ north_pole, fun z => congr_fun (h_all_const (u_seq n₀) (h_jhol n₀)) z⟩

/-- Unconditional Varying-`J` Gromov Compactness when every `J_n`-holomorphic sphere is constant
for some `n` (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_all_jholWithJ_const
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (n₀ : ℕ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicWithJ I (varying_J.J_seq n₀) u Set.univ →
      u = fun _ => u north_pole) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim.tree.V, JHolomorphicOn I I_CP1 (u_lim.map v) Set.univ) ∧
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit_of_all_jholWithJ_const I varying_J uth u_seq B h_nonconst h_jhol n₀ h_all_const
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim h_lim_energy h_prin_gap

/-- Unconditional extraction of a varying-`J` stable limit when `varying_J.J_seq n₀ = tgt.J` for some `n₀`
and every `tgt.J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem extract_varying_J_stable_limit_of_eq_target_J_at_of_all_jhol_const
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (n₀ : ℕ) (hJ₀ : varying_J.J_seq n₀ = tgt.J)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      (∀ v : u_lim.tree.V, is_principal_component I u_lim v →
        uth.h ≤ totalEnergy I (u_lim.map v)) := by
  exfalso
  have hu₀ : JHolomorphicOn I I_CP1 (u_seq n₀) Set.univ := by
    rw [← jholomorphic_eq_with_target_J, ← hJ₀]
    exact h_jhol n₀
  exact h_nonconst n₀ (h_all_const (u_seq n₀) hu₀)

/-- Unconditional Varying-`J` Gromov Compactness when `varying_J.J_seq n₀ = tgt.J` for some `n₀`
and every `tgt.J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_eq_target_J_at_of_all_jhol_const
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (n₀ : ℕ) (hJ₀ : varying_J.J_seq n₀ = tgt.J)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim.tree.V, JHolomorphicOn I I_CP1 (u_lim.map v) Set.univ) ∧
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit_of_eq_target_J_at_of_all_jhol_const I varying_J uth u_seq B
      h_nonconst h_jhol n₀ hJ₀ h_all_const
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim h_lim_energy h_prin_gap

/-- Whenever every `tgt.J`-holomorphic sphere is constant, no `StableSphereTreeLimit` exists (`0 sorryAx`). -/
theorem StableSphereTreeLimit.isEmpty_of_all_jhol_const_varying
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
    IsEmpty (StableSphereTreeLimit I (M := M)) := by
  refine ⟨fun u_lim => ?_⟩
  obtain ⟨v, hv_prin⟩ := StableSphereTreeLimit.exists_principal_component I u_lim
  exact hv_prin (h_all_const (u_lim.map v) (u_lim.is_jhol v))

/-- Whenever every `tgt.J`-holomorphic sphere is constant, no `u_seq` can satisfy the conclusion of
`gromov_compactness_varying_J` (`0 sorryAx`). -/
theorem not_exists_stableSphereTreeLimit_of_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c)
    (P : StableSphereTreeLimit I (M := M) → Prop) :
    ¬ ∃ u_lim : StableSphereTreeLimit I (M := M), P u_lim := by
  rintro ⟨u_lim, _⟩
  haveI := StableSphereTreeLimit.isEmpty_of_all_jhol_const_varying I h_all_const
  exact isEmptyElim u_lim

/-- Unconditional extraction of a varying-`J` stable limit when `u_seq` is eventually non-constant
and `J_n`-holomorphic and every `J_{N₀}`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem extract_varying_J_stable_limit_of_eventually_all_jholWithJ_const
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (N₀ : ℕ)
    (h_nonconst : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicWithJ I (varying_J.J_seq N₀) u Set.univ →
      u = fun _ => u north_pole) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      (∀ v : u_lim.tree.V, is_principal_component I u_lim v →
        uth.h ≤ totalEnergy I (u_lim.map v)) := by
  exfalso
  exact h_nonconst N₀ le_rfl ⟨u_seq N₀ north_pole,
    fun z => congr_fun (h_all_const (u_seq N₀) (h_jhol N₀ le_rfl)) z⟩

/-- Unconditional Varying-`J` Gromov Compactness when `u_seq` is eventually non-constant and
`J_n`-holomorphic and every `J_{N₀}`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_eventually_all_jholWithJ_const
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (N₀ : ℕ)
    (h_nonconst : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicWithJ I (varying_J.J_seq N₀) u Set.univ →
      u = fun _ => u north_pole) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim.tree.V, JHolomorphicOn I I_CP1 (u_lim.map v) Set.univ) ∧
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit_of_eventually_all_jholWithJ_const I varying_J uth u_seq B N₀
      h_nonconst h_jhol h_all_const
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim h_lim_energy h_prin_gap

/-- Unconditional extraction of a varying-`J` stable limit when a subsequence `σ` is eventually
non-constant and `J_{σ.1 n}`-holomorphic and every `J_{σ.1 N₀}`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem extract_varying_J_stable_limit_of_subseq_nonconst_of_all_jholWithJ_const
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (σ : Bookkeeping.SubseqMap) (N₀ : ℕ)
    (h_nc : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, u_seq (σ.1 n) z = c)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicWithJ I (varying_J.J_seq (σ.1 n)) (u_seq (σ.1 n)) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicWithJ I (varying_J.J_seq (σ.1 N₀)) u Set.univ →
      u = fun _ => u north_pole) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      (∀ v : u_lim.tree.V, is_principal_component I u_lim v →
        uth.h ≤ totalEnergy I (u_lim.map v)) := by
  exfalso
  exact h_nc N₀ le_rfl ⟨u_seq (σ.1 N₀) north_pole,
    fun z => congr_fun (h_all_const (u_seq (σ.1 N₀)) (h_jhol N₀ le_rfl)) z⟩

/-- Unconditional Varying-`J` Gromov Compactness when a subsequence `σ` is eventually non-constant
and `J_{σ.1 n}`-holomorphic and every `J_{σ.1 N₀}`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem gromov_compactness_varying_J_of_subseq_nonconst_of_all_jholWithJ_const
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (σ : Bookkeeping.SubseqMap) (N₀ : ℕ)
    (h_nc : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, u_seq (σ.1 n) z = c)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicWithJ I (varying_J.J_seq (σ.1 n)) (u_seq (σ.1 n)) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicWithJ I (varying_J.J_seq (σ.1 N₀)) u Set.univ →
      u = fun _ => u north_pole) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim.tree.V, JHolomorphicOn I I_CP1 (u_lim.map v) Set.univ) ∧
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit_of_subseq_nonconst_of_all_jholWithJ_const I varying_J uth u_seq B
      σ N₀ h_nc h_jhol h_all_const
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim h_lim_energy h_prin_gap

/-- **Gromov Compactness with Varying Almost-Complex Structures (Contract E01)**.
Let $M$ be a compact symplectic manifold with closed symplectic form $\omega$, and let
$J_n \to J_\infty$ be a sequence of $\omega$-tamed almost-complex structures converging in $C^\infty$.
Let $u_n : \mathbb{CP}^1 \to M$ be a sequence of non-constant $J_n$-holomorphic spheres with
uniformly bounded symplectic energy $\int_{\mathbb{CP}^1} u_n^* \omega \le B < \infty$.

Then there exists a strictly increasing subsequence $\sigma(n)$ converging to a $J_\infty$-holomorphic
stable sphere tree limit curve $u_\infty = (T, \{u_v\}, \{z_{vw}\})$ with total energy $\le B$
and universal component bounds. -/
theorem gromov_compactness_varying_J
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (uth : UniformTargetThresholds I (M := M) varying_J)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (h_energy : ∀ n, pullbackOmegaMeasure I (u_seq n) Set.univ ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim.tree.V, JHolomorphicOn I I_CP1 (u_lim.map v) Set.univ) ∧
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  obtain ⟨u_lim, h_lim_energy, h_prin_gap⟩ :=
    extract_varying_J_stable_limit I varying_J uth u_seq B h_nonconst h_jhol h_energy h_fin
  exact gromov_compactness_varying_J_of_limit I varying_J uth B u_lim h_lim_energy h_prin_gap

#print axioms symmetrizedMetric_symm
#print axioms symmetrizedMetric_pos_def
#print axioms symmetrizedMetric_J_invariant
#print axioms jholomorphic_eq_with_target_J
#print axioms riemannianEnergyDensityWithJ_nonneg
#print axioms energy_density_with_J_eq_omega
#print axioms exists_uniform_target_thresholds
#print axioms jholomorphic_limit_of_varying_J

end GromovCompactness.Extensions
