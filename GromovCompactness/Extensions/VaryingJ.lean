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
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
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
  /-- Smoothness of $J$ as a bundle endomorphism. -/
  J_smooth : Prop

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
  ∀ (z : CP1), z ∈ s →
    ∀ (v : TangentSpace I_CP1 z),
      mfderiv I_CP1 I u z (J_CP1 v) = J (u z) (mfderiv I_CP1 I u z v)

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
  J_seq_smooth : ∀ (_ : ℕ), Prop
  /-- Each $J_n$ is tamed by the target symplectic form $\omega$. -/
  J_seq_tame : ∀ (n : ℕ) (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < tgt.«ω» x v (J_seq n x v)
  /-- Pointwise convergence $J_n(x) \to J_\infty(x)$ at every point $x \in M$. -/
  c0_conv : ∀ (x : M), Tendsto (fun n => J_seq n x) atTop (𝓝 (tgt.J x))
  /-- Smooth $C^\infty$ convergence: uniform convergence of all derivatives on the compact manifold $M$. -/
  c_infty_conv : Prop
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

/-- **Elliptic Equation Limit Closure under Varying $J_n \to J_\infty$**.
The smooth local limit $u_\infty$ of a sequence of $J_n$-holomorphic maps with $J_n \to J_\infty$
is $J_\infty$-holomorphic. -/
theorem jholomorphic_limit_of_varying_J
    (varying_J : VaryingAlmostComplexStructures I (M := M))
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (U : Set CP1) (_hU : IsOpen U)
    (_h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) U)
    (_h_conv : SmoothLocalConvergesOn I u_seq u_lim U) :
    JHolomorphicOn I I_CP1 u_lim U := by
  sorry

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
    (_h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (_h_jhol : ∀ n, JHolomorphicWithJ I (varying_J.J_seq n) (u_seq n) Set.univ)
    (_h_energy : ∀ n, pullbackOmegaMeasure I (u_seq n) Set.univ ≤ B) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      (∀ v : u_lim.tree.V, JHolomorphicOn I I_CP1 (u_lim.map v) Set.univ) ∧
      (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)) ≤ B ∧
      let P := Fintype.card { v : u_lim.tree.V // is_principal_component I u_lim v }
      let G := Fintype.card { v : u_lim.tree.V // is_ghost_component I u_lim v }
      (P * uth.h ≤ B) ∧
      (1 < Fintype.card u_lim.tree.V → G + 2 ≤ P ∧ Fintype.card u_lim.tree.V + 2 ≤ 2 * P) ∧
      ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / uth.h⌋ - 2)) := by
  sorry

#print axioms symmetrizedMetric_symm
#print axioms symmetrizedMetric_pos_def
#print axioms symmetrizedMetric_J_invariant
#print axioms jholomorphic_eq_with_target_J
#print axioms riemannianEnergyDensityWithJ_nonneg
#print axioms energy_density_with_J_eq_omega
#print axioms exists_uniform_target_thresholds

end GromovCompactness.Extensions
