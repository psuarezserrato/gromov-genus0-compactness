/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Topology.SmoothLocal
import GromovCompactness.Topology.Subsequence

open scoped Manifold ContDiff Topology MeasureTheory
open Metric Set GromovCompactness

namespace GromovCompactness.Analysis

/-!
# Tasks A04, A05, & A06: Elliptic Toolkit, Nonlinear Bootstrap, and Local Compactness

This module formalizes:
1. `interior_cauchy_riemann_estimate` (Contract A04): Interior $W^{k+1, p}$ estimates for the
   linear Cauchy-Riemann operator on concentric disks.
2. `morrey_sobolev_embedding` (Contract A04): Morrey embedding $W^{1, p} \hookrightarrow C^{0, 1 - 2/p}$
   for $p > 2$ in dimension 2.
3. `WeakJHolomorphicOn` & `nonlinear_elliptic_bootstrap` (Contract A05): Upgrades $C^1$ weak solutions
   of $\bar\partial_J u = 0$ to smooth $C^\infty$ maps.
4. `local_smooth_compactness` (Contract A06): Extraction of $C^\infty_{\mathrm{loc}}$ converging
   subsequences under uniform local gradient bounds via Arzelà-Ascoli.

References:
- Mikhail Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Math. 82 (1985), §1.2.
- Sergei Ivashkovich & Vsevolod Shevchishin, arXiv:math/9912046, §2.1 & §2.2.
- Dusa McDuff & Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology* (2012), Appendix B.4 & B.5, Theorem 4.1.1.
- `gromov_compactness.pdf` §4.1 (Contracts A04, A05, A06).
-/

/-- Cauchy-Riemann operator $\bar\partial f(z) := \frac{1}{2} (\partial_x f + i \partial_y f)$ for maps $f : \mathbb{C} \to \mathbb{C}$. -/
noncomputable def cauchyRiemann (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)

/-- The $L^p$ Sobolev seminorm of order $j$ on a measurable domain $s \subseteq \mathbb{C}$. -/
noncomputable def sobolevSeminorm (p : ℝ) (j : ℕ) (f : ℂ → ℂ) (s : Set ℂ) : ℝ :=
  (∫ z in s, ‖iteratedFDeriv ℝ j f z‖ ^ p) ^ (1 / p)

/-- The Sobolev $W^{k, p}$ norm of a function $f : \mathbb{C} \to \mathbb{C}$ on $s \subseteq \mathbb{C}$. -/
noncomputable def sobolevNorm (p : ℝ) (k : ℕ) (f : ℂ → ℂ) (s : Set ℂ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), sobolevSeminorm p j f s

/-- Interior Cauchy-Riemann Estimate (Contract A04).
For $1 < p < \infty$ and $k \in \mathbb{N}$, interior $W^{k+1, p}$ estimates hold on concentric
disks $D_r \subset D_R$:
$\|f\|_{W^{k+1, p}(D_r)} \le C \left(\|\bar\partial f\|_{W^{k, p}(D_R)} + \|f\|_{L^p(D_R)}\right)$. -/
theorem interior_cauchy_riemann_estimate (p : ℝ) (hp : 1 < p) (k : ℕ) (r R : ℝ) (hrR : 0 < r ∧ r < R) :
    ∃ (C : ℝ), 0 < C ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ (k + 1) f (Metric.closedBall 0 R) →
      sobolevNorm p (k + 1) f (Metric.closedBall 0 r) ≤
        C * (sobolevNorm p k (cauchyRiemann f) (Metric.closedBall 0 R) +
             sobolevNorm p 0 f (Metric.closedBall 0 R)) := by
  sorry

/-- Morrey-Sobolev Embedding in 2D (Contract A04).
For $p > 2$, $W^{1, p}$ functions on 2D disks embed into Hölder continuous functions $C^{0, \alpha}$
with exponent $\alpha = 1 - 2/p$:
$\|f(z) - f(w)\| \le C \mathrm{dist}(z, w)^\alpha \|f\|_{W^{1, p}(D_r)}$. -/
theorem morrey_sobolev_embedding (p : ℝ) (hp : 2 < p) (r : ℝ) (hr : 0 < r) :
    ∃ (C : ℝ) (α : ℝ), 0 < C ∧ α = 1 - 2 / p ∧ 0 < α ∧
    ∀ (f : ℂ → ℂ),
      ContDiffOn ℝ 1 f (Metric.closedBall 0 r) →
      ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      ∀ w ∈ Metric.closedBall (0 : ℂ) r,
        ‖f z - f w‖ ≤ C * (dist z w)^α * sobolevNorm p 1 f (Metric.closedBall 0 r) := by
  sorry

/-- Weak $C^1$ $J$-holomorphic curve (Contract A05):
A map `u : CP1 → M` of class $C^1$ on `s` satisfying the Cauchy-Riemann equation
$du \circ j = J \circ du$ pointwise on `s`.
Unlike `JHolomorphicOn`, this does NOT assume $C^\infty$ smoothness in advance. -/
def WeakJHolomorphicOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (s : Set CP1) : Prop :=
  ContMDiffOn I_CP1 I 1 u s ∧
  ∀ (z : CP1), z ∈ s →
    ∀ (v : TangentSpace I_CP1 z),
      mfderiv I_CP1 I u z (RiemannDomain.j z v) =
        (ClosedTameTarget.J (I := I) (u z)) (mfderiv I_CP1 I u z v)

/-- Every smooth $J$-holomorphic curve is a weak $C^1$ $J$-holomorphic curve. -/
lemma _root_.GromovCompactness.JHolomorphicOn.weakJHolomorphicOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {u : CP1 → M} {s : Set CP1}
    (h : JHolomorphicOn (I := I) (I_dom := I_CP1) u s) :
    WeakJHolomorphicOn I u s := by
  refine ⟨h.1.of_le (by norm_num), h.2⟩

/-- Nonlinear Elliptic Bootstrap (Contract A05).
Every $C^1$ weak solution of the Cauchy-Riemann equation $\bar\partial_J u = 0$ on an open
domain $\Omega \subseteq \mathbb{CP}^1$ is smooth ($C^\infty$). -/
theorem nonlinear_elliptic_bootstrap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I ∞ u Ω := by
  sorry

/-- Local Smooth Compactness Under Gradient Bounds (Contract A06).
Let $u_n : \Omega \to M$ be a sequence of $J$-holomorphic maps satisfying a uniform gradient bound
$\sup_K |du_n| \le C_K < \infty$ on each compact subset $K \subset \Omega$. Then there exists a
subsequence $u_{\sigma(n)}$ converging in $C^\infty_{\mathrm{loc}}(\Omega, M)$ to a $J$-holomorphic map. -/
theorem local_smooth_compactness
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω := by
  sorry

end GromovCompactness.Analysis
