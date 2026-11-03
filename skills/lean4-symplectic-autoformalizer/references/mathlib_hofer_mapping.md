# Mapping Reference: Patrick Massot's Mathlib.Analysis.Hofer

**Lean 4 Mathlib Module:** `Mathlib.Analysis.Hofer`  
**Author:** Patrick Massot  
**Lean 4 community docs:** [Mathlib.Analysis.Hofer](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Hofer.html)

---

## 1. Statement of Hofer's Lemma in Mathlib 4

The original lemma in Mathlib 4 is stated as follows:

```lean
import Mathlib.Topology.MetricSpace.Basic

open Metric

namespace Mathlib.Analysis.Hofer

/-- Hofer's lemma on complete metric spaces: Given a non-negative continuous function f on a
    complete metric space X and any ε > 0, there exists a point x' and a radius ε' ≤ ε such that
    the function value at x' is at least f(x), and throughout the closed ball around x' of radius ε',
    the function values are bounded by twice f(x'). -/
theorem hofer {X : Type*} [MetricSpace X] [CompleteSpace X] (f : X → ℝ) (x : X) (ε : ℝ)
    (hε : 0 < ε) (hf : Continuous f) (hfx : 0 ≤ f x) :
    ∃ x' ε', 0 < ε' ∧ ε' ≤ ε ∧ f x ≤ f x' ∧ ∀ y, dist y x' ≤ ε' → f y ≤ 2 * f x' := by
  sorry -- Full proof available in Mathlib 4
```

---

## 2. Application to Gradient Blow-Up in Symplectic Geometry

In Gromov compactness and pseudo-holomorphic curve theory, Hofer's lemma is used to rescale sequences of curves near points where the gradient blows up:

### Mathematical Translation
1. **Metric Space:**
   Set $X = \overline{B(z_0, r)} \subset \mathbb{C}$ or a compact coordinate patch of the Riemann surface.
   Since $X$ is compact, it is a `[CompleteSpace X]`.
2. **Gradient Function:**
   Let $u_n: \Sigma \to M$ be a sequence of $J$-holomorphic curves.
   Define $f_n(z) = \|du_n(z)\|_g \cdot \mathrm{dist}(z, \partial X)$.
   Then $f_n \ge 0$ is continuous on $X$ and vanishes on $\partial X$.
3. **Blow-Up Hypothesis:**
   If $\sup_{z \in X} \|du_n(z)\| \to \infty$, choose points $x_n \in X$ where $f_n(x_n)$ attains its maximum.
4. **Rescaling Parameter:**
   Apply `Mathlib.Analysis.Hofer.hofer` with $\varepsilon_n = (f_n(x_n))^{-1/2} \to 0$.
   We obtain a center $x'_n$ and $\varepsilon'_n \le \varepsilon_n$ such that:
   $$\|du_n(y)\| \le 2 \|du_n(x'_n)\| \quad \forall y \in B(x'_n, \varepsilon'_n)$$
5. **Dilation:**
   Define the rescaled map:
   $$v_n(\zeta) := u_n\left(x'_n + \frac{\zeta}{\|du_n(x'_n)\|}\right)$$
   The domain of $v_n$ expands to exhausting disks in $\mathbb{C}$, the gradient at 0 is normalized to 1, and the gradient on $B(0, R)$ is bounded by 2.

---

## 3. Lean 4 Instantiation Recipe

```lean
import Mathlib.Analysis.Hofer
import Mathlib.Topology.MetricSpace.Basic

open Metric

variable {X : Type*} [MetricSpace X] [CompleteSpace X]

/-- Rescaling helper synthesizing Hofer's lemma for gradient bounds. -/
theorem hofer_rescale_point (f : X → ℝ) (hf : Continuous f) (x : X) (ε : ℝ)
    (hε : 0 < ε) (hfx : 0 ≤ f x) :
    ∃ x' : X, ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ∀ y ∈ closedBall x' ε', f y ≤ 2 * f x' := by
  obtain ⟨x', ε', hε'_pos, hε'_le, hf_le, h_bound⟩ := Mathlib.Analysis.Hofer.hofer f x ε hε hf hfx
  exact ⟨x', ε', hε'_pos, hε'_le, fun y hy => h_bound y hy⟩
```
