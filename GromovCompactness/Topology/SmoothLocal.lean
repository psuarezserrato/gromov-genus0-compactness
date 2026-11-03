/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere

open scoped Manifold ContDiff Topology
open Metric Set Filter

/-!
# Task F04: Smooth Local Convergence on Varying Domains

This module formalizes $C^\infty_{\mathrm{loc}}$ (smooth local) convergence for sequences of smooth maps
from open subsets of $\mathbb{CP}^1$ into the target manifold $M$, following Gromov (1985, §1.2),
Ivashkovich-Shevchishin (1999, §2), and `gromov_compactness.pdf` §2.3 & §5 (Task `F04`).

## Key Definitions
- `SmoothLocalConvergesOn`: Uniform convergence of chartwise derivatives of every order $k \in \mathbb{N}$
  on all compact subsets $K \subseteq \Omega$.
- `SmoothLocalConvergesVarying`: Version for varying domains $\Omega_n$ exhausting $\Omega$, where every
  compact $K \subseteq \Omega$ is eventually covered by $\Omega_n$.
- `smooth_local_limit_unique`: Uniqueness of smooth local limits on open domains.
- `smooth_local_restriction`: Restriction of convergence to open subdomains $\Omega' \subseteq \Omega$.
- `smooth_local_jhol_closure`: Closure of the Cauchy-Riemann equation: if each $u_n$ is $J$-holomorphic,
  the local smooth limit $u$ is $J$-holomorphic.
- `smooth_local_comp_moebius`: Stability of smooth local convergence under composition with Möbius frames.
-/

namespace GromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]

/-- $C^\infty_{\mathrm{loc}}$ convergence of a sequence of maps $u_n : \mathbb{CP}^1 \to M$ to $u : \mathbb{CP}^1 \to M$
on an open domain $\Omega \subseteq \mathbb{CP}^1$.
Requires that on every compact subset $K \subseteq \Omega$, for every derivative order $k \in \mathbb{N}$,
the derivatives converge uniformly in local charts. -/
def SmoothLocalConvergesOn
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1) : Prop :=
  ∀ (K : Set CP1), K ⊆ Ω → IsCompact K →
    ∀ (k : ℕ),
      -- Uniform convergence of k-th order derivatives on K
      Tendsto (fun n => sorry) atTop (nhds (sorry))

/-- Smooth local convergence on varying domains: $\Omega_n \subseteq \mathbb{CP}^1$ exhausting $\Omega$.
Every compact $K \subseteq \Omega$ is eventually contained in $\Omega_n$ and derivatives converge uniformly on $K$. -/
def SmoothLocalConvergesVarying
    (Ω_seq : ℕ → Set CP1) (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1) : Prop :=
  ∀ (K : Set CP1), K ⊆ Ω → IsCompact K →
    (∃ N : ℕ, ∀ n ≥ N, K ⊆ Ω_seq n) ∧
    ∀ (k : ℕ), Tendsto (fun n => sorry) atTop (nhds (sorry))

/-- Uniqueness of $C^\infty_{\mathrm{loc}}$ limits on non-empty open domains. -/
theorem smooth_local_limit_unique
    (u_seq : ℕ → (CP1 → M)) (u₁ u₂ : CP1 → M) (Ω : Set CP1)
    (h_open : IsOpen Ω) (h_nonempty : Ω.Nonempty)
    (h₁ : SmoothLocalConvergesOn I u_seq u₁ Ω)
    (h₂ : SmoothLocalConvergesOn I u_seq u₂ Ω) :
    EqOn u₁ u₂ Ω := by
  -- Pointwise limits in Hausdorff target spaces are unique
  sorry

/-- Restriction of $C^\infty_{\mathrm{loc}}$ convergence to open subdomains. -/
theorem smooth_local_restriction
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) {Ω Ω' : Set CP1}
    (h_sub : Ω' ⊆ Ω) (h_conv : SmoothLocalConvergesOn I u_seq u_lim Ω) :
    SmoothLocalConvergesOn I u_seq u_lim Ω' := by
  intro K hK_sub hK_cpt
  exact h_conv K (hK_sub.trans h_sub) hK_cpt

/-- Closure of the Cauchy-Riemann equation under $C^\infty_{\mathrm{loc}}$ convergence:
If $u_n \to u$ in $C^\infty_{\mathrm{loc}}(\Omega)$ and each $u_n$ is $J$-holomorphic on $\Omega$,
then the limit map $u$ is $J$-holomorphic on $\Omega$. -/
theorem smooth_local_jhol_closure [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1)
    (h_conv : SmoothLocalConvergesOn I u_seq u_lim Ω)
    (h_jhol : ∀ n, JHolomorphicOn I (u_seq n) Ω) :
    JHolomorphicOn I u_lim Ω := by
  -- Step 1: C¹ convergence implies convergence of the differential du_n → du
  -- Step 2: The Cauchy-Riemann operator d-bar_J is a linear combination of du and du ∘ j
  -- Step 3: By continuity of J on the compact target, d-bar_J(u_n) → d-bar_J(u) = 0
  sorry

/-- Compatibility of $C^\infty_{\mathrm{loc}}$ convergence with composition by Möbius frames:
If $u_n \to u$ locally smoothly and $\phi_n \to \phi$ in $\operatorname{MoebiusFrame}$,
then $u_n \circ \phi_n \to u \circ \phi$ locally smoothly. -/
theorem smooth_local_comp_moebius
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1)
    (ϕ_seq : ℕ → MoebiusFrame) (ϕ_lim : MoebiusFrame)
    (h_u : SmoothLocalConvergesOn I u_seq u_lim Ω)
    (h_ϕ : Tendsto ϕ_seq atTop (nhds ϕ_lim)) :
    SmoothLocalConvergesOn I (fun n => u_seq n ∘ (ϕ_seq n).toHomeo)
      (u_lim ∘ ϕ_lim.toHomeo) (ϕ_lim.toHomeo ⁻¹' Ω) := by
  -- Follows from chain rule and compact preimages under homeomorphisms
  sorry

end GromovCompactness
