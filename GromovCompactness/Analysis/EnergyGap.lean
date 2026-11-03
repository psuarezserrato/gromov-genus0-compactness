/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.EpsilonRegularity

open scoped Manifold ContDiff Topology
open Metric Set GromovCompactness

namespace GromovCompactness.Analysis

/-!
# Task A07: Minimal Energy Gap of Non-Constant Spheres

This module formalizes `sphere_energy_gap` (Contract A07):
There exists a strictly positive constant $\varepsilon_{\mathrm{sph}} > 0$ depending only on
the target manifold $(M, \omega, J)$ such that every non-constant $J$-holomorphic sphere
$u : \mathbb{CP}^1 \to M$ satisfies $E(u) \ge \varepsilon_{\mathrm{sph}}$.

The proof proceeds by covering $\mathbb{CP}^1$ by finitely many disks with small energy,
bounding the image diameter by $O(\sqrt{E})$ via epsilon-regularity (`A03`), showing the
image lies in a contractible Darboux chart, and integrating $u^* d\alpha = 0$ via Stokes'
theorem without requiring rationality assumptions on $[\omega]$.

References:
- Mikhail Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Math. 82 (1985), §1.2.
- Sergei Ivashkovich & Vsevolod Shevchishin, arXiv:math/9912046, Corollary 2.1.3.
- `gromov_compactness.pdf` §4.2 (Contract A07).
-/

/-- Minimal Energy Gap for Non-Constant Spheres (Contract A07).
There exists a strictly positive constant `ε_sph > 0` depending only on `(M, ω, J)` such that
every non-constant `J`-holomorphic sphere `u : CP1 → M` satisfies `E(u) ≥ ε_sph`. -/
theorem sphere_energy_gap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (ε_sph : ℝ), 0 < ε_sph ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ε_sph ≤ totalEnergy I u := by
  sorry

end GromovCompactness.Analysis
