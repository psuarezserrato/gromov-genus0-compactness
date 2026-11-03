/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.LibraryAudit
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Topology.SmoothLocal
import GromovCompactness.Topology.Subsequence
import GromovCompactness.Topology.SphereTree

/-!
# Master Entry Point for Gromov Compactness in Genus 0

This package provides a formalization of Gromov Compactness for genus 0 pseudo-holomorphic curves
(J-holomorphic spheres into compact symplectic manifolds) following:
- Mikhail Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Math. 82 (1985), 307–347.
- Sergei Ivashkovich & Vsevolod Shevchishin, *Complex Curves in Almost-Complex Manifolds and Meromorphic Hulls*, arXiv:math/9912046.
- The mathematical blueprint in `gromov_compactness.pdf`.

## Module Architecture (Phase 1 Foundations: F00–F06)
- `GromovCompactness.LibraryAudit` (`F00`): Mathlib toolchain certification and prerequisite audit.
- `GromovCompactness.Geometry.Target` (`F01`): Compact tame targets $(M, \omega, J)$, symmetrized metric $g$, and Cauchy-Riemann equations.
- `GromovCompactness.Geometry.Sphere` (`F02`): Riemann sphere $\mathbb{CP}^1 \cong S^2$, Möbius frame group $\operatorname{PSL}(2, \mathbb{C})$, affine scalings, and charts.
- `GromovCompactness.Analysis.Energy` (`F03`): Symplectic energy measure, conformal invariance, and area forms.
- `GromovCompactness.Topology.SmoothLocal` (`F04`): $C^\infty_{\mathrm{loc}}$ convergence on exhausting domains and $J$-holomorphic equation closure.
- `GromovCompactness.Topology.Subsequence` (`F05`): Strictly monotone index extractions and countable Cantor diagonal subsequence theorem.
- `GromovCompactness.Topology.SphereTree` (`F06`): Labelled sphere tree data structures, nodal attachments, and ghost component stability.
-/
