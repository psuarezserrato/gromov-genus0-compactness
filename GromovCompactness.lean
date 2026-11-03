/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.LibraryAudit
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.Monotonicity
import GromovCompactness.Analysis.Bochner
import GromovCompactness.Analysis.EpsilonRegularity
import GromovCompactness.Analysis.EllipticBootstrap
import GromovCompactness.Analysis.EnergyGap
import GromovCompactness.Analysis.SingularityRemoval
import GromovCompactness.Analysis.HoferRescaling
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

## Phase 2 Modules (Local Analysis & Calibrated Bubbling: A01–A12, B01–B02)
- `GromovCompactness.Analysis.Monotonicity` (`A01`, `A08`): Mean-value inequality and target monotonicity.
- `GromovCompactness.Analysis.Bochner` (`A02`): Energy-density Bochner differential inequality $\Delta e \ge -be^2 - ce$.
- `GromovCompactness.Analysis.EpsilonRegularity` (`A03`): Epsilon-regularity gradient estimates via `Mathlib.Analysis.Hofer.hofer`.
- `GromovCompactness.Analysis.EllipticBootstrap` (`A04`, `A05`, `A06`): Cauchy-Riemann estimates, nonlinear bootstrap, and local smooth compactness.
- `GromovCompactness.Analysis.EnergyGap` (`A07`): Minimal positive energy gap $\varepsilon_{\mathrm{sph}} > 0$ for non-constant $J$-spheres.
- `GromovCompactness.Analysis.SingularityRemoval` (`A09`, `A10`, `A11`, `A12`): Cylinder localization, exponential decay, Sobolev extension, and smooth singularity removal.
- `GromovCompactness.Analysis.HoferRescaling` (`B01`, `B02`): Universal bubbling threshold $h > 0$ and calibrated moving center/radius rescaling.
-/
