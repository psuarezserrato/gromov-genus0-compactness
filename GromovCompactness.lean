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

-- Phase 3: Concentration Compactness (C01–C03)
import GromovCompactness.Compactness.Measures
import GromovCompactness.Compactness.Concentration
import GromovCompactness.Compactness.Defect

-- Phase 3: Bubbling Engine (B03–B07)
import GromovCompactness.Bubbling.Neck
import GromovCompactness.Bubbling.OneLevel
import GromovCompactness.Bubbling.GhostBranching
import GromovCompactness.Bubbling.Rank
import GromovCompactness.Bubbling.LocalTree

-- Phase 3: Global Tree Assembly & Master Compactness (G01–G05)
import GromovCompactness.Compactness.Assembly
import GromovCompactness.Compactness.Stabilize
import GromovCompactness.Compactness.GenusZero
import GromovCompactness.Topology.ComponentCount
import GromovCompactness.Main

-- Phase 4: Extensions & Moduli Space Topology (E01–E05)
import GromovCompactness.Extensions.VaryingJ
import GromovCompactness.Extensions.MarkedCurves
import GromovCompactness.Extensions.Homology
import GromovCompactness.Extensions.Automorphisms
import GromovCompactness.Extensions.ModuliSpace

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

## Phase 3 Modules (Iterative Bubbling & Global Compactness: C01–C03, B03–B07, G01–G05)
- `GromovCompactness.Compactness.Measures` (`C01`): Weak compactness of energy measures on $\mathbb{CP}^1$.
- `GromovCompactness.Compactness.Concentration` (`C02`): Finite concentration set $S$ and smooth local convergence on $\mathbb{CP}^1 \setminus S$.
- `GromovCompactness.Compactness.Defect` (`C03`): Defect measure identity $\mu = u_0^* \omega + \sum m_p \delta_p$ and energy conservation.
- `GromovCompactness.Bubbling.Neck` (`B03`): Vanishing neck symplectic energy and target metric diameter.
- `GromovCompactness.Bubbling.OneLevel` (`B04`): One-level bubble extraction and node matching $v(\infty) = u_0(p)$.
- `GromovCompactness.Bubbling.GhostBranching` (`B05`): Ghost component branching condition ($\ge 2$ children, nodal degree $\ge 3$).
- `GromovCompactness.Bubbling.Rank` (`B06`): Strict discrete energy rank decrease $\lfloor m_i / h \rfloor < \lfloor m / h \rfloor$.
- `GromovCompactness.Bubbling.LocalTree` (`B07`): Resolution of defect into finite rooted bubble tree via well-founded induction.
- `GromovCompactness.Compactness.Assembly` (`G01`): Prestable tree assembly and global Möbius coordinate frames.
- `GromovCompactness.Compactness.Stabilize` (`G02`): Root stabilization (pruning degree 1 and suppressing degree 2 ghost roots).
- `GromovCompactness.Compactness.GenusZero` (`G03`): Core genus 0 Gromov compactness theorem and CompactnessWitness certificate.
- `GromovCompactness.Topology.ComponentCount` (`G04`): Component bounds $P \cdot h \le B$, $G \le P - 2$, $|V| \le \max(1, 2\lfloor B/h \rfloor - 2)$.
- `GromovCompactness.Main` (`G05`): Master integration theorem `gromov_compactness_genus_zero` and axiom audit.

## Phase 4 Modules (Extensions & Moduli Space Topology: E01–E05)
- `GromovCompactness.Extensions.VaryingJ` (`E01`): Smooth convergence of almost-complex structures $J_n \to J_\infty$, uniform constants, and Gromov compactness transfer.
- `GromovCompactness.Extensions.MarkedCurves` (`E02`): $k$-marked stable curves, cross-ratio projective invariance, ghost bubble collision blow-up, and marked Gromov compactness.
- `GromovCompactness.Extensions.Homology` (`E03`): Preservation of total integral homology class $[u_n] = \sum [u_v] \in H_2(M; \mathbb{Z})$ and tree symplectic area identity.
- `GromovCompactness.Extensions.Automorphisms` (`E04`): Combinatorial tree automorphisms, 3-point Möbius rigidity, and component stability equivalence $\operatorname{stable} \iff \operatorname{Finite}(\operatorname{Aut})$.
- `GromovCompactness.Extensions.ModuliSpace` (`E05`): Marked stable map isomorphism quotient, Gromov metric, Hausdorff separation ($T_2$), and compact Hausdorff moduli space $\overline{\mathcal{M}}_{0, k}(M, J, \le B)$ and $\overline{\mathcal{M}}_{0, k}(M, J, A)$.
-/
