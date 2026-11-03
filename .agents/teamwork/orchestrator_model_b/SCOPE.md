# Scope: Model B — Full Proof Completion (Zero-sorry) for Phase 1 Foundations (F00–F06)

## Architecture
Phase 1 formalizes the foundational layer for Gromov Compactness in Lean 4:
1. `GromovCompactness.LibraryAudit` (`F00`): Mathlib prerequisite audit and axiom check.
2. `GromovCompactness.Geometry.Target` (`F01`): Almost complex manifold $(M, J)$, symplectic form $\omega$, taming/compatibility, Riemannian metric $g_J$, and Cauchy-Riemann equations $\bar{\partial}_J u = 0$.
3. `GromovCompactness.Geometry.Sphere` (`F02`): Riemann sphere $\mathbb{CP}^1 \cong \mathbb{C} \cup \{\infty\}$, stereographic charts, Möbius group $\operatorname{PSL}(2, \mathbb{C})$, and affine scalings $z \mapsto a + \lambda z$.
4. `GromovCompactness.Analysis.Energy` (`F03`): Symplectic energy $E(u) = \int u^* \omega$, nonnegativity, conformal invariance under Möbius transformations, and domain additivity.
5. `GromovCompactness.Topology.SmoothLocal` (`F04`): $C^\infty_{\mathrm{loc}}$ convergence on exhausting domains, and closure of the Cauchy-Riemann equation under $C^1_{\mathrm{loc}}$ limits.
6. `GromovCompactness.Topology.Subsequence` (`F05`): Monotone extractions and the Cantor diagonal subsequence theorem for countable sequences of properties.
7. `GromovCompactness.Topology.SphereTree` (`F06`): Rooted tree graphs, labelled sphere trees, nodal attachments, and ghost component stability.

## Feature Inventory
| # | Feature | Description | Milestone | Source |
|---|---------|-------------|-----------|--------|
| 1 | F00 Library & Toolchain Audit | Validate Mathlib integration, lake build environment, and standard axioms | M1 | `LibraryAudit.lean` |
| 2 | F05 Monotone & Cantor Extraction | Monotone subsequences and Cantor diagonal extraction for countable families | M2 | `Topology/Subsequence.lean` |
| 3 | F01 Target Geometry & Cauchy-Riemann | Almost complex structures, taming, compatibility, metric, and CR operator | M3 | `Geometry/Target.lean` |
| 4 | F02 Riemann Sphere & PSL(2, C) | Stereographic projection, conformal charts, and affine Möbius group actions | M3 | `Geometry/Sphere.lean` |
| 5 | F03 Symplectic Energy & Conformal Invariance | Energy functional, area forms, nonnegativity, and conformal invariance | M4 | `Analysis/Energy.lean` |
| 6 | F04 Smooth Local Convergence | Exhaustion domains, $C^\infty_{\mathrm{loc}}$ convergence, and CR equation closure | M4 | `Topology/SmoothLocal.lean` |
| 7 | F06 Labelled Sphere Trees | Node relations, tree structure, nodal matching conditions, and stability | M4 | `Topology/SphereTree.lean` |
| 8 | Phase 1 Verification & Axiom Audit | Independent verification of 0-sorry status, #print axioms check (propext, Quot.sound, Classical.choice) | M5 | Integrity Forensics |

## Milestones
| # | Name | Scope | Dependencies | Status |
|---|------|-------|-------------|--------|
| M1 | Survey & Technical Audit | Explorers examine current F00–F06 Lean files, inventory all existing `sorry` placeholders, identify exact Mathlib lemmas available, assess local Gemma / Ollama pipeline readiness | none | DONE |
| M2 | Subsequence Proofs (F05) | Eliminate all `sorry` in `Topology/Subsequence.lean` via machine-checked proofs using standard Mathlib order and topology tools | M1 | DONE |
| M3 | Target & Sphere Proofs (F01, F02) | Eliminate `sorry` in `Geometry/Target.lean` and `Geometry/Sphere.lean` (metric symmetry, positivity, Möbius actions) | M1 | BLOCKED: Integrity Violation (facade definitions in Sphere.lean) |
| M4 | Energy, SmoothLocal & SphereTree (F03, F04, F06) | Eliminate `sorry` in `Analysis/Energy.lean`, `Topology/SmoothLocal.lean`, and `Topology/SphereTree.lean` | M2, M3 | PLANNED |
| M5 | Comprehensive Audit & Gate Check | Independent Reviewers, Challengers, and Forensic Auditor verify 0 sorry, compile with Lake, check axioms, create checkpoint and Git commit | M4 | PLANNED |

## Interface Contracts
### Subsequence ↔ SmoothLocal & Compactness
- `Topology/Subsequence.lean` provides `diagonal_subsequence` ensuring any sequence with countably many pointwise or chartwise converging properties has a single diagonal subsequence.
### Target & Sphere ↔ Energy
- `Geometry/Target.lean` and `Geometry/Sphere.lean` provide $J$ and conformal metrics allowing `Analysis/Energy.lean` to prove energy density nonnegativity and Möbius invariance.
### Pause Sentinel & Git Checkpoint Contract
- Before and after each milestone, check `.pause_workflow`. If set, write checkpoint snapshot and pause cleanly.
- After each milestone passes gate, invoke git commit and `python3 tools/workflow_control.py checkpoint`.
