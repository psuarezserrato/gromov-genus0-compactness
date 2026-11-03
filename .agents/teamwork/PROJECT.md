# Project: Autoformalization of Gromov Compactness in Lean 4

## Architecture
The project establishes a comprehensive autoformalization blueprint, reusable agent skills, and local Gemma/Ollama proving pipeline for Gromov compactness for genus 0 pseudo-holomorphic curves in Lean 4.
The mathematical foundation is synthesized from:
1. M. Gromov, "Pseudo holomorphic curves in symplectic manifolds", *Inventiones Math.* 82, 307–347 (1985).
2. S. Ivashkovich, V. Shevchishin, "Complex Curves in Almost-Complex Manifolds and Meromorphic Hulls", arXiv:math/9912046 (1999).
3. The specification document `gromov_compactness.pdf` (November 2026).
4. Mathlib (`Mathlib.Analysis.Hofer` by Patrick Massot, differential geometry, manifolds, Hausdorff distance, Arzelà-Ascoli, graph trees).
5. TauCeti Symplectic Geometry Roadmap (`TauCetiRoadmap/SymplecticGeometry`, `ComplexCurveModuli`, `CotangentLagrangian`).

The system architecture comprises 4 structural layers:
1. **Foundations & Bookkeeping Layer**: Target geometry, Riemann sphere $\mathbb{CP}^1$, energy measure $E(u) = \int u^* \omega$, $C^\infty_{loc}$ convergence on variable domains, subsequence extraction, and labelled sphere trees.
2. **Local Analytic Estimates Layer**: Scalar mean value, Bochner energy-density inequality, epsilon regularity, Euclidean/Sobolev toolkit, nonlinear bootstrap, local compactness, energy gap $\varepsilon_{sph} > 0$, target monotonicity, cylinder localization & exponential decay, and puncture removal.
3. **Concentration & Bubbling Layer**: Weak compactness of energy measures, finite concentration set $S$, defect identity, center calibration, neck energy & diameter vanishing, one-level mass decomposition, ghost branching, and well-founded induction on $\lfloor m / h \rfloor$.
4. **Global Assembly & Stabilization Layer**: Prestable tree assembly, root stabilization, core compactness theorem, component counting $|V| \le 2P - 2$, and extensions (homology preservation, automorphism finiteness, marked curves, already-nodal inputs, moduli topology).

## Feature Inventory
| # | Feature | Description | Milestone | Source |
|---|---------|-------------|-----------|--------|
| 1 | Target & Equation Formalization | `ClosedTameTarget`, $\omega$-taming and compatibility, Cauchy-Riemann operator $\bar{\partial}_J u = 0$ | M1 | `gromov_compactness.pdf` F01, Gromov 1985 |
| 2 | Sphere & Conformal Reparametrizations | $\mathbb{CP}^1 = \mathbb{C} \cup \{\infty\}$, affine scalings $z \mapsto a + \lambda z$, Möbius automorphisms | M1 | `gromov_compactness.pdf` F02 |
| 3 | Energy Measure & Algebra | Nonnegative measure $E(u; A) = \int_A u^* \omega$, conformal invariance, additivity, moving disk convergence | M1 | `gromov_compactness.pdf` F03 |
| 4 | Smooth Local Convergence | $C^\infty_{loc}$ chartwise derivative convergence on varying domains exhausting target | M1 | `gromov_compactness.pdf` F04 |
| 5 | Subsequence Bookkeeping | Strictly increasing index maps, diagonal extraction for countable sequences | M1 | `gromov_compactness.pdf` F05 |
| 6 | Labelled Sphere Trees | Rooted tree $T = (V, E)$, node positions $z_{vw}$, matching values $u_v(z_{vw}) = u_w(z_{wv})$ | M1 | `gromov_compactness.pdf` F06, TauCeti |
| 7 | Hofer Rescaling & Epsilon Regularity | Application of `Mathlib.Analysis.Hofer.hofer`, Bochner inequality, gradient bound $\sup_{D_{r/2}} \|du\|^2 \le C r^{-2} E$ | M1 | `Mathlib.Analysis.Hofer`, `gromov_compactness.pdf` A01-A03 |
| 8 | Elliptic Bootstrap & Local Compactness | Interior estimates for $\bar{\partial}$, $W^{1,p} \to C^\infty$, Arzelà-Ascoli diagonal extraction | M1 | `gromov_compactness.pdf` A04-A06 |
| 9 | Minimal Energy Gap | $\varepsilon_{sph} > 0$ such that every non-constant $J$-sphere has $E(u) \ge \varepsilon_{sph}$ | M1 | Gromov 1985, `gromov_compactness.pdf` A07 |
| 10 | Cylinder Decay & Puncture Removal | Exponential energy/diameter decay on cylinders $[-L, L] \times S^1$, $W^{1,p}$ extension across punctures | M1 | Ivashkovich-Shevchishin, `gromov_compactness.pdf` A08-A12 |
| 11 | Defect Measure & Moving Centers | Weak convergence of energy measures, finite singular set $S$, calibrated centers $a_n$ and scales $\lambda_n$ | M1 | `gromov_compactness.pdf` C01-C03, B01-B02 |
| 12 | Vanishing Neck Energy & Diameter | Explicit quantifiers proving neck energy and diameter vanish as $R \to \infty$ | M1 | `gromov_compactness.pdf` B03 |
| 13 | Ghost Branching & Well-Founded Induction | Constant bubble has $\ge 2$ child nodes, well-founded induction on rank $\lfloor m / h \rfloor$ | M1 | `gromov_compactness.pdf` B04-B07 |
| 14 | Global Assembly & Stabilization | Telescoping global Möbius frames, removing unstable constant roots, $|V| \le 2P - 2$ | M1 | `gromov_compactness.pdf` G01-G05 |
| 15 | Lean 4 Candidate Signatures | Full formal type signatures and docstrings for all core definitions and theorems | M1 | Survey Math & Spec Miner |
| 16 | Skill: `lean4-symplectic-autoformalizer` | Translates informal mathematical proofs into Lean 4 formal statements and proof skeletons | M2 | R2.1, Spec Miner |
| 17 | Skill: `ollama-lean4-gemma-prover` | Local Gemma/Ollama querying for premise selection, tactic search, and lemma extraction | M2 | R2.2, R3, Spec Miner |
| 18 | Skill: `lean4-proof-repair-engine` | Compiler-in-the-loop verification and repair of Lean 4 files against Mathlib/TauCeti | M2 | R2.3, Spec Miner |
| 19 | Local Ollama/Gemma Pipeline & Tooling | Zero-dependency CLI/API client, model fallback cascade, temperature matrix, connectivity check | M3 | R3, Explorer Ollama |
| 20 | Offline / Live Proof Search Verification | Test suites verifying prompt templates, tactic extraction, and dry-run execution | M3, M4 | Acceptance Criteria |
| 21 | Forensic Audit & Integrity Verification | Forensic verification of genuine autoformalization logic, no hardcoding, no false axioms | M4 | System Prompt Hard Constraint |

## Milestones
| # | Name | Scope | Dependencies | Status |
|---|------|-------|-------------|--------|
| M1 | Autoformalization Plan & Blueprint | Generate `GROMOV_COMPACTNESS_BLUEPRINT.md` and `AUTOFORMALIZATION_PLAN.md` in workspace root incorporating Gromov 1985, Ivashkovich-Shevchishin, `gromov_compactness.pdf`, Mathlib, TauCeti, with full dependency graph, candidate Lean 4 type signatures, and 'sorry'-first-pass strategy | none | DONE |
| M2 | Reusable Skill Artifacts | Implement `skills/lean4-symplectic-autoformalizer/SKILL.md`, `skills/ollama-lean4-gemma-prover/SKILL.md`, and `skills/lean4-proof-repair-engine/SKILL.md` with standard frontmatter, scripts, workflows, and references | M1 | DONE |
| M3 | Local Model Integration Pipeline | Implement `tools/ollama_lean4_client.py`, `tools/test_ollama_pipeline.py`, `config/ollama_gemma_config.json`, and `docs/OLLAMA_GEMMA_INTEGRATION.md` | M2 | DONE |
| M4 | Comprehensive E2E Verification & Audit | Independent Reviewers, Challengers, and Forensic Auditor verification across all deliverables | M1, M2, M3 | DONE |

## Interface Contracts
### Blueprint ↔ Skills
- `GROMOV_COMPACTNESS_BLUEPRINT.md` provides the exact formalization contracts (F00-F06, A01-A12, C01-C03, B01-B07, G01-G05, E01-E05), module paths, and candidate Lean 4 signatures.
- `lean4-symplectic-autoformalizer` references the blueprint structure to map informal symplectic arguments into Lean 4 skeletons.

### Skills ↔ Local Ollama Prover
- `ollama-lean4-gemma-prover` executes queries via `tools/ollama_lean4_client.py` targeting `http://localhost:11434` with Gemma chat format (`<start_of_turn>`, `<end_of_turn>`).
- Output format: pure Lean 4 code blocks or structured JSON responses.

### Skills ↔ Repair Engine
- `lean4-proof-repair-engine` parses compiler diagnostics (`lean --json`) and invokes `ollama-lean4-gemma-prover` with localized error contexts and Mathlib symbol matches.

## Code Layout
- Workspace Root: `/Users/pablosuarez/Desktop/SympTopAutoForm`
- Blueprint & Plan:
  - `GROMOV_COMPACTNESS_BLUEPRINT.md`
  - `AUTOFORMALIZATION_PLAN.md`
- Skills:
  - `skills/lean4-symplectic-autoformalizer/SKILL.md`
  - `skills/ollama-lean4-gemma-prover/SKILL.md`
  - `skills/lean4-proof-repair-engine/SKILL.md`
- Local Integration & Tools:
  - `tools/ollama_lean4_client.py`
  - `tools/test_ollama_pipeline.py`
  - `config/ollama_gemma_config.json`
- Tests & Validation:
  - `tests/test_skills_structure.py`
  - `tests/test_blueprint_completeness.py`
