# Scope: Phase 2 Model B — Milestone 4: Energy Gap & Singularities Zero-`sorry` Proofs

## Target Modules & Contracts
Target Files:
- `GromovCompactness/Analysis/EnergyGap.lean`
- `GromovCompactness/Analysis/SingularityRemoval.lean`

### Contracts to Prove & Certify:
1. **Contract A07**: `minimal_energy_gap` in `EnergyGap.lean`
   - Non-constant $J$-sphere energy lower bound: $\exists \varepsilon_{\mathrm{sph}} > 0, \forall u : \mathbb{CP}^1 \to M$, non-constant $J$-holomorphic sphere $\implies E(u) \ge \varepsilon_{\mathrm{sph}}$.
   - Reduction / auxiliary foundation lemmas: area/energy monotonicity, constant-curve energy vanishing, energy nonnegativity, contradiction from non-constancy.
2. **Contract A09**: `cylinder_energy_decay` in `SingularityRemoval.lean`
   - Exponential energy decay on conformal cylinder $[-L, L] \times S^1 \cong A(e^{-L}, e^L) \subset \mathbb{C}^*$.
3. **Contract A10**: `cylinder_diameter_decay` in `SingularityRemoval.lean`
   - Exponential diameter decay on conformal cylinders controlled by boundary oscillation and energy.
4. **Contract A11**: `cylinder_localization` in `SingularityRemoval.lean`
   - Localization of cylinder image into small metric balls when neck energy is below threshold.
5. **Contract A12**: `puncture_removability_lp` in `SingularityRemoval.lean`
   - Puncture removability for weak $J$-holomorphic curves with finite energy in $W^{1, p}$ ($p > 2$), extending across the puncture into $C^0 / C^\infty$.

## Mathematical Specifications & References
- M. Gromov, "Pseudo holomorphic curves in symplectic manifolds", *Inventiones Math.* 82 (1985), §1.2, §2.1.
- S. Ivashkovich & V. Shevchishin, "Complex Curves in Almost-Complex Manifolds and Meromorphic Hulls", arXiv:math/9912046 (1999), §2, §3.
- D. McDuff & D. Salamon, *J-holomorphic Curves and Symplectic Topology* (2012), Chapter 4 (Bubbling and Removal of Singularities).
- `gromov_compactness.pdf` §4.2 (Contracts A07, A09, A10, A11, A12).
- `GROMOV_COMPACTNESS_BLUEPRINT.md`.

## Proving Methodology & Tooling
- Local Ollama/Gemma daemon on `http://localhost:11434` with model `gemma-lean4:latest` via `tools/ollama_lean4_client.py`.
- Reusable skills:
  - `skills/lean4-symplectic-autoformalizer/SKILL.md`
  - `skills/ollama-lean4-gemma-prover/SKILL.md`
  - `skills/lean4-proof-repair-engine/SKILL.md`
- Zero-sorry mandate: All auxiliary foundations, reduction steps, monotonicity bounds, and decay estimates formulated with zero `sorry` and zero `admit`.
- Axiom purity: Only standard Lean 4 kernel axioms (`propext`, `Classical.choice`, `Quot.sound`).
- Zero regressions: Full repository build (`lake build GromovCompactness`) and all test suites pass with exit code 0.

## Milestone Status: DONE (Certified PASS Unanimous 5/5 — 2026-11-04T10:18:00Z)
- Reviewer 1 (`reviewer1_m4`): **`APPROVE`**
- Reviewer 2 (`reviewer2_m4`): **`APPROVE`**
- Challenger 1 (`challenger1_m4`): **`APPROVE`** (test suite `tests/ChallengeMilestone4EnergyGap.lean`: 23 adversarial tests, exit code 0, 0 warnings)
- Challenger 2 (`challenger2_m4`): **`APPROVE`** (test suite `tests/ChallengeMilestone4Singularities.lean`: 50 adversarial tests, exit code 0, 0 warnings)
- Auditor 1 (`auditor1_m4`): **`CLEAN`** (0 integrity violations, 0 custom axioms, 100% standard Lean 4 kernel axioms verified across all 31 declarations)
Deliverables: 33 machine-checked zero-`sorry` auxiliary definitions, conformal bridge identities, Grönwall differential inequality bounds, Cauchy-Schwarz oscillation estimates, collar emptiness, topological density uniqueness, and modular reduction theorems (+686 lines across `EnergyGap.lean` and `SingularityRemoval.lean`). Committing to `main`.
