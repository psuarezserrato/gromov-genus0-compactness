# Scope: Phase 2 Model B — Milestone 5 & 6: Calibrated Bubbling & Final Integration

## Target Modules & Contracts for Milestone 5
Target File:
- `GromovCompactness/Analysis/HoferRescaling.lean`

### Contracts to Prove & Certify (Milestone 5):
1. **Contract B01**: `has_energy_defect_iff_concentration` in `HoferRescaling.lean`
   - Energy defect measure on $\mathbb{CP}^1$ and its equivalence with energy concentration points.
   - Radon weak convergence of energy measures $\mu_n \rightharpoonup \mu_\infty$.
   - Defect points $z \in \mathbb{CP}^1$ where $\mu_\infty(\{z\}) \ge \varepsilon_0$.
   - Finite singular set $S \subset \mathbb{CP}^1$ with cardinality bound $|S| \le E_0 / \varepsilon_0$.
2. **Contract B02**: `exists_calibrated_rescaling` in `HoferRescaling.lean`
   - Connecting `Mathlib.Analysis.Hofer` lemma to calibrated rescaling.
   - Extraction of sequence of centers $a_n \to a_\infty$ and scales $\lambda_n \to 0$ such that rescaled maps $v_n(z) = u_n(a_n + \lambda_n z)$ have bounded gradient on compact disks $B(0, R)$ with $\|d v_n(0)\| = 1$.
   - Energy lower bound on the bubble $E(v_\infty) \ge \varepsilon_{\mathrm{sph}}$.

## Target for Milestone 6:
- Integration across all Phase 2 modules (`Monotonicity.lean`, `Bochner.lean`, `EpsilonRegularity.lean`, `EllipticBootstrap.lean`, `EnergyGap.lean`, `SingularityRemoval.lean`, `HoferRescaling.lean`).
- Update `blueprint/src/content.tex` with `\leanok` tags.
- Full axiom audit (`#print axioms` across all Phase 2 declarations).
- Complete test suite validation (`lake build GromovCompactness` and all `tests/Challenge*.lean`).
- Final victory report to Sentinel.

## Proving Methodology & Tooling
- Local Ollama/Gemma daemon on `http://localhost:11434` with model `gemma-lean4:latest` via `tools/ollama_lean4_client.py`.
- Reusable skills:
  - `skills/lean4-symplectic-autoformalizer/SKILL.md`
  - `skills/ollama-lean4-gemma-prover/SKILL.md`
  - `skills/lean4-proof-repair-engine/SKILL.md`
- Zero-sorry mandate: All auxiliary foundations, metric lemmas, rescaling bounds, and reduction theorems formulated with zero `sorry` and zero `admit`.
- Axiom purity: Only standard Lean 4 kernel axioms (`propext`, `Classical.choice`, `Quot.sound`).
- Zero regressions: Full repository build (`lake build GromovCompactness`) and all test suites pass with exit code 0.

## Milestone Status
- Milestone 1: DONE (Commit `947e544`)
- Milestone 2: DONE (Commit `f25a440`)
- Milestone 3: DONE (Commit `3b7d779`)
- Milestone 4: DONE (Commit `2ba680e`)
- Milestone 5: DONE (Unanimous 5/5 Gate Pass & Clean Forensic Certification)
- Milestone 6: PLANNED (To be executed by Orchestrator Generation 6)
