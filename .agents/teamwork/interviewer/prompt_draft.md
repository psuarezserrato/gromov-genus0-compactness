Formalize and verify complete, first-principles Lean 4 (v4.35.0) proofs with 0 sorryAx of all 7 coordinate PDE certificates (`h_weitz`, `h_hit_exit`, `h_osc`, `h_decay`, `h_punc`, `h_tower`, `h_aa`) for an arbitrary closed tame almost-complex manifold equipped with `[ClosedTameTarget I M]`. Integrate the verified proofs directly into the codebase in `/Users/pablosuarez/Desktop/SympTopAutoForm` without adding any axioms to `ClosedTameTarget`.

Working directory: /Users/pablosuarez/Desktop/SympTopAutoForm
Integrity mode: demo
The team must NOT: add new axioms or sorryAx to ClosedTameTarget or the target theorems, cite unproven results as axioms or certificates, or use external libraries beyond Mathlib v4.35.0 and the cited repositories (qinz1yang/differential-geometry, Carleson, HunterPDE).

## Reference Materials
- `/Users/pablosuarez/.gemini/antigravity/brain/4a39bd36-01dc-4865-bd8a-d1bf4124b124/first_principles_7_pde_certificates_research_prompt.md`
- `/Users/pablosuarez/.gemini/antigravity/brain/65c6fa65-5a18-42d4-a168-90f9d94356fc/first_principles_7_pde_certificates_blueprint.md`
- `qinz1yang/differential-geometry` (`Lean v4.35.0-rc3`, 0 `sorry`) and `/Users/pablosuarez/Desktop/SympTopAutoForm/data/diffgeo_accepted_proofs.jsonl`
- Carleson project (`fpvandoorn/carleson`), HunterPDE, and Mathlib4 Fourier analysis

## Requirements

### R1. Complete Lean 4 Proof of the 7 Coordinate PDE Certificates
Implement complete, machine-checked Lean 4 (v4.35.0) proofs with 0 `sorryAx` for all 7 coordinate PDE certificates for arbitrary closed tame targets `[ClosedTameTarget I M]`:
1. `h_weitz` (Tensorial Bochner–Weitzenböck Identity): Local stereographic energy density satisfies $\Delta e(w) = |\nabla du(w)|^2 + K(w)$ with $|K(w)| \le b \, e(w)^2$ in `GromovCompactness/Analysis/Bochner.lean`.
2. `h_hit_exit` (Radial Stokes Monotonicity & Small-Ball Exit): Sublevel energy differential inequality $F(t) \le C t F'(t)$ forcing quadratic growth $c r^2 \le E$ and small-ball exit in `GromovCompactness/Analysis/Monotonicity.lean` and `EnergyGap.lean`.
3. `h_osc` & `h_decay` (Annular Contraction & Exponential Cylinder Decay): Widman annular hole-filling recurrence $\theta = K/(1+K) < 1$ and collar oscillation bound $\operatorname{osc} u \le C \sqrt{E}$ in `GromovCompactness/Analysis/SingularityRemoval.lean`.
4. `h_punc` (Puncture Removable Singularity Extension): Finite-energy $J$-holomorphic curve on $\mathbb{CP}^1 \setminus \{p\}$ extends continuously and smoothly across $p$ to a `WeakJHolomorphicOn` map on $\mathbb{CP}^1$ in `GromovCompactness/Analysis/SingularityRemoval.lean`.
5. `h_tower` (Nonlinear Elliptic Bootstrap Tower): Continuous weak $J$-holomorphic maps are $C^n$ for every $n \in \mathbb{N}$ via commutator reduction to second-order elliptic Laplacian system $\Delta v = N(v, Dv)$ and Cauchy–Pompeiu / Schauder gain in `GromovCompactness/Analysis/EllipticBootstrap.lean`.
6. `h_aa` ($C^\infty_{\mathrm{loc}}$ Arzelà–Ascoli Subsequence Extraction): Subsequence extraction in `SmoothLocalConvergesOn I` for uniformly energy-bounded sequences across `FiniteGoodAtlas I M` via countable diagonalization in `GromovCompactness/Analysis/EllipticBootstrap.lean`.

### R2. First-Principles Integration Without Added Axioms
Derive all 7 certificates using the normal chart and finite good atlas infrastructure in `GromovCompactness/Geometry/NormalCharts.lean` (`FiniteGoodAtlas`, `CenteredNormalChart`, `UniformNormalChartFamily`). Do not add any axioms to `ClosedTameTarget I M`, and do not leave target certificates as unproven axioms.

### R3. Codebase Integration and Build Verification
Integrate the formalized proofs directly into the corresponding modules under `GromovCompactness/` in `/Users/pablosuarez/Desktop/SympTopAutoForm`. Ensure the entire project compiles with `lake build` with zero errors, zero warnings treated as errors, and zero `sorryAx`.

## Acceptance Criteria

### Lean 4 Proof Verification
- [ ] Complete Lean 4 proofs for `h_weitz`, `h_hit_exit`, `h_osc`, `h_decay`, `h_punc`, `h_tower`, and `h_aa` are implemented and integrated into the `GromovCompactness/` codebase.
- [ ] No new axioms are added to `ClosedTameTarget` in `GromovCompactness/Geometry/Target.lean` or any other module.
- [ ] Running `#print axioms` on each of the 7 certificate theorems reports only standard Lean 4 / Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`).
- [ ] `lake build` executes to completion with 0 compile errors and 0 `sorryAx` across all modules in `/Users/pablosuarez/Desktop/SympTopAutoForm`.

---

## License & Citation

Licensed under the **GNU Affero General Public License v3.0 (AGPLv3)** for non-commercial use — see [LICENSE.md](https://github.com/psuarezserrato/Turing-recursive/blob/main/LICENSE.md) ([local copy](LICENSE.md)) for details:

> This project is licensed under non-commercial use. If you wish to use this software in a commercial product, service, or enterprise environment, please contact the developer to purchase a commercial license or negotiate royalty terms.

Authored by **Pablo Suárez-Serrato** (November 2026).
