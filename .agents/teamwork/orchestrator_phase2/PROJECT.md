# Project: Gromov Compactness (Genus 0) — Phase 2: Local Analysis & Calibrated Bubbling

## Architecture
Phase 2 bridges the foundational geometric setup of Phase 1 (`F00`–`F06`) with the global bubble tree convergence of Phase 3 (`C01`–`C06`). It implements the local analytic regularity engine (Layer 2) and calibrated bubbling rescaling (Layer 3) across 7 modules under `GromovCompactness/Analysis/`:
- `Monotonicity.lean` (`A01`, `A08`): Mean-value inequality and target monotonicity.
- `Bochner.lean` (`A02`): Differential inequality for energy density $\Delta e \ge -b e^2$.
- `EpsilonRegularity.lean` (`A03`): Gradient bound $\sup |du|^2 \le C r^{-2} E$ via `Mathlib.Analysis.Hofer.hofer`.
- `EllipticBootstrap.lean` (`A04`, `A05`, `A06`): Cauchy-Riemann estimates, $W^{1,p} \to C^\infty$ bootstrap, and $C^\infty_{\mathrm{loc}}$ compactness via Arzelà-Ascoli.
- `EnergyGap.lean` (`A07`): Minimal sphere energy $\varepsilon_{\mathrm{sph}} > 0$.
- `SingularityRemoval.lean` (`A09`–`A12`): Small-energy cylinder localization, exponential decay, Sobolev extension, and smooth singularity removal.
- `HoferRescaling.lean` (`B01`, `B02`): Universal threshold $h > 0$ and moving center/radius calibration.

## Feature Inventory
| # | Feature | Description | Milestone | Source |
|---|---|---|---|---|
| 1 | `A01:mean_value` | Scalar Mean-Value Inequality for $\Delta e \ge -b e^2$ | M1 (Model A), M2 (Model B) | Blueprint §4.1, Task A01 |
| 2 | `A02:bochner` | Bochner Energy-Density Differential Inequality | M1 (Model A), M2 (Model B) | Blueprint §4.1, Task A02 |
| 3 | `A03:eps_regularity` | $\varepsilon$-Regularity via `Mathlib.Analysis.Hofer.hofer` | M1 (Model A), M2 (Model B) | Blueprint §4.1, Task A03 |
| 4 | `A04:elliptic_toolkit` | Euclidean Elliptic and Sobolev Toolkit | M1 (Model A), M3 (Model B) | Blueprint §4.1, Task A04 |
| 5 | `A05:bootstrap` | Nonlinear Elliptic Bootstrap ($W^{1,p} \to C^\infty$) | M1 (Model A), M3 (Model B) | Blueprint §4.1, Task A05 |
| 6 | `A06:local_compactness` | $C^\infty_{\mathrm{loc}}$ Compactness under Gradient Bounds | M1 (Model A), M3 (Model B) | Blueprint §4.1, Task A06 |
| 7 | `A07:sphere_energy_gap` | Minimal Energy Gap $\varepsilon_{\mathrm{sph}} > 0$ for Spheres | M1 (Model A), M4 (Model B) | Blueprint §4.2, Task A07 |
| 8 | `A08:monotonicity` | Target Monotonicity Formula ($E \ge c r^2$) | M1 (Model A), M2 (Model B) | Blueprint §4.3, Task A08 |
| 9 | `A09:cylinder_localization` | Small-Energy Cylinder Localization into a Chart | M1 (Model A), M4 (Model B) | Blueprint §4.3, Task A09 |
| 10 | `A10:cylinder_decay` | Cylinder Energy and Diameter Exponential Decay | M1 (Model A), M4 (Model B) | Blueprint §4.3, Task A10 |
| 11 | `A11:puncture_extension` | Continuous & Sobolev Extension Across Punctures | M1 (Model A), M4 (Model B) | Blueprint §4.4, Task A11 |
| 12 | `A12:removal_of_singularities` | Smooth Removal of Isolated Singularities | M1 (Model A), M4 (Model B) | Blueprint §4.4, Task A12 |
| 13 | `B01:threshold_h` | Universal Threshold $h \le \min(\varepsilon_{\mathrm{reg}}/2, \varepsilon_{\mathrm{sph}}, \varepsilon_{\mathrm{neck}}/2)$ | M1 (Model A), M5 (Model B) | Blueprint §4.5, Task B01 |
| 14 | `B02:calibration` | Calibrated Rescaling Centers and Radii ($E(D_{\lambda_n}) = m - h/2$) | M1 (Model A), M5 (Model B) | Blueprint §4.6, Task B02 |
| 15 | `Model_A_Scaffolding` | Lean 4 Typechecked Skeletons with `sorry` for all 7 modules | M1 | Dispatch Stage 1 |
| 16 | `Blueprint_Linking` | Exact `\lean{...}` and `\uses{...}` in `blueprint/src/content.tex` | M1, M6 | Dispatch Stage 1 & 2 |
| 17 | `Lake_Build_Verify` | Clean compilation under `lake build GromovCompactness` | M1, M6 | Acceptance Criteria |
| 18 | `Checkpoint_Commit` | Git commit & workflow control checkpoint | M1, M6 | Workflow Discipline |

## Milestones
| # | Name | Scope | Dependencies | Status |
|---|---|---|---|---|
| M1 | Phase 2 Model A Scaffolding | Scaffold all 7 modules in `GromovCompactness/Analysis/` with typechecked signatures, imports, docstrings, and `sorry` stubs; link in `GromovCompactness.lean` and `blueprint/src/content.tex`; verify `lake build`; commit & checkpoint | Phase 1 (`F00`–`F06`) | IN_PROGRESS |
| M2 | Phase 2 Model B: Regularity Engine | Zero-`sorry` proof completion of `A01` (Mean-Value), `A02` (Bochner), `A08` (Monotonicity), and `A03` ($\varepsilon$-Regularity) | M1 | PLANNED |
| M3 | Phase 2 Model B: Elliptic Bootstrap | Zero-`sorry` proof completion of `A04` (Elliptic Toolkit), `A05` (Nonlinear Bootstrap), and `A06` (Local Compactness) | M1, M2 | PLANNED |
| M4 | Phase 2 Model B: Energy Gap & Singularities | Zero-`sorry` proof completion of `A07` (Energy Gap) and `A09`–`A12` (Cylinder Decay & Removal of Singularities) | M1, M2, M3 | PLANNED |
| M5 | Phase 2 Model B: Calibrated Bubbling | Zero-`sorry` proof completion of `B01` (Universal Threshold $h$) and `B02` (Calibrated Rescaling) | M1, M2, M4 | PLANNED |
| M6 | Phase 2 Integration & Blueprint Certification | Tag all Phase 2 declarations with `\leanok`, verify full `lake build`, run forensic audit & verification gate, commit & push to GitHub | M1–M5 | PLANNED |

## Interface Contracts
### `Monotonicity.lean` (`A01`, `A08`) ↔ `EpsilonRegularity.lean` (`A03`)
- `scalar_mean_value_inequality (b : ℝ) (hb : 0 ≤ b)` provides constants $\eta, C > 0$ such that $L^1$ energy bound implies $L^\infty$ bound on $D_{r/2}$.
- `target_monotonicity` ensures $c r^2 \le E(u; u^{-1}(B_r(x)))$ for $r \le r_0$.

### `Bochner.lean` (`A02`) ↔ `EpsilonRegularity.lean` (`A03`)
- `bochner_differential_inequality` provides target curvature constant $b \ge 0$ such that $\Delta e \ge -b e^2$.

### `EpsilonRegularity.lean` (`A03`) ↔ Downstream Modules (`A07`, `A09`, `A10`, `B01`)
- `epsilon_regularity` provides $\varepsilon_{\mathrm{reg}} > 0, C_{\mathrm{reg}} > 0$ with $\sup_{D_{r/2}} |du|^2 \le C_{\mathrm{reg}} r^{-2} E(u; D_r)$.
- Uses Patrick Massot's `hofer` from `Mathlib.Analysis.Hofer`.

### `EllipticBootstrap.lean` (`A04`, `A05`, `A06`) ↔ `SingularityRemoval.lean` (`A12`)
- `interior_cauchy_riemann_estimate` provides interior $W^{k+1, p}$ estimates.
- `nonlinear_elliptic_bootstrap` upgrades continuous weak solutions to smooth $C^\infty$.
- `local_smooth_compactness` produces $C^\infty_{\mathrm{loc}}$ converging subsequences.

### `SingularityRemoval.lean` (`A09`–`A12`) ↔ `HoferRescaling.lean` (`B01`, `B02`)
- `cylinder_exponential_decay` provides $\varepsilon_{\mathrm{neck}} > 0$ and exponential decay constants $C_0, a > 0$.
- `removal_of_singularities` guarantees unique smooth extension across punctures for finite energy curves.
- `TargetThresholds` (`B01`) packages $h \le \min(\varepsilon_{\mathrm{reg}}/2, \varepsilon_{\mathrm{sph}}, \varepsilon_{\mathrm{neck}}/2)$ in `GromovCompactness.Bubbling`.
- `CalibratedRescaling` (`B02`) extracts moving centers $a_n \to p$ and radii $\lambda_n \to 0$ with $E(f_n; D_{\lambda_n}(a_n)) = m - h/2$.

## Code Layout
```
GromovCompactness/
├── Basic.lean
├── LibraryAudit.lean
├── Geometry/
│   ├── Target.lean
│   └── Sphere.lean
├── Analysis/
│   ├── Energy.lean
│   ├── Monotonicity.lean        # A01, A08
│   ├── Bochner.lean             # A02
│   ├── EpsilonRegularity.lean   # A03
│   ├── EllipticBootstrap.lean   # A04, A05, A06
│   ├── EnergyGap.lean           # A07
│   ├── SingularityRemoval.lean  # A09, A10, A11, A12
│   └── HoferRescaling.lean      # B01, B02 (with GromovCompactness.Bubbling re-exports)
└── Topology/
    ├── SmoothLocal.lean
    ├── Subsequence.lean
    └── SphereTree.lean
```
All modules exported by `GromovCompactness.lean`.
LaTeX blueprint source: `blueprint/src/content.tex`.
