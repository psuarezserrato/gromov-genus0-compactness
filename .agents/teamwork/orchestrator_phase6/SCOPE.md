# Scope: Phase 6 Local Analysis (A01–A12 + B01)

## Architecture
Local analytic estimates layer for pseudo-holomorphic curves in almost-complex manifolds:
- Mean-value inequality and Bochner differential inequality for gradient/energy density
- ε-regularity theorem and gradient decay
- $C^{k,\alpha}$ Hölder/Schauder interior Cauchy-Riemann estimates and Pompeiu operators
- Nonlinear elliptic bootstrap ($W^{1,p} / C^1 \to C^\infty$)
- Local smooth compactness via Arzelà-Ascoli and diagonal extraction
- Target monotonicity and minimal sphere energy gap ($\varepsilon_{sph} > 0$)
- Cylinder exponential decay in cylindrical coordinates and localization
- Removable singularities across isolated punctures ($W^{1,p} \to C^1 \to C^\infty$)
- Universal target thresholds (`exists_target_thresholds`, `B01`)

## Feature Inventory
| # | Feature | Description | Milestone | Source |
|---|---------|-------------|-----------|--------|
| 1 | `scalar_mean_value_inequality` | Sub-mean-value property for subharmonic functions with quadratic absorption | M1 | Contract A01, COMPLETION_PLAN #1 |
| 2 | `bochner_differential_inequality` | $\Delta e \ge -b e^2 - c e$ coordinate computation or Euclidean density | M1 | Contract A02, COMPLETION_PLAN #2 |
| 3 | `epsilon_regularity` | $E(u; D_r) < \varepsilon_{reg} \implies \sup_{D_{r/2}} e \le C r^{-2} E$ | M1 | Contract A03, COMPLETION_PLAN #3 |
| 4 | `interior_cauchy_riemann_estimate` | $\|f\|_{C^{k+1,\alpha}(D_r)} \le C(\|\bar{\partial} f\|_{C^{k,\alpha}(D_R)} + \|f\|_{C^0(D_R)})$ | M2 | Contract A04, COMPLETION_PLAN #4 |
| 5 | `cauchy_pompeiu_holder_gain` | $\|f\|_{C^{0,\alpha}(D_r)} \le C(\|\bar{\partial} f\|_{C^0(D_R)} + \|f\|_{C^0(D_R)})$ | M2 | Contract A04, COMPLETION_PLAN #5 |
| 6 | `nonlinear_elliptic_bootstrap` | $C^1 + \bar{\partial}_J u = 0 \implies C^\infty$ | M2 | Contract A05, COMPLETION_PLAN #6 |
| 7 | `local_smooth_compactness` | Uniform gradient bounds $\implies C^\infty_{loc}$ convergence | M2 | Contract A06, COMPLETION_PLAN #7 |
| 8 | `target_monotonicity` | $E(u; u^{-1}(B_r(x))) \ge c r^2$ for $r \le r_0$ | M3 | Contract A08, COMPLETION_PLAN #8 |
| 9 | `sphere_energy_gap` | Nonconstant $J$-sphere $\implies E(u) \ge \varepsilon_{sph} > 0$ | M3 | Contract A07, COMPLETION_PLAN #9 |
| 10 | `cylinder_localization` | Small annulus energy $\implies$ inner annulus image in small ball | M4 | Contract A09, COMPLETION_PLAN #10 |
| 11 | `cylinder_exponential_decay` | Annulus energy decay $E \le C_0 ((r/r_1)^a + (r_2/R)^a) E_{ann}$ | M4 | Contract A10, COMPLETION_PLAN #11 |
| 12 | `puncture_sobolev_extension` | Finite energy map on $S^2 \setminus \{p\} \implies C^1$ extension across $p$ | M4 | Contract A11, COMPLETION_PLAN #12 |
| 13 | `removal_of_singularities` | Smooth extension across $p$ | M4 | Contract A12, COMPLETION_PLAN #13 |
| 14 | `exists_target_thresholds` | Existence of $(\varepsilon_{reg}, \varepsilon_{sph}, \delta_0, C)$ | M4 | Contract B01 |

## Milestones
| # | Name | Scope | Dependencies | Status |
|---|------|-------|-------------|--------|
| M1 | Mean-Value Inequality, Bochner & ε-Regularity | A01–A03 (`#1–#3`) | none | IN_PROGRESS |
| M2 | $C^{k,\alpha}$ Hölder/Schauder & Bootstrap | A04–A06 (`#4–#7`) | M1 | PLANNED |
| M3 | Target Monotonicity & Sphere Energy Gap | A07–A08 (`#8–#9`) | M1 | PLANNED |
| M4 | Cylinder Decay, Puncture Extension, Singularities & Thresholds | A09–A12 + B01 (`#10–#13`) | M1, M2, M3 | PLANNED |
| M5 | Phase 6 Final Gate & Census Certification | Axiom census, fine-tuning update, blueprint | M1–M4 | PLANNED |

## Interface Contracts
### M1 (`A01–A03`) ↔ M2 (`A04–A06`) & M4 (`A09–A12`)
- `epsilon_regularity` (`A03`): provides interior gradient bounds on disks with small energy, consumed by `local_smooth_compactness` (`A06`), `cylinder_localization` (`A09`), and `exists_target_thresholds` (`B01`).
- `scalar_mean_value_inequality` (`A01`) & `bochner_differential_inequality` (`A02`): compose to prove `epsilon_regularity` (`A03`).

### M2 (`A04–A06`) ↔ M4 (`A09–A12`)
- `nonlinear_elliptic_bootstrap` (`A05`): takes $C^1$ weak $J$-holomorphic maps to $C^\infty$, consumed by `removal_of_singularities` (`A12`).
- `interior_cauchy_riemann_estimate` (`A04`) & `cauchy_pompeiu_holder_gain`: provide $C^{k,\alpha}$ Schauder estimates for difference quotient induction.

### M3 (`A07–A08`) ↔ M4 (`B01`)
- `sphere_energy_gap` (`A07`): provides positive lower bound $\varepsilon_{sph} > 0$ for nonconstant $J$-spheres, directly consumed by `exists_target_thresholds` (`B01`).
- `target_monotonicity` (`A08`): gives $r^2$ energy growth in balls, bounding image scale.

### M4 (`A09–A12` + `B01`) ↔ Phase 7 Bubbling & Assembly
- `removal_of_singularities` (`A12`) and `exists_target_thresholds` (`B01`) are core inputs to Phase 7 concentration and bubbling.

## Code Layout
- `GromovCompactness/Analysis/MeanValueInequality.lean` (Contracts A01, A02)
- `GromovCompactness/Analysis/EpsilonRegularity.lean` (Contract A03)
- `GromovCompactness/Analysis/EllipticBootstrap.lean` (Contracts A04, A05, A06)
- `GromovCompactness/Analysis/Monotonicity.lean` (Contract A08)
- `GromovCompactness/Analysis/EnergyGap.lean` (Contract A07)
- `GromovCompactness/Analysis/CylinderDecay.lean` / `SingularityRemoval.lean` (Contracts A09, A10)
- `GromovCompactness/Analysis/PunctureExtension.lean` / `SingularityRemoval.lean` (Contract A11)
- `GromovCompactness/Analysis/RemovalOfSingularities.lean` / `SingularityRemoval.lean` (Contract A12)
- `GromovCompactness/Analysis/HoferRescaling.lean` (Contract B01)
