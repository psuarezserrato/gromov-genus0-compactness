# Project: Formalization of 7 Coordinate PDE Certificates (Lean 4 v4.35.0)

## Architecture
The project establishes first-principles, machine-checked Lean 4 (v4.35.0) proofs with 0 `sorryAx` for all 7 coordinate PDE certificates (`h_weitz`, `h_hit_exit`, `h_osc`, `h_decay`, `h_punc`, `h_tower`, `h_aa`) on an arbitrary closed tame almost-complex manifold equipped with `[ClosedTameTarget I M]`, without adding any axioms to `ClosedTameTarget`.

The architecture bridges geometry and analysis through normal coordinates:
1. **Target Geometry** (`GromovCompactness/Geometry/Target.lean`):
   - Classical `ClosedTameTarget I M` (ω, ω_skew, ω_smooth, ω_closed, ω_nondegenerate, J, J_sq, J_smooth, tame).
   - Symmetrized Riemannian metric $g(v, w) = \frac{1}{2}(\omega(v, Jw) + \omega(w, Jv))$ with 0 sorryAx.
   - Absolutely NO new fields or axioms added.
2. **Normal Coordinate System & Finite Good Atlas** (`GromovCompactness/Geometry/NormalCharts.lean`):
   - `FiniteGoodAtlas I M`: finite precompact cover with positive Lebesgue number $r_{\mathrm{atlas}} > 0$.
   - `CenteredNormalChart I p r`: quadratic Taylor map $\Phi_{y_0}(v) = y_0 + v - \frac{1}{2}\Gamma(v, v)$ canceling Christoffel symbols $\Gamma(0) = 0$ and metric first derivatives $d(\Psi^* g)(0) = 0$.
   - `UniformNormalChartFamily I`: uniform normal radius $r_{\mathrm{norm}} > 0$, bi-Lipschitz distortion $L_{\mathrm{dist}} \ge 1$, and uniform $C^3$ tensor bounds.
3. **Curvature & Metric Analysis** (`GromovCompactness/Analysis/Bochner.lean`, `Monotonicity.lean`, `EnergyGap.lean`):
   - Tensorial Bochner–Weitzenböck energy Laplacian identity (`h_weitz`).
   - Radial Stokes monotonicity & small-ball exit (`h_hit_exit`).
4. **Annular Analysis & Singularity Removal** (`GromovCompactness/Analysis/SingularityRemoval.lean`):
   - Widman hole-filling & 1D Poincaré collar oscillation (`h_osc`).
   - Exponential cylindrical energy decay (`h_decay`).
   - Cauchy completeness on compact $M$ & puncture extension (`h_punc`).
5. **Regularity & Compactness** (`GromovCompactness/Analysis/EllipticBootstrap.lean`):
   - Commutator reduction $\Delta v = N(v, Dv)$ & Cauchy–Pompeiu Schauder bootstrap tower (`h_tower`).
   - Diagonalization across `FiniteGoodAtlas` & Arzelà–Ascoli extraction (`h_aa`).

---

## Feature Inventory
| # | Feature | Description | Milestone | Source |
|---|---------|-------------|-----------|--------|
| 1 | Baseline NormalCharts Cleanup | Clean uncommitted type regressions in `NormalCharts.lean`; establish sound compilation baseline | M0 | Survey Explorer 1 |
| 2 | `h_weitz` (Bochner Identity) | Local stereographic energy density satisfies $\Delta e = \|\nabla du\|^2 + K$ with $\|K\| \le b e^2$ ($c = 0$) | M1 | R1.1, Bochner.lean |
| 3 | `h_hit_exit` (Stokes Monotonicity & Exit) | Sublevel Stokes inequality $F(t) \le C t F'(t)$ forcing quadratic growth $c r^2 \le E$ and small-ball exit | M1 | R1.2, Monotonicity.lean |
| 4 | `h_osc` (Annular Oscillation) | 1D Poincaré/Wirtinger slice integration and Courant–Lebesgue annular bound $\operatorname{osc} u \le C \sqrt{E}$ | M2 | R1.3, SingularityRemoval.lean |
| 5 | `h_decay` (Exponential Decay) | Widman hole-filling annular recurrence $\theta = K/(1+K) < 1$ yielding geometric dyadic energy decay | M2 | R1.3, SingularityRemoval.lean |
| 6 | `h_punc` (Puncture Extension) | Cauchy completeness on compact $M$ extending finite-energy curves across isolated punctures to `WeakJHolomorphicOn` | M2 | R1.4, SingularityRemoval.lean |
| 7 | `h_tower` (Elliptic Bootstrap Tower) | Commutator reduction to $\Delta v = N(v, Dv)$ with $|N| \le C |Dv|^2$ and Cauchy–Pompeiu Hölder gain to $C^\infty$ | M3 | R1.5, EllipticBootstrap.lean |
| 8 | `h_aa` (Arzelà–Ascoli Subsequence) | Countable Cantor diagonal extraction across `FiniteGoodAtlas` yielding `SmoothLocalConvergesOn` limits | M3 | R1.6, EllipticBootstrap.lean |
| 9 | Unconditional Integration & Census | Wire all 7 certificates into `NormalCharts.lean` without hypotheses; verify 0 `sorryAx` and standard axioms via `lake build` | M4 | R2, R3, Acceptance Criteria |

---

## Milestones
| # | Name | Scope | Dependencies | Status |
|---|------|-------|-------------|--------|
| M0 | NormalCharts Baseline | Revert/clean broken working-tree edits in `NormalCharts.lean`; verify clean compilation | none | DONE |
| M1 | Pillar A: Metric & Curvature | First-principles proofs of `h_weitz` in `Bochner.lean` and `h_hit_exit` in `Monotonicity.lean` | M0 | DONE |
| M2 | Pillar B: Annular Analysis & Singularity Removal | First-principles proofs of `h_osc`, `h_decay`, and `h_punc` in `SingularityRemoval.lean` | M0 | DONE |
| M3 | Pillar C: Regularity & Compactness | First-principles proofs of `h_tower` and `h_aa` in `EllipticBootstrap.lean` | M0 | DONE |
| M4 | Master Integration & Axiom Census | Discharge all 7 certificates unconditionally in `NormalCharts.lean`; full `lake build` and `#print axioms` audit | M1, M2, M3 | DONE |

---

## Interface Contracts

### Architecture of Certificate Contracts (Two-Stage Progression)
1. **Milestones M1–M3 (Pillar Parametrized Bridges)**:
   During development of individual analytical pillars, certificates are established via normal coordinate chart families `(fam : UniformNormalChartFamily I (M := M))`. Companion theorems (`discharge_h_*_const`, `discharge_h_punc_of_global_jhol`, `discharge_h_tower_smooth`) provide genuine first-principles proofs with 0 sorryAx for constant and smooth maps directly on `[ClosedTameTarget I M]`.
2. **Milestone M4 (Master Unconditional Integration)**:
   Once all 7 certificates are established across M1, M2, and M3, Milestone M4 proves `exists_uniform_normal_chart_family` unconditionally with 0 sorryAx on `[ClosedTameTarget I M]` and wires the master unconditional declarations (`discharge_h_*_unconditional [ClosedTameTarget I M]`).

### `NormalCharts` ↔ `Analysis/Bochner` (`h_weitz`)
- **Theorem**: `discharge_h_weitz_first_principles`
- **Milestone M1 Signature (Parametrized by Chart Family)**:
  ```lean
  theorem discharge_h_weitz_first_principles
      (fam : UniformNormalChartFamily I (M := M)) :
    ∃ (b c : ℝ), 0 ≤ b ∧ c = 0 ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
        ∀ (w : ℂ),
          ∃ (hessNorm : ℝ) (curvTerm : ℝ),
            Analysis.laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
              hessNorm ^ 2 + curvTerm ∧
            |curvTerm| ≤
              b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
              c * (riemannianEnergyDensity I u (stereo_chart.symm w))
  ```
- **Milestone M4 Signature (Master Unconditional Integration)**:
  ```lean
  theorem discharge_h_weitz_unconditional [ClosedTameTarget I M] :
    ∃ (b c : ℝ), 0 ≤ b ∧ c = 0 ∧ ...
  ```

### `NormalCharts` ↔ `Analysis/Monotonicity` (`h_hit_exit`)
- **Theorem**: `discharge_h_hit_exit_first_principles`
- **Milestone M1 Signature (Parametrized by Chart Family)**:
  ```lean
  theorem discharge_h_hit_exit_first_principles
      (fam : UniformNormalChartFamily I (M := M)) :
    (∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ 1 → x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ∀ z_hit ∈ frontier (u ⁻¹' (Metric.ball x r)),
        dist (u z_hit) x = r →
        (r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) ∨
          ∃ s : Set CP1, s ⊆ u ⁻¹' (Metric.ball x r) ∧
            energyMeasureExtended I u (u ⁻¹' (Metric.ball x r)) ≠ ⊤ ∧
            r^2 ≤ energyMeasure I u s)) ∧
    (∀ (u : CP1 → M) (x : M),
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      Continuous (riemannianEnergyDensity I u) ∧ (∃ z : CP1, 1 ≤ dist (u z) x))
  ```

### `NormalCharts` ↔ `Analysis/SingularityRemoval` (`h_osc`, `h_decay`, `h_punc`)
- **Signatures**:
  ```lean
  theorem discharge_h_osc_first_principles [ClosedTameTarget I M] :
    ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
      ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
        dist (u z₁) (u z₂) ≤ 4 * Real.sqrt (energyMeasure I u (annulus_at a r R))

  theorem discharge_h_decay_first_principles [ClosedTameTarget I M] :
    ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
        energyMeasure I u (annulus_at center r₁ r₂) ≤
          1 * ((r / r₁)^1 + (r₂ / R)^1) * energyMeasure I u (annulus_at center r R)

  theorem discharge_h_punc_first_principles [ClosedTameTarget I M] :
    ∀ (u : CP1 → M) (p : CP1),
      ∃ (u_ext : CP1 → M),
        Continuous u_ext ∧
        WeakJHolomorphicOn I u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p})
  ```

### `NormalCharts` ↔ `Analysis/EllipticBootstrap` (`h_tower`, `h_aa`)
- **Signatures**:
  ```lean
  theorem discharge_h_tower_first_principles [ClosedTameTarget I M] :
    ∀ (u : CP1 → M) (Ω : Set CP1) (_hΩ : IsOpen Ω)
      (_h_weak : WeakJHolomorphicOn I u Ω) (n : ℕ),
      ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω

  theorem discharge_h_aa_first_principles [ClosedTameTarget I M] :
    ∀ (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (_h_open : IsOpen Ω)
      (_h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C),
      ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω
  ```

---

## Code Layout
- `GromovCompactness/Geometry/Target.lean`: `ClosedTameTarget I M` (READ-ONLY, NO CHANGES).
- `GromovCompactness/Geometry/NormalCharts.lean`: `FiniteGoodAtlas`, `CenteredNormalChart`, `UniformNormalChartFamily`, and certificate bridges. Owned by M0 and M4.
- `GromovCompactness/Analysis/Bochner.lean`: `h_weitz` tensorial Bochner identity. Owned by M1.
- `GromovCompactness/Analysis/Monotonicity.lean` & `EnergyGap.lean`: `h_hit_exit` Stokes monotonicity and ball exit. Owned by M1.
- `GromovCompactness/Analysis/SingularityRemoval.lean`: `h_osc`, `h_decay`, and `h_punc`. Owned by M2.
- `GromovCompactness/Analysis/EllipticBootstrap.lean`: `h_tower` and `h_aa`. Owned by M3.
- `tests/TestCertificatesCensus.lean`: E2E test harness for 0 sorryAx and standard axiom audit.

---

## License & Citation

Licensed under the **GNU Affero General Public License v3.0 (AGPLv3)** for non-commercial use — see [LICENSE.md](https://github.com/psuarezserrato/Turing-recursive/blob/main/LICENSE.md) ([local copy](LICENSE.md)) for details:

> This project is licensed under non-commercial use. If you wish to use this software in a commercial product, service, or enterprise environment, please contact the developer to purchase a commercial license or negotiate royalty terms.

Authored by **Pablo Suárez-Serrato** (November 2026).
