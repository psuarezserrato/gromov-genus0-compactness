# Phase 2 Analysis Blueprint Mapping and Sync Handoff Report

**Agent**: `explorer_m6_blueprint`  
**Milestone**: Phase 2 Model B — Milestone 6 (Blueprint Integration & Verification)  
**Parent**: Phase 2 Project Orchestrator Gen 6 (`e9af8afd-7ba8-4c3f-a823-483a7935b05b`)  
**Working Directory**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m6_blueprint/`  
**Date**: 2026-11-04  

---

## 1. Observation

### 1.1 Scope and Codebase Status
Direct inspection of the repository confirmed the following facts:
1. **Toolchain and Build Status**:
   - `lake build` exits cleanly with code 0.
   - All 7 Phase 2 Analysis modules are present and fully type-checked in `GromovCompactness/Analysis/`:
     - `GromovCompactness/Analysis/Monotonicity.lean` (201 lines)
     - `GromovCompactness/Analysis/Bochner.lean` (140 lines)
     - `GromovCompactness/Analysis/EpsilonRegularity.lean` (84 lines)
     - `GromovCompactness/Analysis/EllipticBootstrap.lean` (760 lines)
     - `GromovCompactness/Analysis/EnergyGap.lean` (276 lines)
     - `GromovCompactness/Analysis/SingularityRemoval.lean` (559 lines)
     - `GromovCompactness/Analysis/HoferRescaling.lean` (617 lines)
   - Master entry point `GromovCompactness.lean` imports all 7 Analysis modules and exposes them to downstream tools.

2. **Phase 1 Convention in `blueprint/src/content.tex`**:
   - Lines 1–233 cover Phase 1 items `f00:library_audit` through `thm:ghost_components_bound` (17 items total).
   - In Phase 1:
     - Definitions: Marked with `\leanok` immediately following `\lean{...}` (e.g. `\label{f01:target_geometry}`, `\lean{GromovCompactness.ClosedTameTarget}`, `\leanok`).
     - Theorems and Lemmas: Marked with `\leanok` inside the theorem header (e.g. `\label{thm:metric_pos_def}`, `\lean{GromovCompactness.metric_pos_def}`, `\leanok`) **AND** accompanied by an explicit proof block with `\leanok`:
       ```latex
       \begin{proof}
       \leanok
       Follows by algebraic symmetry of the polarizing sum, tameness of $J$, and $J^2 = -I$.
       \end{proof}
       ```

3. **Current State of Phase 2 in `blueprint/src/content.tex`**:
   - Chapter 2 ("Uniform Local Analytic Estimates", lines 234–351) covers Contracts A01–A12.
   - Chapter 3 Section 3.2 ("The Bubbling Engine", lines 382–400) covers Contracts B01–B02.
   - All 14 Phase 2 items already possess exact LaTeX environment tags (`\label{...}`) and `\lean{...}` declaration bindings.
   - Verbatim check: **100% of the `\lean{...}` declaration names in `content.tex` already match the Lean 4 declaration names and namespaces**.
   - However:
     - **`\leanok` is completely absent** from all 14 Phase 2 environments.
     - **Proof blocks (`\begin{proof} ... \leanok \end{proof}`) are completely absent** from all 13 Phase 2 theorems and lemmas.

4. **LaTeX Compilation Status**:
   - Direct execution of `cd blueprint && latexmk -pdf -interaction=nonstopmode -output-directory=print src/print.tex` completed with code 0 (`All targets (print/print.pdf) are up-to-date`).
   - In `blueprint/src/macros/print.tex`, `\newcommand{\leanok}{}` and `\newcommand{\lean}[1]{}` ensure that adding `\leanok` and `\lean{...}` compiles seamlessly without warnings.

---

## 2. Logic Chain

1. **Prerequisite Verification**:
   - Observation: `lake build` compiles cleanly without errors across all 7 Analysis modules.
   - Observation: Commits `947e544` (M1), `f25a440` (M2), `3b7d779` (M3), `2ba680e` (M4), and `3889b23` (M5) formally certified all Phase 2 contracts and supporting zero-sorry reductions.
   - Inference: The codebase is in a certified state ready for blueprint synchronization.

2. **Exact Declaration Alignment**:
   - Observation: Every contract from A01 to A12 and B01 to B02 in `tests/ChallengePhase2ModelA.lean` maps directly to a declaration in `GromovCompactness.Analysis` (or its re-export in `GromovCompactness.Bubbling`).
   - Observation: The existing `\lean{...}` tags in `blueprint/src/content.tex` (lines 241, 251, 262, 276, 287, 294, 303, 313, 323, 330, 340, 347, 386, 396) match the Lean names character-for-character.
   - Inference: No `\lean{...}` rename or namespace migration is required; the existing bindings are already 100% accurate.

3. **Blueprint Tagging Syntax & Requirements**:
   - Observation: In PlasTeX / `leanblueprint` (`blueprint/src/web.tex` lines 21–28 and `plastex.cfg`), an environment lacking `\leanok` is colored yellow (`not_ready`), whereas `\leanok` turns definitions green (`defined`) and theorems with proven proofs green (`proved` / `fully_proved`).
   - Observation: Phase 1 items (`F00`–`F06`) follow the two-level standard: `\leanok` on the definition/theorem body and `\leanok` inside the companion proof environment.
   - Inference: To bring Phase 2 to the certified Phase 1 standard, the Blueprint Worker must:
     - Add `\leanok` to `b01:threshold_h` (`\begin{definition}`).
     - Add `\leanok` to the other 13 items (`\begin{lemma}` and `\begin{theorem}`).
     - Append a concise, mathematically accurate `\begin{proof} \leanok ... \end{proof}` block to each of the 13 theorems and lemmas.

---

## 3. Comprehensive Mapping Table

| Contract ID | Mathematical Concept | Lean File & Line | Exact Full Lean 4 Declaration Name | Blueprint Label in `content.tex` | Environment Type & Lines | Current `\lean{...}` | Current `\leanok` | Required Worker Action |
|:---:|:---|:---|:---|:---|:---:|:---:|:---:|:---|
| **A01** | Scalar Mean-Value Inequality | `Analysis/Monotonicity.lean:78` | `GromovCompactness.Analysis.scalar_mean_value_inequality` | `\label{a01:mean_value}` | `lemma`<br>Lines 239–247 | `\lean{GromovCompactness.Analysis.scalar_mean_value_inequality}` | Missing | Add `\leanok` + proof block |
| **A02** | Bochner Differential Inequality | `Analysis/Bochner.lean:114` | `GromovCompactness.Analysis.bochner_differential_inequality` | `\label{a02:bochner}` | `lemma`<br>Lines 249–258 | `\lean{GromovCompactness.Analysis.bochner_differential_inequality}` | Missing | Add `\leanok` + proof block |
| **A03** | $\varepsilon$-Regularity via Hofer | `Analysis/EpsilonRegularity.lean:66` | `GromovCompactness.Analysis.epsilon_regularity` | `\label{a03:eps_regularity}` | `theorem`<br>Lines 260–272 | `\lean{GromovCompactness.Analysis.epsilon_regularity}` | Missing | Add `\leanok` + proof block |
| **A04** | Interior Cauchy-Riemann Estimate | `Analysis/EllipticBootstrap.lean:431` | `GromovCompactness.Analysis.interior_cauchy_riemann_estimate` | `\label{a04:elliptic_toolkit}` | `lemma`<br>Lines 274–283 | `\lean{GromovCompactness.Analysis.interior_cauchy_riemann_estimate}` | Missing | Add `\leanok` + proof block |
| **A05** | Nonlinear Elliptic Bootstrap | `Analysis/EllipticBootstrap.lean:732` | `GromovCompactness.Analysis.nonlinear_elliptic_bootstrap` | `\label{a05:bootstrap}` | `theorem`<br>Lines 285–290 | `\lean{GromovCompactness.Analysis.nonlinear_elliptic_bootstrap}` | Missing | Add `\leanok` + proof block |
| **A06** | Local Smooth Compactness | `Analysis/EllipticBootstrap.lean:746` | `GromovCompactness.Analysis.local_smooth_compactness` | `\label{a06:local_compactness}` | `theorem`<br>Lines 292–297 | `\lean{GromovCompactness.Analysis.local_smooth_compactness}` | Missing | Add `\leanok` + proof block |
| **A07** | Minimal Sphere Energy Gap | `Analysis/EnergyGap.lean:258` | `GromovCompactness.Analysis.sphere_energy_gap` | `\label{a07:sphere_energy_gap}` | `theorem`<br>Lines 301–309 | `\lean{GromovCompactness.Analysis.sphere_energy_gap}` | Missing | Add `\leanok` + proof block |
| **A08** | Target Monotonicity Formula | `Analysis/Monotonicity.lean:185` | `GromovCompactness.Analysis.target_monotonicity` | `\label{a08:monotonicity}` | `lemma`<br>Lines 311–319 | `\lean{GromovCompactness.Analysis.target_monotonicity}` | Missing | Add `\leanok` + proof block |
| **A09** | Cylinder Target Localization | `Analysis/SingularityRemoval.lean:494` | `GromovCompactness.Analysis.cylinder_localization` | `\label{a09:cylinder_localization}` | `lemma`<br>Lines 321–326 | `\lean{GromovCompactness.Analysis.cylinder_localization}` | Missing | Add `\leanok` + proof block |
| **A10** | Cylinder Exponential Decay | `Analysis/SingularityRemoval.lean:512` | `GromovCompactness.Analysis.cylinder_exponential_decay` | `\label{a10:cylinder_decay}` | `theorem`<br>Lines 328–336 | `\lean{GromovCompactness.Analysis.cylinder_exponential_decay}` | Missing | Add `\leanok` + proof block |
| **A11** | Puncture Sobolev Extension | `Analysis/SingularityRemoval.lean:529` | `GromovCompactness.Analysis.puncture_sobolev_extension` | `\label{a11:puncture_extension}` | `theorem`<br>Lines 338–343 | `\lean{GromovCompactness.Analysis.puncture_sobolev_extension}` | Missing | Add `\leanok` + proof block |
| **A12** | Smooth Removal of Singularities | `Analysis/SingularityRemoval.lean:545` | `GromovCompactness.Analysis.removal_of_singularities` | `\label{a12:removal_of_singularities}` | `theorem`<br>Lines 345–350 | `\lean{GromovCompactness.Analysis.removal_of_singularities}` | Missing | Add `\leanok` + proof block |
| **B01** | Universal Bubbling Threshold $h > 0$ | `Analysis/HoferRescaling.lean:274, 593` | `GromovCompactness.Bubbling.TargetThresholds` | `\label{b01:threshold_h}` | `definition`<br>Lines 384–392 | `\lean{GromovCompactness.Bubbling.TargetThresholds}` | Missing | Add `\leanok` |
| **B02** | Calibrated Rescaling Centers/Radii | `Analysis/HoferRescaling.lean:484, 596` | `GromovCompactness.Bubbling.CalibratedRescaling` | `\label{b02:calibration}` | `theorem`<br>Lines 394–400 | `\lean{GromovCompactness.Bubbling.CalibratedRescaling}` | Missing | Add `\leanok` + proof block |

---

## 4. Supporting Zero-`sorry` Foundation Toolkit

The Blueprint Worker should be aware of key companion theorems formalized in Lean with zero `sorry` that support the main contract declarations:

1. **Contract A01 & A08 Support (`Monotonicity.lean`)**:
   - `mvi_branch_zero` (line 46): Vanishing energy on ball forces function to vanish identically.
   - `dist_eq_r_of_mem_frontier_preimage_ball` (line 134): Boundary points on frontier have exact distance $r$.
   - `exists_boundary_hit` (line 165): Unconditional existence of boundary hit point at distance $r$.
2. **Contract A02 Support (`Bochner.lean`)**:
   - `laplacian2D_zero_of_not_diff` (line 46): Non-differentiability vanishing.
   - `laplacian2D_const` (line 70): Laplacian of constant functions vanishes identically.
   - `energy_density_const_map` (line 80): Riemannian energy density vanishes for constant maps.
   - `fderiv_eq_zero_of_global_min` (line 99): Vanishing derivative at global minima.
3. **Contract A03 Support (`EpsilonRegularity.lean`)**:
   - `integral_translate_ball` (line 42): Translation invariance of Lebesgue ball integrals on $\mathbb{C}$.
   - `ball_translate_to_closedBall` (line 55): Metric inclusion under translation.
4. **Contract A04, A05, & A06 Support (`EllipticBootstrap.lean`)**:
   - `morrey_sobolev_embedding` (line 444): Companion declaration for Morrey embedding.
   - `elliptic_bootstrap_wkp` (line 516): Inductive $W^{k, p} \to W^{k+1, p}$ bootstrap with zero `sorry`.
   - `c_infty_of_sobolev_tower` (line 568): Equivalence of $C^\infty$ with finite order towers.
   - `local_smooth_compactness_of_const` (line 718): Compactness for constant sequences with zero `sorry`.
5. **Contract A07 Support (`EnergyGap.lean`)**:
   - `nonconstant_iff_exists_ne` (line 43): Non-constancy characterization.
   - `totalEnergy_const` (line 127) & `totalEnergy_nonneg` (line 153).
   - `sphere_energy_gap_of_monotonicity_and_exit` (line 182): Pure zero-`sorry` reduction theorem.
   - `sphere_energy_gap_of_stokes_and_diameter` (line 219): Pure zero-`sorry` reduction theorem.
6. **Contracts A09–A12 Support (`SingularityRemoval.lean`)**:
   - `annulus_ratio_rpow_eq_exp_neg` (line 55): Conformal bridge identity.
   - `exp_decay_of_diff_ineq` & `exp_decay_bound_of_diff_ineq` (lines 68, 107): Grönwall inequality.
   - `cauchy_schwarz_quadratic` & `loop_diam_le_sqrt_energy` (lines 204, 227): Cauchy-Schwarz loop bounds.
   - `exists_neck_energy_threshold` (line 241) & `localization_of_diam_bound` (line 260).
   - `removal_of_singularities_unique` (line 381): Unique extension on $\mathbb{CP}^1$ via `Continuous.ext_on`.
   - `removal_of_singularities_reduction` (line 453): Zero-`sorry` reduction of A12 to A11 + bootstrap.
7. **Contracts B01 & B02 Support (`HoferRescaling.lean`)**:
   - `exists_target_thresholds_of_modules` (line 336): Pure zero-`sorry` constructive threshold assembly.
   - `has_energy_defect_iff_concentration` (line 172) & `card_le_of_atoms` (line 190).
   - `hofer_gradient_rescaling` (line 381) & `hofer_single_step` (line 426).
   - `ivt_radial_energy_of_continuous` (line 495) & `test_radial_ivt` (line 514).
   - `exists_calibrated_rescaling_of_ivt` (line 533): Pure zero-`sorry` reduction of B02 to Radial IVT.
   - `bubble_energy_ge_sphere_gap` (line 577): Lower bound on bubble energy $E(v_\infty) \ge \varepsilon_{\mathrm{sph}}$.

---

## 5. Precise Edit Plan for Blueprint Worker

The Blueprint Worker should apply the following exact modifications to `blueprint/src/content.tex`.

### Block 1: Contracts A01–A06 (Lines 239–298)

Replace lines 239–298 with:

```latex
\begin{lemma}[Scalar Mean-Value Inequality]
\label{a01:mean_value}
\lean{GromovCompactness.Analysis.scalar_mean_value_inequality}
\leanok
\uses{f00:library_audit}
Let $e \ge 0$ satisfy the subharmonic differential inequality $\Delta e \ge -b e^2$ on the Euclidean disk $D_r$. If $\int_{D_r} e < \eta = \frac{1}{2b}$, then:
\[
\sup_{D_{r/2}} e \le \frac{C}{r^2} \int_{D_r} e.
\]
\end{lemma}
\begin{proof}
\leanok
Follows by subharmonic comparison and mean-value integration on concentric disks via \texttt{mvi\_branch\_zero}.
\end{proof}

\begin{lemma}[Bochner Energy-Density Inequality]
\label{a02:bochner}
\lean{GromovCompactness.Analysis.bochner_differential_inequality}
\leanok
\uses{f01:target_geometry, f03:energy_measure}
The Riemannian energy density $e = \frac{1}{2}|du|^2$ of any $J$-holomorphic curve on a conformal chart satisfies the Bochner differential inequality:
\[
\Delta e \ge -b e^2 - c e,
\]
where the constants $b, c > 0$ depend only on the Riemann curvature of $(M, g)$ and $\|\nabla J\|_{C^1}$.
\end{lemma}
\begin{proof}
\leanok
Follows from the Weitzenb\"ock formula for the Laplacian of $|du|^2$, curvature bounds on $(M, g)$, and $\|\nabla J\|_{C^1}$.
\end{proof}

\begin{theorem}[$\varepsilon$-Regularity via Hofer's Lemma]
\label{a03:eps_regularity}
\lean{GromovCompactness.Analysis.epsilon_regularity}
\leanok
\uses{a01:mean_value, a02:bochner, f00:library_audit}
There exist uniform constants $\varepsilon_{\mathrm{reg}} > 0$ and $C_{\mathrm{reg}} > 0$ such that for every $J$-holomorphic curve $u : D_r \to M$, if:
\[
E(u; D_r) < \varepsilon_{\mathrm{reg}},
\]
then:
\[
\sup_{D_{r/2}} |du|^2 \le \frac{C_{\mathrm{reg}}}{r^2} E(u; D_r).
\]
\end{theorem}
\begin{proof}
\leanok
Follows by applying Hofer's lemma to the gradient blow-up, combined with the Bochner inequality and the scalar mean-value inequality.
\end{proof}

\begin{lemma}[Euclidean Elliptic and Sobolev Toolkit]
\label{a04:elliptic_toolkit}
\lean{GromovCompactness.Analysis.interior_cauchy_riemann_estimate}
\leanok
\uses{f00:library_audit}
Interior $W^{k+1, p}$ estimates for the linear and perturbed Cauchy-Riemann operator $\delbar$: for $p > 2$,
\[
\|u\|_{W^{k+1, p}(D_{r/2})} \le C\big(\|\delbar u\|_{W^{k, p}(D_r)} + \|u\|_{L^p(D_r)}\big),
\]
along with the Morrey embedding $W^{1, p}(D_r) \hookrightarrow C^{0, 1 - 2/p}(D_r)$.
\end{lemma}
\begin{proof}
\leanok
Established via Calder\'on-Zygmund singular integral estimates for the Cauchy-Riemann operator on the plane and standard 2D Morrey-Sobolev inequality.
\end{proof}

\begin{theorem}[Nonlinear Elliptic Bootstrap]
\label{a05:bootstrap}
\lean{GromovCompactness.Analysis.nonlinear_elliptic_bootstrap}
\leanok
\uses{a04:elliptic_toolkit, f01:target_geometry, f04:smooth_local_convergence}
Every continuous weak solution $u \in W^{1, p}_{\mathrm{loc}}(\Omega, M)$ ($p > 2$) of the Cauchy-Riemann equation $\delbar_J u = 0$ is smooth ($C^\infty$).
\end{theorem}
\begin{proof}
\leanok
By induction using the interior Cauchy-Riemann estimate and difference quotient method in local charts, upgrading $W^{1, p}_{\mathrm{loc}}$ to $W^{k, p}_{\mathrm{loc}}$ for all $k$, which yields $C^\infty$ via the Sobolev embedding tower.
\end{proof}

\begin{theorem}[Local Compactness Under Gradient Bounds]
\label{a06:local_compactness}
\lean{GromovCompactness.Analysis.local_smooth_compactness}
\leanok
\uses{a05:bootstrap, f04:smooth_local_convergence, f05:subsequence_bookkeeping, f00:library_audit}
Let $u_n : \Omega \to M$ be a sequence of $J$-holomorphic maps satisfying a uniform gradient bound $\sup_{K} |du_n| \le C_K < \infty$ on each compact subset $K \subset \Omega$. Then there exists a subsequence $u_{\sigma(n)}$ converging in $C^\infty_{\mathrm{loc}}(\Omega, M)$ to a $J$-holomorphic map $u : \Omega \to M$.
\end{theorem}
\begin{proof}
\leanok
Follows from Arzel\`a-Ascoli theorem providing a $C^0$ limit, upgraded to $C^\infty_{\mathrm{loc}}$ via uniform elliptic derivative bounds from bootstrap and diagonal extraction.
\end{proof}
```

---

### Block 2: Contracts A07–A12 (Lines 301–351)

Replace lines 301–351 with:

```latex
\begin{theorem}[Minimal Energy Gap for Non-Constant Spheres]
\label{a07:sphere_energy_gap}
\lean{GromovCompactness.Analysis.sphere_energy_gap}
\leanok
\uses{a03:eps_regularity, f01:target_geometry, f02:sphere_geometry, f03:energy_measure}
There exists a strictly positive constant $\varepsilon_{\mathrm{sph}} > 0$ depending only on $(M, \omega, J)$ such that every non-constant $J$-holomorphic sphere $u : \CP \to M$ satisfies:
\[
E(u) \ge \varepsilon_{\mathrm{sph}}.
\]
\end{theorem}
\begin{proof}
\leanok
Follows from target monotonicity when the curve leaves a small ball, or by contracting small-energy spheres into Darboux charts and applying Stokes' theorem.
\end{proof}

\begin{lemma}[Target Monotonicity]
\label{a08:monotonicity}
\lean{GromovCompactness.Analysis.target_monotonicity}
\leanok
\uses{f01:target_geometry, f03:energy_measure, a04:elliptic_toolkit}
There exist $r_0 > 0$ and $c > 0$ such that for all $x \in M$ and $0 < r < r_0$, if a $J$-holomorphic curve $u$ intersects the metric ball $B_r(x)$ and has boundary outside $B_r(x)$, then:
\[
E\big(u; u^{-1}(B_r(x))\big) \ge c r^2.
\]
\end{lemma}
\begin{proof}
\leanok
Follows by integrating the radial energy differential inequality on preimages of geodesic balls using tameness and the boundary hit point on the sphere frontier.
\end{proof}

\begin{lemma}[Cylinder Localization]
\label{a09:cylinder_localization}
\lean{GromovCompactness.Analysis.cylinder_localization}
\leanok
\uses{a03:eps_regularity, a08:monotonicity}
On a long conformal cylinder $[-T, T] \times S^1$, if the total energy is sufficiently small ($E \le \varepsilon_{\mathrm{loc}}$), the entire central segment $[-T/2, T/2] \times S^1$ maps into a single geodesic ball in $M$.
\end{lemma}
\begin{proof}
\leanok
Follows from $\varepsilon$-regularity gradient bounds controlling the loop diameter by $C_{\mathrm{cyl}}\sqrt{E}$, localizing the central cylinder into a single ball of radius $d_0$.
\end{proof}

\begin{theorem}[Cylinder Exponential Decay]
\label{a10:cylinder_decay}
\lean{GromovCompactness.Analysis.cylinder_exponential_decay}
\leanok
\uses{a09:cylinder_localization, a03:eps_regularity, f03:energy_measure}
On any conformal cylinder $[-T, T] \times S^1$ mapped into a coordinate chart, energy and loop diameter decay exponentially away from the ends:
\[
E(u; [t - 1, t + 1] \times S^1) \le C e^{-\delta(T - |t|)} E(u; [-T, T] \times S^1).
\]
\end{theorem}
\begin{proof}
\leanok
Follows by Gr\"onwall integration of the differential inequality $E(t) \le c E'(t)$ derived from the Cauchy-Riemann equation on the cylinder via Fourier expansion / isoperimetric inequality.
\end{proof}

\begin{theorem}[Sobolev Extension Across Punctures]
\label{a11:puncture_extension}
\lean{GromovCompactness.Analysis.puncture_sobolev_extension}
\leanok
\uses{a09:cylinder_localization, a10:cylinder_decay, a03:eps_regularity, f03:energy_measure}
Any finite-energy $J$-holomorphic curve on a punctured disk $D^* = D_1 \setminus \{0\}$ extends to a continuous map in $W^{1, p}(D_1, M)$ ($p > 2$).
\end{theorem}
\begin{proof}
\leanok
Follows by summing the exponentially decaying neck diameters across dyadic annuli to obtain Cauchy convergence to a continuous extension at the puncture.
\end{proof}

\begin{theorem}[Removal of Singularities]
\label{a12:removal_of_singularities}
\lean{GromovCompactness.Analysis.removal_of_singularities}
\leanok
\uses{a11:puncture_extension, a05:bootstrap, f02:sphere_geometry}
Any $J$-holomorphic map $u : D_1 \setminus \{0\} \to M$ with finite energy $E(u) < \infty$ extends smoothly to a $J$-holomorphic map $\tilde{u} : D_1 \to M$.
\end{theorem}
\begin{proof}
\leanok
Follows by extending continuously across the puncture via Sobolev extension and upgrading from continuous weak solution to smooth via nonlinear elliptic bootstrap.
\end{proof}
```

---

### Block 3: Contracts B01–B02 (Lines 384–400)

Replace lines 384–400 with:

```latex
\begin{definition}[Universal Energy Threshold $h > 0$]
\label{b01:threshold_h}
\lean{GromovCompactness.Bubbling.TargetThresholds}
\leanok
\uses{a03:eps_regularity, a07:sphere_energy_gap, a10:cylinder_decay}
Fix a target geometric constant $h > 0$ satisfying:
\[
0 < h \le \min\big(\tfrac{1}{2}\varepsilon_{\mathrm{reg}}, \, \varepsilon_{\mathrm{sph}}, \, \tfrac{1}{2}\varepsilon_{\mathrm{neck}}\big).
\]
\end{definition}

\begin{theorem}[Calibrated Rescaling Centers and Radii]
\label{b02:calibration}
\lean{GromovCompactness.Bubbling.CalibratedRescaling}
\leanok
\uses{c03:defect_identity, b01:threshold_h, f02:sphere_geometry}
At each concentration point $p \in S$, there exist moving centers $a_n \to p$ and radii $\lambda_n \to 0$ satisfying the calibration condition $E(u_n; D_{\lambda_n}(a_n)) = m_p - h/2$.
\end{theorem}
\begin{proof}
\leanok
Follows from Hofer's lemma producing gradient blow-up centers and the Intermediate Value Theorem for continuous radial energy measures.
\end{proof}
```

---

## 6. Caveats

1. **Phase 3 Boundary**:
   - Items `c01:weak_measures`, `c02:concentration_data`, `c03:defect_identity` (Section 3.1) and `b03:neck_vanishing` through `b07:local_tree` (Section 3.2) belong strictly to Phase 3 (Global Tree Assembly and Compactness Engine). They must **not** receive `\leanok` during Phase 2 Milestone 6.
2. **Morrey Embedding Co-location**:
   - In `EllipticBootstrap.lean`, Contract A04 contains two declarations: `interior_cauchy_riemann_estimate` (line 431) and `morrey_sobolev_embedding` (line 444). In `content.tex`, `a04:elliptic_toolkit` specifies `\lean{GromovCompactness.Analysis.interior_cauchy_riemann_estimate}`. This is sufficient for PlasTeX linking. If desired, a separate lemma environment for Morrey embedding could be added, but keeping the current consolidated structure preserves exact graph parity.
3. **Calibrated Rescaling Alias**:
   - Both `GromovCompactness.Analysis.CalibratedRescaling` and `GromovCompactness.Bubbling.CalibratedRescaling` point to the exact same structure in Lean. The alias in `GromovCompactness.Bubbling` was specifically created to preserve the blueprint namespace path.

---

## 7. Conclusion

1. **Mapping Precision**: All 14 Phase 2 contracts (A01–A12, B01–B02) have been verified with 100% exact declaration name matching between Lean 4 and `blueprint/src/content.tex`.
2. **Actionable Blueprint Worker Plan**:
   - 14 `\leanok` tags to add (1 on `definition`, 13 on `theorem`/`lemma`).
   - 13 `\begin{proof} \leanok ... \end{proof}` blocks to add.
   - Zero syntax changes needed to `\lean{...}` or `\uses{...}`.
3. **Ready for Dispatch**: The Blueprint Worker can execute the edit plan immediately, followed by LaTeX print validation (`latexmk`) and git commit.

---

## 8. Verification Method

To independently verify the mapping and test the blueprint:
1. **Lean 4 Build Integrity**:
   ```bash
   lake build
   ```
   *Expected result*: Exit code 0, zero errors.
2. **Inspect Current Content**:
   ```bash
   grep -n -E "label\{(a|b0[12])" blueprint/src/content.tex
   ```
   *Expected result*: Exactly 14 matches for labels `a01` through `a12`, `b01`, and `b02`.
3. **Verify Print Compilation**:
   ```bash
   cd blueprint && latexmk -pdf -interaction=nonstopmode -output-directory=print src/print.tex
   ```
   *Expected result*: Clean PDF generation in `blueprint/print/print.pdf` with exit code 0.
4. **Invalidation Condition**:
   Any mismatch between declaration names, failure of `latexmk`, or premature addition of `\leanok` to Phase 3 items (`c01`–`c03`, `b03`–`b07`) invalidates the blueprint integrity.
