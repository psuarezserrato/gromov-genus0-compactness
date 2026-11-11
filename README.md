# Genus-Zero Gromov Compactness in Lean 4

A machine-checked Lean 4 / Mathlib (`v4.35.0`) formalization of **Gromov's Compactness Theorem for genus-zero $J$-holomorphic curves** in closed tame symplectic manifolds, engineered with a multi-agent workflow in Google Antigravity and verified via `leanblueprint`.

---

## Verification Summary

| Metric | Status |
| :--- | :--- |
| **Lean / Mathlib Toolchain** | `leanprover/lean4:v4.35.0` (`Mathlib v4.35.0`) |
| **Library Size** | 37 modules (`GromovCompactness.lean` + 36 submodules), **57,480 lines of Lean code** |
| **Kernel Soundness** | **`0 sorryAx`**, **0 custom axioms** across all modules |
| **Foundational Axioms** | Standard Lean 4 axioms only: `[propext, Classical.choice, Quot.sound]` |
| **Blueprint Dependency Graph** | **76 nodes — 100% Green** (63 proved `#1CAC78` theorem nodes, 13 `#B0ECA3` definition nodes, 0 unproved nodes) |
| **Tracked Blueprint Declarations** | **362 Lean declarations** in [`blueprint/lean_decls`](blueprint/lean_decls) verified via `#print axioms` |
| **Integration & Sanity Suites** | [`tests/TestNormalCharts.lean`](tests/TestNormalCharts.lean) (29 suites, 1,312 LOC) & [`tests/CertificateSanity.lean`](tests/CertificateSanity.lean) (8 non-vacuity suites, 381 LOC) |

---

## Reports & Blueprints

- **Executive Final Report (6 pages, with portrait dependency graph):** [`report/gromov_genus0_final_report.pdf`](report/gromov_genus0_final_report.pdf) ([LaTeX source](report/gromov_genus0_final_report.tex))
- **Full Technical & Workflow Report:** [`report/gromov_lean_report.pdf`](report/gromov_lean_report.pdf) ([LaTeX source](report/gromov_lean_report.tex))
- **Blueprint Print PDF:** [`blueprint/print/print.pdf`](blueprint/print/print.pdf) ([LaTeX source](blueprint/src/content.tex))
- **Blueprint Dependency Graph (Static PDF & Interactive Web):** [`report/blueprint_dep_graph.pdf`](report/blueprint_dep_graph.pdf) | [`blueprint/web/dep_graph_document.html`](blueprint/web/dep_graph_document.html)
- **Original Mathematical Specification (39 Contracts):** [`gromov_compactness.pdf`](gromov_compactness.pdf)

---

## Mathematical Overview & Master Theorem (`thm_main`)

Let $(M, \omega, J)$ be a compact, boundaryless smooth manifold equipped with a closed nondegenerate two-form $\omega$ and an $\omega$-tame almost-complex structure $J$, with associated Riemannian metric $g(v,w) = \tfrac{1}{2}(\omega(v,Jw) + \omega(w,Jv))$ and Dirichlet energy

$$E(u) = \frac{1}{2}\int_{\mathbb{CP}^1} |du|_g^2\,\mathrm{dvol}_{\mathbb{CP}^1}$$

defined using the spherical Jacobian $4/(1+|w|^2)^2$ in stereographic coordinates.

### Master Entry Points in [`GromovCompactness/Main.lean`](GromovCompactness/Main.lean)

Given a sequence $u_n : \mathbb{CP}^1 \to M$ of nonconstant $J$-holomorphic spheres with uniformly bounded energy $E(u_n) \le B$, the master theorem establishes the existence of a strictly increasing subsequence $\sigma : \mathbb{N} \to \mathbb{N}$ converging in the `CompactnessWitness` sense to a `StableSphereTreeLimit` $u_{\mathrm{lim}} = (T, \{u_v\}_{v\in V}, \{z_{vw}\})$ satisfying:

1. **Component regularity & nodal matching:** Each $u_v : \mathbb{CP}^1 \to M$ is smooth and $J$-holomorphic, and $u_v(z_{vw}) = u_w(z_{wv})$ across every edge $v \sim w$ of the finite tree $T = (V,E)$, with pairwise distinct nodal points on each component.
2. **Deligne–Mumford–Kontsevich stability:** Every ghost component ($u_v$ constant) has nodal degree $\deg_T(v) \ge 3$.
3. **Rescaled $C^\infty_{\mathrm{loc}}$ convergence & neck collapse:** Moving Möbius frames $\phi_{v,n} \in \mathrm{PSL}(2,\mathbb{C})$ satisfy $u_{\sigma(n)} \circ \phi_{v,n} \to u_v$ in $C^\infty_{\mathrm{loc}}(\mathbb{CP}^1 \setminus Z_v)$ away from incident nodes $Z_v$, and $\phi_{v,n}^{-1} \circ \phi_{w,n} \to z_{vw}$ locally uniformly on $\mathbb{CP}^1 \setminus \{z_{wv}\}$.
4. **Global energy conservation:** $\lim_{n\to\infty} E(u_{\sigma(n)}) = \sum_{v\in V} E(u_v) \le B$.
5. **Universal linear component bounds:** With $P$ principal (nonconstant) and $G$ ghost (constant) components and energy quantum $h > 0$:
   $$P \cdot h \le B, \qquad G + 2 \le P \quad\text{and}\quad |V| + 2 \le 2P \quad (|V| > 1), \qquad (|V| : \mathbb{Z}) \le \max\!\big(1, 2\lfloor B/h \rfloor - 2\big).$$

The master theorem is exposed through four primary Lean 4 declarations:
- **`gromov_compactness_genus_zero_of_rotations`** ([`Main.lean:816`](GromovCompactness/Main.lean#L816)): Master theorem from a threshold bundle `th : TargetThresholds I M`, smooth extraction off the singular set, one-level bubbling, and conformal rotations to the southern hemisphere.
- **`gromov_compactness_genus_zero_of_properties`** ([`Main.lean:843`](GromovCompactness/Main.lean#L843)): Constructs `th` internally via `TargetThresholds.of_properties` from `WeitzenbockDecompositionProperty` (`cert_weitz`), `HitExitProperty` (`cert_hit`), and `CylinderEnergyDecayProperty` (`cert_decay`).
- **`gromov_compactness_genus_zero_of_bounded_geometry_certs`** ([`Main.lean:876`](GromovCompactness/Main.lean#L876)): Discharges the analytic threshold properties on any `[BoundedChartedTarget I M]` from the canonical Taylor normal-chart family `construct_uniform_normal_chart_family I` equipped with `UniformNormalChartCertificates`.
- **`gromov_compactness_genus_zero_of_thresholds`** ([`Main.lean:69`](GromovCompactness/Main.lean#L69)): Core modular reduction combining `gromov_compactness_core_of_thresholds` with `Topology.component_count_bounds`.

---

## Unconditional Proofs vs. Geometric Normal-Chart Reductions

The formalization maintains a strict, transparent boundary between unconditional theorems proved directly from Mathlib first principles and local coordinate PDE reductions on general manifolds:

- **Unconditionally Proved Pillars:**
  - *Global combinatorics, tree grafting, and stabilization:* Depth-indexed global Möbius frames (`global_frame_recursion`), finite-set inductive root grafting (`graft_root_sphere_tree_realized`), strong induction on $|V|$ pruning degree-1 and suppressing degree-2 ghost roots (`stabilize_prestable_tree`), and universal component counting bounds (`component_count_bounds`).
  - *Measure theory and flat elliptic analysis:* Finiteness of extended energy for every $C^1$ sphere (`energyMeasureExtended_lt_top_of_contMDiff`), Prokhorov weak sequential compactness on $\mathbb{CP}^1$ via Mathlib's Riesz–Markov–Kakutani representation (`RealRMK.rieszMeasure`) and Portmanteau theorem, the flat scalar mean-value inequality, 2D Morrey–Sobolev embedding, and the Cauchy–Pompeiu integral Hölder gain.
  - *Normal-chart infrastructure and concrete regimes:* Finite good coordinate atlases with positive Lebesgue radius (`exists_finiteGoodAtlas`), `mfderiv` factorization through fixed charts (`tangentCoordChange`), quadratic Taylor centered normal charts with Koszul Christoffel cancellation at the origin, unconditional instantiation on $(\mathbb{CP}^1, \omega_{\mathrm{FS}}, J_{\mathrm{std}})$ (`concrete_CP1`), and unconditional genus-zero Gromov compactness in sub-threshold ($B < \varepsilon_{\mathrm{sph}}$), symplectically aspherical, and discrete target regimes.
  - *All five extension tracks (E01–E05):* Smooth $\mathrm{GL}(2,\mathbb{C})$ Möbius lifting (`MoebiusFrame.ofMatrix`), 3-point homeomorphism rigidity (`moebiusFrame_three_point_rigidity`) and 3-point transitivity (`exists_moebiusFrame_three_points`), finite effective automorphisms and Kontsevich stability equivalence, varying-$J$ compactness ($J_n \to J$), $k$-marked curve extraction, and sequential metrizability / compact Hausdorff equivalence $\overline{\mathcal M}_{0,3}(M,J,\le B) \cong M$ for $0 \le B < \varepsilon_{\mathrm{sph}}$.
- **First-Principles Analytical Reductions in Normal Charts:**
  - On a general compact tame manifold $(M,\omega,J)$, the local analytic properties (`cert_weitz`, `cert_decay`, `cert_osc`, `cert_punc`, `cert_tower`, `cert_hit`, `cert_aa`) and sequence-relative bubbling/extraction contracts (`cert_onelevel`, `cert_conc`, `cert_concdefect`, `cert_thresholds`) are proved as theorems reducing the global geometric statements to centered normal-chart remainder/slice bounds (`UniformNormalChartCertificates`) and conformal rotations (`h_rot`).

---

## Repository Structure

```text
SympTopAutoForm/
├── GromovCompactness.lean               # Root umbrella import module
├── GromovCompactness/
│   ├── Geometry/                        # Target manifolds (F01), CP1 & Möbius group (F02), NormalCharts (N1–N3)
│   ├── Analysis/                        # Energy (F03), Bochner/Weitzenböck, Hofer ε-regularity, Decay,
│   │                                    # Monotonicity, EnergyGap, EllipticBootstrap, SingularityRemoval (A01–A12)
│   ├── Topology/                        # SmoothLocal C^∞_loc (F04), Subsequence (F05), SphereTree &
│   │                                    # ComponentCount (F06, G04)
│   ├── Bubbling/                        # Hofer calibrated rescaling, Neck, OneLevel, LocalTree (B01–B07)
│   ├── Compactness/                     # Measures, Concentration, Defect (C01–C03), Assembly, Stabilize,
│   │                                    # GenusZero (G01–G03)
│   ├── Extensions/                      # VaryingJ (E01), MarkedCurves (E02), HomologyClass (E03),
│   │                                    # Automorphisms (E04), ModuliSpace (E05)
│   └── Main.lean                        # Master Genus-Zero Gromov Compactness theorems (G05 / thm_main)
├── blueprint/
│   ├── src/content.tex                  # 76-node leanblueprint DAG specification
│   ├── dep_graph.dot                    # Exported Graphviz dependency graph
│   ├── lean_decls                       # 362 verified Lean declarations linked from the blueprint
│   └── print/print.pdf                  # Compiled blueprint PDF
├── report/
│   ├── gromov_genus0_final_report.pdf   # Short executive report (5 pages + portrait dependency graph)
│   ├── gromov_lean_report.pdf           # Detailed technical report
│   └── blueprint_dep_graph.pdf          # Rendered full dependency graph
└── tests/
    ├── TestNormalCharts.lean            # 29 end-to-end integration and axiom verification suites
    └── CertificateSanity.lean           # 8 semantic non-vacuity and hypothesis satisfiability checks
```

---

## Building and Verifying

### 1. Build the Lean 4 Library
Requires [`elan`](https://github.com/leanprover/elan) (which automatically selects `leanprover/lean4:v4.35.0` from [`lean-toolchain`](lean-toolchain)):

```bash
lake build
```

### 2. Run the Verification & Sanity Test Suites

```bash
lake env lean tests/TestNormalCharts.lean
lake env lean tests/CertificateSanity.lean
```

### 3. Rebuild Blueprint Web Graph & PDFs (Optional)
With the `leanblueprint` environment (`graphviz`, `pygraphviz`, `leanblueprint`, and `pdflatex`):

```bash
./blueprint/export_dep_graph.sh
(cd blueprint/src && pdflatex -interaction=nonstopmode -output-directory=../print print.tex && pdflatex -interaction=nonstopmode -output-directory=../print print.tex)
(cd report && pdflatex -interaction=nonstopmode gromov_genus0_final_report.tex && pdflatex -interaction=nonstopmode gromov_genus0_final_report.tex)
```

---

## License & Citation

Licensed under the **GNU Affero General Public License v3.0 (AGPLv3)** for non-commercial use — see [`LICENSE.md`](LICENSE.md) for details:

> This project is licensed under non-commercial use. If you wish to use this software in a commercial product, service, or enterprise environment, please contact the developer to purchase a commercial license or negotiate royalty terms.

Authored by **Pablo Suárez-Serrato** (November 2026).
