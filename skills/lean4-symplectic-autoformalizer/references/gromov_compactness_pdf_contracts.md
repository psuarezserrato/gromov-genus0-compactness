# Mathematical Specification: gromov_compactness.pdf Formalization Contracts

**Source Document:** `gromov_compactness.pdf` — *"Genus-zero Gromov compactness: A proof blueprint for Lean formalization"*, November 3, 2026.

---

## 1. Scope and Strategy

The document establishes sequential Gromov compactness for genus 0 pseudo-holomorphic curves in a closed tame target manifold $(M, \omega, J)$.

### Four Architectural Layers:
1. **Foundations & Bookkeeping Layer (F00–F06)**
2. **Local Analytic Estimates Layer (A01–A12)**
3. **Concentration & Bubbling Layer (C01–C03, B01–B07)**
4. **Global Assembly & Stabilization Layer (G01–G05)**
5. **Extensions Track (E01–E05)**

### The 'Sorry'-First-Pass Strategy:
Per user specification (2026-11-03), any missing foundational prerequisite (e.g. general Sobolev Morrey embedding $p > 2$ or nonlinear bootstrap) is declared with an exact formal type signature and a structured `sorry` proof stub, allowing downstream global combinatorial and topological proof closures to compile and verify without delay.

---

## 2. Exhaustive Index of 32 Formalization Contracts

### Foundations & Bookkeeping Track
- **F00: Pin the project and audit the library**
  - *Dependencies:* None.
  - *File:* `GromovCompactness/LibraryAudit.lean`
  - *Output:* Audit smooth forms, Stokes, metrics/distance, sphere charts, finite measures, Arzelà-Ascoli, Sobolev/Morrey, finite trees.
- **F01: Target geometry and the equation**
  - *Dependencies:* F00.
  - *File:* `GromovCompactness/Geometry/Target.lean`
  - *Output:* `ClosedTameTarget`, `JHolomorphicOn`, symmetrized metric $g(v, w) = \frac{1}{2}(\omega(v, Jw) + \omega(w, Jv))$, finite charts.
- **F02: Sphere and conformal reparametrizations**
  - *Dependencies:* F00.
  - *File:* `GromovCompactness/Geometry/Sphere.lean`
  - *Output:* Compact Riemann sphere $\mathbb{CP}^1$, affine maps $z \mapsto a + \lambda z$, inversion $z \mapsto 1/z$, Möbius automorphisms.
- **F03: Energy measure and its algebra**
  - *Dependencies:* F01, F02, F04.
  - *File:* `GromovCompactness/Analysis/Energy.lean`
  - *Output:* Nonnegative Borel energy measure, finite real energy API, additivity, conformal invariance, zero energy iff constant.
- **F04: Smooth local convergence on varying domains**
  - *Dependencies:* F01, F02.
  - *File:* `GromovCompactness/Topology/SmoothLocal.lean`
  - *Output:* `SmoothLocalConvergesOn`, chartwise uniform convergence of every derivative on compact exhaustion, moving-point evaluation.
- **F05: Subsequence and diagonal bookkeeping**
  - *Dependencies:* F00.
  - *File:* `GromovCompactness/Topology/Subsequence.lean`
  - *Output:* Strictly increasing index map type, diagonal extraction for countable families, composition and refinement lemmas.
- **F06: Labelled trees and convergence data**
  - *Dependencies:* F01, F02, F03, F04, F05.
  - *File:* `GromovCompactness/Topology/SphereTree.lean`
  - *Output:* Rooted tree $T = (V, E)$, node positions $z_{vw}$, node matching $u_v(z_{vw}) = u_w(z_{wv})$, convergence witness predicate.

### Local Analytic Estimates Track
- **A01: Scalar mean-value inequality**
  - *Dependencies:* F00.
  - *File:* `GromovCompactness/Analysis/MeanValue.lean`
  - *Contract:* For $\Delta e \ge -b e^2$, $\int_{D_r} e < \eta \implies \sup_{D_{r/2}} e \le C r^{-2} \int_{D_r} e$.
- **A02: Energy-density differential inequality**
  - *Dependencies:* F01, F03.
  - *File:* `GromovCompactness/Analysis/Bochner.lean`
  - *Contract:* Covariant Bochner identity for Euclidean-domain density $e = |du|^2/2$ satisfying $\Delta e \ge -b e^2$.
- **A03: Epsilon regularity**
  - *Dependencies:* A01, A02.
  - *File:* `GromovCompactness/Analysis/EpsilonRegularity.lean`
  - *Contract:* Gradient bound $\sup_{D_{r/2}} |du|^2 \le C r^{-2} E(u; D_r)$ under $E(u; D_r) < \varepsilon_{reg}$.
- **A04: Euclidean elliptic and Sobolev toolkit**
  - *Dependencies:* F00.
  - *File:* `GromovCompactness/Analysis/EllipticToolkit.lean`
  - *Contract:* Interior estimate for $D = \partial_s + J_0 \partial_t$, Morrey embedding $p > 2$, Arzelà-Ascoli.
- **A05: Nonlinear elliptic bootstrap**
  - *Dependencies:* A04, F01, F04.
  - *File:* `GromovCompactness/Analysis/Bootstrap.lean`
  - *Contract:* Continuous $W^{1,p}_{loc}$ weak solution ($p > 2$) is smooth with derivative bounds on smaller disks.
- **A06: Compactness under local gradient bounds**
  - *Dependencies:* A05, F04, F05.
  - *File:* `GromovCompactness/Analysis/LocalCompactness.lean`
  - *Contract:* Sequence of curves with uniform gradient bounds has a subsequence converging in $C^\infty_{loc}$.
- **A07: Positive energy of a nonconstant sphere**
  - *Dependencies:* A03, F01, F02, F03.
  - *File:* `GromovCompactness/Analysis/EnergyGap.lean`
  - *Contract:* Minimal energy quantum $\varepsilon_{sph} > 0$ such that non-constant $u: \mathbb{CP}^1 \to M$ has $E(u) \ge \varepsilon_{sph}$.
- **A08: Target monotonicity**
  - *Dependencies:* F01, F03, A04.
  - *File:* `GromovCompactness/Analysis/Monotonicity.lean`
  - *Contract:* Area lower bound $E(u; u^{-1}(B_r(x))) \ge c r^2$ for $x \in u(\mathrm{int} \Sigma)$.
- **A09: Localization of a small-energy cylinder**
  - *Dependencies:* A03, A08.
  - *File:* `GromovCompactness/Analysis/CylinderLocalization.lean`
  - *Contract:* $E(v) < \eta(d_0) \implies \mathrm{diam}\, v([-L+1, L-1] \times S^1) < d_0$.
- **A10: Energy and diameter decay on long cylinders**
  - *Dependencies:* A09, A03, F03.
  - *File:* `GromovCompactness/Analysis/CylinderDecay.lean`
  - *Contract:* Exponential decay $E(v; \mathrm{trimmed}) \le C_0 e^{-aT} E(v)$ and $\mathrm{diam} \le C_0 e^{-aT/2} \sqrt{E(v)}$.
- **A11: Continuous and Sobolev extension at a puncture**
  - *Dependencies:* A09, A10, A03, F03.
  - *File:* `GromovCompactness/Analysis/PunctureExtension.lean`
  - *Contract:* Finite-energy curve on $D_1 \setminus \{0\}$ extends continuously and in $W^{1,p}$.
- **A12: Removal of singularities**
  - *Dependencies:* A11, A05, F02.
  - *File:* `GromovCompactness/Analysis/Removal.lean`
  - *Contract:* Extension is smooth and $J$-holomorphic with preserved energy; extends finite-energy curves on $\mathbb{C}$ to $\mathbb{CP}^1$.

### Concentration & Bubbling Track
- **C01: Weak compactness of energy measures**
  - *Dependencies:* F03, F05.
  - *File:* `GromovCompactness/Compactness/Measures.lean`
  - *Contract:* Prokhorov weak convergence of bounded Radon measures on compact space.
- **C02: Finite concentration and smooth convergence**
  - *Dependencies:* C01, A03, A06, A12.
  - *File:* `GromovCompactness/Compactness/Concentration.lean`
  - *Contract:* Extract finite singular set $S = \{p : \mu(\{p\}) \ge \varepsilon_{reg}\}$ with $|S| \le B/\varepsilon_{reg}$ and $C^\infty_{loc}$ convergence on $\mathbb{CP}^1 \setminus S$.
- **C03: Defect identity and moving centers**
  - *Dependencies:* C02, F03.
  - *File:* `GromovCompactness/Compactness/Defect.lean`
  - *Contract:* Defect measure identity $\mu = \mu_{u_0} + \sum_{p \in S} m_p \delta_p$ and $\lim E(u_n) = E(u_0) + \sum m_p$.
- **B01: Choose a common positive threshold**
  - *Dependencies:* A03, A07, A10.
  - *File:* `GromovCompactness/Bubbling/Threshold.lean`
  - *Contract:* Fixed universal threshold $0 < h \le \min(\varepsilon_{reg}/2, \varepsilon_{sph}, \varepsilon_{neck}/2)$.
- **B02: Center and calibrate a rescaling**
  - *Dependencies:* C03, B01, F02.
  - *File:* `GromovCompactness/Bubbling/Calibration.lean`
  - *Contract:* Choose $a_n \in D_{1/2}$ maximizing gradient and $\lambda_n > 0$ such that $E(f_n; D_{\lambda_n}(a_n)) = m - h/2$.
- **B03: Neck energy and diameter with explicit quantifiers**
  - *Dependencies:* B02, A10, C03.
  - *File:* `GromovCompactness/Bubbling/Neck.lean`
  - *Contract:* Quantified vanishing of neck annulus energy and image diameter as $R \to \infty$.
- **B04: One-level mass decomposition and node matching**
  - *Dependencies:* B03, C02, C03, A12.
  - *File:* `GromovCompactness/Bubbling/OneLevel.lean`
  - *Contract:* Rescaled map $v_n \to v$, $m = E(v) + \sum_{i=1}^k m_i$, and $f(0) = v(\infty)$.
- **B05: A constant rescaled component has two children**
  - *Dependencies:* B04, B02.
  - *File:* `GromovCompactness/Bubbling/GhostBranching.lean`
  - *Contract:* If $v$ is constant, maximizing center forces an atom at 0 with mass $\le m - h/2$, forcing $k \ge 2$ children and degree $\ge 3$ (including parent node $\infty$).
- **B06: Energy rank strictly decreases**
  - *Dependencies:* B04, B05, B01.
  - *File:* `GromovCompactness/Bubbling/Rank.lean`
  - *Contract:* For each child, $m_i \le m - h \implies \lfloor m_i / h \rfloor < \lfloor m / h \rfloor$.
- **B07: Resolve one defect into a finite rooted tree**
  - *Dependencies:* B06, F06, F05.
  - *File:* `GromovCompactness/Bubbling/LocalTree.lean`
  - *Contract:* Well-founded induction on $\lfloor m / h \rfloor$ to resolve single defect into finite rooted tree.

### Global Assembly & Stabilization Track
- **G01: Assemble global frames and the prestable limit**
  - *Dependencies:* B07, C03, F02, F06.
  - *File:* `GromovCompactness/Compactness/Assembly.lean`
  - *Contract:* Global prestable tree assembly, global Möbius frames, neighboring frame collapse.
- **G02: Stabilize without weakening convergence**
  - *Dependencies:* G01, C02, F06.
  - *File:* `GromovCompactness/Compactness/Stabilize.lean`
  - *Contract:* Prune degree 1 constant root or suppress degree 2 constant root without losing energy identity.
- **G03: Core theorem and constant alternative**
  - *Dependencies:* G02, A07.
  - *File:* `GromovCompactness/Compactness/GenusZero.lean`
  - *Contract:* Theorem 1: Subsequence convergence to stable sphere tree with $|V| \le 2P - 2$.
- **G04: Component counts**
  - *Dependencies:* F06, B01.
  - *File:* `GromovCompactness/Topology/ComponentCount.lean`
  - *Contract:* Ghost count $G \le P - 2$, $|V| \le \max(1, 2\lfloor B/h \rfloor - 2)$ (or $+ k$ for marked curves).
- **G05: Final core integration and audit**
  - *Dependencies:* G03, G04.
  - *File:* `GromovCompactness/Main.lean`
  - *Contract:* Export complete verified theorem with dependency audit and `#print axioms` validation.

### Extensions Track
- **E01: Integral homology class is preserved** ($[u_{\sigma(n)}] = \sum [u_v]$ in $H_2(M; \mathbb{Z})$).
- **E02: Component stability equals finite automorphisms**.
- **E03: Fixed marked smooth-sphere sequences**.
- **E04: Already nodal stable genus-zero inputs**.
- **E05: Topological compactness of the moduli space**.

---

## 3. The 8 Mathematical Stress Cases

1. **Unrestricted Non-Compact Target ($M = \mathbb{C}$):** Constant maps escaping to infinity demonstrate that target compactness is essential even with energy 0.
2. **Domain Dilation ($u_n(z) = nz$):** Convergence on original domain loses a non-constant component; demonstrates necessity of moving Möbius frames.
3. **Ghost Trees from Multiple Concentration Clusters:** A constant base with several clusters requires ghost components with $E = 0$.
4. **Multiple Covers:** Maps with non-trivial branch points or covering degrees must be admitted; no injectivity assumptions permitted.
5. **Concentration Point on Calibration Circle ($|z| = 1$):** Radial energy continuity holds without assuming $|z|=1$ is a continuity set.
6. **Inequality Margin Consistency:** Strict vs non-strict inequalities at thresholds must preserve margin $h \le \min(\varepsilon_{reg}/2, \varepsilon_{sph}, \varepsilon_{neck}/2)$.
7. **Colliding Domain Labels:** Marked constant sequence requires domain reparametrization even without bubbling.
8. **Varying Homology Classes:** Sequences of curves need not share the same homology class $[u_n]$; fixed energy bound is sufficient.
