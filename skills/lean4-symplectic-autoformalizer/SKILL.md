---
name: lean4-symplectic-autoformalizer
description: >-
  Translates informal mathematical definitions, theorems, and proofs from
  Gromov (1985), Ivashkovich-Shevchishin (1999), and gromov_compactness.pdf
  into syntactically valid Lean 4 types, structures, and proof skeletons.
  Aligns prerequisites with Mathlib (e.g. Mathlib.Analysis.Hofer) and the
  TauCeti Symplectic Geometry Roadmap.
---

# Lean 4 Symplectic Autoformalizer

## Overview

The `lean4-symplectic-autoformalizer` skill automates the translation of informal mathematical literature in symplectic topology and pseudo-holomorphic curve theory into formal Lean 4 declarations, inductive types, structures, and proof skeletons.

It specifically operationalizes the mathematics of:
1. **Mikhail Gromov (1985)**: *"Pseudo holomorphic curves in symplectic manifolds"*, *Inventiones Mathematicae* 82, 307–347. Covers almost complex structures, $\omega$-taming, $J$-holomorphic curves, energy functionals, and bubbling-off.
2. **Sergey Ivashkovich & Viatcheslav Shevchishin (1999)**: *"Complex Curves in Almost-Complex Manifolds and Meromorphic Hulls"*, arXiv:math/9912046. Covers bubbling-off, area bounds, tree-like connectedness for genus 0, and cusp-curve convergence.
3. **Gromov Compactness Blueprint (`gromov_compactness.pdf`)**: 32 formalization contracts across Foundations (F00–F06), Local Analysis (A01–A12), Concentration & Defect (C01–C03), Bubbling & Induction (B01–B07), Global Assembly & Stabilization (G01–G05), and Extensions (E01–E05), plus 8 mathematical stress cases.
4. **Mathlib 4 Infrastructure**: Direct alignment with `Mathlib.Analysis.Hofer` (Patrick Massot's gradient blow-up rescaling lemma), `Mathlib.Geometry.Manifold.SmoothManifoldWithCorners`, and metric spaces.
5. **TauCeti Roadmap**: Aligns with `TauCetiRoadmap/SymplecticGeometry` and moduli space specifications.

---

## Triggers & Invocation Criteria

### Trigger When:
- Translating informal symplectic definitions, lemmas, or theorems into Lean 4 code.
- Constructing formal type signatures for almost complex structures, symplectic forms, $\bar{\partial}_J$ equations, and bubble trees.
- Generating structured proof skeletons (`by sorry`) with intermediate proof milestones and step-by-step comments.
- Mapping informal analytic steps (e.g. Hofer's lemma, energy gap, neck decay, ghost branching) to Mathlib declarations.

### Do Not Trigger When:
- Searching for interactive tactics on an existing open goal (use `ollama-lean4-gemma-prover`).
- Repairing syntax or type errors in broken `.lean` code (use `lean4-proof-repair-engine`).
- Managing external project configuration or git repositories.

---

## Dependencies & Environmental Requirements

- **Python 3.6+** (Standard library: `argparse`, `json`, `re`, `pathlib`, `sys`).
- **Mathlib 4**: Modules `Mathlib.Analysis.Hofer`, `Mathlib.Geometry.Manifold.SmoothManifoldWithCorners`, `Mathlib.Topology.MetricSpace.Basic`.
- **References**:
  - `references/gromov_1985_core_lemmas.md`
  - `references/ivashkovich_shevchishin_bubble_tree.md`
  - `references/gromov_compactness_pdf_contracts.md`
  - `references/mathlib_hofer_mapping.md`
  - `references/lean4_symplectic_prelude.lean`

---

## Quick Start

### 1. Extract Mathematical Symbols & Hypotheses
Extract variables, hypotheses, and assertions from informal mathematical text:
```bash
python3 skills/lean4-symplectic-autoformalizer/scripts/autoformalize.py extract-symbols \
  --input skills/lean4-symplectic-autoformalizer/examples/gromov_compactness_sample_input.md \
  --output /tmp/extracted_symbols.json
```

### 2. Autoformalize into a Lean 4 Skeleton
Generate a complete, syntactically valid Lean 4 file with structured proof stubs:
```bash
python3 skills/lean4-symplectic-autoformalizer/scripts/autoformalize.py translate \
  --input skills/lean4-symplectic-autoformalizer/examples/gromov_compactness_sample_input.md \
  --output /tmp/GromovCompactnessGenerated.lean \
  --target-module SympTopAutoForm.GromovCompactness \
  --proof-level skeleton
```

### 3. Verify Alignment with Mathlib
Check that generated types correctly align with Mathlib 4:
```bash
python3 skills/lean4-symplectic-autoformalizer/scripts/autoformalize.py align-mathlib \
  --concept "hofer_gradient_rescaling" \
  --output /tmp/mathlib_alignment.json
```

---

## Operational Workflows

### Workflow 1: Translating Informal Symplectic Definitions to Lean 4

When formalizing geometry from Gromov (1985) §0.2 or `gromov_compactness.pdf` F01:
1. **Target Manifold Definition**:
   Define a compact, boundaryless, finite-dimensional smooth manifold $M$:
   ```lean
   variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
   variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
   variable (M : Type*) [MetricSpace M] [CompactSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
   ```
2. **Symplectic Form & Taming**:
   Define closed non-degenerate 2-form $\omega$ and almost complex endomorphism $J: TM \to TM$:
   ```lean
   structure AlmostComplexStructure where
     J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x
     J_sq : ∀ (x : M) (v : TangentSpace I x), J x (J x v) = -v

   def IsTamed (J : AlmostComplexStructure I M) (ω : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) : Prop :=
     ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < ω x v (J.J x v)
   ```
3. **Riemannian Metric Symmetrization**:
   Following `gromov_compactness.pdf` §2.1, do NOT assert that $\omega(v, Jw)$ is symmetric under taming. Instead use the explicit symmetrization:
   $$g(v, w) = \frac{1}{2}(\omega(v, Jw) + \omega(w, Jv))$$

### Workflow 2: Mapping Gradient Rescaling to `Mathlib.Analysis.Hofer`

When formalizing bubbling-off at points of gradient blow-up:
1. **Mathematical Precondition**:
   Let $u_n : S^2 \to M$ be a sequence with $E(u_n) \le B$ and $\sup |du_n| \to \infty$.
2. **Direct Application of Hofer's Lemma**:
   `Mathlib.Analysis.Hofer` provides:
   ```lean
   theorem hofer [MetricSpace X] [CompleteSpace X] (f : X → ℝ) (x : X) (ε : ℝ)
       (hε : 0 < ε) (hf : Continuous f) (hfx : 0 ≤ f x) :
       ∃ x' ε', 0 < ε' ∧ ε' ≤ ε ∧ f x ≤ f x' ∧ ∀ y, dist y x' ≤ ε' → f y ≤ 2 * f x'
   ```
3. **Rescaling Transformation**:
   Define affine coordinate dilation $z \mapsto a_n + \lambda_n z$ with $\lambda_n = (f(x_n'))^{-1} \to 0$.
   The rescaled curve $v_n(z) = u_n(a_n + \lambda_n z)$ satisfies $|dv_n(0)| = 1$ and $|dv_n(z)| \le 2$ on $B(0, \varepsilon_n' / \lambda_n)$.

### Workflow 3: Bubble Tree & Moduli Convergence Formalization

Following `gromov_compactness.pdf` §2.2–§2.3 and Ivashkovich-Shevchishin (1999):
1. **Labelled Sphere Tree Structure**:
   - Vertices $V = \mathrm{Fin}(N+1)$ with root vertex 0.
   - Directed edge relation $E_T \subset V \times V$ forming an acyclic tree.
   - Incident node positions $z_{vw} \in \mathbb{CP}^1$ pairwise distinct for each $v$.
   - Node matching condition: $u_v(z_{vw}) = u_w(z_{wv})$.
2. **Stability Criterion**:
   - Every constant component $v$ has $\mathrm{deg}(v) \ge 3$ (or $\mathrm{deg}(v) + k_v \ge 3$ with markings).
   - Component bounds: $G \le P - 2$ constant ghosts for $P$ nonconstant components; $|V| \le 2P - 2$.
3. **Convergence Witness**:
   - Strictly increasing subsequence $\sigma : \mathbb{N} \to \mathbb{N}$.
   - Möbius frame sequence $\phi_{v,n} : \mathbb{CP}^1 \to \mathbb{CP}^1$.
   - $C^\infty_{loc}$ convergence $u_{\sigma(n)} \circ \phi_{v,n} \to u_v$ on $\mathbb{CP}^1 \setminus Z_v$.
   - Vanishing neck energy and diameter on all connecting annuli.

### Workflow 4: The 'Sorry'-First-Pass Strategy for Unblocking Downstream Progress

Following explicit user instructions (2026-11-03):
When autoformalizing an advanced mathematical theory (like Gromov compactness), deep analytic prerequisites (such as non-linear $W^{1,p}$ elliptic bootstrapping, Morrey embeddings for general $p > 2$, or isoperimetric inequalities for non-integrable almost complex targets) may not yet exist as verified theorems in Mathlib or TauCeti:
1. **Never stall downstream progress**:
   Do not halt the formalization pipeline waiting for deep PDE foundational libraries.
2. **Synthesize rigorous candidate declarations**:
   Formalize the missing prerequisite as an explicit Lean 4 `theorem` or `lemma` signature with complete type signatures, hypotheses, and docstrings.
3. **Stub with structured `sorry` bodies**:
   Equip the lemma with `:= by sorry` or intermediate `have` statements punctuated by `sorry`:
   ```lean
   /-- Candidate lemma for non-linear elliptic bootstrap (Contract A05).
       Prerequisite not currently complete in Mathlib 4; stubbed with sorry
       on first pass to unblock downstream compactness assembly. -/
   theorem nonlinear_elliptic_bootstrap
       (u : Sphere2 → M) (h_weak : IsWeakJHolomorphic J u) :
       ContMDiff 𝓘(ℝ, 2) I ⊤ u := by
     sorry
   ```
4. **Enable verified downstream composition**:
   Downstream theorems (e.g. `gromov_compactness_genus_zero`, tree assembly, component counting) can immediately `apply` or `exact` these candidate lemmas, allowing kernel checking of the global combinatorial, topological, and geometric argument structure.
5. **Auditing and Axiom Tracking**:
   The Lean compiler and `#print axioms` will transparently track `sorryAx` on these unproved nodes, guaranteeing that no false or admitted axioms are silently introduced into the trusted kernel.

---

## Utility Script: `scripts/autoformalize.py`

The helper script provides four subcommands:

| Subcommand | Description | Arguments |
|------------|-------------|-----------|
| `translate` | Autoformalizes informal text into Lean 4 source | `--input <file>`, `--output <file>`, `--target-module <name>`, `--proof-level <skeleton\|statement>` |
| `extract-symbols` | Extracts mathematical symbols and relations to JSON | `--input <file>`, `--output <file>` |
| `align-mathlib` | Queries Mathlib alignment for a concept or identifier | `--concept <name>`, `--output <file>` |
| `test` | Runs internal test suite validating all subcommands | `--output <file>` (optional) |

### CLI Example:
```bash
python3 skills/lean4-symplectic-autoformalizer/scripts/autoformalize.py test
```

---

## Common Mistakes & Edge Cases

1. **Boundary Failure of Hofer's Lemma**:
   - *Mistake*: Applying Hofer's lemma on an open domain $D^2$ without tracking distance to the boundary $\partial D^2$.
   - *Fix*: Rescale with balls of radius $\varepsilon_n \le \frac{1}{2} d(x_n, \partial D)$, ensuring the rescaled balls remain interior.
2. **Ghost Bubbles with Zero Energy**:
   - *Mistake*: Assuming every bubble component has positive symplectic energy.
   - *Fix*: Constant components ("ghosts") have $E(v) = 0$ but carry topological branching ($\ge 2$ child nodes). Account for them in the stability bound $G \le P - 2$.
3. **Non-Integrable $J$ Local Charts**:
   - *Mistake*: Assuming holomorphic local coordinates exist for $(M, J)$.
   - *Fix*: $J$ is merely an almost complex structure; use real smooth charts with the Cauchy-Riemann differential operator $du \circ j = J \circ du$.
4. **Neck Annulus Energy Leaks**:
   - *Mistake*: Concluding energy conservation purely from Fatou's lemma without proving neck energy vanishes.
   - *Fix*: Apply cylinder decay (Contract B03) to prove $\lim_{R \to \infty} \lim_{n \to \infty} E(u_n; A(R\lambda_n, \delta)) = 0$.
