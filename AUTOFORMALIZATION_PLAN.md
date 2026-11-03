# Autoformalization Plan: Genus-Zero Gromov Compactness in Lean 4

**Strategic Implementation Roadmap, Agent Coordination, and Local Gemma/Ollama Proving Pipeline**  
**Document Status**: Official Implementation Plan  
**Date**: November 2026  
**Target Toolchain**: Lean 4 / Mathlib4 / Lake / Ollama Local Prover  
**Companion Blueprint**: `GROMOV_COMPACTNESS_BLUEPRINT.md`  

---

## 1. Executive Strategy & Autoformalization Objectives

### 1.1 The Mission
The objective of this plan is to execute the end-to-end autoformalization of **Gromov Compactness for Genus 0 Pseudo-Holomorphic Curves** ($J$-holomorphic spheres) in **Lean 4**, strictly fulfilling the 39 formal contracts (F00–F06, A01–A12, C01–C03, B01–B07, G01–G05, E01–E05) specified in `GROMOV_COMPACTNESS_BLUEPRINT.md` and `gromov_compactness.pdf`.

To maximize engineering efficiency while strictly conserving compute and maintaining uncompromising mathematical integrity:
1. **Modular Contract Gating**: The proof is partitioned into 39 decoupled task contracts with explicit Lean 4 type signatures. Each contract is developed, verified, and audited in isolation before integration.
2. **Local Proving Pipeline via Ollama & Gemma**: Repetitive lemma translation, tactic search, premise selection, and compiler error repair are delegated to a local **Gemma** model running via **Ollama** (`http://localhost:11434`), requiring zero external API compute.
3. **'Sorry'-First-Pass Strategy**: As a first pass, if a needed prerequisite result or auxiliary lemma is not readily found in Mathlib or TauCeti, its formal declaration and candidate type signature are established precisely, and the proof is left with `sorry`. Downstream proofs and declarations proceed immediately using the results and interfaces that are available, completely avoiding pipeline blocking.
4. **Staged Integrity & Final Axiom Gating**: While `sorry` stubs are permitted during Pass 1 to unblock downstream progress, Phase 4 completion Gate `G05` enforces systematic `sorry` elimination across the dependency closure, certifying the completed proof via `#print axioms` (admitting only `propext`, `Quot.sound`, `Classical.choice`).

---

## 2. Six-Phase Implementation Roadmap

The project is structured into six sequential phases with strict completion gates:

```
=============================================================================================
Phase 0: Environment Setup, Toolchain Pinning, and Library Audit
         [F00] Lake configuration, Mathlib4 pin, symbol audit
=============================================================================================
                                     │
                                     ▼
=============================================================================================
Phase 1: Foundations, Target Geometry, and Sphere Trees
         [F01] ClosedTameTarget & CR operator
         [F02] CP^1 & Möbius frame group
         [F03] Symplectic energy measure & algebra
         [F04] C^∞_loc convergence on exhausting domains
         [F05] Strictly increasing subsequences & diagonal extraction
         [F06] Labelled sphere tree data & topological stability
=============================================================================================
                                     │
                                     ▼
=============================================================================================
Phase 2: Local Analytic Estimates & Regularity Engine
         [A01] Scalar mean-value inequality
         [A02] Bochner energy-density inequality (Δe ≥ -be²)
         [A03] Epsilon regularity (via Mathlib.Analysis.Hofer.hofer)
         [A04] Euclidean elliptic & Sobolev toolkit (W^{k+1, p} estimates)
         [A05] Nonlinear elliptic bootstrap (W^{1, p}_loc → C^∞)
         [A06] Local C^∞ compactness under gradient bounds (Arzelà-Ascoli)
         [A07] Non-constant sphere energy gap (ε_sph > 0 via Stokes)
         [A08] Target monotonicity (E(u⁻¹(B_r)) ≥ c r²)
         [A09] Small-energy cylinder localization into a chart
         [A10] Long cylinder exponential energy & diameter decay
         [A11] Continuous & Sobolev extension at a puncture
         [A12] Smooth removal of singularities
=============================================================================================
                                     │
                                     ▼
=============================================================================================
Phase 3: Concentration Compactness & Single Bubble Resolution
         [C01] Weak compactness of energy measures
         [C02] Finite concentration set S & smooth convergence off S
         [C03] Defect measure identity & moving centers
         [B01] Universal positive threshold h ≤ min(ε_reg/2, ε_sph, ε_neck/2)
         [B02] Center and calibrate rescaling (a_n, λ_n with E(D_{λ_n}) = m - h/2)
         [B03] Vanishing neck energy and diameter (explicit quantifiers)
         [B04] One-level mass decomposition & node matching (f(0) = v(∞))
         [B05] Ghost branching: constant components have ≥ 2 child bubbles
=============================================================================================
                                     │
                                     ▼
=============================================================================================
Phase 4: Inductive Tree Resolution, Global Assembly, and Core Theorem
         [B06] Energy rank strict decrease: ⌊m_i / h⌋ < ⌊m / h⌋
         [B07] Resolve single defect into finite rooted tree (well-founded induction)
         [G01] Global Möbius frame assembly & prestable limit
         [G02] Root stabilization (pruning degree 1 / suppressing degree 2 constant roots)
         [G03] Master Genus 0 Compactness Theorem (Theorem 1 Core)
         [G04] Numerical component bounds (G ≤ P - 2, |V| ≤ 2P - 2)
         [G05] Core integration gate & full axiom audit (#print axioms)
=============================================================================================
                                     │
                                     ▼
=============================================================================================
Phase 5: Global Extensions & Moduli Space Topology
         [E01] Integral homology class preservation ([u_n] = ∑ [u_v] in H_2(M; ℤ))
         [E02] Stability ↔ finiteness of automorphism group
         [E03] Marked sphere sequences & ratio-of-differences normalization
         [E04] Already-nodal stable genus-0 inputs
         [E05] Compact Hausdorff topology of the moduli space M̄_{0, k}(M, A; J)
=============================================================================================
```

---

## 3. Agent Task Force Roles & Operational Architecture

The autoformalization workflow operates via a specialized multi-agent architecture:

| Agent Role | Primary Responsibilities | Key Inputs | Outputs / Artifacts |
|---|---|---|---|
| **Spec Miner** | Extracts informal mathematical structures from Gromov (1985), Ivashkovich-Shevchishin (1999), and `gromov_compactness.pdf`. Deconstructs proofs into formal lemma specs. | Literature papers, PDF specification | Formal lemma requirements, interface specs |
| **Worker Blueprint** | Authors and maintains `GROMOV_COMPACTNESS_BLUEPRINT.md` and `AUTOFORMALIZATION_PLAN.md`. Formulates candidate Lean 4 type signatures and docstrings. | Math specs, Mathlib inventory | Master Blueprint, Implementation Plan |
| **Implementer Agent** | Writes formal Lean 4 definitions, statements, and skeleton proofs. Orchestrates tactical proofs and structure instantiation. | Blueprint signatures, Mathlib modules | `GromovCompactness/*.lean` files |
| **Ollama Gemma Prover** | Performs automated proof search, premise selection, tactic suggestion, and lemma proving on local hardware via `http://localhost:11434`. | Prompt packets, Lean error contexts | Lean 4 proof blocks, tactics |
| **Proof Repair Engine** | Compiler-in-the-loop diagnostic runner. Invokes `lake build` / `lean --json`, captures type mismatches and missing premises, and applies iterative repairs. | Compiler JSON diagnostics | Patch suggestions, repaired files |
| **Forensic Auditor / QA** | Verifies dependency acyclicity, audits `#print axioms`, validates all 8 mathematical stress cases, and prevents mock or facade implementations. | Built Lean environment, AST | Audit reports, attestation files |

---

## 4. Local Gemma / Ollama Proving Pipeline

To conserve external compute, the project integrates a dedicated local proving pipeline powered by **Ollama** running **Gemma** models.

### 4.1 Infrastructure & Connectivity
- **Target Endpoint**: `http://localhost:11434`
- **Recommended Models**:
  1. `gemma2:27b` (Primary proving model for complex multi-step tactical proofs)
  2. `gemma2:9b` (Fast model for lemma translation, premise selection, and boilerplate)
  3. `gemma2:2b` (Ultra-low latency model for syntax repair and formatting)
  4. Fallback: `deepseek-r1:14b` or `qwen2.5-coder:14b` for deep tactical search.
- **Client Tooling**: `tools/ollama_lean4_client.py` provides a Python-based CLI/API client with JSON streaming, health checking, temperature control, and automatic retry.

### 4.2 Gemma Prompt Engineering Templates

#### Template 1: Informal-to-Formal Lean 4 Translation
```markdown
<start_of_turn>user
You are an expert Lean 4 mathematician and autoformalizer.
Translate the following informal mathematical lemma into a formal Lean 4 declaration.

### Target Environment:
- Mathlib4 (latest)
- Open namespaces: `GromovCompactness`, `MeasureTheory`, `Metric`, `Set`
- Typeclass: `[ClosedTameTarget I M]`

### Informal Lemma:
"Let u: CP^1 -> M be a non-constant J-holomorphic sphere. Then its symplectic energy
E(u) = ∫ u^* ω is bounded below by a strictly positive constant ε_sph > 0 depending only on M, ω, and J."

### Requirements:
1. Provide valid Lean 4 syntax.
2. Include comprehensive docstrings explaining the mathematical role.
3. State all hypotheses explicitly (smoothness, J-holomorphicity, non-constancy).
4. Output only the Lean 4 code block.
<end_of_turn>
<start_of_turn>model
```

#### Template 2: Tactical Proof Search & Tactic Suggestion
```markdown
<start_of_turn>user
You are an expert Lean 4 tactic prover.
Complete the proof of the following theorem or suggest the next tactical steps.

### Goal State:
```lean
theorem energy_rank_strict_decrease (m m_i h : ℝ) (hm : 0 < m) (hh : 0 < h)
    (hle : m_i ≤ m - h) :
    Nat.floor (m_i / h) < Nat.floor (m / h) := by
  sorry
```

### Context & Available Lemmas:
- `Nat.floor_lt_floor_of_le_sub`
- `div_le_div_right`
- `sub_div`

### Instruction:
Provide the complete tactical proof inside `by ...`. Use standard Mathlib tactics (`apply`, `linarith`, `nlinarith`, `omega`, `positivity`).
<end_of_turn>
<start_of_turn>model
```

#### Template 3: Diagnostic-Driven Proof Repair
```markdown
<start_of_turn>user
You are a Lean 4 compiler repair engine. Fix the following compilation error.

### Source Code:
```lean
theorem metric_pos_def (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < ClosedTameTarget.metric I M x v v := by
  dsimp [ClosedTameTarget.metric]
  have h_tame := ClosedTameTarget.tame x v hv
  linarith
```

### Compiler Diagnostic (`lean --json`):
```json
{
  "pos": {"line": 4, "col": 2},
  "severity": "error",
  "message": "type mismatch\n  have h_tame : 0 < ω x v (J x v)\nexpected\n  0 < (1 / 2) * (ω x v (J x v) + ω x v (J x v))"
}
```

### Instruction:
Analyze the error, provide the corrected proof script, and explain the fix.
<end_of_turn>
<start_of_turn>model
```

---

## 5. Detailed Task Contract Execution Plan

Below is the execution matrix detailing work streams, owner files, dependencies, and validation methods for all 39 contracts:

### 5.1 Track 1: Foundations & Bookkeeping (`F00`–`F06`)
| Task | Target File | Status | Primary Focus | Acceptance Test |
|---|---|---|---|---|
| **F00** | `GromovCompactness/LibraryAudit.lean` | `FROM_SCRATCH` | Toolchain pin & dependency verification | `lake build` zero warnings |
| **F01** | `GromovCompactness/Geometry/Target.lean` | `ALIGNED_WITH_TAUCETI` | `ClosedTameTarget`, metric $g$, $\bar{\partial}_J u = 0$ | Metric positivity & $J$-invariance proved |
| **F02** | `GromovCompactness/Geometry/Sphere.lean` | `ALREADY_IN_MATHLIB` | $\mathbb{CP}^1$ charts, affine maps, Möbius group | Group action and biholomorphicity proved |
| **F03** | `GromovCompactness/Analysis/Energy.lean` | `FROM_SCRATCH` | Extended measure $\mu_u$, real wrapper $E(u; A)$, $u^* \omega$ | Conformal invariance & additivity proved |
| **F04** | `GromovCompactness/Topology/SmoothLocal.lean` | `FROM_SCRATCH` | $C^\infty_{\mathrm{loc}}$ convergence on exhausting domains | Limit uniqueness & equation closure |
| **F05** | `GromovCompactness/Topology/Subsequence.lean` | `FROM_SCRATCH` | Strictly increasing maps, Cantor diagonal extraction | Diagonal subsequence lemma proved |
| **F06** | `GromovCompactness/Topology/SphereTree.lean` | `ALREADY_IN_MATHLIB` | `SphereTree`, node points, matching, stability | Tree grafting & distinctness preserved |

#### 5.1.1 Phase 1 Resource and Timeline Estimates (Model A vs. Model B)

Phase 1 establishes the package infrastructure (`lakefile.lean`, `lean-toolchain`, `GromovCompactness.lean`), foundational geometric structures, analysis wrappers, and combinatorial sphere tree definitions (`F00`–`F06`). The resource commitment is rigorously evaluated across two operational paradigms: **Model A** (`sorry`-first-pass skeleton strategy) and **Model B** (full zero-`sorry` machine-checked proof completion).

| Dimension | Model A: `sorry`-First-Pass Strategy (Scaffolded Skeleton) | Model B: Full Proof Completion (Zero-`sorry` Formalization) |
|---|---|---|
| **Objective** | Formal definitions, type signatures, docstrings, and verified typechecked skeletons with structured `sorry` placeholders for unproved lemmas. Enables all downstream modules (`A01`–`G05`) to import and build unblocked. | Complete machine-checked proofs of all lemmas and structural properties without `sorry`, adhering strictly to standard Lean 4 axioms and Mathlib compatibility. |
| **Agent Runs / Swarms** | **6 – 10 agent runs** (1–2 iterative runs per module `F00`–`F06` plus orchestrator synchronization). | **80 – 120 agent runs** (incorporating automated proof search, tactic suggestion, premise selection, and iterative repair loops). |
| **Compute Time (Ollama + Lean 4)** | **15 – 30 minutes** of local compute (local Gemma 2 inference via Ollama + `lake build` elaboration). | **12 – 24 compute hours** (distributed local Gemma/Ollama proof search iterations, multi-candidate verification, and compiler re-checking). |
| **Human-in-the-Loop Oversight** | **1 – 2 hours** (reviewing type signatures, typeclass ergonomics, notation, and literature alignment with Gromov 1985 & Ivashkovich-Shevchishin). | **15 – 25 hours** (guiding hard analytical lemmas, differential forms integration, Stokes theorem on manifolds, and Mathlib gaps). |
| **Calendar Elapsed Time** | **~1 to 2 hours** from launch to working typechecked skeleton. | **3 to 5 business days** for an active formalization team. |
| **Downstream Unblocking** | **Immediate**: downstream modules (`A01`–`G05`) can import and elaborate types right away. | **Deferred**: downstream modules must wait for all foundation proofs to clear. |

##### Detailed Module-by-Module Estimates for Phase 1:

| Task ID | Module File | Model A Skeleton (Agent / Compute / Human) | Model B Full Proof (Agent / Compute / Human) | Critical Mathematical Milestones |
|---|---|---|---|---|
| **F00** | `LibraryAudit.lean` | 1 run / 2 min / 10 min human | 2 runs / 15 min / 30 min human | Audit record verification, Mathlib toolchain pinning (`v4.16.0`). |
| **F01** | `Geometry/Target.lean` | 1–2 runs / 5 min / 15 min human | 15–20 runs / 2–3 hrs / 3–4 hrs human | `ClosedTameTarget`, metric positivity & $J$-invariance, Cauchy-Riemann operator. |
| **F02** | `Geometry/Sphere.lean` | 1–2 runs / 5 min / 15 min human | 10–15 runs / 1–2 hrs / 2–3 hrs human | $\mathbb{CP}^1$ Riemann sphere, `MoebiusFrame` action, affine rescalings $z \mapsto a + \lambda z$. |
| **F03** | `Analysis/Energy.lean` | 1–2 runs / 5 min / 20 min human | 20–25 runs / 4–6 hrs / 4–5 hrs human | Borel energy measure $\mu_u$, conformal invariance $E(u \circ \phi) = E(u)$, $u^* \omega$ identity. |
| **F04** | `Topology/SmoothLocal.lean` | 1–2 runs / 5 min / 15 min human | 15–20 runs / 3–5 hrs / 3–4 hrs human | $C^\infty_{\mathrm{loc}}$ convergence on exhausting domains, Cauchy-Riemann equation closure. |
| **F05** | `Topology/Subsequence.lean` | 1 run / 3 min / 10 min human | 8–10 runs / 1–2 hrs / 1–2 hrs human | Strictly monotone maps `SubseqMap`, Cantor diagonal extraction theorem. |
| **F06** | `Topology/SphereTree.lean` | 1–2 runs / 5 min / 15 min human | 15–20 runs / 3–4 hrs / 3–4 hrs human | `SphereTree` combinatorial trees, nodal matching, ghost component bound $G \le P - 2$. |
| **Total** | **Phase 1 Infrastructure** | **~8 runs / ~25 min / ~1.5 hrs** | **~90–110 runs / ~16–22 hrs / ~18–22 hrs** | **Complete Phase 1 Foundations layer ready for Tracks 2–4.** |

##### Operational Control: Pause and Resume Mechanism
To allow researchers and agents to pause and resume the autoformalization pipeline at any point without losing progress or corrupting state, Phase 1 provides the `tools/workflow_control.py` utility:
- **Pause at any time**: `python3 tools/workflow_control.py pause --reason "Your reason"`
- **Resume at any time**: `python3 tools/workflow_control.py resume`
- **Inspect live status**: `python3 tools/workflow_control.py status`
- **Save progress checkpoint**: `python3 tools/workflow_control.py checkpoint --label "descriptive_label"`
- **Run verification test**: `python3 tools/workflow_control.py test`

This guarantees complete operational flexibility, allowing long-running proof searches or human reviews to proceed smoothly without system lock-in.

### 5.2 Track 2: Local Analytic Estimates (`A01`–`A12`)
| Task | Target File | Status | Primary Focus | Acceptance Test |
|---|---|---|---|---|
| **A01** | `GromovCompactness/Analysis/MeanValue.lean` | `FROM_SCRATCH` | Scalar mean-value lemma for $\Delta e \ge -b e^2$ | $L^\infty$ bound on $D_{r/2}$ via $\int_{D_r} e$ |
| **A02** | `GromovCompactness/Analysis/Bochner.lean` | `FROM_SCRATCH` | Bochner energy-density differential inequality | Target curvature constant $b \ge 0$ extracted |
| **A03** | `GromovCompactness/Analysis/EpsilonRegularity.lean` | `ALREADY_IN_MATHLIB` | $\varepsilon$-regularity estimate via `Mathlib.Analysis.Hofer` | $\sup_{D_{r/2}} \|du\|^2 \le C r^{-2} E$ proved |
| **A04** | `GromovCompactness/Analysis/EllipticToolkit.lean` | `ALIGNED_WITH_TAUCETI` | Cauchy-Riemann $W^{k+1, p}$ interior bounds, Morrey | $L^p$ Calderón-Zygmund bounds verified |
| **A05** | `GromovCompactness/Analysis/Bootstrap.lean` | `FROM_SCRATCH` | Weak $W^{1, p} \to C^\infty$ nonlinear bootstrap | Smoothness of continuous weak solutions |
| **A06** | `GromovCompactness/Analysis/LocalCompactness.lean` | `ALREADY_IN_MATHLIB` | $C^\infty_{\mathrm{loc}}$ compactness via Arzelà-Ascoli | Diagonal extraction of smooth limit |
| **A07** | `GromovCompactness/Analysis/EnergyGap.lean` | `FROM_SCRATCH` | $\varepsilon_{\mathrm{sph}} > 0$ for non-constant spheres | Stokes theorem on contractible target chart |
| **A08** | `GromovCompactness/Analysis/Monotonicity.lean` | `FROM_SCRATCH` | Target monotonicity $E(u^{-1}(B_r(x))) \ge c r^2$ | Coarea and isoperimetric inequality |
| **A09** | `GromovCompactness/Analysis/CylinderLocalization.lean` | `FROM_SCRATCH` | Small-energy cylinder image in one target chart | Target diameter $< d_0$ verified |
| **A10** | `GromovCompactness/Analysis/CylinderDecay.lean` | `FROM_SCRATCH` | Exponential energy & diameter decay on $[-L, L] \times S^1$ | Differential inequality $F(T) \le -C F'(T)$ |
| **A11** | `GromovCompactness/Analysis/PunctureExtension.lean` | `FROM_SCRATCH` | Continuous and $W^{1, p}$ extension at puncture | Power bounds $E(D_r) \le C r^{2\alpha}$ proved |
| **A12** | `GromovCompactness/Analysis/Removal.lean` | `FROM_SCRATCH` | Singularity removal theorem | Smooth $J$-holomorphic extension on $D_1$ |

### 5.3 Track 3: Concentration Compactness & Bubbling Engine (`C01`–`C03`, `B01`–`B07`)
| Task | Target File | Status | Primary Focus | Acceptance Test |
|---|---|---|---|---|
| **C01** | `GromovCompactness/Compactness/Measures.lean` | `FROM_SCRATCH` | Weak convergence of energy measures $\mu_n \rightharpoonup \mu$ | Weak compactness of Radon measures |
| **C02** | `GromovCompactness/Compactness/Concentration.lean` | `FROM_SCRATCH` | Finite singular set $S$, smooth convergence off $S$ | Card bound $|S| \le B / \varepsilon_{\mathrm{reg}}$ |
| **C03** | `GromovCompactness/Compactness/Defect.lean` | `FROM_SCRATCH` | Defect measure identity $\mu = u_0^* \omega + \sum m_p \delta_p$ | Mass conservation on isolating disks |
| **B01** | `GromovCompactness/Bubbling/Threshold.lean` | `FROM_SCRATCH` | Universal energy quantum $h \le \min(\varepsilon_{\mathrm{reg}}/2, \dots)$ | Global threshold record defined |
| **B02** | `GromovCompactness/Bubbling/Calibration.lean` | `FROM_SCRATCH` | Gradient maximum $a_n$, calibration $E(D_{\lambda_n}) = m - h/2$ | Centers $a_n \to 0$ and radii $\lambda_n \to 0$ |
| **B03** | `GromovCompactness/Bubbling/Neck.lean` | `FROM_SCRATCH` | Vanishing neck energy & diameter with explicit $\forall \exists$ | Quantified neck predicate verified |
| **B04** | `GromovCompactness/Bubbling/OneLevel.lean` | `FROM_SCRATCH` | One-level bubble $v$, defects $q_i$, $f(0) = v(\infty)$ | Mass identity $m = E(v) + \sum m_i$ |
| **B05** | `GromovCompactness/Bubbling/GhostBranching.lean` | `FROM_SCRATCH` | Constant bubbles branch ($\ge 2$ children $+ \infty$) | Stability $\operatorname{deg}(v) \ge 3$ proved for ghosts |
| **B06** | `GromovCompactness/Bubbling/Rank.lean` | `FROM_SCRATCH` | Strict rank decrease $\lfloor m_i / h \rfloor < \lfloor m / h \rfloor$ | Natural number arithmetic lemma |
| **B07** | `GromovCompactness/Bubbling/LocalTree.lean` | `FROM_SCRATCH` | Well-founded induction resolving defect into tree | Tree convergence of single defect |

### 5.4 Track 4: Global Assembly & Master Theorems (`G01`–`G05`)
| Task | Target File | Status | Primary Focus | Acceptance Test |
|---|---|---|---|---|
| **G01** | `GromovCompactness/Compactness/Assembly.lean` | `FROM_SCRATCH` | Telescoping global Möbius frames $\phi_{v, n}$ | Frame collapse condition $\phi_v^{-1} \circ \phi_w \to z_{vw}$ |
| **G02** | `GromovCompactness/Compactness/Stabilize.lean` | `FROM_SCRATCH` | Pruning deg 1 / suppressing deg 2 constant root | Smooth upgrade across deleted node |
| **G03** | `GromovCompactness/Compactness/GenusZero.lean` | `FROM_SCRATCH` | Master Core Compactness Theorem | Theorem 1 statement verified |
| **G04** | `GromovCompactness/Topology/ComponentCount.lean` | `FROM_SCRATCH` | Bounds $G \le P - 2$ and $|V| \le 2P - 2$ | Numerical bound via sum of degrees |
| **G05** | `GromovCompactness/Main.lean` | `FROM_SCRATCH` | Full build closure & `#print axioms` audit | Zero `sorryAx`, standard axioms only |

### 5.5 Track 5: Extensions (`E01`–`E05`)
| Task | Target File | Status | Primary Focus | Acceptance Test |
|---|---|---|---|---|
| **E01** | `GromovCompactness/Topology/Homology.lean` | `FROM_SCRATCH` | $[u_n] = \sum [u_v]$ in $H_2(M; \mathbb{Z})$ | 2-chain neck pinching & geodesic homotopy |
| **E02** | `GromovCompactness/Topology/Automorphisms.lean` | `FROM_SCRATCH` | Stability $\iff$ finite automorphism group | Permutation of finite target fibers |
| **E03** | `GromovCompactness/Compactness/Marked.lean` | `FROM_SCRATCH` | $k$-marked sphere sequence compactness | Cross-ratio normalization of collisions |
| **E04** | `GromovCompactness/Compactness/NodalInput.lean` | `FROM_SCRATCH` | Compactness for already-nodal stable inputs | Simultaneous subsequence gluing |
| **E05** | `GromovCompactness/Topology/ModuliCompactness.lean` | `FROM_SCRATCH` | Compact Hausdorff moduli space $\overline{\mathcal{M}}_{0, k}$ | Metric topology & Gromov convergence |

---

## 6. Mathematical Stress Case Audit & Quality Assurance

Every contract must satisfy the formal validation criteria derived from the 8 stress cases in `gromov_compactness.pdf` §6:

```
STRESS CASE 1: Non-compact Target M = ℂ
  - Test: Check ClosedTameTarget definition in F01.
  - Requirement: Must carry [CompactSpace M].
  - Failure condition: Allowing unconstrained constant sequences u_n = n.

STRESS CASE 2: Domain Collapse u_n(z) = n z on CP^1
  - Test: Check CompactnessWitness definition in F06 / G03.
  - Requirement: Must quantify over moving Möbius frames ϕ_{v, n}.
  - Failure condition: Asserting convergence only on the original domain.

STRESS CASE 3: Constant Base with Concentration Clusters (Ghosts)
  - Test: Check B05 and G02.
  - Requirement: B05 must prove ≥ 2 child nodes for constant bubbles; G02 must stabilize the root.
  - Failure condition: Producing a tree with unstable ghost nodes (deg ≤ 2).

STRESS CASE 4: Multiple Covers (z ↦ z^d)
  - Test: Inspect monotonicity A08 and removal A12.
  - Requirement: No assumption of injectivity or somewhere-injectivity.
  - Failure condition: Relying on embeddedness or non-branching.

STRESS CASE 5: Concentration on Calibration Circle |z| = 1
  - Test: Inspect B02 calibration equation and B05 atom mass bound.
  - Requirement: Exact target energy m - h/2 isolates the atom at 0 with mass ≤ m - h/2.
  - Failure condition: Assuming |z| = 1 is a continuity circle for the limit measure.

STRESS CASE 6: Strict vs. Non-Strict Energy Thresholds
  - Test: Check TargetThresholds in B01.
  - Requirement: h ≤ min(ε_reg/2, ε_sph, ε_neck/2) fixed once and for all.
  - Failure condition: Re-choosing or shrinking h dynamically during induction.

STRESS CASE 7: Colliding Marked Points on Constant Spheres
  - Test: Inspect E03.
  - Requirement: Insert ghost components using ratio-of-differences coordinates.
  - Failure condition: Colliding markings landing on nodes without bubble insertion.

STRESS CASE 8: Varying Homology Classes
  - Test: Inspect G03 and E01.
  - Requirement: G03 must not assume fixed homology; E01 must prove homology preservation.
  - Failure condition: Assuming fixed homology as a prerequisite for extraction.
```

---

## 7. Verification Protocols & Anti-Cheating Integrity Rules

### 7.1 Staged Verification Protocol ('Sorry'-First-Pass Model)
To ensure rapid execution without blocking dependencies, verification proceeds through three explicit stages:
1. **Pass 1: Interface & Skeleton Verification**:
   - For any needed prerequisite lemma not found in Mathlib/TauCeti, the formal statement is defined and the proof is left with `sorry`.
   - Downstream contracts compile against these candidate signatures without obstruction.
   - Pass 1 Acceptance: File compiles with `lake build`, types are well-formed, and downstream theorems can consume the declaration.
2. **Pass 2: Tactical Proving & Lemma Infilling**:
   - Local Gemma/Ollama provers and specialist agents target `sorry` stubs, applying Mathlib tactics and premises.
3. **Pass 3: Final Kernel Verification Gate (`G05`)**:
   - Systematic elimination of all `sorry` stubs in the dependency closure of `gromov_compactness_genus_zero`.
   - Command `#print axioms gromov_compactness_genus_zero` must report zero `sorryAx` and only standard Lean axioms.

### 7.2 Hard Integrity Constraints
1. **No Mock Implementations**: Dummy functions that return synthetic values without executing genuine mathematical reasoning are strictly prohibited.
2. **No False Axioms**: Adding unproved mathematical statements as `axiom` in Lean 4 will trigger immediate rejection by the Forensic Auditor.
3. **No Unsound Kernel Bypasses**: The kernel must enforce type soundness throughout.
4. **Independent Dependency Audit**: An automated test suite `tests/test_blueprint_completeness.py` verifies that all 39 contracts have unique files, valid dependencies, and no circular references.

### 7.3 The Completion Checklist for Each Task Contract
- **Pass 1 Checklist (Skeleton Gate)**:
  - [ ] Lean 4 file `GromovCompactness/.../XYZ.lean` exists and typechecks under `lake build`.
  - [ ] All definitions correspond to genuine geometric/topological concepts.
  - [ ] Downstream contracts can import and consume the declared types and theorem statements.
  - [ ] Proofs of missing prerequisites are explicitly stubbed with `sorry` (not `axiom`).
- **Pass 3 Checklist (Final Core Integration Gate `G05`)**:
  - [ ] Lean 4 file `GromovCompactness/.../XYZ.lean` builds with zero `sorry`.
  - [ ] The command `#print axioms XYZ` reports only standard Lean 4 axioms:
    - `propext` (Propositional Extensionality)
    - `Quot.sound` (Quotient Soundness)
    - `Classical.choice` (Axiom of Choice)
  - [ ] No `sorryAx` or unproved project hypothesis appears in the axiom report.
  - [ ] Unit tests exercise the definitions and prove consistency.

