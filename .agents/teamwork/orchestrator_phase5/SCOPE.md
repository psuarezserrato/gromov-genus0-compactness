# Scope: Phase 5 (Definition Repair, Statement Audit, Gemma 9B Specialization, and First Sorry-Free Closures)

## Architecture
Phase 5 establishes the foundation for the entire Gromov Compactness autoformalization by:
1. Setting up strict 9B-only local Gemma configuration, extracting all verified (goal, proof) pairs, building premise retrieval, and specializing `gemma-lean4:latest` via `Modelfile.gromov-lean4`.
2. Constructing a fast (< 3 min) module-prefix-scoped mechanical kernel axiom census (`tests/PhaseAxiomCensus.lean`, P0-6).
3. Repairing critical mathematical definitions and statements:
   - `GromovCompactness/Analysis/Energy.lean`: Spherical Jacobian factor / intrinsic metric on CP1, smooth finiteness before `.toReal`, strictly positive energy for non-constant smooth maps, unconditional conformal invariance without `h_conf` (P0-1, P0-2).
   - `Target.lean` & `VaryingJ.lean`: Concrete smoothness and closedness predicates for `ω` and `J` (P0-3).
   - `Monotonicity.lean` & `Bochner.lean` & `EpsilonRegularity.lean`: Differential inequality alignment (`Δe ≥ -b e² - c e`) and Euclidean density convention on discs in ℂ (P0-4, P0-5).
   - `Assembly.lean`: Restating `assemble_global_frames` using rescaling data (P0-7).
   - `ModuliSpace.lean`: Eliminating sorry-defined definitions (`GromovConverges`, `gromovDist`, `moduliSpaceMetric`, `ModuliSpaceInClass`) (P0-8).
   - `Main.lean` & docstrings: Fixing misleading docstrings, labeling reductions as conditional (P0-9).
   - `WeakJHolomorphicOn` clarification recorded in blueprint (P0-10).
4. Proving the first sorry-free target closures in `Extensions/Automorphisms.lean` (#30, #31, #33, #34) using the specialized 9B Gemma loop.
5. Verifying 100% `sorryAx`-free status across all target modules via the new census tool and 5-agent gate.

## Feature Inventory
| # | Feature | Description | Milestone | Source |
|---|---------|-------------|-----------|--------|
| 1 | 9B Ollama Policy & Config | Restrict to installed 9B models, query /api/tags, eliminate 404s | M1 | COMPLETION_PLAN §5.1 |
| 2 | Accepted Proofs Extraction | Extract verified (goal, proof) pairs to data/gemma_accepted_proofs.jsonl | M1 | COMPLETION_PLAN §5.1 & §5.5 |
| 3 | BM25 Premise Index | Build local premise retriever over Mathlib + project declarations | M1 | COMPLETION_PLAN §5.2 |
| 4 | Gemma 9B Specialization | Build Modelfile.gromov-lean4 with Gromov/Mathlib v4.16 prompt + exemplars | M1 | COMPLETION_PLAN §5.1 & §5.5 |
| 5 | Usage Ledger | Log /api/generate proving calls to .agents/gemma_usage.jsonl | M1 | COMPLETION_PLAN §5.4 |
| 6 | Fast Phase Axiom Census (P0-6) | Build tests/PhaseAxiomCensus.lean (< 3 min, single-traversal, exact sorryAx names) | M1 | COMPLETION_PLAN P0-6 |
| 7 | Energy Measure Repair (P0-1) | Include spherical Jacobian / intrinsic measure, finiteness before toReal, positive energy test | M2 | COMPLETION_PLAN P0-1 |
| 8 | Unconditional Energy Conformal Invariance (P0-2) | Prove energy_conformal_invariant without circular h_conf | M2 | COMPLETION_PLAN P0-2 |
| 9 | Concrete Target Predicates (P0-3) | Replace unconstrained ω_closed and J_smooth with concrete predicates | M2 | COMPLETION_PLAN P0-3 |
| 10 | Differential Inequality Alignment (P0-4) | Align scalar_mean_value_inequality and bochner_differential_inequality | M3 | COMPLETION_PLAN P0-4 |
| 11 | Density Convention (P0-5) | Restate Euclidean density convention for A02/A03 on discs in ℂ | M3 | COMPLETION_PLAN P0-5 |
| 12 | Assembly Rescaling Frames (P0-7) | Restate assemble_global_frames from CalibratedRescaling data | M3 | COMPLETION_PLAN P0-7 |
| 13 | Eliminate Sorry Defs in ModuliSpace (P0-8) | Concretely define Gromov convergence and homology class, remove sorry defs | M3 | COMPLETION_PLAN P0-8 |
| 14 | Docstring & Reduction Audit (P0-9) | Fix misleading docstrings, label reductions as conditional | M3 | COMPLETION_PLAN P0-9 |
| 15 | Elliptic Bootstrap & Singularity Removal Bridge (P0-10) | Switch A04 to C^{k,\alpha} Hölder/Schauder, bridge A11→A05→A12 with 0 direct sorry in removal_of_singularities | M3 | USER APPROVED DIRECTIVE |
| 16 | Core Call-Graph Wiring (P0-11 / G03-W) | Wire G02↔G03, G01↔C02+C03+B07, B07↔B06+B05+B04, Measures & A03/A07/A12, #audit_wiring | M3, M4 | USER APPROVED DIRECTIVE |
| 17 | Proof Closures #30, #31, #33, #34 | Close 4 leaf declarations in Extensions/Automorphisms.lean with 0 sorry | M4 | COMPLETION_PLAN §3.4 E04 |
| 18 | Phase 5 Census & Gate Certification | Full 5-agent gate & mechanical census certification | M5 | COMPLETION_PLAN §0 & §6 |

## Milestones
| # | Name | Scope | Dependencies | Status |
|---|------|-------|-------------|--------|
| M1 | Plumbing, 9B Ollama Policy & Specialization, Census Tool | Features 1-6 (P0-6, §5.1, §5.5) | none | DONE |
| M2 | Energy & Target Definition Repairs | Features 7-9 (P0-1, P0-2, P0-3) | M1 | DONE |
| M3 | PDE, Density, Frame, ModuliSpace & Core Wiring Components 1-4 | Features 10-15, 16 (Comp 1-4: P0-4, P0-5, P0-7..P0-11) | M2 | DONE |
| M4 | Sorry-Free Closures E04 & #audit_wiring Certification | Features 16 (Comp 5 #audit_wiring), 17 (#30, #31, #33, #34) | M1, M2, M3 | DONE |
| M5 | Phase 5 Gate & Kernel Axiom Census Certification | Feature 18 (Full gate & census) | M1, M2, M3, M4 | DONE |

## Interface Contracts
- `tests/PhaseAxiomCensus.lean`: Invoked via `lake env lean tests/PhaseAxiomCensus.lean -- [ModulePrefix]`. Scans the environment for declarations in `ModulePrefix`, collects axioms in a single traversal, prints exact `sorryAx`-dependent constants, and exits with non-zero if any `sorryAx` is found.
- `tools/ollama_lean4_client.py`: Queries `/api/tags`, uses strictly 9B models (`gemma-lean4:latest` / `gemma2:9b-instruct-q5_K_M`), logs to `.agents/gemma_usage.jsonl`.
- `GromovCompactness/Analysis/Energy.lean`: `energyMeasureExtended` integrates against Lebesgue with spherical Jacobian or spherical measure on CP1. `energy_conformal_invariant` proved unconditionally.
- `GromovCompactness/Target.lean`: `ClosedTameTarget` specifies `ω_closed` and `J_smooth` using concrete Mathlib manifold differential topology predicates.
- `GromovCompactness/Extensions/Automorphisms.lean`: `moebius_three_point_rigidity`, `ghost_component_pure_automorphism_trivial`, `pure_component_automorphisms_finite`, and `full_automorphisms_finite_iff_pure_finite` are 100% sorry-free.
