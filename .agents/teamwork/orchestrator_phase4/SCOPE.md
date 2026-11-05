# Phase 4 Scope & Execution Plan: Extensions, Moduli Space Hausdorff Topology & Analytic Leaf Closure

## 1. Objectives & Target Contracts
Implement and certify Phase 4 of the Gromov Compactness autoformalization based on Gromov (1985), Ivashkovich & Shevchishin (1999), and the blueprint contracts:
- **`E01` (Varying $J_n \to J$ in $C^\infty$)**:
  - `VaryingAlmostComplexStructures`: Smooth convergence of tamed/compatible structures on $(M, \omega)$.
  - Uniform constants: $\varepsilon_{\mathrm{reg}}(J_n)$, $\hbar(J_n)$, $C_{\mathrm{mono}}(J_n)$ bounded uniformly away from zero on compact families.
  - Gromov compactness transfer for $J_n$-holomorphic curves.
- **`E02` (Marked Curves & Cross-Ratio Stability)**:
  - $k$-marked genus 0 curves $(u_n, z_{n,1}, \dots, z_{n,k})$ on $\mathbb{CP}^1$.
  - Pairwise collision blow-up into ghost bubbles with $\ge 3$ special points (nodes + marked points).
  - Deligne–Mumford / Kontsevich stable map space $\overline{\mathcal{M}}_{0,k}(M, J, \le B)$.
- **`E03` (Homological Invariance)**:
  - Total homology class preservation $[u_n] = \sum_{v \in V(T)} [u_{\infty, v}] \in H_2(M; \mathbb{Z})$.
  - Symplectic area identity $\langle [\omega], [u_n] \rangle = \sum E(u_{\infty, v})$.
- **`E04` (Automorphism Group Finiteness)**:
  - Automorphism group $\mathrm{Aut}(T, \{u_v\}, \{z_i\})$ finiteness for genus 0 stable maps.
  - 3-point Möbius rigidity: $\mathrm{Aut}(u_v)$ is trivial on ghosts ($\ge 3$ special points) and finite on non-constant components ($E \ge \hbar$).
- **`E05` (Gromov Topology & Compact Hausdorff Moduli Space)**:
  - Gromov convergence topology on $\overline{\mathcal{M}}_{0,k}(M, J, \le B)$.
  - Hausdorff separation (uniqueness of Gromov limits up to stable map isomorphism).
  - Sequential compactness of the moduli space.
  - Update `tools/workflow_control.py` so all Phase 4 contracts are recognized and tracked.

## 2. Milestones
- **Milestone 1**: Phase 4 Model A Survey & Scaffolding Architecture (Lean 4 modules under `GromovCompactness/Extensions/` or `Moduli/`, re-exported in `GromovCompactness.lean`, linked in `blueprint/src/content.tex`).
- **Milestone 2**: Model A 5-Agent Verification Gate & Git Checkpoint Commit (`chk_phase4_model_a`).
- **Milestone 3**: Phase 4 Model B Part 1: Zero-sorry proofs for Varying $J$ (`E01`) & Marked Curves (`E02`).
- **Milestone 4**: Phase 4 Model B Part 2: Zero-sorry proofs for Homological Invariance (`E03`) & Automorphism Finiteness (`E04`).
- **Milestone 5**: Phase 4 Model B Part 3: Zero-sorry proofs for Moduli Space Hausdorff Topology & Compactness (`E05`).
- **Milestone 6**: Phase 4 Victory, Blueprint Sync, PDF compilation, 5-Agent Gate & Sentinel Handoff.
