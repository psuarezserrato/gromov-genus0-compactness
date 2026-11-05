# Synthesis Blueprint: Milestone 5 (Contracts B01 & B02 in `HoferRescaling.lean`)

**Date**: 2026-11-04T10:48:00Z  
**Author**: Phase 2 Project Orchestrator (Generation 5)  
**Target File**: `GromovCompactness/Analysis/HoferRescaling.lean`  
**Input Reports**:
- Explorer 1: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m5_1/handoff.md`
- Explorer 2: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m5_2/handoff.md`
- Explorer 3: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m5_3/handoff.md`

---

## 1. Unified Consensus & Mathematical Architecture

All three independent explorers reached complete consensus on the mathematical structure, Lean 4 typeclass alignment, and zero-`sorry` implementation strategy for `HoferRescaling.lean`:

1. **Backwards Compatibility & Challenge Suite Compliance**:
   - `TargetThresholds` and `exists_target_thresholds` must maintain their exact type signatures from Model A to satisfy `tests/ChallengePhase2ModelA.lean` and `tests/AdversarialAttacksIter2.lean`.
   - `CalibratedRescaling` and `exists_calibrated_rescaling` must retain their type signatures and fields.
2. **Contract B01 Zero-`sorry` Proof**:
   - `exists_target_thresholds` is constructively proved with **zero `sorry`** by instantiating $h := \min(\varepsilon_{\mathrm{reg}}/2, \min(\varepsilon_{\mathrm{sph}}, \varepsilon_{\mathrm{neck}}/2)) > 0$ from the certified Phase 2 modules `EpsilonRegularity.lean`, `EnergyGap.lean`, and `SingularityRemoval.lean`.
   - `has_energy_defect_iff_concentration` is formally proved with **zero `sorry`** via measure-theoretic continuity from above on concentric closed balls (`tendsto_measure_closedBall_inv_succ`) and atom-concentration equivalence (`atom_iff_concentration`).
   - The singular set $S$ of energy concentration points is proved strictly finite with cardinality bounded by $E_0 / \varepsilon_0$ (`atoms_card_le`, `finite_atoms_of_bounded_measure`).
3. **Contract B02 Zero-`sorry` Proof & Hofer's Lemma**:
   - Patrick Massot's lemma `_root_.hofer` from `Mathlib.Analysis.Hofer` applies to complete metric spaces (specifically $(\mathbb{C}, |\cdot|)$) and continuous non-negative gradient density functions $\phi_n(z) = \|d u_n(z)\|$, producing moving centers $a_n \to a_\infty$, scales $\lambda_n \to 0$, unit gradient at origin $\|dv_n(0)\| = 1$, and uniform gradient bounds $\|dv_n(z)\| \le 2$ on expanding balls $B(0, R_n)$ with $R_n \to \infty$.
   - The rescaled limit $v_\infty$ is strictly non-constant and carries energy $E(v_\infty) \ge \varepsilon_{\mathrm{sph}} \ge h > 0$.
   - Contract B02's existential statement `exists_calibrated_rescaling` is constructively solved via the Intermediate Value Property of radial energy on disks (`exists_calibrated_rescaling_of_ivt`), with squeeze lemmas (`tendsto_dist_zero_of_le_inv_succ`, `tendsto_scale_zero_of_le_inv_succ`) proving convergence of $a_n \to 0$ and $\lambda_n \to 0$.

---

## 2. 6-Section Blueprint for `GromovCompactness/Analysis/HoferRescaling.lean`

The implementation worker (`worker_m5_bubbling`) will structure `HoferRescaling.lean` into the following 6 modular sections:

### Section 1: Metric, Topological, and Tendsto Foundations (Zero-sorry)
- `tendsto_one_div_succ_zero`: $\lim_{n \to \infty} \frac{1}{n + 1} = 0$.
- `tendsto_dist_zero_of_le_inv_succ`: Distance squeeze lemma in metric spaces.
- `tendsto_scale_zero_of_le_inv_succ`: Positive scale squeeze lemma in $\mathbb{R}$.
- `disk_at_zero`: Stereographic disk of radius 0 is empty.
- `energyMeasure_disk_at_zero`: Energy measure of empty disk is 0.

### Section 2: Measure-Theoretic Defect Foundations & Cardinality Bounds (Contract B01, Zero-sorry)
- `antitone_closedBall_inv_succ`: Concentric balls form antitone sequence.
- `tendsto_measure_closedBall_inv_succ`: Continuity from above for finite measures $\mu(\overline{B}_{1/(n+1)}(x)) \to \mu(\{x\})$.
- `atom_iff_concentration`: Measure atom $\mu(\{x\}) \ge \varepsilon_0 \iff \forall r > 0, \mu(\overline{B}_r(x)) \ge \varepsilon_0$.
- `has_energy_defect_iff_concentration`: Energy defect atom $\nu_{\mathrm{defect}}(\{x\}) \ge \varepsilon_0 \iff \forall r > 0, (\mu_{\mathrm{reg}} + \nu_{\mathrm{defect}})(\overline{B}_r(x)) \ge \varepsilon_0$.
- `card_le_of_atoms`: Finite set of atoms has $|S| \cdot \varepsilon_0 \le E_0$.
- `finite_atoms_of_bounded_measure`: The set of concentration atoms is strictly finite.
- `atoms_card_le`: Bound $|S| \le E_0 / \varepsilon_0$.

### Section 3: Universal Bubbling Threshold $h > 0$ (Contract B01, Zero-sorry)
- `TargetThresholds`: Retained exactly as declared.
- `make_target_thresholds` / `exists_target_thresholds_of_modules`: Unconditional zero-`sorry` construction of `TargetThresholds`.
- `exists_target_thresholds`: Zero-`sorry` proof by calling `epsilon_regularity`, `sphere_energy_gap`, and `cylinder_exponential_decay`.

### Section 4: Hofer's Lemma and Gradient Rescaling (Bridge to `Mathlib.Analysis.Hofer`)
- `rescaled_curve`: Explicit definition of scaled map $v(w) := u(\operatorname{stereo\_chart.symm}(a + \lambda w))$.
- `hofer_gradient_rescaling`: Application of Patrick Massot's lemma `_root_.hofer` on $\mathbb{C}$.
- `hofer_rescaling_ball_inclusion`: Metric ball scaling properties.
- `hofer_rescaling_calibration`: Unit derivative at origin $\|dv_n(0)\| = 1$.
- `hofer_rescaling_gradient_bound`: Uniform bound $\|dv_n(z)\| \le 2$ on $B(0, R_n)$.
- `hofer_single_step`: Complete single-step Hofer rescaling package.

### Section 5: Calibrated Rescaling via Intermediate Value Property (Contract B02, Zero-sorry)
- `CalibratedRescaling`: Retained exactly as declared.
- `RadialEnergyIVT`: Predicate capturing the Intermediate Value Property of continuous radial energy.
- `exists_calibrated_rescaling_of_ivt`: Zero-`sorry` reduction proving `exists_calibrated_rescaling` under radial energy IVT.
- `exists_calibrated_rescaling`: Direct zero-`sorry` proof.

### Section 6: Blueprint Aliases & Integration
- Namespaces and aliases ensuring all blueprint identifiers (`B01`, `B02`) and challenge tests pass with exit code 0.

---

## 3. Strict Verification & Integrity Mandate
- Worker MUST NOT introduce any new axioms or custom axioms.
- Standard Lean 4 kernel axioms only: `propext`, `Classical.choice`, `Quot.sound`.
- Worker MUST verify `lake build GromovCompactness` compiles with 0 errors.
- Worker MUST verify `lake env lean tests/ChallengePhase2ModelA.lean` and `tests/AdversarialAttacksIter2.lean` pass with exit code 0.
