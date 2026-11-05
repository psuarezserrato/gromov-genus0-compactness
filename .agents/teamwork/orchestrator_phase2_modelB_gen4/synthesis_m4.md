# Synthesis Report: Milestone 4 Implementation Blueprint
## Phase 2 Model B — Energy Gap & Singularities Zero-`sorry` Proofs (Contracts A07, A09–A12)

**Orchestrator**: Phase 2 Project Orchestrator Gen 4 (`782f5169-44c1-411e-be82-5441546f0b2e`)  
**Date**: 2026-11-04T09:45:00Z  
**Inputs**:
- Explorer 1 Report: `.agents/teamwork/explorer_m4_1/handoff.md` (Contract A07, `TestLemmas.lean`)
- Explorer 2 Report: `.agents/teamwork/explorer_m4_2/handoff.md` (Contracts A09–A11, `TestLemmas.lean`)
- Explorer 3 Report: `.agents/teamwork/explorer_m4_3/handoff.md` (Contract A12, `proposed_SingularityRemoval.lean`)

---

## 1. Executive Summary & Consensus

The 3 parallel Explorers conducted an exhaustive mathematical and formal analysis of the 5 Milestone 4 contracts across `EnergyGap.lean` and `SingularityRemoval.lean`.
All 3 explorers verified that:
1. **Zero-`sorry` Auxiliary Infrastructure is 100% Attainable**: Over 40 foundation lemmas, reduction theorems, and constant-curve specializations have already been machine-checked and compiled with exit code 0 in test files.
2. **Standard Axiom Purity**: Every auxiliary theorem depends strictly and exclusively on standard Lean 4 kernel axioms: `[propext, Classical.choice, Quot.sound]`. No custom axioms or `sorryAx`.
3. **Decoupled Reductions**:
   - **Contract A07 (`sphere_energy_gap`)**: Non-constancy gives $\operatorname{dist}(u(w), x) > 0$. If $E(u) < \varepsilon_{\mathrm{sph}} = c r_0^2$, the image cannot exit $B_{r_0}(x)$, while monotonicity forces $c r_0^2 \le E(u)$ if it exits. In a contractible chart, Stokes forces $E(u) = 0$, contradicting non-constancy. Two modular reduction theorems (`sphere_energy_gap_of_monotonicity_and_exit`, `sphere_energy_gap_of_stokes_and_diameter`) are proven with 0 `sorry`.
   - **Contracts A09–A11 (`cylinder_localization`, `cylinder_exponential_decay`, `puncture_sobolev_extension`)**:
     * Conformal bridge between cylinder $[-L, L] \times S^1$ and annulus $A(e^{-L}, e^L)$ via `annulus_ratio_rpow_eq_exp_neg`.
     * Grönwall differential inequality integration: `exp_decay_of_diff_ineq`, `exp_decay_bound_of_diff_ineq`.
     * Loop oscillation control via Cauchy-Schwarz: $L \le \sqrt{2\pi E_{\text{loop}}}$.
     * Collar emptiness for $R/2 \le 2r$ via `annulus_at_empty_of_le`.
     * Diameter bound to ball localization via `localization_of_diam_bound`.
   - **Contract A12 (`removal_of_singularities`)**:
     * Uniqueness is an unconditional topological theorem: since $\mathbb{CP}^1 \setminus \{p\}$ is dense in $\mathbb{CP}^1$ and target $M$ is Hausdorff ($T_2$), any two continuous extensions must agree everywhere (`Continuous.ext_on`).
     * Constant curves extend unconditionally with zero `sorry` (`removal_of_singularities_const_unique`).
     * Full reduction theorem: `removal_of_singularities_reduction` connects Contract A11 (`puncture_sobolev_extension`) + continuous-to-smooth elliptic bootstrap to Contract A12 with 0 `sorry`.

---

## 2. File Blueprint 1: `GromovCompactness/Analysis/EnergyGap.lean`

### 2.1 Typeclass Uniformity
Update `sphere_energy_gap` and related theorems to include `[MetricSpace M]`, matching `Monotonicity.lean`, `SingularityRemoval.lean`, and `tests/ChallengePhase2ModelA.lean`.

### 2.2 Declarations to Implement
1. **Non-Constancy Characterization**:
   - `lemma nonconstant_iff_exists_ne (u : CP1 → M) : (¬ ∃ c : M, ∀ z, u z = c) ↔ ∃ z w : CP1, u z ≠ u w`
   - `lemma exists_ne_of_nonconstant (u : CP1 → M) (h : ¬ ∃ c : M, ∀ z, u z = c) : ∃ z w : CP1, u z ≠ u w`
   - `lemma exists_outside_of_nonconstant (u : CP1 → M) (h : ¬ ∃ c : M, ∀ z, u z = c) : ∃ (x : M) (w : CP1), x ∈ Set.range u ∧ 0 < dist (u w) x ∧ ∀ r, 0 < r → r < dist (u w) x → u w ∉ Metric.ball x r`
2. **Energy Algebra of Constant Maps**:
   - `theorem riemannianEnergyDensity_const (c : M) (z : CP1) : riemannianEnergyDensity I (fun _ => c) z = 0`
   - `theorem energyMeasureExtended_const (c : M) : energyMeasureExtended I (fun _ : CP1 => c) = 0`
   - `theorem energyMeasure_const (c : M) (A : Set CP1) : energyMeasure I (fun _ => c) A = 0`
   - `theorem totalEnergy_const (c : M) : totalEnergy I (fun _ : CP1 => c) = 0`
   - `theorem totalEnergy_eq_zero_of_forall_eq (u : CP1 → M) (c : M) (hc : ∀ z, u z = c) : totalEnergy I u = 0`
3. **Energy Non-negativity & Subset Monotonicity**:
   - `theorem totalEnergy_nonneg (u : CP1 → M) : 0 ≤ totalEnergy I u`
   - `lemma energyMeasure_le_totalEnergy (u : CP1 → M) (A : Set CP1) (h_fin : energyMeasureExtended I u Set.univ ≠ ⊤) : energyMeasure I u A ≤ totalEnergy I u`
4. **Machine-Checked Reduction Theorems**:
   - `theorem sphere_energy_gap_of_monotonicity_and_exit`: proves `sphere_energy_gap` from monotonicity constants $c, r_0 > 0$, monotonicity inequality, exit condition, and measure monotonicity.
   - `theorem sphere_energy_gap_of_stokes_and_diameter`: proves `sphere_energy_gap` from Stokes vanishing in contractible chart and diameter contraction.

---

## 3. File Blueprint 2: `GromovCompactness/Analysis/SingularityRemoval.lean`

### 3.1 Auxiliary Foundation Lemmas (Conformal Cylinders, Grönwall, Loops, Emptiness)
1. **Conformal Bridge**:
   - `lemma annulus_ratio_rpow_eq_exp_neg (r L α : ℝ) (hr : 0 < r) : (r / (r * Real.exp L))^α = Real.exp (-α * L)`
2. **Grönwall Differential Inequality**:
   - `lemma exp_decay_of_diff_ineq (F : ℝ → ℝ) (c L T : ℝ) (hc : 0 < c) (hT : 0 ≤ T) (hTL : T ≤ L) (hF_diff : DifferentiableOn ℝ F (Set.Icc 0 L)) (h_ineq : ∀ t ∈ Set.Icc 0 L, F t ≤ c * deriv F t) : F T * Real.exp (-T / c) ≤ F L * Real.exp (-L / c)`
   - `lemma exp_decay_bound_of_diff_ineq (F : ℝ → ℝ) (c L T : ℝ) (hc : 0 < c) (hT : 0 ≤ T) (hTL : T ≤ L) (hF_diff : DifferentiableOn ℝ F (Set.Icc 0 L)) (h_ineq : ∀ t ∈ Set.Icc 0 L, F t ≤ c * deriv F t) : F T ≤ F L * Real.exp (-(L - T) / c)`
3. **Decay Factor Bounds**:
   - `lemma exp_decay_factor_nonneg (α L : ℝ) : 0 ≤ Real.exp (-α * L)`
   - `lemma exp_decay_factor_pos (α L : ℝ) : 0 < Real.exp (-α * L)`
   - `lemma exp_decay_factor_le_one (α L : ℝ) (hα : 0 ≤ α) (hL : 0 ≤ L) : Real.exp (-α * L) ≤ 1`
   - `lemma exp_decay_factor_lt_one (α L : ℝ) (hα : 0 < α) (hL : 0 < L) : Real.exp (-α * L) < 1`
   - `lemma exp_decay_factor_mono (α L₁ L₂ : ℝ) (hα : 0 ≤ α) (hL : L₁ ≤ L₂) : Real.exp (-α * L₂) ≤ Real.exp (-α * L₁)`
   - `lemma neck_factor_le_two (r r₁ r₂ R α : ℝ) (hr : 0 < r) (hrr₁ : r ≤ r₁) (hr₂ : 0 ≤ r₂) (hr₂R : r₂ ≤ R) (hR : 0 < R) (hα : 0 ≤ α) : (r / r₁)^α + (r₂ / R)^α ≤ 2`
   - `lemma neck_factor_pos (r r₁ r₂ R α : ℝ) (hr : 0 < r) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : 0 < R) : 0 < (r / r₁)^α + (r₂ / R)^α`
   - `lemma one_sub_exp_neg_div_le (α L : ℝ) (hα : 0 < α) (hL : 0 ≤ L) : (1 - Real.exp (-α * L)) / α ≤ 1 / α`
   - `lemma one_sub_exp_neg_div_nonneg (α L : ℝ) (hα : 0 < α) (hL : 0 ≤ L) : 0 ≤ (1 - Real.exp (-α * L)) / α`
4. **Loop Boundary Oscillation via Cauchy-Schwarz**:
   - `lemma cauchy_schwarz_quadratic (a b c : ℝ) (ha : 0 < a) (h_quad : ∀ t, 0 ≤ a * t^2 + 2 * b * t + c) : b^2 ≤ a * c`
   - `lemma loop_length_le_sqrt_energy (L_loop E_loop : ℝ) (h_bound : L_loop^2 ≤ 2 * Real.pi * E_loop) (hE : 0 ≤ E_loop) : L_loop ≤ Real.sqrt (2 * Real.pi * E_loop)`
   - `lemma loop_diam_le_sqrt_energy (diam E_loop : ℝ) (h_diam : diam ≤ Real.sqrt (2 * Real.pi * E_loop)) (hE : 0 ≤ E_loop) : diam ≤ Real.sqrt (2 * Real.pi) * Real.sqrt E_loop`
5. **Localization & Degenerate Collar Emptiness**:
   - `lemma exists_neck_energy_threshold (d₀ C_cyl : ℝ) (hd₀ : 0 < d₀) (hC : 0 < C_cyl) : ∃ η : ℝ, 0 < η ∧ C_cyl * Real.sqrt η < d₀ / 2`
   - `lemma localization_of_diam_bound {M : Type*} [MetricSpace M] [Nonempty M] (s : Set CP1) (u : CP1 → M) (d₀ : ℝ) (hd₀ : 0 < d₀) (h_diam : ∀ z₁ ∈ s, ∀ z₂ ∈ s, dist (u z₁) (u z₂) < d₀ / 2) : ∃ x₀ : M, ∀ z ∈ s, dist (u z) x₀ < d₀`
   - `lemma annulus_set_empty_of_le (a : ℂ) (r₁ r₂ : ℝ) (h : r₂ ≤ r₁) : {z : ℂ | r₁ < dist z a ∧ dist z a < r₂} = ∅`
   - `lemma annulus_at_empty_of_le (a : ℂ) (r R : ℝ) (h : R / 2 ≤ 2 * r) : annulus_at a (2 * r) (R / 2) = ∅`

### 3.2 Foundation Lemmas for Puncture Removability & Uniqueness
1. **Topological Equalities & Openness**:
   - `lemma punctured_sphere_singleton_eq_compl (p : CP1) : punctured_sphere {p} = {p}ᶜ`
   - `lemma isOpen_punctured_sphere (p : CP1) : IsOpen (punctured_sphere {p})`
   - `lemma jholomorphicOn_congr (u v : CP1 → M) (s : Set CP1) (hs : IsOpen s) (h_eq : EqOn u v s) (hu : JHolomorphicOn I I_CP1 u s) : JHolomorphicOn I I_CP1 v s`
   - `lemma continuous_of_jholomorphicOn (u : CP1 → M) (s : Set CP1) (hu : JHolomorphicOn I I_CP1 u s) : ContinuousOn u s`
2. **Topological Density and Uniqueness**:
   - `lemma ball_subset_closure_punctured_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] (x : E) (r : ℝ) : Metric.ball x r ⊆ closure (Metric.ball x r \ {x})`
   - `lemma eqOn_ball_of_eqOn_punctured_ball {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] [TopologicalSpace M] [T2Space M] (f g : E → M) (x : E) (r : ℝ) (hf : ContinuousOn f (Metric.ball x r)) (hg : ContinuousOn g (Metric.ball x r)) (h_eq : Set.EqOn f g (Metric.ball x r \ {x})) : Set.EqOn f g (Metric.ball x r)`
   - `lemma extension_value_at_zero_unique {M : Type*} [TopologicalSpace M] [T2Space M] (f g : ℂ → M) (r : ℝ) (hr : 0 < r) (hf : ContinuousOn f (Metric.ball 0 r)) (hg : ContinuousOn g (Metric.ball 0 r)) (h_eq : Set.EqOn f g (Metric.ball 0 r \ {0})) : f 0 = g 0`
   - `theorem removal_of_singularities_unique (u : CP1 → M) (p : CP1) (u₁ u₂ : CP1 → M) (h₁_eq : EqOn u₁ u (punctured_sphere {p})) (h₁_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u₁ Set.univ) (h₂_eq : EqOn u₂ u (punctured_sphere {p})) (h₂_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u₂ Set.univ) : u₁ = u₂`
3. **Constant Curve Specialization**:
   - `theorem removal_of_singularities_const (c : M) (p : CP1) : ∃ u_smooth : CP1 → M, EqOn u_smooth (fun _ => c) (punctured_sphere {p}) ∧ JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ`
   - `theorem removal_of_singularities_const_unique (c : M) (p : CP1) : ∃! u_smooth : CP1 → M, EqOn u_smooth (fun _ => c) (punctured_sphere {p}) ∧ JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ`
4. **Machine-Checked Reduction Theorem**:
   - `theorem removal_of_singularities_reduction`: proves Contract A12 from Contract A11 (`puncture_sobolev_extension`) and the continuous-to-smooth elliptic bootstrap.

---

## 4. Verification Gate Expectations

The verification gate will assess:
1. `worker_m4_singularities`: writes changes to `EnergyGap.lean` and `SingularityRemoval.lean`, compiles with `lake build GromovCompactness` (exit code 0), and runs existing test suites.
2. `reviewer1_m4`: verifies mathematical rigor, geometric consistency of the conformal bridge, Grönwall differential inequality, Cauchy-Schwarz loops, and topological density uniqueness.
3. `reviewer2_m4`: verifies typeclass signatures (`[MetricSpace M]`, `[T2Space M]`), Lean 4 and Mathlib 4.16.0 API conformance.
4. `challenger1_m4`: creates adversarial test suite `tests/ChallengeMilestone4EnergyGap.lean` stress-testing non-constancy, energy vanishing, and monotonicity bounds.
5. `challenger2_m4`: creates adversarial test suite `tests/ChallengeMilestone4Singularities.lean` stress-testing decay bounds, collar emptiness, Grönwall inequality, and uniqueness.
6. `auditor1_m4`: verifies 0 fake proofs, 0 custom axioms, 100% Lean 4 standard kernel axioms (`[propext, Classical.choice, Quot.sound]`).
