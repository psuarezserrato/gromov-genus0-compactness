/-
Sanity checks on the hypotheses of the master theorem.

S1. The non-certificate hypotheses of `gromov_compactness_genus_zero` are satisfiable:
    the constant sequence `u_n = id : CP1 → CP1` is nonconstant, J-holomorphic, and has finite,
    positive, bounded energy.
S2. The certificate `h_one_level` used up to commit `0a3de26` is over-strong: together with any
    `TargetThresholds`, it forces a J-holomorphic sphere of energy *exactly* `m` for every
    `m ∈ [h, 2h)`. On targets with quantized sphere energies (e.g. `CP1`, where energies are
    multiples of `4π`) this is false, so the old reduction was vacuous there. It has been replaced
    by the sequence-relative `Bubbling.OneLevelCertificate` and `Assembly.ConcDefectCertificate`.
S3. The replacement is not refuted by the same argument: `IsDefectSeq` ties the mass to an actual
    defect of a sequence, and a sequence with no energy concentration has no defect of mass `≥ h`
    at a point where its energy measure on small disks tends to zero.
S4. The old `h_graft_extract` is contradictory if two grafted trees with different total defect
    mass exist for a sequence with convergent energies.
S5. `affine_scaling` genuinely translates the origin to `stereo_chart.symm a`.
S6. `SmoothLocalConvergesOn` is satisfiable for the nonconstant map `id : CP1 → CP1`.
S7. The unconditioned `h_aa_prop` (prior to D1 repair, omitting `JHolomorphicOn`) is false on any
    target `M` with two distinct points `p ≠ q`, via `u = Function.update (fun _ => q) north_pole p`.
S8. The unconditioned `h_decay_prop` (prior to D2 repair, omitting `ε_neck` smallness) is false for
    any finite-energy `J`-holomorphic map with positive energy on a fixed annulus, by sending
    `r → 0⁺` and `R → ∞`.
-/
import GromovCompactness

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory Filter GromovCompactness GromovCompactness.Analysis

namespace GromovCompactness.CertificateSanity

/-! ## S1: the non-certificate hypotheses are satisfiable on `CP1` -/

theorem s1_main_hypotheses_satisfiable :
    (∀ _n : ℕ, ¬ ∃ c : CP1, ∀ z, (id : CP1 → CP1) z = c) ∧
    (∀ _n : ℕ, JHolomorphicOn I_CP1 I_CP1 (id : CP1 → CP1) Set.univ) ∧
    (∀ _n : ℕ, energyMeasureExtended I_CP1 (id : CP1 → CP1) Set.univ < ⊤) ∧
    0 < totalEnergy I_CP1 (id : CP1 → CP1) := by
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => concrete_nonconstant_map_finite_energy,
    concrete_nonconstant_map_positive_energy⟩
  · rintro ⟨c, hc⟩
    exact GromovCompactness.north_pole_ne_south_pole
      ((hc north_pole).trans (hc south_pole).symm)
  · exact concrete_nonconstant_map_jhol

/-! ## S2: the old `h_one_level` forces a continuum of sphere energies -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-- The certificate `h_one_level` exactly as it appeared in `Main.lean` at commit `0a3de26`. -/
def OldOneLevel (th : Bubbling.TargetThresholds I M) : Prop :=
  ∀ (m : ℝ), th.h ≤ m → ∀ (b : M),
    (∃ v : CP1 → M,
      JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
      m = totalEnergy I v ∧
      v north_pole = b ∧
      energyMeasure I v (disk_at 0 1) = m - th.h / 2) ∨
    (∃ v : CP1 → M,
      JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
      totalEnergy I v ≤ m - th.h ∧
      v north_pole = b ∧
      totalEnergy I v - energyMeasure I v (disk_at 0 1) = th.h / 2) ∨
    (∃ (v : CP1 → M) (q : Finset ℂ) (m_child : ℂ → ℝ),
      JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
      (∀ z ∈ q, ‖z‖ < 1) ∧
      (∀ z ∈ q, th.h ≤ m_child z) ∧
      (∀ z ∉ q, m_child z = 0) ∧
      m = totalEnergy I v + ∑ z ∈ q, m_child z ∧
      v north_pole = b ∧
      totalEnergy I v - energyMeasure I v (disk_at 0 1) = th.h / 2) ∨
    (∃ (v : CP1 → M) (q : Finset ℂ) (m_child : ℂ → ℝ),
      JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
      (∀ z ∈ q, th.h ≤ m_child z) ∧
      (∀ z ∉ q, m_child z = 0) ∧
      m = totalEnergy I v + ∑ z ∈ q, m_child z ∧
      v north_pole = b ∧
      energyMeasure I v (disk_at 0 1) + ∑ z ∈ q.filter (fun w => ‖w‖ < 1), m_child z =
        m - th.h / 2)

lemma sum_eq_zero_or_ge (h : ℝ) (hh : 0 < h) (s : Finset ℂ) (g : ℂ → ℝ)
    (hg : ∀ z ∈ s, h ≤ g z) : ∑ z ∈ s, g z = 0 ∨ h ≤ ∑ z ∈ s, g z := by
  rcases s.eq_empty_or_nonempty with hs | ⟨z, hz⟩
  · left; simp [hs]
  · right
    exact (hg z hz).trans (Finset.single_le_sum (fun w hw => hh.le.trans (hg w hw)) hz)

lemma energy_zero_of_const (v : CP1 → M) (hc : ∃ c : M, ∀ z, v z = c) (s : Set CP1) :
    energyMeasure I v s = 0 := by
  obtain ⟨c, hc⟩ := hc
  have hv : v = fun _ => c := funext hc
  subst hv
  exact Bubbling.energyMeasure_const_eq_zero I c s

lemma h_le_energy_of_nonconst (th : Bubbling.TargetThresholds I M) (v : CP1 → M)
    (hv : JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ)
    (hnc : ¬ ∃ c : M, ∀ z, v z = c) : th.h ≤ totalEnergy I v :=
  th.h_le_sph.trans (th.h_sph v hv hnc)

/-- If the exterior unit-disk energy of `v` is `h/2 > 0`, then `v` is nonconstant. -/
lemma nonconst_of_exterior (th : Bubbling.TargetThresholds I M) (v : CP1 → M)
    (hd : totalEnergy I v - energyMeasure I v (disk_at 0 1) = th.h / 2) :
    ¬ ∃ c : M, ∀ z, v z = c := by
  intro hc
  have h1 : totalEnergy I v = 0 := energy_zero_of_const I v hc Set.univ
  have h2 : energyMeasure I v (disk_at 0 1) = 0 := energy_zero_of_const I v hc _
  have := th.h_pos
  rw [h1, h2] at hd
  linarith

/-- **S2.** The old `h_one_level` forces a `J`-holomorphic sphere of energy exactly `m` for every
`m ∈ [h, 2h)`. -/
theorem s2_old_one_level_forces_energy (th : Bubbling.TargetThresholds I M)
    (h_old : OldOneLevel I th) (m : ℝ) (hm1 : th.h ≤ m) (hm2 : m < 2 * th.h) (b : M) :
    ∃ v : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧ totalEnergy I v = m := by
  have hh := th.h_pos
  rcases h_old m hm1 b with ⟨v, hv, hm, -, -⟩ | ⟨v, hv, hle, -, hd⟩ |
      ⟨v, q, mc, hv, -, hpos, -, hsum, -, hd⟩ | ⟨v, q, mc, hv, hpos, -, hsum, -, hcal⟩
  · exact ⟨v, hv, hm.symm⟩
  · have := h_le_energy_of_nonconst I th v hv (nonconst_of_exterior I th v hd)
    exact absurd hle (by linarith)
  · have hE := h_le_energy_of_nonconst I th v hv (nonconst_of_exterior I th v hd)
    rcases sum_eq_zero_or_ge th.h hh q mc hpos with h0 | hge
    · exact ⟨v, hv, by linarith⟩
    · exact absurd hsum (by linarith)
  · by_cases hc : ∃ c : M, ∀ z, v z = c
    · -- constant root: the exterior children carry mass exactly h/2, impossible
      have h1 : totalEnergy I v = 0 := energy_zero_of_const I v hc Set.univ
      have h2 : energyMeasure I v (disk_at 0 1) = 0 := energy_zero_of_const I v hc _
      have hsplit := Finset.sum_filter_add_sum_filter_not q (fun w => ‖w‖ < 1) mc
      have hout : ∑ z ∈ q.filter (fun w => ¬ ‖w‖ < 1), mc z = th.h / 2 := by linarith
      rcases sum_eq_zero_or_ge th.h hh (q.filter (fun w => ¬ ‖w‖ < 1)) mc
          (fun z hz => hpos z (Finset.mem_filter.mp hz).1) with h0 | hge
      · exact absurd hout (by linarith)
      · exact absurd hout (by linarith)
    · have hE := h_le_energy_of_nonconst I th v hv hc
      rcases sum_eq_zero_or_ge th.h hh q mc hpos with h0 | hge
      · exact ⟨v, hv, by linarith⟩
      · exact absurd hsum (by linarith)

/-- **S2'.** Consequently, the old `h_one_level` is refuted on any target with an energy gap:
if no `J`-holomorphic sphere has energy in `[h, 2h)` except at isolated values, a single
missing value suffices. -/
theorem s2_old_one_level_false_of_missing_energy (th : Bubbling.TargetThresholds I M)
    (m : ℝ) (hm1 : th.h ≤ m) (hm2 : m < 2 * th.h) (b : M)
    (h_missing : ∀ v : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ →
      totalEnergy I v ≠ m) :
    ¬ OldOneLevel I th := by
  intro h_old
  obtain ⟨v, hv, hE⟩ := s2_old_one_level_forces_energy I th h_old m hm1 hm2 b
  exact h_missing v hv hE

/-! ## S3: the replacement certificate only concerns genuine defects -/

/-- **S3.** If the energy of `f n` on small disks around `a` tends to `0` uniformly in `n`
(no concentration), then `f` has no defect of positive mass at `a`; so `OneLevelCertificate`
places no demand at such points. -/
theorem s3_no_defect_without_concentration (f : ℕ → (CP1 → M)) (a : ℂ) (m : ℝ) (b : M)
    (hm : 0 < m)
    (h_small : ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ n, energyMeasure I (f n) (disk_at a r) < ε) :
    ¬ Bubbling.IsDefectSeq I f a m b := by
  rintro ⟨-, -, -, h_mass, -⟩
  obtain ⟨r₁, hr₁, h1⟩ := h_mass (m / 2) (by linarith)
  obtain ⟨r₂, hr₂, h2⟩ := h_small (m / 2) (by linarith)
  have hr : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  obtain ⟨n, hn⟩ := (h1 (min r₁ r₂) hr (min_le_left _ _)).exists
  have hlt := h2 (min r₁ r₂) hr (min_le_right _ _) n
  have := (abs_lt.mp hn).1
  linarith

#print axioms s1_main_hypotheses_satisfiable
#print axioms s2_old_one_level_forces_energy
#print axioms s2_old_one_level_false_of_missing_energy
#print axioms s3_no_defect_without_concentration


/-! ## S4: the old `h_graft_extract` is contradictory for sequences with convergent energies -/

/-- The energy conclusion of the old `h_graft_extract` (as at `0a3de26`): for *every* defect-mass
function `m` and *every* grafted tree `P`, some subsequence has energies converging to
`E(u₀) + Σ m`. -/
def OldGraftEnergy (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M) : Prop :=
  ∀ (cdata : Compactness.ConcentrationData I u_seq B th) (m : CP1 → ℝ)
    (_P : Assembly.PartialRootGraftedTree I u_seq B th cdata m cdata.S),
    ∃ σ : Bookkeeping.SubseqMap, Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p))

/-- **S4.** If the energies of `u_seq` converge and two grafted trees with different total defect
mass exist for the same concentration data, the old graft certificate is false. -/
theorem s4_old_graft_contradiction (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (th : Bubbling.TargetThresholds I M) (h_old : OldGraftEnergy I u_seq B th)
    (L : ℝ) (h_conv : Tendsto (fun n => totalEnergy I (u_seq n)) atTop (𝓝 L))
    (cdata : Compactness.ConcentrationData I u_seq B th) (m₁ m₂ : CP1 → ℝ)
    (P₁ : Assembly.PartialRootGraftedTree I u_seq B th cdata m₁ cdata.S)
    (P₂ : Assembly.PartialRootGraftedTree I u_seq B th cdata m₂ cdata.S)
    (h_ne : ∑ p ∈ cdata.S, m₁ p ≠ ∑ p ∈ cdata.S, m₂ p) : False := by
  obtain ⟨σ₁, h₁⟩ := h_old cdata m₁ P₁
  obtain ⟨σ₂, h₂⟩ := h_old cdata m₂ P₂
  have e₁ := tendsto_nhds_unique (h_conv.comp σ₁.2.tendsto_atTop) h₁
  have e₂ := tendsto_nhds_unique (h_conv.comp σ₂.2.tendsto_atTop) h₂
  exact h_ne (by linarith)

#print axioms s4_old_graft_contradiction

/-! ## S5: affine_scaling respects its center -/

/-- **S5.** The affine scaling frame $w \mapsto a + \lambda w$ maps the south pole (origin $0 \in \mathbb{C}$)
to `stereo_chart.symm a`. For $a \ne 0$, this genuinely displaces the origin, confirming the center $a$ is incorporated. -/
theorem s5_affine_scaling_center (a : ℂ) (scale : ℝ) (hscale : 0 < scale) :
    (affine_scaling a scale hscale).toHomeo south_pole = stereo_chart.symm a ∧
    (a ≠ 0 → (affine_scaling a 1 one_pos).toHomeo south_pole ≠ south_pole) :=
  ⟨affine_scaling_south_pole a scale hscale, fun ha => affine_scaling_south_pole_ne a ha⟩

#print axioms s5_affine_scaling_center

/-! ## S6: SmoothLocalConvergesOn is satisfiable for nonconstant smooth maps -/

/-- **S6.** `SmoothLocalConvergesOn` is satisfiable for the nonconstant smooth identity map `id : CP1 → CP1`. -/
theorem s6_smooth_local_converges_on_id :
    SmoothLocalConvergesOn I_CP1 (fun _ => (id : CP1 → CP1)) id Set.univ :=
  smoothLocalConvergesOn_const I_CP1 id Set.univ contMDiff_id

#print axioms s6_smooth_local_converges_on_id

/-! ## S7: the old `h_aa_prop` without `JHolomorphicOn` (audit D1) is false on any nontrivial `M` -/

/-- The unconditioned `h_aa_prop` statement (prior to D1 repair), which omitted `JHolomorphicOn`. -/
def OldArzelaAscoliProp : Prop :=
  ∀ (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1),
    IsOpen Ω →
    (∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) →
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω

/-- A two-valued discontinuous map `u = Function.update (fun _ => q) north_pole p` with `p ≠ q` is
not continuous at `north_pole`. -/
lemma not_continuousAt_update_north_pole {p q : M} (hpq : p ≠ q) :
    ¬ ContinuousAt (Function.update (fun _ : CP1 => q) north_pole p) north_pole := by
  intro hcont
  have h_dense : Dense ({north_pole}ᶜ : Set CP1) :=
    Analysis.dense_compl_singleton_of_connected north_pole
  have h_mem : north_pole ∈ closure ({north_pole}ᶜ : Set CP1) := by
    rw [h_dense.closure_eq]
    exact mem_univ north_pole
  have : (𝓝[≠] north_pole).NeBot := mem_closure_iff_nhdsWithin_neBot.mp h_mem
  have h1 : Tendsto (Function.update (fun _ : CP1 => q) north_pole p) (𝓝[≠] north_pole) (𝓝 p) := by
    simpa [Function.update_self] using hcont.mono_left nhdsWithin_le_nhds
  have h_ev : (fun _ : CP1 => q) =ᶠ[𝓝[≠] north_pole] Function.update (fun _ : CP1 => q) north_pole p := by
    rw [eventuallyEq_nhdsWithin_iff]
    exact Eventually.of_forall fun z hz => (Function.update_of_ne hz p (fun _ : CP1 => q)).symm
  have h2 : Tendsto (Function.update (fun _ : CP1 => q) north_pole p) (𝓝[≠] north_pole) (𝓝 q) :=
    tendsto_const_nhds.congr' h_ev
  exact hpq (tendsto_nhds_unique h1 h2)

/-- The manifold derivative `mfderiv` of `Function.update (fun _ => q) north_pole p` vanishes everywhere on `CP1`. -/
lemma mfderiv_update_north_pole_eq_zero {p q : M} (hpq : p ≠ q) (z : CP1) :
    mfderiv I_CP1 I (Function.update (fun _ : CP1 => q) north_pole p) z = 0 := by
  by_cases hz : z = north_pole
  · subst hz
    apply mfderiv_zero_of_not_mdifferentiableAt
    intro hdiff
    exact not_continuousAt_update_north_pole hpq hdiff.continuousAt
  · have h_ev : Function.update (fun _ : CP1 => q) north_pole p =ᶠ[𝓝 z] (fun _ : CP1 => q) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
      exact Function.update_of_ne hw _ _
    rw [h_ev.mfderiv_eq]
    exact mfderiv_const
      (I := I_CP1) (I' := I) (x := z) (c := q)

/-- Consequently, the Riemannian energy density of `Function.update (fun _ => q) north_pole p` vanishes everywhere. -/
lemma riemannianEnergyDensity_update_north_pole_eq_zero {p q : M} (hpq : p ≠ q) (z : CP1) :
    riemannianEnergyDensity I (Function.update (fun _ : CP1 => q) north_pole p) z = 0 := by
  dsimp [riemannianEnergyDensity]
  have h1 : mfderiv I_CP1 I (Function.update (fun _ : CP1 => q) north_pole p) z e1 = 0 := by
    rw [mfderiv_update_north_pole_eq_zero I hpq z]
    rfl
  have h2 : mfderiv I_CP1 I (Function.update (fun _ : CP1 => q) north_pole p) z e2 = 0 := by
    rw [mfderiv_update_north_pole_eq_zero I hpq z]
    rfl
  rw [h1, h2]
  dsimp [ClosedTameTarget.metric]
  simp

/-- **S7 (Audit D1 Refutation).** On any target manifold `M` with two distinct points `p ≠ q`,
the unconditioned `OldArzelaAscoliProp` (without `JHolomorphicOn`) is false. -/
theorem s7_old_h_aa_prop_false_without_jhol {p q : M} (hpq : p ≠ q) :
    ¬ OldArzelaAscoliProp I (M := M) := by
  intro h_old
  let u : CP1 → M := Function.update (fun _ : CP1 => q) north_pole p
  have h_grad : ∀ K ⊆ (Set.univ : Set CP1), IsCompact K →
      ∃ C > 0, ∀ _n : ℕ, ∀ z ∈ K, riemannianEnergyDensity I u z ≤ C := by
    intro K _ _
    refine ⟨1, one_pos, fun _ z _ => ?_⟩
    rw [riemannianEnergyDensity_update_north_pole_eq_zero I hpq z]
    exact zero_le_one
  obtain ⟨σ, u_lim, h_conv⟩ := h_old (fun _ => u) Set.univ isOpen_univ h_grad
  have h_core : CoreSmoothLocalConvergesOn I (fun _ => u) u_lim Set.univ := h_conv []
  have h_eq : u = u_lim := by
    funext z
    have h_pt := (h_core.2 {z} (subset_univ _) isCompact_singleton).1 z (mem_singleton z)
    exact tendsto_nhds_unique tendsto_const_nhds h_pt
  have h_cont : ContinuousAt u north_pole := by
    rw [h_eq]
    exact h_core.1.continuousOn.continuousAt univ_mem
  exact not_continuousAt_update_north_pole hpq h_cont

#print axioms s7_old_h_aa_prop_false_without_jhol

/-! ## S8: the old `h_decay_prop` without `ε_neck` smallness (audit D2) is false for any map with positive annular energy -/

/-- The unconditioned `h_decay_prop` statement (prior to D2 repair), which asserted
`SatisfiesCylinderEnergyDecay` (`C₀ = 1, a = 1`) for all `0 < r` and `2 * r < R` without any
small-energy condition `energyMeasure I u (annulus_at center r R) < ε_neck`. -/
def OldCylinderDecayProp : Prop :=
  ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
    0 < r → 2 * r < R →
    JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
    SatisfiesCylinderEnergyDecay I u center r R

/-- **S8 (Audit D2 Refutation).** If a `J`-holomorphic map `u : CP1 → M` has finite total energy
and positive energy on some fixed annulus `annulus_at center r₁ r₂` (`0 < r₁ < r₂`), then the
unconditioned `OldCylinderDecayProp` is false: sending `r → 0⁺` and `R → ∞` makes the right-hand
side `(r / r₁ + r₂ / R) * E(A(r, R))` strictly smaller than `E(A(r₁, r₂))`. -/
theorem s8_old_h_decay_prop_false_without_smallness
    (u : CP1 → M) (center : ℂ) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_fin : energyMeasureExtended I u Set.univ ≠ ⊤)
    (h_pos : 0 < energyMeasure I u (annulus_at center r₁ r₂)) :
    ¬ OldCylinderDecayProp I (M := M) := by
  intro h_old
  set E_in := energyMeasure I u (annulus_at center r₁ r₂)
  set E_tot := energyMeasure I u Set.univ
  have hEtot_nonneg : 0 ≤ E_tot := ENNReal.toReal_nonneg
  have hDenom_pos : 0 < E_tot + 1 := by linarith
  let r : ℝ := min (r₁ / 2) ((E_in / 4) * r₁ / (E_tot + 1))
  have hr_pos : 0 < r := lt_min (by linarith) (div_pos (mul_pos (by linarith) hr₁) hDenom_pos)
  have hr_lt_r₁ : r < r₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let R : ℝ := max (2 * r₂) (r₂ * (E_tot + 1) / (E_in / 4))
  have hr₂_pos : 0 < r₂ := lt_trans hr₁ hr₁₂
  have h2r_lt_R : 2 * r < R := by
    have h2r : 2 * r < 2 * r₂ := by linarith
    exact lt_of_lt_of_le h2r (le_max_left _ _)
  have hr₂_lt_R : r₂ < R := by
    have hr₂_lt : r₂ < 2 * r₂ := by linarith
    exact lt_of_lt_of_le hr₂_lt (le_max_left _ _)
  have h_ineq := h_old u center r R hr_pos h2r_lt_R hu r₁ r₂ hr_lt_r₁ hr₁₂ hr₂_lt_R
  rw [Real.rpow_one, Real.rpow_one, one_mul] at h_ineq
  have hE_le_tot : energyMeasure I u (annulus_at center r R) ≤ E_tot := by
    dsimp [E_tot, energyMeasure]
    exact ENNReal.toReal_mono h_fin (measure_mono (subset_univ _))
  have h_term1 : r / r₁ ≤ (E_in / 4) / (E_tot + 1) := by
    rw [div_le_iff₀ hr₁]
    have h_min : r ≤ (E_in / 4) * r₁ / (E_tot + 1) := min_le_right _ _
    linarith [show (E_in / 4) * r₁ / (E_tot + 1) = ((E_in / 4) / (E_tot + 1)) * r₁ by ring]
  have h_term2 : r₂ / R ≤ (E_in / 4) / (E_tot + 1) := by
    have hR_pos : 0 < R := lt_trans hr₂_pos hr₂_lt_R
    rw [div_le_div_iff₀ hR_pos hDenom_pos]
    have h_max : r₂ * (E_tot + 1) / (E_in / 4) ≤ R := le_max_right _ _
    have h_mul := (div_le_iff₀ (show 0 < E_in / 4 by linarith)).mp h_max
    linarith
  have h_sum : r / r₁ + r₂ / R ≤ (E_in / 2) / (E_tot + 1) := by
    calc r / r₁ + r₂ / R
        ≤ (E_in / 4) / (E_tot + 1) + (E_in / 4) / (E_tot + 1) := add_le_add h_term1 h_term2
      _ = (E_in / 2) / (E_tot + 1) := by ring
  have h_prod : (r / r₁ + r₂ / R) * energyMeasure I u (annulus_at center r R) ≤ E_in / 2 := by
    calc (r / r₁ + r₂ / R) * energyMeasure I u (annulus_at center r R)
        ≤ ((E_in / 2) / (E_tot + 1)) * (E_tot + 1) := by
          apply mul_le_mul h_sum (le_trans hE_le_tot (by linarith)) ENNReal.toReal_nonneg
          positivity
      _ = E_in / 2 := div_mul_cancel₀ (E_in / 2) (by linarith)
  linarith

#print axioms s8_old_h_decay_prop_false_without_smallness

end GromovCompactness.CertificateSanity
