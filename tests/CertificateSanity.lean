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

end GromovCompactness.CertificateSanity
