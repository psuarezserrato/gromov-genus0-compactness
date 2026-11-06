import GromovCompactness.Topology.RieszMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Metrizable.Basic

/-!
# Sequential Prokhorov compactness for a compact metric space

Bounded sequences of finite Borel measures on a compact metric space `X` have a subsequence that
converges against every `f : C(X, ℝ)` to a finite measure.  Built from the vendored Riesz–Markov
theorem (`GromovCompactness.Topology.RMK.exists_measure_of_posLinear`) by a diagonal argument over a
dense sequence of `C(X, ℝ)`.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace GromovCompactness.Topology.RMK

variable {X : Type*} [MetricSpace X] [CompactSpace X]

theorem exists_dense_seq_continuousMap : ∃ D : ℕ → C(X, ℝ), DenseRange D := by
  exact TopologicalSpace.exists_dense_seq C(X, ℝ)

theorem exists_subseq_converges_all (a : ℕ → ℕ → ℝ) (C : ℕ → ℝ) (hb : ∀ n k, |a n k| ≤ C k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, ∃ l : ℝ, Tendsto (fun n => a (φ n) k) atTop (𝓝 l) := by
  have hK : IsCompact (Set.pi Set.univ (fun k : ℕ => Set.Icc (-C k) (C k))) :=
    isCompact_univ_pi (fun k => isCompact_Icc)
  have hmem : ∀ n, (fun k => a n k) ∈ Set.pi Set.univ (fun k : ℕ => Set.Icc (-C k) (C k)) := by
    intro n k _
    exact abs_le.mp (hb n k)
  obtain ⟨x, _, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  refine ⟨φ, hφ, fun k => ⟨x k, ?_⟩⟩
  exact tendsto_pi_nhds.mp hlim k

theorem converges_of_dense_of_bounded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℕ → E →L[ℝ] ℝ) (B : ℝ) (hT : ∀ n, ‖T n‖ ≤ B) (D : ℕ → E) (hD : DenseRange D)
    (hconv : ∀ k, ∃ l : ℝ, Tendsto (fun n => T n (D k)) atTop (𝓝 l)) (f : E) :
    ∃ l : ℝ, Tendsto (fun n => T n f) atTop (𝓝 l) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hT 0)
  suffices h : CauchySeq (fun n => T n f) from cauchySeq_tendsto_of_complete h
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hB1 : 0 < B + 1 := by linarith
  set δ := ε / (4 * (B + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨k, hk⟩ := hD.exists_dist_lt f hδpos
  obtain ⟨l, hl⟩ := hconv k
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hl.cauchySeq (ε / 2) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 : ∀ j, dist (T j f) (T j (D k)) ≤ B * δ := by
    intro j
    rw [dist_eq_norm, ← map_sub]
    calc ‖T j (f - D k)‖ ≤ ‖T j‖ * ‖f - D k‖ := (T j).le_opNorm _
      _ ≤ B * δ := by
        rw [← dist_eq_norm]
        exact mul_le_mul (hT j) hk.le dist_nonneg hB0
  have h2 := hN m hm n hn
  have hBδ : B * δ ≤ ε / 4 := by
    have hδ' : δ * (4 * (B + 1)) = ε := by
      rw [hδ]; field_simp
    have hexp : δ * (4 * (B + 1)) = 4 * (B * δ) + 4 * δ := by ring
    linarith
  have tri := dist_triangle4 (T m f) (T m (D k)) (T n (D k)) (T n f)
  have e1 := h1 m
  have e2 : dist (T n (D k)) (T n f) ≤ B * δ := by rw [dist_comm]; exact h1 n
  linarith

theorem exists_limit_functional (T : ℕ → C(X, ℝ) →ₗ[ℝ] ℝ)
    (hpos : ∀ n f, 0 ≤ f → 0 ≤ T n f)
    (hconv : ∀ f, ∃ l : ℝ, Tendsto (fun n => T n f) atTop (𝓝 l)) :
    ∃ Λ : C(X, ℝ) →ₗ[ℝ] ℝ, (∀ f, 0 ≤ f → 0 ≤ Λ f) ∧
      ∀ f, Tendsto (fun n => T n f) atTop (𝓝 (Λ f)) := by
  choose l hl using hconv
  let Λ : C(X, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := l
      map_add' := fun f g => by
        have h1 : Tendsto (fun n => T n (f + g)) atTop (𝓝 (l f + l g)) := by
          simpa [map_add] using (hl f).add (hl g)
        exact tendsto_nhds_unique (hl (f + g)) h1
      map_smul' := fun c f => by
        have h1 : Tendsto (fun n => T n (c • f)) atTop (𝓝 (c • l f)) := by
          simpa [map_smul] using (hl f).const_smul c
        simpa using tendsto_nhds_unique (hl (c • f)) h1 }
  exact ⟨Λ, fun f hf => ge_of_tendsto' (hl f) (fun n => hpos n f hf), hl⟩

theorem abs_integral_le_mass_mul_norm [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℝ)) :
    |∫ x, f x ∂μ| ≤ (μ Set.univ).toReal * ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => f x) (C := ‖f‖)
    (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x)
  rw [Real.norm_eq_abs] at h
  rw [mul_comm]
  exact h

/-- **Sequential Prokhorov compactness** on a compact metric space (Level 2). -/
theorem prokhorov_seq_compact [MeasurableSpace X] [BorelSpace X]
    (μ : ℕ → Measure X) [∀ n, IsFiniteMeasure (μ n)] (B : ℝ≥0)
    (hB : ∀ n, μ n Set.univ ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ν : Measure X, IsFiniteMeasure ν ∧ ν Set.univ ≤ B ∧
      ∀ f : C(X, ℝ), Tendsto (fun n => ∫ x, f x ∂(μ (φ n))) atTop (𝓝 (∫ x, f x ∂ν)) := by
  have hint : ∀ n (f : C(X, ℝ)), Integrable (fun x => f x) (μ n) := fun n f =>
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let Tlin : ∀ n, C(X, ℝ) →ₗ[ℝ] ℝ := fun n =>
    { toFun := fun f => ∫ x, f x ∂(μ n)
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (hint n f) (hint n g)
      map_smul' := fun c f => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
  have hmass : ∀ n, (μ n Set.univ).toReal ≤ (B : ℝ) := fun n => by
    have := ENNReal.toReal_mono ENNReal.coe_ne_top (hB n)
    simpa using this
  have hbound : ∀ n (f : C(X, ℝ)), ‖Tlin n f‖ ≤ (B : ℝ) * ‖f‖ := fun n f => by
    have h5 := abs_integral_le_mass_mul_norm (μ n) f
    rw [Real.norm_eq_abs]
    exact h5.trans (mul_le_mul_of_nonneg_right (hmass n) (norm_nonneg _))
  let T : ∀ n, C(X, ℝ) →L[ℝ] ℝ := fun n => (Tlin n).mkContinuous (B : ℝ) (hbound n)
  have hT : ∀ n, ‖T n‖ ≤ (B : ℝ) := fun n =>
    LinearMap.mkContinuous_norm_le _ B.2 _
  have hTapp : ∀ n f, T n f = ∫ x, f x ∂(μ n) := fun n f => rfl
  obtain ⟨D, hD⟩ := exists_dense_seq_continuousMap (X := X)
  obtain ⟨φ, hφ, hφconv⟩ := exists_subseq_converges_all (fun n k => T n (D k))
    (fun k => (B : ℝ) * ‖D k‖) (fun n k => by
      rw [← Real.norm_eq_abs]
      exact (T n).le_opNorm (D k) |>.trans (mul_le_mul_of_nonneg_right (hT n) (norm_nonneg _)))
  have hall : ∀ f, ∃ l : ℝ, Tendsto (fun n => T (φ n) f) atTop (𝓝 l) :=
    converges_of_dense_of_bounded (fun n => T (φ n)) (B : ℝ) (fun n => hT (φ n)) D hD hφconv
  obtain ⟨Λ, hΛpos, hΛlim⟩ := exists_limit_functional (fun n => Tlin (φ n))
    (fun n f hf => integral_nonneg (fun x => hf x)) hall
  obtain ⟨ν, hν, hνΛ⟩ := exists_measure_of_posLinear Λ hΛpos
  refine ⟨φ, hφ, ν, hν, ?_, fun f => ?_⟩
  · have h1 : Λ 1 ≤ (B : ℝ) := by
      refine le_of_tendsto' (hΛlim 1) (fun n => ?_)
      show ∫ x, (1 : C(X, ℝ)) x ∂(μ (φ n)) ≤ B
      simpa [Measure.real] using hmass (φ n)
    have h2 : (ν Set.univ).toReal ≤ (B : ℝ) := by
      have := hνΛ 1
      simpa [← this, Measure.real] using h1
    rw [← ENNReal.toReal_le_toReal (measure_ne_top ν _) ENNReal.coe_ne_top]
    simpa [Measure.real] using h2
  · rw [hνΛ f]
    exact hΛlim f

end GromovCompactness.Topology.RMK

#print axioms GromovCompactness.Topology.RMK.prokhorov_seq_compact
