import GromovCompactness.Vendor.RieszMarkovKakutani

open MeasureTheory Filter Topology
open scoped NNReal ENNReal CompactlySupported

namespace GromovCompactness.Topology.RMK

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- A4: Riesz–Markov for a compact metric space. -/
theorem exists_measure_of_posLinear [MeasurableSpace X] [BorelSpace X]
    (Λ : C(X, ℝ) →ₗ[ℝ] ℝ) (hΛ : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ Λ f) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ ∀ f : C(X, ℝ), ∫ x, f x ∂μ = Λ f := by
  -- identify `C(X, ℝ)` with `C_c(X, ℝ)` (X is compact)
  let toC : C(X, ℝ) → C_c(X, ℝ) := fun f => ⟨f, HasCompactSupport.of_compactSpace f⟩
  let Λ' : C_c(X, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun g => Λ g.toContinuousMap
      map_add' := fun g h => by
        rw [← map_add]; rfl
      map_smul' := fun c g => by
        rw [RingHom.id_apply, ← map_smul]; rfl }
  have hΛ' : ∀ g : C_c(X, ℝ), 0 ≤ g → 0 ≤ Λ' g := fun g hg => hΛ g.toContinuousMap hg
  refine ⟨RealRMK.rieszMeasure hΛ', ?_, fun f => ?_⟩
  · refine ⟨?_⟩
    have h := RealRMK.rieszMeasure_le_of_eq_one hΛ' (f := toC 1) (fun x => zero_le_one)
      (isCompact_univ : IsCompact (Set.univ : Set X)) (fun x _ => rfl)
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  · have := RealRMK.integral_rieszMeasure hΛ' (toC f)
    simpa [Λ', toC] using this

end GromovCompactness.Topology.RMK

#print axioms GromovCompactness.Topology.RMK.exists_measure_of_posLinear
