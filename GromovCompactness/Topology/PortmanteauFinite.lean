import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Portmanteau for finite measures on a compact metric space

If `∫ f dμₙ → ∫ f dν` for every `f : C(X, ℝ)` (finite measures `μₙ`, `ν`), then
`limsup μₙ K ≤ ν K` for closed `K`, and `μₙ A → ν A` whenever `ν (frontier A) = 0`.
Mathlib v4.16 states the null-frontier result only for probability measures, so the finite-measure
version is proved here with real-valued estimates.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace GromovCompactness.Topology.RMK

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- Package a finite measure as a `FiniteMeasure`. -/
def ofMeasure {Y : Type*} [MeasurableSpace Y] (m : Measure Y) [IsFiniteMeasure m] :
    FiniteMeasure Y := ⟨m, inferInstance⟩

@[simp] lemma coe_ofMeasure {Y : Type*} [MeasurableSpace Y] (m : Measure Y) [IsFiniteMeasure m] :
    ((ofMeasure m : FiniteMeasure Y) : Measure Y) = m := rfl

theorem tendsto_finiteMeasure_of_integral [MeasurableSpace X] [BorelSpace X]
    (μ : ℕ → Measure X) [∀ n, IsFiniteMeasure (μ n)] (ν : Measure X) [IsFiniteMeasure ν]
    (h : ∀ f : C(X, ℝ), Tendsto (fun n => ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun n => ofMeasure (μ n)) atTop (𝓝 (ofMeasure ν)) := by
  rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  simpa using h (f : C(X, ℝ))

/-- Portmanteau, closed sets. -/
theorem limsup_closed_le_of_tendsto_integral [MeasurableSpace X] [BorelSpace X]
    (μ : ℕ → Measure X) [∀ n, IsFiniteMeasure (μ n)] (ν : Measure X) [IsFiniteMeasure ν]
    (h : ∀ f : C(X, ℝ), Tendsto (fun n => ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂ν)))
    (K : Set X) (hK : IsClosed K) : limsup (fun n => μ n K) atTop ≤ ν K :=
  FiniteMeasure.limsup_measure_closed_le_of_tendsto (tendsto_finiteMeasure_of_integral μ ν h) hK

/-- Portmanteau, null-frontier sets, finite measures. -/
theorem tendsto_measure_of_null_frontier_finite [MeasurableSpace X] [BorelSpace X]
    (μ : ℕ → Measure X) [∀ n, IsFiniteMeasure (μ n)] (ν : Measure X) [IsFiniteMeasure ν]
    (h : ∀ f : C(X, ℝ), Tendsto (fun n => ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂ν)))
    (A : Set X) (hA : ν (frontier A) = 0) : Tendsto (fun n => μ n A) atTop (𝓝 (ν A)) := by
  have hclosed := fun (K : Set X) (hK : IsClosed K) =>
    limsup_closed_le_of_tendsto_integral μ ν h K hK
  have upper : ∀ K : Set X, IsClosed K → ∀ ε > 0,
      ∀ᶠ n in atTop, (μ n K).toReal ≤ (ν K).toReal + ε := by
    intro K hK ε hε
    have hlt : limsup (fun n => μ n K) atTop < ν K + ENNReal.ofReal ε :=
      lt_of_le_of_lt (hclosed K hK)
        (ENNReal.lt_add_right (measure_ne_top ν K) (by simpa using hε))
    filter_upwards [Filter.eventually_lt_of_limsup_lt hlt] with n hn
    have h1 : (μ n K).toReal ≤ (ν K + ENNReal.ofReal ε).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top ν K, ENNReal.ofReal_ne_top⟩)
        hn.le
    simpa [ENNReal.toReal_add (measure_ne_top ν K) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hε.le] using h1
  have hmass : Tendsto (fun n => (μ n Set.univ).toReal) atTop (𝓝 (ν Set.univ).toReal) := by
    simpa using h 1
  have hsplit : ∀ (m : Measure X) [IsFiniteMeasure m] (s : Set X), MeasurableSet s →
      (m s).toReal + (m sᶜ).toReal = (m Set.univ).toReal := fun m _ s hs => by
    rw [← ENNReal.toReal_add (measure_ne_top m s) (measure_ne_top m sᶜ),
      measure_add_measure_compl hs]
  have hcl : ν (closure A) = ν A := by
    apply le_antisymm
    · calc ν (closure A) ≤ ν (A ∪ frontier A) := measure_mono (fun x hx => by
            by_cases hxA : x ∈ A
            · exact Or.inl hxA
            · exact Or.inr ⟨hx, fun hi => hxA (interior_subset hi)⟩)
        _ ≤ ν A + ν (frontier A) := measure_union_le _ _
        _ = ν A := by rw [hA, add_zero]
    · exact measure_mono subset_closure
  have hint : ν (interior A) = ν A := by
    apply le_antisymm
    · exact measure_mono interior_subset
    · calc ν A ≤ ν (interior A ∪ frontier A) := measure_mono (fun x hx => by
            by_cases hxi : x ∈ interior A
            · exact Or.inl hxi
            · exact Or.inr ⟨subset_closure hx, hxi⟩)
        _ ≤ ν (interior A) + ν (frontier A) := measure_union_le _ _
        _ = ν (interior A) := by rw [hA, add_zero]
  have hF₂ : IsClosed (interior A)ᶜ := isOpen_interior.isClosed_compl
  have hreal : Tendsto (fun n => (μ n A).toReal) atTop (𝓝 (ν A).toReal) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      set δ := ((ν A).toReal - a) / 3 with hδ
      have hδpos : 0 < δ := by rw [hδ]; linarith
      have e1 := upper (interior A)ᶜ hF₂ δ hδpos
      have e2 : ∀ᶠ n in atTop, (ν Set.univ).toReal - δ < (μ n Set.univ).toReal :=
        (tendsto_order.1 hmass).1 _ (by linarith)
      filter_upwards [e1, e2] with n hn1 hn2
      have s1 := hsplit (μ n) (interior A) isOpen_interior.measurableSet
      have s2 := hsplit ν (interior A) isOpen_interior.measurableSet
      have hmono : (μ n (interior A)).toReal ≤ (μ n A).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono interior_subset)
      have hνi : (ν (interior A)).toReal = (ν A).toReal := by rw [hint]
      linarith
    · intro b hb
      set δ := (b - (ν A).toReal) / 2 with hδ
      have hδpos : 0 < δ := by rw [hδ]; linarith
      have e1 := upper (closure A) isClosed_closure δ hδpos
      filter_upwards [e1] with n hn1
      have hmono : (μ n A).toReal ≤ (μ n (closure A)).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono subset_closure)
      have hνc : (ν (closure A)).toReal = (ν A).toReal := by rw [hcl]
      linarith
  exact (ENNReal.tendsto_toReal_iff (fun n => measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

end GromovCompactness.Topology.RMK

#print axioms GromovCompactness.Topology.RMK.limsup_closed_le_of_tendsto_integral
#print axioms GromovCompactness.Topology.RMK.tendsto_measure_of_null_frontier_finite
