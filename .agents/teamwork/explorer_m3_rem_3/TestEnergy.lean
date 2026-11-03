import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory

namespace RemediatedEnergy

open GromovCompactness

noncomputable def northPole : CP1 :=
  ⟨EuclideanSpace.single (2 : Fin 3) 1, by
    rw [mem_sphere_zero_iff_norm]
    simp [EuclideanSpace.norm_single]⟩

instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable def stereoNorth : PartialHomeomorph CP1 ℂ :=
  (stereographic' 2 northPole).transHomeomorph c_equiv_e2.toHomeomorph.symm

lemma stereoNorth_target : stereoNorth.target = Set.univ := by
  simp [stereoNorth]

/-- Remediated disk_at -/
def disk_at (a : ℂ) (r : ℝ) : Set CP1 :=
  stereoNorth.symm '' (Metric.ball a r)

noncomputable instance : MeasurableSpace CP1 := borel CP1
instance : BorelSpace CP1 := ⟨rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

noncomputable def energyMeasureExtended (I : ModelWithCorners ℝ E H) (u : CP1 → M) :
    MeasureTheory.Measure CP1 := by
  sorry

noncomputable def energyMeasure (I : ModelWithCorners ℝ E H) (u : CP1 → M) (A : Set CP1) : ℝ :=
  (energyMeasureExtended I u A).toReal

noncomputable def totalEnergy (I : ModelWithCorners ℝ E H) (u : CP1 → M) : ℝ :=
  energyMeasure I u Set.univ

theorem energy_nonneg (u : CP1 → M) (A : Set CP1) :
    0 ≤ energyMeasure I u A := by
  dsimp [energyMeasure]
  exact ENNReal.toReal_nonneg

theorem energy_additive (u : CP1 → M) {A₁ A₂ : Set CP1}
    (h_disj : Disjoint A₁ A₂) (hA₁ : MeasurableSet A₁) (hA₂ : MeasurableSet A₂) :
    energyMeasure I u (A₁ ∪ A₂) = energyMeasure I u A₁ + energyMeasure I u A₂ := by
  dsimp [energyMeasure]
  sorry

theorem energy_conformal_invariant (u : CP1 → M) (ϕ : MoebiusFrame) (A : Set CP1) :
    energyMeasure I (u ∘ ϕ.toHomeo) (ϕ.toHomeo ⁻¹' A) = energyMeasure I u A := by
  sorry

theorem energy_eq_pullback_omega (u : CP1 → M) (h_jhol : JHolomorphicOn I I_CP1 u Set.univ) (A : Set CP1) :
    energyMeasure I u A = (sorry : ℝ) := by
  sorry

theorem energy_point_null (u : CP1 → M) (p : CP1) :
    energyMeasure I u {p} = 0 := by
  sorry

theorem energy_circle_null (u : CP1 → M) (a : ℂ) (r : ℝ) (hr : 0 < r) :
    energyMeasure I u (stereoNorth.symm '' Metric.sphere a r) = 0 := by
  sorry

theorem energy_moving_disk_continuous (u : CP1 → M) (a : ℂ) :
    Continuous (fun (r : ℝ) => energyMeasure I u (disk_at a r)) := by
  sorry

structure EnergyBoundedSequence (u_seq : ℕ → (CP1 → M)) (B : ℝ) : Prop where
  bound_nonneg : 0 ≤ B
  bounded : ∀ n, totalEnergy I (u_seq n) ≤ B

end RemediatedEnergy
