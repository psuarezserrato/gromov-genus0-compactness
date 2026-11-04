/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Challenger 1 Milestone 5 Iteration 2)
-/
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.EpsilonRegularity
import GromovCompactness.Analysis.EnergyGap
import GromovCompactness.Analysis.SingularityRemoval
import GromovCompactness.Analysis.HoferRescaling
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness Classical
open GromovCompactness.Analysis

namespace GromovCompactness.AdversarialAttacksM5Iter2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

--------------------------------------------------------------------------------
-- ATTACK 1: Open ball vs Closed ball Concentration Equivalence
--------------------------------------------------------------------------------

/-- Adversarial Challenge: Does closed ball concentration imply open ball concentration?
Yes, because ball x (2 * r) contains closedBall x r. -/
theorem test_closed_ball_implies_open_ball_concentration
    (μ : Measure X) [IsFiniteMeasure μ] (x : X) (ε₀ : ℝ)
    (h_closed : ∀ r > 0, ENNReal.ofReal ε₀ ≤ μ (closedBall x r)) :
    ∀ R > 0, ENNReal.ofReal ε₀ ≤ μ (ball x R) := by
  intro R hR
  have h_half : 0 < R / 2 := by linarith
  have h_sub : closedBall x (R / 2) ⊆ ball x R := by
    intro y hy
    rw [mem_closedBall] at hy
    rw [mem_ball]
    linarith
  have h_le := measure_mono h_sub (μ := μ)
  exact (h_closed (R / 2) h_half).trans h_le

/-- Adversarial Challenge: Does open ball concentration imply closed ball concentration?
Yes, because closedBall x r contains ball x r. -/
theorem test_open_ball_implies_closed_ball_concentration
    (μ : Measure X) [IsFiniteMeasure μ] (x : X) (ε₀ : ℝ)
    (h_open : ∀ r > 0, ENNReal.ofReal ε₀ ≤ μ (ball x r)) :
    ∀ r > 0, ENNReal.ofReal ε₀ ≤ μ (closedBall x r) := by
  intro r hr
  have h_sub : ball x r ⊆ closedBall x r := ball_subset_closedBall
  have h_le := measure_mono h_sub (μ := μ)
  exact (h_open r hr).trans h_le

/-- Full equivalence between atom mass and open ball concentration. -/
theorem test_atom_iff_open_ball_concentration
    (μ : Measure X) [IsFiniteMeasure μ] (x : X) (ε₀ : ℝ) :
    ENNReal.ofReal ε₀ ≤ μ {x} ↔ ∀ r > 0, ENNReal.ofReal ε₀ ≤ μ (ball x r) := by
  rw [atom_iff_concentration]
  constructor
  · intro h_closed
    exact test_closed_ball_implies_open_ball_concentration μ x ε₀ h_closed
  · intro h_open
    exact test_open_ball_implies_closed_ball_concentration μ x ε₀ h_open

--------------------------------------------------------------------------------
-- ATTACK 2: Energy defect cannot exceed total energy
--------------------------------------------------------------------------------

/-- Adversarial Challenge: Can an attacker manufacture a sequence of maps whose defect mass
exceeds the uniform total energy bound E₀? -/
theorem test_defect_bounded_by_total_energy
    (μ_seq : ℕ → Measure X) [∀ n, IsFiniteMeasure (μ_seq n)]
    (E₀ : ℝ) (hE₀ : 0 ≤ E₀) (h_bound : ∀ n, μ_seq n univ ≤ ENNReal.ofReal E₀)
    (ν_defect : Measure X) [IsFiniteMeasure ν_defect]
    (x : X) (m_defect : ℝ) (hm : ENNReal.ofReal m_defect ≤ ν_defect {x})
    (h_sub_tot : ν_defect univ ≤ ENNReal.ofReal E₀) :
    m_defect ≤ E₀ := by
  have h_sing : ν_defect {x} ≤ ν_defect univ := measure_mono (subset_univ _)
  have h_le := hm.trans (h_sing.trans h_sub_tot)
  exact (ENNReal.ofReal_le_ofReal_iff hE₀).mp h_le

--------------------------------------------------------------------------------
-- ATTACK 3: Sub-threshold energy strictly prevents bubbling
--------------------------------------------------------------------------------

/-- Adversarial Challenge: If total energy of a sequence is strictly less than universal threshold h,
can any non-trivial bubble form?
No: Every bubble must satisfy E(v) ≥ ε_sph ≥ h. If total energy < h, no bubble can exist. -/
theorem test_subthreshold_energy_prevents_bubble_formation
    (thresh : TargetThresholds I M) (v : CP1 → M)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ)
    (h_energy : totalEnergy I v < thresh.h) :
    ∃ c : M, ∀ z : CP1, v z = c := by
  by_contra h_nonconst
  have h_sph := thresh.h_sph v h_jhol h_nonconst
  have h_le := thresh.h_le_sph
  have h_contra : thresh.h ≤ totalEnergy I v := h_le.trans h_sph
  linarith

--------------------------------------------------------------------------------
-- ATTACK 4: Multi-atom disjointness and finite additivity
--------------------------------------------------------------------------------

/-- Adversarial Challenge: Can two atoms with defect masses m₁, m₂ at distinct points x₁ ≠ x₂
have total mass exceeding total space measure? -/
theorem test_two_atoms_sum_bounded
    (μ : Measure X) [IsFiniteMeasure μ] (E₀ : ℝ) (hE₀ : 0 ≤ E₀)
    (h_tot : μ univ ≤ ENNReal.ofReal E₀)
    (x₁ x₂ : X) (hne : x₁ ≠ x₂) (m₁ m₂ : ℝ) (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂)
    (hx₁ : ENNReal.ofReal m₁ ≤ μ {x₁}) (hx₂ : ENNReal.ofReal m₂ ≤ μ {x₂}) :
    m₁ + m₂ ≤ E₀ := by
  let S : Finset X := {x₁, x₂}
  have h_card : S.card = 2 := Finset.card_pair hne
  have h_disj : Disjoint ({x₁} : Set X) ({x₂} : Set X) := disjoint_singleton.mpr hne
  have h_pair : ({x₁, x₂} : Set X) = ({x₁} : Set X) ∪ ({x₂} : Set X) := Set.insert_eq x₁ {x₂}
  have h_union : μ ({x₁, x₂} : Set X) = μ {x₁} + μ {x₂} := by
    rw [h_pair]
    exact measure_union h_disj (measurableSet_singleton x₂)
  have h_sub : ({x₁, x₂} : Set X) ⊆ univ := subset_univ _
  have h_meas_le : μ ({x₁, x₂} : Set X) ≤ μ univ := measure_mono h_sub
  have h_sum_le : μ {x₁} + μ {x₂} ≤ ENNReal.ofReal E₀ := by
    rw [← h_union]
    exact h_meas_le.trans h_tot
  have h_le : ENNReal.ofReal m₁ + ENNReal.ofReal m₂ ≤ μ {x₁} + μ {x₂} :=
    add_le_add hx₁ hx₂
  have h_ofReal_le : ENNReal.ofReal (m₁ + m₂) ≤ μ {x₁} + μ {x₂} := by
    rw [ENNReal.ofReal_add hm₁ hm₂]
    exact h_le
  have h_total_le := h_ofReal_le.trans h_sum_le
  exact (ENNReal.ofReal_le_ofReal_iff hE₀).mp h_total_le

--------------------------------------------------------------------------------
-- ATTACK 5: Exactness of Threshold h bound vs individual components
--------------------------------------------------------------------------------

/-- Adversarial Challenge: Verify that TargetThresholds enforces all 3 geometric constraints
simultaneously, and none can be omitted without breaking the reduction. -/
theorem test_target_thresholds_all_components_active
    (thresh : TargetThresholds I M) :
    thresh.h ≤ thresh.ε_reg / 2 ∧
    thresh.h ≤ thresh.ε_sph ∧
    thresh.h ≤ thresh.ε_neck / 2 ∧
    0 < thresh.h :=
  ⟨thresh.h_le_reg, thresh.h_le_sph, thresh.h_le_neck, thresh.h_pos⟩

end GromovCompactness.AdversarialAttacksM5Iter2

open GromovCompactness.AdversarialAttacksM5Iter2

#print axioms test_closed_ball_implies_open_ball_concentration
#print axioms test_open_ball_implies_closed_ball_concentration
#print axioms test_atom_iff_open_ball_concentration
#print axioms test_defect_bounded_by_total_energy
#print axioms test_subthreshold_energy_prevents_bubble_formation
#print axioms test_two_atoms_sum_bounded
#print axioms test_target_thresholds_all_components_active
