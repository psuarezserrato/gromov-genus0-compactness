import GromovCompactness
import GromovCompactness.Analysis.HoferRescaling

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness
open GromovCompactness.Analysis
open GromovCompactness.Bubbling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

#print axioms GromovCompactness.Bubbling.exists_target_thresholds_of_modules
#print axioms GromovCompactness.Bubbling.exists_calibrated_rescaling_of_ivt
#print axioms GromovCompactness.Bubbling.exists_calibrated_rescaling

namespace VerifyChallengeQueries

theorem challenge_query_B01_reduction
    (ε_reg C_reg : ℝ) (h_reg_pos : 0 < ε_reg) (h_Creg_pos : 0 < C_reg)
    (h_reg : ∀ (u : CP1 → M) (a : ℂ) (r : ℝ) (_ : 0 < r),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (disk_at a r) < ε_reg →
      ∀ z ∈ disk_at a (r / 2),
        riemannianEnergyDensity I u z ≤ C_reg * r^(-2 : ℝ) * energyMeasure I u (disk_at a r))
    (ε_sph : ℝ) (h_sph_pos : 0 < ε_sph)
    (h_sph : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ε_sph ≤ totalEnergy I u)
    (C_neck a_decay ε_neck : ℝ)
    (h_Cneck_pos : 0 < C_neck) (h_a_pos : 0 < a_decay) (h_neck_pos : 0 < ε_neck)
    (h_neck : ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      0 < r → 2 * r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r R) < ε_neck →
      ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
        energyMeasure I u (annulus_at center r₁ r₂) ≤
          C_neck * ((r / r₁)^a_decay + (r₂ / R)^a_decay) * energyMeasure I u (annulus_at center r R)) :
    Nonempty (GromovCompactness.Bubbling.TargetThresholds I M) :=
  GromovCompactness.Bubbling.exists_target_thresholds_of_modules I ε_reg C_reg h_reg_pos h_Creg_pos h_reg
    ε_sph h_sph_pos h_sph C_neck a_decay ε_neck h_Cneck_pos h_a_pos h_neck_pos h_neck

theorem challenge_query_B02
    (u_seq : ℕ → (CP1 → M)) (thresh : GromovCompactness.Bubbling.TargetThresholds I M)
    (m_defect : ℝ) (hm : thresh.h ≤ m_defect)
    (h_jhol : ∀ (n : ℕ), JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_defect : ∀ (n : ℕ), ∃ (a_n : ℂ) (R_n : ℝ),
      dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
      0 < R_n ∧ R_n ≤ 1 / ((n : ℝ) + 1) ∧
      m_defect - thresh.h / 2 ≤ energyMeasure I (u_seq n) (disk_at a_n R_n))
    (h_ivt : GromovCompactness.Bubbling.RadialEnergyIVT I (M := M)) :
    Nonempty (GromovCompactness.Bubbling.CalibratedRescaling I u_seq thresh m_defect) :=
  GromovCompactness.Bubbling.exists_calibrated_rescaling I u_seq thresh m_defect hm h_jhol h_defect h_ivt

#print axioms challenge_query_B01_reduction
#print axioms challenge_query_B02

end VerifyChallengeQueries
