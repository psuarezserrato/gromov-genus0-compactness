import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import GromovCompactness.Geometry.Sphere

open Metric Set MeasureTheory

namespace Remediated

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

noncomputable instance : MeasurableSpace CP1 := borel CP1
instance : BorelSpace CP1 := ⟨rfl⟩

instance : TopologicalSpace MoebiusFrame :=
  TopologicalSpace.induced (fun ϕ => (ϕ.toHomeo : CP1 → CP1)) inferInstance

/-- Disk of radius r centered at a ∈ ℂ in CP1 via stereographic projection -/
def disk_at (a : ℂ) (r : ℝ) : Set CP1 :=
  stereoNorth.symm '' (Metric.ball a r)

/-- Annulus $A(r, R; a) = \{z \in \mathbb{C} : r < |z - a| < R\} \subset \mathbb{CP}^1$. -/
def annulus_at (a : ℂ) (r R : ℝ) : Set CP1 :=
  stereoNorth.symm '' {z : ℂ | r < dist z a ∧ dist z a < R}

/-- Concentric circle boundary of radius r centered at a ∈ ℂ in CP1. -/
def circle_at (a : ℂ) (r : ℝ) : Set CP1 :=
  stereoNorth.symm '' (Metric.sphere a r)

lemma disk_at_mono (a : ℂ) {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) : disk_at a r₁ ⊆ disk_at a r₂ := by
  dsimp [disk_at]
  exact image_subset _ (Metric.ball_subset_ball h)

lemma north_pole_not_mem_disk_at (a : ℂ) (r : ℝ) : northPole ∉ disk_at a r := by
  intro h
  rcases h with ⟨w, hw, hw_eq⟩
  have h_source := stereoNorth.map_target (show w ∈ stereoNorth.target by simp [stereoNorth])
  rw [hw_eq] at h_source
  dsimp [stereoNorth] at h_source
  simp only [PartialHomeomorph.transHomeomorph_source, stereographic'_source] at h_source
  exact h_source rfl

lemma north_pole_not_mem_annulus_at (a : ℂ) (r R : ℝ) : northPole ∉ annulus_at a r R := by
  intro h
  rcases h with ⟨w, hw, hw_eq⟩
  have h_source := stereoNorth.map_target (show w ∈ stereoNorth.target by simp [stereoNorth])
  rw [hw_eq] at h_source
  dsimp [stereoNorth] at h_source
  simp only [PartialHomeomorph.transHomeomorph_source, stereographic'_source] at h_source
  exact h_source rfl

lemma is_open_disk_at (a : ℂ) (r : ℝ) : IsOpen (disk_at a r) := by
  dsimp [disk_at]
  apply stereoNorth.isOpen_image_symm_of_subset_target isOpen_ball
  rw [stereoNorth_target]
  exact subset_univ _

lemma is_open_annulus_at (a : ℂ) (r R : ℝ) : IsOpen (annulus_at a r R) := by
  dsimp [annulus_at]
  have h_open : IsOpen {z : ℂ | r < dist z a ∧ dist z a < R} := by
    exact isOpen_Ioo.preimage (continuous_id.dist continuous_const)
  apply stereoNorth.isOpen_image_symm_of_subset_target h_open
  rw [stereoNorth_target]
  exact subset_univ _

lemma measurable_set_disk_at (a : ℂ) (r : ℝ) : MeasurableSet (disk_at a r) :=
  (is_open_disk_at a r).measurableSet

lemma center_mem_disk_at (a : ℂ) {r : ℝ} (hr : 0 < r) : stereoNorth.symm a ∈ disk_at a r := by
  dsimp [disk_at]
  exact mem_image_of_mem stereoNorth.symm (Metric.mem_ball_self hr)

lemma annulus_subset_disk (a : ℂ) (r R : ℝ) : annulus_at a r R ⊆ disk_at a R := by
  dsimp [annulus_at, disk_at]
  apply image_subset
  intro z hz
  exact hz.2

#print axioms disk_at_mono
#print axioms north_pole_not_mem_disk_at
#print axioms is_open_disk_at
#print axioms is_open_annulus_at
#print axioms measurable_set_disk_at
#print axioms center_mem_disk_at
#print axioms annulus_subset_disk

end Remediated
