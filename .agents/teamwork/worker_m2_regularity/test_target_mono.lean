import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Connected.Clopen
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness

lemma rank_e3 : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
  apply Module.one_lt_rank_of_one_lt_finrank
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  rw [hfin]
  norm_num

lemma isConnected_sphere_3 : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  isConnected_sphere rank_e3 0 (by norm_num)

instance connectedSpace_CP1 : ConnectedSpace CP1 :=
  Subtype.connectedSpace isConnected_sphere_3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

lemma continuous_dist_u (u : CP1 → M) (x : M) (h_cont : Continuous u) :
    Continuous (fun z => dist (u z) x) :=
  h_cont.dist continuous_const

lemma dist_le_of_mem_closure_preimage_ball (u : CP1 → M) (x : M) (r : ℝ)
    (h_cont : Continuous u) (z : CP1)
    (hz : z ∈ closure (u ⁻¹' (Metric.ball x r))) :
    dist (u z) x ≤ r := by
  have h_closed : IsClosed {w : CP1 | dist (u w) x ≤ r} :=
    isClosed_le (continuous_dist_u u x h_cont) continuous_const
  have h_sub : (u ⁻¹' (Metric.ball x r)) ⊆ {w : CP1 | dist (u w) x ≤ r} := by
    intro w hw
    have : dist (u w) x < r := Metric.mem_ball.mp hw
    exact le_of_lt this
  have h_clos_sub := closure_minimal h_sub h_closed
  exact h_clos_sub hz

lemma dist_eq_r_of_mem_frontier_preimage_ball (u : CP1 → M) (x : M) (r : ℝ)
    (h_cont : Continuous u) (z : CP1)
    (hz : z ∈ frontier (u ⁻¹' (Metric.ball x r))) :
    dist (u z) x = r := by
  have h_open : IsOpen (u ⁻¹' (Metric.ball x r)) := isOpen_ball.preimage h_cont
  rw [frontier, h_open.interior_eq] at hz
  have hz_clos := hz.1
  have hz_not := hz.2
  have h_le := dist_le_of_mem_closure_preimage_ball u x r h_cont z hz_clos
  have h_ge : r ≤ dist (u z) x := by
    by_contra h_lt
    push_neg at h_lt
    apply hz_not
    exact Metric.mem_ball.mpr h_lt
  exact le_antisymm h_le h_ge

lemma frontier_preimage_ball_nonempty (u : CP1 → M) (x : M) (r : ℝ) (hr : 0 < r)
    (hx : x ∈ Set.range u)
    (h_out : ∃ z, u z ∉ Metric.ball x r) :
    (frontier (u ⁻¹' (Metric.ball x r))).Nonempty := by
  rw [nonempty_frontier_iff]
  constructor
  · rcases hx with ⟨z, rfl⟩
    exact ⟨z, Metric.mem_ball_self hr⟩
  · intro h
    rcases h_out with ⟨z, hz⟩
    have : z ∈ (Set.univ : Set CP1) := mem_univ z
    rw [← h] at this
    exact hz this

theorem exists_boundary_hit (u : CP1 → M) (x : M) (r : ℝ) (hr : 0 < r)
    (h_cont : Continuous u)
    (hx : x ∈ Set.range u)
    (h_out : ∃ z, u z ∉ Metric.ball x r) :
    ∃ z : CP1, z ∈ frontier (u ⁻¹' (Metric.ball x r)) ∧ dist (u z) x = r := by
  obtain ⟨z, hz⟩ := frontier_preimage_ball_nonempty u x r hr hx h_out
  exact ⟨z, hz, dist_eq_r_of_mem_frontier_preimage_ball u x r h_cont z hz⟩

lemma continuous_of_jhol (u : CP1 → M)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    Continuous u := by
  have h_diff := h_jhol.1
  rw [contMDiffOn_univ] at h_diff
  exact h_diff.continuous

theorem test_target_monotonicity :
    ∃ (c r₀ : ℝ), 0 < c ∧ 0 < r₀ ∧
    ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) := by
  use 1, 1
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro u x r hr hr0 hx hu h_nonconst h_out
  obtain ⟨z_hit, hz_hit, hdist⟩ := exists_boundary_hit u x r hr (continuous_of_jhol I u hu) hx h_out
  sorry
