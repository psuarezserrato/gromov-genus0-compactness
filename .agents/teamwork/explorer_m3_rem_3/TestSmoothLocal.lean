import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere

open scoped Manifold ContDiff Topology
open Metric Set Filter

namespace RemediatedSmoothLocal

open GromovCompactness

instance : TopologicalSpace MoebiusFrame :=
  TopologicalSpace.induced (fun ϕ => (ϕ.toHomeo : CP1 → CP1)) inferInstance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

def SmoothLocalConvergesOn (I : ModelWithCorners ℝ E H)
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1) : Prop :=
  ∀ (K : Set CP1), K ⊆ Ω → IsCompact K →
    ∀ (k : ℕ),
      Tendsto (fun (_ : ℕ) => (sorry : ℝ)) (atTop : Filter ℕ) (nhds (sorry : ℝ))

def SmoothLocalConvergesVarying (I : ModelWithCorners ℝ E H)
    (Ω_seq : ℕ → Set CP1) (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1) : Prop :=
  ∀ (K : Set CP1), K ⊆ Ω → IsCompact K →
    (∃ N : ℕ, ∀ n ≥ N, K ⊆ Ω_seq n) ∧
    ∀ (k : ℕ), Tendsto (fun (_ : ℕ) => (sorry : ℝ)) (atTop : Filter ℕ) (nhds (sorry : ℝ))

theorem smooth_local_limit_unique
    (u_seq : ℕ → (CP1 → M)) (u₁ u₂ : CP1 → M) (Ω : Set CP1)
    (h_open : IsOpen Ω) (h_nonempty : Ω.Nonempty)
    (h₁ : SmoothLocalConvergesOn I u_seq u₁ Ω)
    (h₂ : SmoothLocalConvergesOn I u_seq u₂ Ω) :
    EqOn u₁ u₂ Ω := by
  sorry

theorem smooth_local_restriction
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) {Ω Ω' : Set CP1}
    (h_sub : Ω' ⊆ Ω) (h_conv : SmoothLocalConvergesOn I u_seq u_lim Ω) :
    SmoothLocalConvergesOn I u_seq u_lim Ω' := by
  dsimp [SmoothLocalConvergesOn] at *
  intro K hK_sub hK_cpt
  exact h_conv K (hK_sub.trans h_sub) hK_cpt

theorem smooth_local_jhol_closure [CompactSpace M] [ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1)
    (h_conv : SmoothLocalConvergesOn I u_seq u_lim Ω)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Ω) :
    JHolomorphicOn I I_CP1 u_lim Ω := by
  sorry

theorem smooth_local_comp_moebius
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1)
    (ϕ_seq : ℕ → MoebiusFrame) (ϕ_lim : MoebiusFrame)
    (h_u : SmoothLocalConvergesOn I u_seq u_lim Ω)
    (h_ϕ : Tendsto ϕ_seq atTop (nhds ϕ_lim)) :
    SmoothLocalConvergesOn I (fun n => u_seq n ∘ (ϕ_seq n).toHomeo)
      (u_lim ∘ ϕ_lim.toHomeo) (ϕ_lim.toHomeo ⁻¹' Ω) := by
  sorry

end RemediatedSmoothLocal
