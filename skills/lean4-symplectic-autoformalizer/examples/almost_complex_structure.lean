/-!
# Example: Almost Complex Structure and Symplectic Compatibility
-/

import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Topology.MetricSpace.Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable (M : Type*) [MetricSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]

/-- Fiberwise endomorphism J of TM with J^2 = -Id. -/
structure AlmostComplexStructure where
  J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x
  J_sq : ∀ (x : M) (v : TangentSpace I x), J x (J x v) = -v

/-- J is tamed by ω if ω(v, J v) > 0 for all non-zero v. -/
def IsTamed (J : AlmostComplexStructure I M) (ω : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) : Prop :=
  ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < ω x v (J.J x v)
