import GromovCompactness.Geometry.Sphere
import GromovCompactness.Geometry.Target

open scoped Manifold ContDiff Topology
open GromovCompactness

#synth MeasurableSpace CP1
#synth BorelSpace CP1
#synth IsManifold I_CP1 ∞ CP1
#synth TopologicalSpace MoebiusFrame

noncomputable example : MeasurableSpace CP1 := inferInstance
example : BorelSpace CP1 := inferInstance
example : IsManifold I_CP1 ∞ CP1 := inferInstance
example : TopologicalSpace MoebiusFrame := inferInstance
