/-
Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
Released under the GNU Affero General Public License v3.0 (AGPLv3) for non-commercial use;
see LICENSE.md for details.
This project is licensed under non-commercial use. If you wish to use this software in a
commercial product, service, or enterprise environment, please contact the developer to purchase
a commercial license or negotiate royalty terms.
Authors: Pablo Suárez-Serrato (November 2026)
-/

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
