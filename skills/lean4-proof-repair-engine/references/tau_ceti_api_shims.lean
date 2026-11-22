/-
Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
Released under the GNU Affero General Public License v3.0 (AGPLv3) for non-commercial use;
see LICENSE.md for details.
This project is licensed under non-commercial use. If you wish to use this software in a
commercial product, service, or enterprise environment, please contact the developer to purchase
a commercial license or negotiate royalty terms.
Authors: Pablo Suárez-Serrato (November 2026)
-/

/-!
# TauCeti API Shims for Mathlib 4 Compatibility

Bridges naming and structural discrepancies between the TauCeti Symplectic Geometry
Roadmap (`TauCetiRoadmap/SymplecticGeometry`) and upstream Mathlib 4 releases.
-/

import Mathlib.Analysis.Hofer
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Geometry.Manifold.DifferentialForm
import Mathlib.Topology.MetricSpace.Basic

open Metric Set Filter

namespace TauCetiShims

/-- Shim alias for almost complex manifold structure -/
abbrev AlmostComplexManifold (M : Type*) [MetricSpace M] :=
  SympTopAutoForm.AlmostComplexStructure

/-- Direct alias for Patrick Massot's Hofer lemma -/
theorem tauceti_hofer {X : Type*} [MetricSpace X] [CompleteSpace X] (f : X → ℝ) (x : X) (ε : ℝ)
    (hε : 0 < ε) (hf : Continuous f) (hfx : 0 ≤ f x) :
    ∃ x' ε', 0 < ε' ∧ ε' ≤ ε ∧ f x ≤ f x' ∧ ∀ y, dist y x' ≤ ε' → f y ≤ 2 * f x' :=
  Mathlib.Analysis.Hofer.hofer f x ε hε hf hfx

end TauCetiShims
