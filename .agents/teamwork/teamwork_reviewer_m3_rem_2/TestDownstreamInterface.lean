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
open Metric Set MeasureTheory
open GromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

-- Check that energyMeasure type signature works with CP1
def dummyEnergy (u : CP1 → M) (A : Set CP1) (hA : MeasurableSet A) : ℝ := 0

-- Check conformal pullback with MoebiusFrame
def testConformal (u : CP1 → M) (ϕ : MoebiusFrame) (A : Set CP1) : Set CP1 :=
  ϕ.toHomeo ⁻¹' A

-- Check moving disk continuity signature
def testMovingDisk (u : CP1 → M) (a : ℂ) (r : ℝ) : Set CP1 :=
  disk_at a r

-- Check smooth local convergence signature with MoebiusFrame
def testSmoothComp (u : CP1 → M) (ϕ : MoebiusFrame) : CP1 → M :=
  u ∘ ϕ.toHomeo
