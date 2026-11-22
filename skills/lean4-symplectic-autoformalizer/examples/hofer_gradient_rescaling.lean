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
# Example: Hofer Gradient Rescaling for Pseudo-Holomorphic Curves
-/

import Mathlib.Analysis.Hofer
import Mathlib.Topology.MetricSpace.Basic

open Metric

variable {X : Type*} [MetricSpace X] [CompleteSpace X]

/-- Rescaling helper synthesizing Patrick Massot's Hofer lemma. -/
theorem hofer_gradient_rescaling (f : X → ℝ) (hf : Continuous f) (x : X) (ε : ℝ)
    (hε : 0 < ε) (hfx : 0 ≤ f x) :
    ∃ x' : X, ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ f x ≤ f x' ∧ ∀ y ∈ closedBall x' ε', f y ≤ 2 * f x' := by
  obtain ⟨x', ε', hε'_pos, hε'_le, hf_le, h_bound⟩ := Mathlib.Analysis.Hofer.hofer f x ε hε hf hfx
  exact ⟨x', ε', hε'_pos, hε'_le, hf_le, fun y hy => h_bound y hy⟩
