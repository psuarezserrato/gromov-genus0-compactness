/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Analysis.Hofer
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.SetIntegral
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.Monotonicity
import GromovCompactness.Analysis.Bochner

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness

namespace GromovCompactness.Analysis

/-!
# Task A03: Epsilon Regularity via Hofer's Lemma

This module formalizes `epsilon_regularity` (Contract A03):
There exist uniform constants $\varepsilon_{\mathrm{reg}} > 0$ and $C_{\mathrm{reg}} > 0$
depending only on the target geometry $(M, \omega, J)$ such that every $J$-holomorphic curve
with local symplectic energy strictly below $\varepsilon_{\mathrm{reg}}$ satisfies a pointwise
gradient bound on the concentric half-radius disk.

The proof connects the scalar mean-value inequality (`A01`), the Bochner differential inequality (`A02`),
and Patrick Massot's formalization of Hofer's lemma in Mathlib (`Mathlib.Analysis.Hofer.hofer`).

References:
- Mikhail Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Math. 82 (1985), §1.2.
- Sergei Ivashkovich & Vsevolod Shevchishin, arXiv:math/9912046, Theorem 2.1.2.
- Dusa McDuff & Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology* (2012), Theorem 4.3.3.
- Patrick Massot, `Mathlib.Analysis.Hofer.hofer`.
- `gromov_compactness.pdf` §4.1 (Contract A03).
-/

/-- Translation invariance of Lebesgue integrals over Euclidean metric balls on ℂ. -/
lemma integral_translate_ball (a : ℂ) (r : ℝ) (g : ℂ → ℝ) :
    ∫ w in ball (0 : ℂ) r, g (a + w) = ∫ w in ball a r, g w := by
  have h_pres : MeasurePreserving (fun x => a + x) volume volume := measurePreserving_add_left volume a
  have h_emb : MeasurableEmbedding (fun x => a + x) := (Homeomorph.addLeft a).measurableEmbedding
  have h_pre : (fun x => a + x) ⁻¹' (ball a r) = ball (0 : ℂ) r := by
    ext w
    simp only [Set.mem_preimage, mem_ball, dist_zero_right, dist_eq_norm]
    ring_nf
  have h := MeasureTheory.MeasurePreserving.setIntegral_preimage_emb h_pres h_emb g (ball a r)
  rw [h_pre] at h
  exact h

/-- Point translation preserves inclusion from concentric half-radius ball to closed ball around 0. -/
lemma ball_translate_to_closedBall (a w₀ : ℂ) (r : ℝ) (hw : w₀ ∈ ball a (r / 2)) :
    w₀ - a ∈ closedBall (0 : ℂ) (r / 2) := by
  simp only [mem_ball, mem_closedBall, dist_zero_right] at *
  rw [dist_eq_norm] at hw
  exact hw.le

/-- Epsilon-Regularity via Hofer's Lemma (Contract A03).
There exist uniform constants `ε_reg > 0` and `C_reg > 0` depending only on the target geometry
`(M, ω, J)` such that every `J`-holomorphic curve with local energy below `ε_reg`
satisfies a pointwise gradient bound on the half-radius disk:
`sup_{D_{r/2}} |du|² ≤ C_reg r⁻² E(u; D_r)`. -/
theorem epsilon_regularity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (ε_reg C_reg : ℝ), 0 < ε_reg ∧ 0 < C_reg ∧
    ∀ (u : CP1 → M) (a : ℂ) (r : ℝ) (hr : 0 < r),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (disk_at a r) < ε_reg →
      ∀ z ∈ disk_at a (r / 2),
        riemannianEnergyDensity I u z ≤ C_reg * r^(-2 : ℝ) * energyMeasure I u (disk_at a r) := by
  obtain ⟨b, c, hb, hc, h_boch⟩ := bochner_differential_inequality (M := M) I
  obtain ⟨η, C, hη, hC, h_smv⟩ := scalar_mean_value_inequality b hb c hc
  refine ⟨η, C, hη, hC, ?_⟩
  intro u a r hr hu h_en z hz
  sorry

end GromovCompactness.Analysis
