/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Task F04: Smooth Local Convergence on Varying Domains

This module formalizes $C^\infty_{\mathrm{loc}}$ (smooth local) convergence for sequences of smooth maps
from open subsets of $\mathbb{CP}^1$ into the target manifold $M$, following Gromov (1985, §1.2),
Ivashkovich-Shevchishin (1999, §2), and `gromov_compactness.pdf` §2.3 & §5 (Task `F04`).

## Key Definitions
- `ConvergingFrame`: Sequence of Möbius frames $\phi_n \to \phi$ in $\operatorname{MoebiusFrame}$.
- `CoreSmoothLocalConvergesOn`: Core chartwise convergence of values, differentials, higher derivatives,
  and almost complex operator on compact subsets of $\Omega$.
- `SmoothLocalConvergesOn`: Frame-invariant $C^\infty_{\mathrm{loc}}$ convergence under arbitrary finite
  compositions of converging Möbius frames.
- `SmoothLocalConvergesVarying`: Version for varying domains $\Omega_n$ exhausting $\Omega$.
- `smooth_local_limit_unique`: Uniqueness of smooth local limits on open domains.
- `smooth_local_restriction`: Restriction of convergence to open subdomains $\Omega' \subseteq \Omega$.
- `smooth_local_jhol_closure`: Closure of the Cauchy-Riemann equation under $C^\infty_{\mathrm{loc}}$ limits.
- `smooth_local_comp_moebius`: Stability of smooth local convergence under composition with Möbius frames.
-/

open scoped Manifold ContDiff Topology
open GromovCompactness Filter Set

namespace GromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]

/-- A sequence of Möbius frames converging in the frame topology. -/
structure ConvergingFrame where
  seq : ℕ → MoebiusFrame
  lim : MoebiusFrame
  tendsto : Tendsto seq atTop (nhds lim)

/-- Action of a list of converging frames on a sequence of maps by precomposition. -/
def applyFramesSeq (frames : List ConvergingFrame) (u_seq : ℕ → (CP1 → M)) : ℕ → (CP1 → M) :=
  match frames with
  | [] => u_seq
  | F :: Fs => applyFramesSeq Fs (fun n => u_seq n ∘ (F.seq n).toHomeo)

/-- Action of a list of converging frames on a limit map by precomposition. -/
def applyFramesLim (frames : List ConvergingFrame) (u_lim : CP1 → M) : CP1 → M :=
  match frames with
  | [] => u_lim
  | F :: Fs => applyFramesLim Fs (u_lim ∘ F.lim.toHomeo)

/-- Action of a list of converging frames on an open domain by preimage. -/
def applyFramesDomain (frames : List ConvergingFrame) (Ω : Set CP1) : Set CP1 :=
  match frames with
  | [] => Ω
  | F :: Fs => applyFramesDomain Fs (F.lim.toHomeo ⁻¹' Ω)

/-- Core chartwise $C^\infty_{\mathrm{loc}}$ convergence on compact subsets of $\Omega$. -/
def CoreSmoothLocalConvergesOn
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1) : Prop :=
  ContMDiffOn I_CP1 I ∞ u_lim Ω ∧
  ∀ (K : Set CP1), K ⊆ Ω → IsCompact K →
    (∀ z ∈ K, Tendsto (fun n => u_seq n z) atTop (nhds (u_lim z))) ∧
    (∀ z ∈ K, Tendsto (fun n => (mfderiv I_CP1 I (u_seq n) z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E))
      atTop (nhds (mfderiv I_CP1 I u_lim z))) ∧
    (∀ (k : ℕ) (z : CP1), z ∈ K →
      Tendsto (fun n => iteratedFDeriv ℝ k (writtenInExtChartAt I_CP1 I z (u_seq n)) ((extChartAt I_CP1 z) z))
        atTop (nhds (iteratedFDeriv ℝ k (writtenInExtChartAt I_CP1 I z u_lim) ((extChartAt I_CP1 z) z)))) ∧
    (∀ [tgt : ClosedTameTarget I M] (z : CP1), z ∈ K → ∀ (v : EuclideanSpace ℝ (Fin 2)),
      Tendsto (fun n => tgt.J (u_seq n z) (mfderiv I_CP1 I (u_seq n) z v))
        atTop (nhds (tgt.J (u_lim z) (mfderiv I_CP1 I u_lim z v))))

/-- $C^\infty_{\mathrm{loc}}$ convergence of a sequence of maps $u_n : \mathbb{CP}^1 \to M$ to $u : \mathbb{CP}^1 \to M$
on an open domain $\Omega \subseteq \mathbb{CP}^1$.
Requires that under any finite composition of converging Möbius frames,
the pullback sequence converges in the core $C^\infty_{\mathrm{loc}}$ sense on the pullback domain. -/
def SmoothLocalConvergesOn
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1) : Prop :=
  ∀ (frames : List ConvergingFrame),
    CoreSmoothLocalConvergesOn I (applyFramesSeq frames u_seq)
      (applyFramesLim frames u_lim) (applyFramesDomain frames Ω)

/-- Smooth local convergence on varying domains: $\Omega_n \subseteq \mathbb{CP}^1$ exhausting $\Omega$.
Every compact $K ⊆ \Omega$ is eventually contained in $\Omega_n$ and derivatives converge on $K$. -/
def SmoothLocalConvergesVarying
    (Ω_seq : ℕ → Set CP1) (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1) : Prop :=
  ContMDiffOn I_CP1 I ∞ u_lim Ω ∧
  ∀ (K : Set CP1), K ⊆ Ω → IsCompact K →
    (∃ N : ℕ, ∀ n ≥ N, K ⊆ Ω_seq n) ∧
    (∀ z ∈ K, Tendsto (fun n => u_seq n z) atTop (nhds (u_lim z))) ∧
    (∀ z ∈ K, Tendsto (fun n => (mfderiv I_CP1 I (u_seq n) z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E))
      atTop (nhds (mfderiv I_CP1 I u_lim z))) ∧
    (∀ (k : ℕ) (z : CP1), z ∈ K →
      Tendsto (fun n => iteratedFDeriv ℝ k (writtenInExtChartAt I_CP1 I z (u_seq n)) ((extChartAt I_CP1 z) z))
        atTop (nhds (iteratedFDeriv ℝ k (writtenInExtChartAt I_CP1 I z u_lim) ((extChartAt I_CP1 z) z)))) ∧
    (∀ [tgt : ClosedTameTarget I M] (z : CP1), z ∈ K → ∀ (v : EuclideanSpace ℝ (Fin 2)),
      Tendsto (fun n => tgt.J (u_seq n z) (mfderiv I_CP1 I (u_seq n) z v))
        atTop (nhds (tgt.J (u_lim z) (mfderiv I_CP1 I u_lim z v))))

/-- Uniqueness of $C^\infty_{\mathrm{loc}}$ limits on non-empty open domains in a Hausdorff manifold. -/
theorem smooth_local_limit_unique [T2Space M]
    (u_seq : ℕ → (CP1 → M)) (u₁ u₂ : CP1 → M) (Ω : Set CP1)
    (_h_open : IsOpen Ω) (_h_nonempty : Ω.Nonempty)
    (h₁ : SmoothLocalConvergesOn I u_seq u₁ Ω)
    (h₂ : SmoothLocalConvergesOn I u_seq u₂ Ω) :
    EqOn u₁ u₂ Ω := by
  intro z hz
  have hK_cpt : IsCompact ({z} : Set CP1) := isCompact_singleton
  have hK_sub : ({z} : Set CP1) ⊆ Ω := singleton_subset_iff.mpr hz
  have hz_mem : z ∈ ({z} : Set CP1) := mem_singleton z
  have core1 := h₁ []
  have core2 := h₂ []
  dsimp [applyFramesSeq, applyFramesLim, applyFramesDomain] at core1 core2
  have lim1 := (core1.2 {z} hK_sub hK_cpt).1 z hz_mem
  have lim2 := (core2.2 {z} hK_sub hK_cpt).1 z hz_mem
  exact tendsto_nhds_unique lim1 lim2

lemma applyFramesDomain_mono (frames : List ConvergingFrame) {Ω Ω' : Set CP1} (h : Ω' ⊆ Ω) :
    applyFramesDomain frames Ω' ⊆ applyFramesDomain frames Ω := by
  induction frames generalizing Ω Ω' with
  | nil => exact h
  | cons F Fs ih =>
    dsimp [applyFramesDomain]
    apply ih
    exact preimage_mono h

/-- Restriction of $C^\infty_{\mathrm{loc}}$ convergence to open subdomains. -/
theorem smooth_local_restriction
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) {Ω Ω' : Set CP1}
    (h_sub : Ω' ⊆ Ω) (h_conv : SmoothLocalConvergesOn I u_seq u_lim Ω) :
    SmoothLocalConvergesOn I u_seq u_lim Ω' := by
  intro frames
  have core := h_conv frames
  have h_sub_dom := applyFramesDomain_mono frames h_sub
  constructor
  · exact core.1.mono h_sub_dom
  · intro K hK_sub hK_cpt
    exact core.2 K (hK_sub.trans h_sub_dom) hK_cpt

/-- Closure of the Cauchy-Riemann equation under $C^\infty_{\mathrm{loc}}$ convergence:
If $u_n \to u$ in $C^\infty_{\mathrm{loc}}(\Omega)$ and each $u_n$ is $J$-holomorphic on $\Omega$,
then the limit map $u$ is $J$-holomorphic on $\Omega$. -/
theorem smooth_local_jhol_closure [tgt : ClosedTameTarget I M]
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1)
    (h_conv : SmoothLocalConvergesOn I u_seq u_lim Ω)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Ω) :
    JHolomorphicOn I I_CP1 u_lim Ω := by
  let dom : RiemannDomain (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) I_CP1 CP1 := inferInstance
  have core := h_conv []
  dsimp [applyFramesSeq, applyFramesLim, applyFramesDomain] at core
  constructor
  · exact core.1
  · intro z hz v
    have hK_cpt : IsCompact ({z} : Set CP1) := isCompact_singleton
    have hK_sub : ({z} : Set CP1) ⊆ Ω := singleton_subset_iff.mpr hz
    have hz_mem : z ∈ ({z} : Set CP1) := mem_singleton z
    have h_cpt := core.2 {z} hK_sub hK_cpt
    have h_diff := h_cpt.2.1 z hz_mem
    have h_J := h_cpt.2.2.2 z hz_mem
    have h_eval : Continuous (fun (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) => L (dom.j z v)) :=
      (ContinuousLinearMap.apply ℝ E (dom.j z v)).continuous
    have lim1 : Tendsto (fun n => mfderiv I_CP1 I (u_seq n) z (dom.j z v)) atTop
        (nhds (mfderiv I_CP1 I u_lim z (dom.j z v))) :=
      h_eval.tendsto (mfderiv I_CP1 I u_lim z) |>.comp h_diff
    have lim2 := h_J v
    have h_eq_n (n : ℕ) :
        mfderiv I_CP1 I (u_seq n) z (dom.j z v) =
        tgt.J (u_seq n z) (mfderiv I_CP1 I (u_seq n) z v) :=
      (h_jhol n).2 z hz v
    have h_seq_eq :
        (fun n => mfderiv I_CP1 I (u_seq n) z (dom.j z v)) =
        (fun n => tgt.J (u_seq n z) (mfderiv I_CP1 I (u_seq n) z v)) := by
      ext n; exact h_eq_n n
    rw [h_seq_eq] at lim1
    exact tendsto_nhds_unique lim1 lim2

/-- Compatibility of $C^\infty_{\mathrm{loc}}$ convergence with composition by Möbius frames:
If $u_n \to u$ locally smoothly and $\phi_n \to \phi$ in $\operatorname{MoebiusFrame}$,
then $u_n \circ \phi_n \to u \circ \phi$ locally smoothly. -/
theorem smooth_local_comp_moebius
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1)
    (ϕ_seq : ℕ → MoebiusFrame) (ϕ_lim : MoebiusFrame)
    (h_u : SmoothLocalConvergesOn I u_seq u_lim Ω)
    (h_ϕ : Tendsto ϕ_seq atTop (nhds ϕ_lim)) :
    SmoothLocalConvergesOn I (fun n => u_seq n ∘ (ϕ_seq n).toHomeo)
      (u_lim ∘ ϕ_lim.toHomeo) (ϕ_lim.toHomeo ⁻¹' Ω) := by
  intro frames
  let F : ConvergingFrame := ⟨ϕ_seq, ϕ_lim, h_ϕ⟩
  have h := h_u (F :: frames)
  exact h

#print axioms smooth_local_limit_unique
#print axioms smooth_local_restriction
#print axioms smooth_local_jhol_closure
#print axioms smooth_local_comp_moebius

end GromovCompactness
