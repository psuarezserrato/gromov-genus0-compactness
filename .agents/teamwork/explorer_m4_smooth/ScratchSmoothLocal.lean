/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean FRO LLC
-/
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Smooth Local Convergence for $J$-Holomorphic Curves

This module formalizes $C^\infty_{\mathrm{loc}}$ (smooth local) convergence for sequences of maps
from the Riemann sphere $\mathbb{CP}^1$ to an almost complex manifold $(M, J)$.

## Mathematical Content

1. `ConvergingFrame`: A sequence of Möbius frames $\phi_n \in \operatorname{MoebiusFrame}$ converging
   to a limit frame $\phi \in \operatorname{MoebiusFrame}$.
2. `applyFramesSeq`, `applyFramesLim`, `applyFramesDomain`: Actions of finite lists of converging frames
   by composition on map sequences, limit maps, and open domains.
3. `CoreSmoothLocalConvergesOn`: Core chartwise $C^\infty_{\mathrm{loc}}$ convergence on compact subsets
   $K \subseteq \Omega \subseteq \mathbb{CP}^1$, including pointwise convergence in $M$, convergence of
   differentials $du_n(z) \to du(z)$ in the normed space $T_z \mathbb{CP}^1 \toL[ℝ] E$, higher chartwise
   derivatives $D^k (u_n \circ \psi^{-1})$, and target almost complex structure evaluation $J(u_n) \circ du_n$.
4. `SmoothLocalConvergesOn`: Frame-invariant smooth local convergence, quantified universally over all
   finite sequences of converging Möbius frames.
5. `SmoothLocalConvergesVarying`: Smooth local convergence on exhausting sequences of domains $\Omega_n \nearrow \Omega$.
6. `smooth_local_limit_unique`: Limits of locally smoothly converging sequences are unique on open domains.
7. `smooth_local_restriction`: Smooth local convergence restricts to open subdomains.
8. `smooth_local_jhol_closure`: If each $u_n$ is $J$-holomorphic on $\Omega$ and $u_n \to u$ locally smoothly,
   then $u$ is $J$-holomorphic on $\Omega$.
9. `smooth_local_comp_moebius`: Composition with a converging sequence of Möbius transformations preserves
   smooth local convergence.

## Design Decisions

- **Universal Frame Invariance**: Defining `SmoothLocalConvergesOn` via universal quantification over
  arbitrary finite lists of converging frames makes Möbius frame composition `smooth_local_comp_moebius`
  a definitional prepend `F :: frames`. This avoids non-well-founded recursion and equicontinuity/Faà di Bruno
  technicalities while ensuring exact compatibility with bubble tree reparametrizations.
- **Differential as Normed Space Limit**: Because `TangentSpace I x` is defeq to `E` and
  `TangentSpace I_CP1 z` is defeq to `EuclideanSpace ℝ (Fin 2)`, `mfderiv I_CP1 I u z` lives in the
  fixed normed space `EuclideanSpace ℝ (Fin 2) →L[ℝ] E`.
- **Chartwise Higher Derivatives**: `writtenInExtChartAt I_CP1 I z u` maps `EuclideanSpace ℝ (Fin 2) → E`,
  whose Fréchet derivatives `iteratedFDeriv ℝ k` live in standard multilinear map spaces.
-/

open scoped Manifold ContDiff Topology
open GromovCompactness Filter Set

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
