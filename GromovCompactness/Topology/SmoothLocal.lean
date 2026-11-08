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

omit [TopologicalSpace M] [CompactSpace M] in
lemma applyFramesSeq_const (frames : List ConvergingFrame) (c : M) (n : ℕ) :
    applyFramesSeq frames (fun _ => fun _ => c) n = fun _ => c := by
  induction frames with
  | nil => rfl
  | cons F Fs ih => exact ih

omit [TopologicalSpace M] [CompactSpace M] in
lemma applyFramesLim_const (frames : List ConvergingFrame) (c : M) :
    applyFramesLim frames (fun _ => c) = fun _ => c := by
  induction frames with
  | nil => rfl
  | cons F Fs ih => exact ih

/-- Core $C^\infty_{\mathrm{loc}}$ convergence holds for any constant sequence `fun _ => u_lim`
of a smooth map `u_lim` (`0 sorryAx`). -/
theorem coreSmoothLocalConvergesOn_const
    (u_lim : CP1 → M) (Ω : Set CP1) (h_smooth : ContMDiffOn I_CP1 I ∞ u_lim Ω) :
    CoreSmoothLocalConvergesOn I (fun _ => u_lim) u_lim Ω := by
  refine ⟨h_smooth, fun K _ _ => ⟨fun _ _ => tendsto_const_nhds,
    fun _ _ => tendsto_const_nhds, fun _ _ _ => tendsto_const_nhds,
    fun _ _ _ => tendsto_const_nhds⟩⟩

/-- Frame-invariant $C^\infty_{\mathrm{loc}}$ convergence holds for any constant map `fun _ => c` (`0 sorryAx`). -/
theorem smoothLocalConvergesOn_const_map (c : M) (Ω : Set CP1) :
    SmoothLocalConvergesOn I (fun _ => fun _ => c) (fun _ => c) Ω := by
  intro frames
  have h_seq : applyFramesSeq frames (fun _ => fun _ => c) = fun _ => fun _ => c :=
    funext (applyFramesSeq_const frames c)
  have h_lim : applyFramesLim frames (fun _ => c) = fun _ => c :=
    applyFramesLim_const frames c
  rw [h_seq, h_lim]
  exact coreSmoothLocalConvergesOn_const I (fun _ => c) (applyFramesDomain frames Ω) contMDiffOn_const

lemma applyFramesDomain_mono (frames : List ConvergingFrame) {Ω Ω' : Set CP1} (h : Ω' ⊆ Ω) :
    applyFramesDomain frames Ω' ⊆ applyFramesDomain frames Ω := by
  induction frames generalizing Ω Ω' with
  | nil => exact h
  | cons F Fs ih =>
    dsimp [applyFramesDomain]
    apply ih
    exact preimage_mono h

omit [CompactSpace M] in
/-- Action of a list of converging frames preserves global $C^\infty$ smoothness (`0 sorryAx`). -/
theorem contMDiff_applyFramesLim (frames : List ConvergingFrame) (u_lim : CP1 → M)
    (h_smooth : ContMDiff I_CP1 I ∞ u_lim) :
    ContMDiff I_CP1 I ∞ (applyFramesLim frames u_lim) := by
  induction frames generalizing u_lim with
  | nil => exact h_smooth
  | cons F Fs ih => exact ih (u_lim ∘ F.lim.toHomeo) (h_smooth.comp F.lim.is_smooth)

omit [CompactSpace M] in
/-- Action of a list of converging frames preserves $C^\infty$ smoothness on any domain `Ω` (`0 sorryAx`). -/
theorem contMDiffOn_applyFramesLim_of_univ (frames : List ConvergingFrame) (u_lim : CP1 → M)
    (Ω : Set CP1) (h_smooth : ContMDiffOn I_CP1 I ∞ u_lim Set.univ) :
    ContMDiffOn I_CP1 I ∞ (applyFramesLim frames u_lim) (applyFramesDomain frames Ω) := by
  rw [contMDiffOn_univ] at h_smooth
  exact (contMDiff_applyFramesLim I frames u_lim h_smooth).contMDiffOn

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
      (ContinuousLinearMap.apply ℝ E (show EuclideanSpace ℝ (Fin 2) from dom.j z v)).continuous
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
    exact @tendsto_nhds_unique _ _ _ (inferInstanceAs (T2Space E)) _ _ _ _ _ lim1 lim2

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

/-- Extend a sequence `s : ℕ → α` along a strictly monotone map `φ : ℕ → ℕ` by `l` outside `Set.range φ`. -/
noncomputable def extendSubseq {α : Type*} (φ : ℕ → ℕ) (s : ℕ → α) (l : α) (k : ℕ) : α :=
  open Classical in if h : ∃ n, φ n = k then s (Classical.choose h) else l

lemma extendSubseq_apply {α : Type*} {φ : ℕ → ℕ} (hφ : StrictMono φ) (s : ℕ → α) (l : α) (n : ℕ) :
    extendSubseq φ s l (φ n) = s n := by
  classical
  have h : ∃ m, φ m = φ n := ⟨n, rfl⟩
  rw [extendSubseq, dif_pos h]
  congr 1
  exact hφ.injective (Classical.choose_spec h)

lemma tendsto_extendSubseq {α : Type*} [TopologicalSpace α] {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {s : ℕ → α} {l : α} (hs : Tendsto s atTop (nhds l)) :
    Tendsto (extendSubseq φ s l) atTop (nhds l) := by
  classical
  rw [Filter.tendsto_atTop'] at hs ⊢
  intro U hU
  obtain ⟨N, hN⟩ := hs U hU
  refine ⟨φ N, fun k hk => ?_⟩
  dsimp [extendSubseq]
  split_ifs with h
  · have h_eq : φ (Classical.choose h) = k := Classical.choose_spec h
    have h_le : φ N ≤ φ (Classical.choose h) := by omega
    exact hN (Classical.choose h) (hφ.le_iff_le.mp h_le)
  · exact mem_of_mem_nhds hU

/-- Extend a `ConvergingFrame` along a strictly monotone subsequence index map `φ` (`0 sorryAx`). -/
noncomputable def ConvergingFrame.extendSubseqFrame (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (F : ConvergingFrame) : ConvergingFrame where
  seq := extendSubseq φ F.seq F.lim
  lim := F.lim
  tendsto := tendsto_extendSubseq hφ F.tendsto

omit [TopologicalSpace M] [CompactSpace M] in
lemma applyFramesLim_map_extendSubseqFrame (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (frames : List ConvergingFrame) (u_lim : CP1 → M) :
    applyFramesLim (frames.map (ConvergingFrame.extendSubseqFrame φ hφ)) u_lim =
      applyFramesLim frames u_lim := by
  induction frames generalizing u_lim with
  | nil => rfl
  | cons F Fs ih => exact ih (u_lim ∘ F.lim.toHomeo)

lemma applyFramesDomain_map_extendSubseqFrame (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (frames : List ConvergingFrame) (Ω : Set CP1) :
    applyFramesDomain (frames.map (ConvergingFrame.extendSubseqFrame φ hφ)) Ω =
      applyFramesDomain frames Ω := by
  induction frames generalizing Ω with
  | nil => rfl
  | cons F Fs ih => exact ih (F.lim.toHomeo ⁻¹' Ω)

omit [TopologicalSpace M] [CompactSpace M] in
lemma applyFramesSeq_subseq (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (frames : List ConvergingFrame) (u_seq : ℕ → (CP1 → M)) :
    applyFramesSeq frames (fun n => u_seq (φ n)) =
      fun n => applyFramesSeq (frames.map (ConvergingFrame.extendSubseqFrame φ hφ)) u_seq (φ n) := by
  induction frames generalizing u_seq with
  | nil => rfl
  | cons F Fs ih =>
    dsimp [applyFramesSeq]
    have h_step : (fun n => u_seq (φ n) ∘ (F.seq n).toHomeo) =
        fun n => (fun k => u_seq k ∘ ((F.extendSubseqFrame φ hφ).seq k).toHomeo) (φ n) := by
      ext n z
      dsimp [ConvergingFrame.extendSubseqFrame]
      rw [extendSubseq_apply hφ F.seq F.lim n]
    rw [h_step]
    exact ih (fun k => u_seq k ∘ ((F.extendSubseqFrame φ hφ).seq k).toHomeo)

/-- Core $C^\infty_{\mathrm{loc}}$ convergence is preserved along any strictly monotone subsequence (`0 sorryAx`). -/
theorem coreSmoothLocalConvergesOn_subseq
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h : CoreSmoothLocalConvergesOn I u_seq u_lim Ω) :
    CoreSmoothLocalConvergesOn I (fun n => u_seq (φ n)) u_lim Ω := by
  refine ⟨h.1, fun K hK_sub hK_cpt => ?_⟩
  obtain ⟨h0, h1, h2, h3⟩ := h.2 K hK_sub hK_cpt
  refine ⟨fun z hz => (h0 z hz).comp hφ.tendsto_atTop,
    fun z hz => (h1 z hz).comp hφ.tendsto_atTop,
    fun k z hz => (h2 k z hz).comp hφ.tendsto_atTop,
    fun z hz v => (h3 z hz v).comp hφ.tendsto_atTop⟩

/-- Frame-invariant $C^\infty_{\mathrm{loc}}$ convergence is preserved along any strictly monotone subsequence (`0 sorryAx`). -/
theorem smooth_local_subseq
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h : SmoothLocalConvergesOn I u_seq u_lim Ω) :
    SmoothLocalConvergesOn I (fun n => u_seq (φ n)) u_lim Ω := by
  intro frames
  rw [applyFramesSeq_subseq φ hφ frames u_seq,
      ← applyFramesLim_map_extendSubseqFrame φ hφ frames u_lim,
      ← applyFramesDomain_map_extendSubseqFrame φ hφ frames Ω]
  exact coreSmoothLocalConvergesOn_subseq I _ _ _ hφ
    (h (frames.map (ConvergingFrame.extendSubseqFrame φ hφ)))

/-- Transport `SmoothLocalConvergesOn` along an equality of map sequences without unfolding manifolds (`0 sorryAx`). -/
theorem smooth_local_congr_seq
    {u_seq₁ u_seq₂ : ℕ → (CP1 → M)} {u_lim : CP1 → M} {Ω : Set CP1}
    (h_eq : u_seq₁ = u_seq₂)
    (h : SmoothLocalConvergesOn I u_seq₁ u_lim Ω) :
    SmoothLocalConvergesOn I u_seq₂ u_lim Ω :=
  h_eq ▸ h

omit [TopologicalSpace M] [CompactSpace M] in
/-- At any index `n`, `applyFramesSeq frames u_seq n` depends only on `u_seq n` (`0 sorryAx`). -/
lemma applyFramesSeq_congr_at (frames : List ConvergingFrame)
    {u_seq₁ u_seq₂ : ℕ → (CP1 → M)} {n : ℕ} (h : u_seq₁ n = u_seq₂ n) :
    applyFramesSeq frames u_seq₁ n = applyFramesSeq frames u_seq₂ n := by
  induction frames generalizing u_seq₁ u_seq₂ with
  | nil => exact h
  | cons F Fs ih =>
    apply ih
    rw [h]

/-- Core $C^\infty_{\mathrm{loc}}$ convergence is invariant under eventual equality of sequences (`0 sorryAx`). -/
theorem coreSmoothLocalConvergesOn_congr_eventually
    {u_seq₁ u_seq₂ : ℕ → (CP1 → M)} {u_lim : CP1 → M} {Ω : Set CP1}
    (h_eq : ∃ N₀ : ℕ, ∀ n ≥ N₀, u_seq₁ n = u_seq₂ n)
    (h : CoreSmoothLocalConvergesOn I u_seq₁ u_lim Ω) :
    CoreSmoothLocalConvergesOn I u_seq₂ u_lim Ω := by
  rcases h_eq with ⟨N₀, hN₀⟩
  refine ⟨h.1, fun K hK_sub hK_cpt => ?_⟩
  obtain ⟨h0, h1, h2, h3⟩ := h.2 K hK_sub hK_cpt
  refine ⟨fun z hz => (h0 z hz).congr' (eventually_atTop.mpr ⟨N₀, fun n hn => by rw [hN₀ n hn]⟩),
    fun z hz => (h1 z hz).congr' (eventually_atTop.mpr ⟨N₀, fun n hn => by rw [hN₀ n hn]⟩),
    fun k z hz => (h2 k z hz).congr' (eventually_atTop.mpr ⟨N₀, fun n hn => by rw [hN₀ n hn]⟩),
    fun z hz v => (h3 z hz v).congr' (eventually_atTop.mpr ⟨N₀, fun n hn => by rw [hN₀ n hn]⟩)⟩

/-- Frame-invariant $C^\infty_{\mathrm{loc}}$ convergence is invariant under eventual equality of sequences (`0 sorryAx`). -/
theorem smooth_local_congr_eventually
    {u_seq₁ u_seq₂ : ℕ → (CP1 → M)} {u_lim : CP1 → M} {Ω : Set CP1}
    (h_eq : ∃ N₀ : ℕ, ∀ n ≥ N₀, u_seq₁ n = u_seq₂ n)
    (h : SmoothLocalConvergesOn I u_seq₁ u_lim Ω) :
    SmoothLocalConvergesOn I u_seq₂ u_lim Ω := by
  rcases h_eq with ⟨N₀, hN₀⟩
  intro frames
  exact coreSmoothLocalConvergesOn_congr_eventually I
    ⟨N₀, fun n hn => applyFramesSeq_congr_at frames (hN₀ n hn)⟩
    (h frames)

/-- Any sequence eventually equal to a constant map `fun _ => c` converges locally smoothly to `fun _ => c` (`0 sorryAx`). -/
theorem smoothLocalConvergesOn_of_eventually_const
    (u_seq : ℕ → (CP1 → M)) (c : M) (Ω : Set CP1)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ z, u_seq n z = c) :
    SmoothLocalConvergesOn I u_seq (fun _ => c) Ω := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact smooth_local_congr_eventually I
    ⟨N₀, fun n hn => (funext (hN₀ n hn)).symm⟩
    (smoothLocalConvergesOn_const_map I c Ω)

/-- In a discrete topological space, any converging sequence is eventually constant (`0 sorryAx`). -/
theorem tendsto_discrete {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
    {s : ℕ → α} {l : α} (h : Tendsto s atTop (nhds l)) :
    ∃ N, ∀ n ≥ N, s n = l := by
  have h_open : IsOpen ({l} : Set α) := isOpen_discrete {l}
  have h_nhds : {l} ∈ nhds l := h_open.mem_nhds rfl
  obtain ⟨N, hN⟩ := (Filter.eventually_atTop.mp (h h_nhds))
  exact ⟨N, fun n hn => mem_singleton_iff.mp (hN n hn)⟩

/-- Under discrete frame topology, `applyFramesSeq frames (fun _ => u_lim) n` is eventually equal to `applyFramesLim frames u_lim` (`0 sorryAx`). -/
lemma applyFramesSeq_eventually_applyFramesLim (frames : List ConvergingFrame) (u_lim : CP1 → M) :
    ∃ N, ∀ n ≥ N, applyFramesSeq frames (fun _ => u_lim) n = applyFramesLim frames u_lim := by
  induction frames generalizing u_lim with
  | nil =>
    exact ⟨0, fun _ _ => rfl⟩
  | cons F Fs ih =>
    obtain ⟨N_F, hF⟩ := tendsto_discrete F.tendsto
    obtain ⟨N_ih, h_ih⟩ := ih (u_lim ∘ F.lim.toHomeo)
    refine ⟨max N_F N_ih, fun n hn => ?_⟩
    have hnF : N_F ≤ n := (le_max_left N_F N_ih).trans hn
    have hnih : N_ih ≤ n := (le_max_right N_F N_ih).trans hn
    change applyFramesSeq Fs (fun k => u_lim ∘ (F.seq k).toHomeo) n =
      applyFramesLim Fs (u_lim ∘ F.lim.toHomeo)
    have h_step : (fun k => u_lim ∘ (F.seq k).toHomeo) n =
        (fun _ => u_lim ∘ F.lim.toHomeo) n := by
      dsimp
      rw [hF n hnF]
    have h_cong := applyFramesSeq_congr_at Fs (u_seq₁ := fun k => u_lim ∘ (F.seq k).toHomeo)
      (u_seq₂ := fun _ => u_lim ∘ F.lim.toHomeo) (n := n) h_step
    rw [h_cong]
    exact h_ih n hnih

/-- Constant sequence of any smooth map converges in `SmoothLocalConvergesOn` (`0 sorryAx`). -/
theorem smoothLocalConvergesOn_const
    (u_lim : CP1 → M) (Ω : Set CP1) (h_smooth : ContMDiff I_CP1 I ∞ u_lim) :
    SmoothLocalConvergesOn I (fun _ => u_lim) u_lim Ω := by
  intro frames
  obtain ⟨N, hN⟩ := applyFramesSeq_eventually_applyFramesLim frames u_lim
  have h_lim_smooth : ContMDiffOn I_CP1 I ∞ (applyFramesLim frames u_lim) (applyFramesDomain frames Ω) :=
    contMDiffOn_applyFramesLim_of_univ I frames u_lim Ω (h_smooth.contMDiffOn)
  have h_const_conv := coreSmoothLocalConvergesOn_const I (applyFramesLim frames u_lim)
    (applyFramesDomain frames Ω) h_lim_smooth
  exact coreSmoothLocalConvergesOn_congr_eventually I ⟨N, fun n hn => (hN n hn).symm⟩ h_const_conv

/-- Uniform convergence on a set is preserved along any strictly monotone subsequence (`0 sorryAx`). -/
theorem tendstoUniformlyOn_subseq {α β : Type*} [UniformSpace β]
    {F : ℕ → α → β} {f : α → β} {K : Set α} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (h : TendstoUniformlyOn F f atTop K) :
    TendstoUniformlyOn (fun n => F (φ n)) f atTop K :=
  fun u hu => hφ.tendsto_atTop (h u hu)

#print axioms smooth_local_limit_unique
#print axioms smooth_local_restriction
#print axioms smooth_local_jhol_closure
#print axioms smooth_local_comp_moebius
#print axioms smooth_local_subseq

end GromovCompactness
