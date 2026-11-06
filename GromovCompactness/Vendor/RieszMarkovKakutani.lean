/-
Vendored backport of the real-valued Riesz–Markov–Kakutani theorem to Mathlib v4.16.0.

Provenance: Mathlib commit 0c2287c997d441f56da560642ceae6bf40271350 (2025-04-12, PR #12290, Lean v4.19.0-rc2):
  Mathlib/Order/Interval/Set/Union.lean
  Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Basic.lean
  Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean
plus the helper lemmas `exists_add_of_le`, `toReal`, `toRealLinearMap`, `toNNRealLinear` (from
Mathlib/Topology/ContinuousMap/CompactlySupported.lean at that commit) and `Content.mk_apply`
(from Mathlib/MeasureTheory/Measure/Content.lean at that commit), which are absent in v4.16.0.
Copyright (c) 2022-2025 Jesse Reimann, Kalle Kytölä, Yoh Tanimoto, Oliver Butterley.
Released under Apache 2.0 license as described in the Mathlib LICENSE file.

NOTE: do not import `Mathlib.MeasureTheory.Integral.RieszMarkovKakutani` together with this module
(both define `rieszContent`, `rieszContentAux` at root namespace).
-/
import Mathlib.MeasureTheory.Measure.Content
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Data.Finset.Range
import Mathlib.Data.Set.Lattice

section CSAdd
open scoped NNReal CompactlySupported
namespace CompactlySupportedContinuousMap
variable {α : Type*} [TopologicalSpace α]

protected lemma exists_add_of_le {f₁ f₂ : C_c(α, ℝ≥0)} (h : f₁ ≤ f₂) : ∃ (g : C_c(α, ℝ≥0)),
    f₁ + g = f₂ := by
  refine ⟨⟨f₂.1 - f₁.1, ?_⟩, ?_⟩
  · apply (f₁.hasCompactSupport'.union f₂.hasCompactSupport').of_isClosed_subset isClosed_closure
    rw [tsupport, tsupport, ← closure_union]
    apply closure_mono
    intro x hx
    contrapose! hx
    simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, Set.mem_union, Function.mem_support,
      ne_eq, not_or, Decidable.not_not, ContinuousMap.coe_sub, Pi.sub_apply] at hx ⊢
    simp [hx.1, hx.2]
  · ext x
    simpa [← NNReal.coe_add] using add_tsub_cancel_of_le (h x)



/-- The compactly supported continuous `ℝ≥0`-valued function as a compactly supported `ℝ`-valued
function. -/
noncomputable def toReal (f : C_c(α, ℝ≥0)) : C_c(α, ℝ) :=
  f.compLeft ContinuousMap.coeNNRealReal

@[simp]
lemma toReal_apply (f : C_c(α, ℝ≥0)) (x : α) : f.toReal x = f x := compLeft_apply rfl _ _

@[simp] lemma toReal_nonneg {f : C_c(α, ℝ≥0)} : 0 ≤ f.toReal := fun _ ↦ by simp

@[simp] lemma toReal_add (f g : C_c(α, ℝ≥0)) : (f + g).toReal = f.toReal + g.toReal := by ext; simp
@[simp] lemma toReal_smul (r : ℝ≥0) (f : C_c(α, ℝ≥0)) : (r • f).toReal = r • f.toReal := by
  ext; simp [NNReal.smul_def]

lemma nnrealPart_sub_nnrealPart_neg (f : C_c(α, ℝ)) :
    (nnrealPart f).toReal - (nnrealPart (-f)).toReal = f := by
  ext x
  simp

/-- The compactly supported continuous `ℝ≥0`-valued function as a compactly supported `ℝ`-valued
function. -/
noncomputable def toRealLinearMap : C_c(α, ℝ≥0) →ₗ[ℝ≥0] C_c(α, ℝ) where
  toFun := toReal
  map_add' f g := by ext x; simp
  map_smul' a f := by ext x; simp [NNReal.smul_def]

@[simp, norm_cast]
lemma coe_toRealLinearMap : (toRealLinearMap : C_c(α, ℝ≥0) → C_c(α, ℝ)) = toReal := rfl

lemma toRealLinearMap_apply (f : C_c(α, ℝ≥0)) : toRealLinearMap f = f.toReal := rfl

lemma toRealLinearMap_apply_apply (f : C_c(α, ℝ≥0)) (x : α) :
    toRealLinearMap f x = (f x).toReal := by simp

/-- For a positive linear functional `Λ : C_c(α, ℝ) → ℝ`, define a `ℝ≥0`-linear map. -/
noncomputable def toNNRealLinear (Λ : C_c(α, ℝ) →ₗ[ℝ] ℝ) (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f) :
    C_c(α, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 where
  toFun f := ⟨Λ (toRealLinearMap f), hΛ _ <| by simp⟩
  map_add' f g := by ext; simp
  map_smul' a f := by ext; simp [NNReal.smul_def]

@[simp]
lemma toNNRealLinear_apply (Λ : C_c(α, ℝ) →ₗ[ℝ] ℝ) (hΛ) (f : C_c(α, ℝ≥0)) :
    toNNRealLinear Λ hΛ f = Λ (toReal f) := rfl

@[simp] lemma toNNRealLinear_inj (Λ₁ Λ₂ : C_c(α, ℝ) →ₗ[ℝ] ℝ) (hΛ₁ hΛ₂) :
    toNNRealLinear Λ₁ hΛ₁ = toNNRealLinear Λ₂ hΛ₂ ↔ Λ₁ = Λ₂ := by
  simp only [LinearMap.ext_iff, NNReal.eq_iff, toNNRealLinear_apply]
  refine ⟨fun h f ↦ ?_, fun h f ↦ by rw [LinearMap.ext h]⟩
  rw [← nnrealPart_sub_nnrealPart_neg f]
  simp_rw [map_sub, h]

end CompactlySupportedContinuousMap
end CSAdd

namespace MeasureTheory.Content
open scoped NNReal ENNReal
@[simp]
lemma mk_apply {G : Type*} [TopologicalSpace G] (toFun : TopologicalSpace.Compacts G → ℝ≥0)
    (mono' sup_disjoint' sup_le') (K : TopologicalSpace.Compacts G) :
    (Content.mk toFun mono' sup_disjoint' sup_le') K = toFun K := rfl
end MeasureTheory.Content

section VUnion

/-!
# Extra lemmas about unions of intervals

This file contains lemmas about finite unions of intervals which can't be included with the lemmas
concerning infinite unions in `Order.Interval.Set.Disjoint` because we use `Finset.range`.
-/

open Set

/-- Union of consecutive intervals contains the interval defined by the initial and final points. -/
theorem Ioc_subset_biUnion_Ioc {X : Type*} [LinearOrder X] (N : ℕ) (a : ℕ → X) :
    Ioc (a 0) (a N) ⊆ ⋃ i ∈ Finset.range N, Ioc (a i) (a (i + 1)) := by
  induction N with
  | zero => simp
  | succ N ih => calc
    _ ⊆ Ioc (a 0) (a N) ∪ Ioc (a N) (a (N + 1)) := Ioc_subset_Ioc_union_Ioc
    _ ⊆ _ := by simpa [Finset.range_succ] using union_subset_union_right (Ioc (a N) (a (N + 1))) ih

/-- Union of consecutive intervals contains the interval defined by the initial and final points. -/
theorem Ico_subset_biUnion_Ico {X : Type*} [LinearOrder X] (N : ℕ) (a : ℕ → X) :
    Ico (a 0) (a N) ⊆ ⋃ i ∈ Finset.range N, Ico (a i) (a (i + 1)) := by
  induction N with
  | zero => simp
  | succ N ih => calc
    _ ⊆ Ico (a 0) (a N) ∪ Ico (a N) (a (N + 1)) := Ico_subset_Ico_union_Ico
    _ ⊆ _ := by simpa [Finset.range_succ] using union_subset_union_right (Ico (a N) (a (N + 1))) ih

end VUnion


/-!
#  Riesz–Markov–Kakutani representation theorem

This file will prove the Riesz-Markov-Kakutani representation theorem on a locally compact
T2 space `X`. As a special case, the statements about linear functionals on bounded continuous
functions follows.

To make use of the existing API, the measure is constructed from a content `λ` on the
compact subsets of a locally compact space X, rather than the usual construction of open sets in the
literature.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/


noncomputable section

open scoped BoundedContinuousFunction NNReal ENNReal
open Set Function TopologicalSpace CompactlySupported CompactlySupportedContinuousMap
  MeasureTheory

variable {X : Type*} [TopologicalSpace X]
variable (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0)

/-! ### Construction of the content: -/

section Monotone

lemma CompactlySupportedContinuousMap.monotone_of_nnreal : Monotone Λ := by
  intro f₁ f₂ h
  obtain ⟨g, hg⟩ := CompactlySupportedContinuousMap.exists_add_of_le h
  rw [← hg]
  simp

/-- The positivity of a linear functional `Λ` implies that `Λ` is monotone. -/
lemma CompactlySupportedContinuousMap.monotone_of_nonneg {Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ}
    (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f) : Monotone Λ := by
  intro f₁ f₂ h
  have : 0 ≤ Λ (f₂ - f₁) := by
    apply hΛ
    intro x
    simp only [coe_zero, Pi.zero_apply, coe_sub, Pi.sub_apply, sub_nonneg]
    exact h x
  calc Λ f₁ ≤ Λ f₁ + Λ (f₂ - f₁) := by exact (le_add_iff_nonneg_right (Λ f₁)).mpr this
  _ =  Λ (f₁ + (f₂ - f₁)) := by exact Eq.symm (LinearMap.map_add Λ f₁ (f₂ - f₁))
  _ = Λ f₂ := by congr; exact add_sub_cancel f₁ f₂

end Monotone

/-- Given a positive linear functional `Λ` on continuous compactly supported functions on `X`
with values in `ℝ≥0`, for `K ⊆ X` compact define `λ(K) = inf {Λf | 1≤f on K}`.
When `X` is a locally compact T2 space, this will be shown to be a
content, and will be shown to agree with the Riesz measure on the compact subsets `K ⊆ X`. -/
def rieszContentAux : Compacts X → ℝ≥0 := fun K =>
  sInf (Λ '' { f : C_c(X, ℝ≥0) | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x })

section RieszMonotone

variable [T2Space X] [LocallyCompactSpace X]

/-- For any compact subset `K ⊆ X`, there exist some compactly supported continuous nonnegative
functions `f` on `X` such that `f ≥ 1` on `K`. -/
theorem rieszContentAux_image_nonempty (K : Compacts X) :
    (Λ '' { f : C_c(X, ℝ≥0) | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x }).Nonempty := by
  rw [image_nonempty]
  obtain ⟨V, hVcp, hKsubintV⟩ := exists_compact_superset K.2
  have hIsCompact_closure_interior : IsCompact (closure (interior V)) := by
    apply IsCompact.of_isClosed_subset hVcp isClosed_closure
    nth_rw 2 [← closure_eq_iff_isClosed.mpr (IsCompact.isClosed hVcp)]
    exact closure_mono interior_subset
  obtain ⟨f, hsuppfsubV, hfeq1onK, hfinicc⟩ :=
    exists_tsupport_one_of_isOpen_isClosed isOpen_interior hIsCompact_closure_interior
      (IsCompact.isClosed K.2) hKsubintV
  have hfHasCompactSupport : HasCompactSupport f :=
    IsCompact.of_isClosed_subset hVcp (isClosed_tsupport f)
      (Set.Subset.trans hsuppfsubV interior_subset)
  use nnrealPart ⟨f, hfHasCompactSupport⟩
  intro x hx
  apply le_of_eq
  simp only [nnrealPart_apply, CompactlySupportedContinuousMap.coe_mk]
  rw [← Real.toNNReal_one, Real.toNNReal_eq_toNNReal_iff (zero_le_one' ℝ) (hfinicc x).1]
  exact hfeq1onK.symm hx

/-- Riesz content `λ` (associated with a positive linear functional `Λ`) is
monotone: if `K₁ ⊆ K₂` are compact subsets in `X`, then `λ(K₁) ≤ λ(K₂)`. -/
theorem rieszContentAux_mono {K₁ K₂ : Compacts X} (h : K₁ ≤ K₂) :
    rieszContentAux Λ K₁ ≤ rieszContentAux Λ K₂ :=
  csInf_le_csInf (OrderBot.bddBelow _) (rieszContentAux_image_nonempty Λ K₂)
    (image_subset Λ (setOf_subset_setOf.mpr fun _ f_hyp x x_in_K₁ => f_hyp x (h x_in_K₁)))

end RieszMonotone

section RieszSubadditive

/-- Any compactly supported continuous nonnegative `f` such that `f ≥ 1` on `K` gives an upper bound
on the content of `K`; namely `λ(K) ≤ Λ f`. -/
theorem rieszContentAux_le {K : Compacts X} {f : C_c(X, ℝ≥0)} (h : ∀ x ∈ K, (1 : ℝ≥0) ≤ f x) :
    rieszContentAux Λ K ≤ Λ f :=
  csInf_le (OrderBot.bddBelow _) ⟨f, ⟨h, rfl⟩⟩

variable [T2Space X] [LocallyCompactSpace X]

/-- The Riesz content can be approximated arbitrarily well by evaluating the positive linear
functional on test functions: for any `ε > 0`, there exists a compactly supported continuous
nonnegative function `f` on `X` such that `f ≥ 1` on `K` and such that `λ(K) ≤ Λ f < λ(K) + ε`. -/
theorem exists_lt_rieszContentAux_add_pos (K : Compacts X) {ε : ℝ≥0} (εpos : 0 < ε) :
    ∃ f : C_c(X, ℝ≥0), (∀ x ∈ K, (1 : ℝ≥0) ≤ f x) ∧ Λ f < rieszContentAux Λ K + ε := by
  --choose a test function `f` s.t. `Λf = α < λ(K) + ε`
  obtain ⟨α, ⟨⟨f, f_hyp⟩, α_hyp⟩⟩ :=
    exists_lt_of_csInf_lt (rieszContentAux_image_nonempty Λ K)
      (lt_add_of_pos_right (rieszContentAux Λ K) εpos)
  refine ⟨f, f_hyp.left, ?_⟩
  rw [f_hyp.right]
  exact α_hyp

/-- The Riesz content `λ` associated to a given positive linear functional `Λ` is
finitely subadditive: `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)` for any compact subsets `K₁, K₂ ⊆ X`. -/
theorem rieszContentAux_sup_le (K1 K2 : Compacts X) :
    rieszContentAux Λ (K1 ⊔ K2) ≤ rieszContentAux Λ K1 + rieszContentAux Λ K2 := by
  apply _root_.le_of_forall_pos_le_add
  intro ε εpos
  --get test functions s.t. `λ(Ki) ≤ Λfi ≤ λ(Ki) + ε/2, i=1,2`
  obtain ⟨f1, f_test_function_K1⟩ := exists_lt_rieszContentAux_add_pos Λ K1 (half_pos εpos)
  obtain ⟨f2, f_test_function_K2⟩ := exists_lt_rieszContentAux_add_pos Λ K2 (half_pos εpos)
  --let `f := f1 + f2` test function for the content of `K`
  have f_test_function_union : ∀ x ∈ K1 ⊔ K2, (1 : ℝ≥0) ≤ (f1 + f2) x := by
    rintro x (x_in_K1 | x_in_K2)
    · exact le_add_right (f_test_function_K1.left x x_in_K1)
    · exact le_add_left (f_test_function_K2.left x x_in_K2)
  --use that `Λf` is an upper bound for `λ(K1⊔K2)`
  apply (rieszContentAux_le Λ f_test_function_union).trans (le_of_lt _)
  rw [map_add]
  --use that `Λfi` are lower bounds for `λ(Ki) + ε/2`
  apply lt_of_lt_of_le (_root_.add_lt_add f_test_function_K1.right f_test_function_K2.right)
    (le_of_eq _)
  rw [add_assoc, add_comm (ε / 2), add_assoc, add_halves ε, add_assoc]

end RieszSubadditive


section PartitionOfUnity

variable [T2Space X] [LocallyCompactSpace X]

lemma exists_continuous_add_one_of_isCompact_nnreal
    {s₀ s₁ : Set X} {t : Set X} (s₀_compact : IsCompact s₀) (s₁_compact : IsCompact s₁)
    (t_compact : IsCompact t) (disj : Disjoint s₀ s₁) (hst : s₀ ∪ s₁ ⊆ t) :
    ∃ (f₀ f₁ : C_c(X, ℝ≥0)), EqOn f₀ 1 s₀ ∧ EqOn f₁ 1 s₁ ∧ EqOn (f₀ + f₁) 1 t := by
  set so : Fin 2 → Set X := fun j => if j = 0 then s₀ᶜ else s₁ᶜ with hso
  have soopen (j : Fin 2) :  IsOpen (so j) := by
    fin_cases j
    · simp only [hso, Fin.zero_eta, Fin.isValue, ↓reduceIte, isOpen_compl_iff]
      exact IsCompact.isClosed <| s₀_compact
    · simp only [hso, Fin.isValue, Fin.mk_one, one_ne_zero, ↓reduceIte, isOpen_compl_iff]
      exact IsCompact.isClosed <| s₁_compact
  have hsot : t ⊆ ⋃ j, so j := by
    rw [hso]
    simp only [Fin.isValue]
    intro x hx
    rw [mem_iUnion]
    rw [← subset_compl_iff_disjoint_right, ← compl_compl s₀, compl_subset_iff_union] at disj
    have h : x ∈ s₀ᶜ ∨ x ∈ s₁ᶜ := by
      rw [← mem_union, disj]
      exact mem_univ _
    apply Or.elim h
    · intro h0
      use 0
      simp only [Fin.isValue, ↓reduceIte]
      exact h0
    · intro h1
      use 1
      simp only [Fin.isValue, one_ne_zero, ↓reduceIte]
      exact h1
  obtain ⟨f, f_supp_in_so, sum_f_one_on_t, f_in_icc, f_hcs⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact soopen t_compact hsot
  use (nnrealPart (⟨f 1, f_hcs 1⟩ : C_c(X, ℝ))),
    (nnrealPart (⟨f 0, f_hcs 0⟩ : C_c(X, ℝ)))
  simp only [Fin.isValue, CompactlySupportedContinuousMap.coe_add]
  have sum_one_x (x : X) (hx : x ∈ t) : (f 0) x + (f 1) x = 1 := by
    simpa only [Finset.sum_apply, Fin.sum_univ_two, Fin.isValue, Pi.one_apply]
      using sum_f_one_on_t hx
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [Fin.isValue, nnrealPart_apply,
      CompactlySupportedContinuousMap.coe_mk, Pi.one_apply, Real.toNNReal_eq_one]
    have : (f 0) x = 0 := by
      rw [← nmem_support]
      have : s₀ ⊆ (tsupport (f 0))ᶜ := by
        apply subset_trans _ (compl_subset_compl.mpr (f_supp_in_so 0))
        rw [hso]
        simp only [Fin.isValue, ↓reduceIte, compl_compl, subset_refl]
      apply not_mem_of_mem_compl
      exact mem_of_subset_of_mem (subset_trans this (compl_subset_compl_of_subset subset_closure))
        hx
    rw [union_subset_iff] at hst
    rw [← sum_one_x x (mem_of_subset_of_mem hst.1 hx), this]
    exact Eq.symm (AddZeroClass.zero_add ((f 1) x))
  · intro x hx
    simp only [Fin.isValue, nnrealPart_apply,
      CompactlySupportedContinuousMap.coe_mk, Pi.one_apply, Real.toNNReal_eq_one]
    have : (f 1) x = 0 := by
      rw [← nmem_support]
      have : s₁ ⊆ (tsupport (f 1))ᶜ := by
        apply subset_trans _ (compl_subset_compl.mpr (f_supp_in_so 1))
        rw [hso]
        simp only [Fin.isValue, one_ne_zero, ↓reduceIte, compl_compl, subset_refl]
      apply not_mem_of_mem_compl
      exact mem_of_subset_of_mem (subset_trans this (compl_subset_compl_of_subset subset_closure))
        hx
    rw [union_subset_iff] at hst
    rw [← sum_one_x x (mem_of_subset_of_mem hst.2 hx), this]
    exact Eq.symm (AddMonoid.add_zero ((f 0) x))
  · intro x hx
    simp only [Fin.isValue, Pi.add_apply, nnrealPart_apply,
      CompactlySupportedContinuousMap.coe_mk, Pi.one_apply]
    rw [Real.toNNReal_add_toNNReal (f_in_icc 1 x).1 (f_in_icc 0 x).1, add_comm]
    simp only [Fin.isValue, Real.toNNReal_eq_one]
    exact sum_one_x x hx

end PartitionOfUnity

section RieszContentAdditive

variable [T2Space X] [LocallyCompactSpace X]

lemma rieszContentAux_union {K₁ K₂ : TopologicalSpace.Compacts X}
    (disj : Disjoint (K₁ : Set X) K₂) :
    rieszContentAux Λ (K₁ ⊔ K₂) = rieszContentAux Λ K₁ + rieszContentAux Λ K₂ := by
  refine le_antisymm (rieszContentAux_sup_le Λ K₁ K₂) ?_
  refine le_csInf (rieszContentAux_image_nonempty Λ (K₁ ⊔ K₂)) ?_
  intro b ⟨f, ⟨hf, Λf_eq_b⟩⟩
  have hsuppf : ∀ x ∈ K₁ ⊔ K₂, x ∈ support f := by
    intro x hx
    rw [mem_support]
    exact ne_of_gt <| lt_of_lt_of_le (zero_lt_one' ℝ≥0) (hf x hx)
  have hsubsuppf : (K₁ : Set X) ∪ (K₂ : Set X) ⊆ tsupport f := subset_trans hsuppf subset_closure
  obtain ⟨g₁, g₂, hg₁, hg₂, sum_g⟩ := exists_continuous_add_one_of_isCompact_nnreal K₁.isCompact'
    K₂.isCompact' f.hasCompactSupport'.isCompact disj hsubsuppf
  have f_eq_sum : f = g₁ * f + g₂ * f := by
    ext x
    simp only [CompactlySupportedContinuousMap.coe_add, CompactlySupportedContinuousMap.coe_mul,
      Pi.add_apply, Pi.mul_apply, NNReal.coe_add, NNReal.coe_mul,
      Eq.symm (RightDistribClass.right_distrib _ _ _), ← NNReal.coe_add, ← Pi.add_apply]
    by_cases h : f x = 0
    · rw [h]
      simp only [NNReal.coe_zero, NNReal.coe_add, mul_zero]
    · push_neg at h
      simp only [CompactlySupportedContinuousMap.coe_add, ContinuousMap.toFun_eq_coe,
        CompactlySupportedContinuousMap.coe_toContinuousMap] at sum_g
      rw [sum_g (mem_of_subset_of_mem subset_closure (mem_support.mpr h))]
      simp only [Pi.one_apply, NNReal.coe_one, one_mul]
  rw [← Λf_eq_b, f_eq_sum, map_add]
  have aux₁ : ∀ x ∈ K₁, 1 ≤ (g₁ * f) x := by
    intro x x_in_K₁
    simp [hg₁ x_in_K₁, hf x (mem_union_left _ x_in_K₁)]
  have aux₂ : ∀ x ∈ K₂, 1 ≤ (g₂ * f) x := by
    intro x x_in_K₂
    simp [hg₂ x_in_K₂, hf x (mem_union_right _ x_in_K₂)]
  exact add_le_add (rieszContentAux_le Λ aux₁) (rieszContentAux_le Λ aux₂)

end RieszContentAdditive

section RieszContentRegular

variable [T2Space X] [LocallyCompactSpace X]

/-- The content induced by the linear functional `Λ`. -/
noncomputable def rieszContent (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0) : Content X where
  toFun := rieszContentAux Λ
  mono' := fun _ _ ↦ rieszContentAux_mono Λ
  sup_disjoint' := fun _ _ disj _ _ ↦ rieszContentAux_union Λ disj
  sup_le' := rieszContentAux_sup_le Λ

lemma rieszContent_ne_top {K : Compacts X} : rieszContent Λ K ≠ ⊤ := by
  simp [rieszContent, ne_eq, ENNReal.coe_ne_top, not_false_eq_true]

lemma contentRegular_rieszContent : (rieszContent Λ).ContentRegular := by
  intro K
  simp only [rieszContent, le_antisymm_iff, le_iInf_iff, ENNReal.coe_le_coe, Content.mk_apply]
  refine ⟨fun K' hK' ↦ rieszContentAux_mono Λ (hK'.trans interior_subset), ?_⟩
  rw [iInf_le_iff]
  intro b hb
  rw [rieszContentAux, ENNReal.le_coe_iff]
  have : b < ⊤ := by
    obtain ⟨F, hF⟩ := exists_compact_superset K.2
    exact (le_iInf_iff.mp (hb ⟨F, hF.1⟩) hF.2).trans_lt ENNReal.coe_lt_top
  refine ⟨b.toNNReal, (ENNReal.coe_toNNReal this.ne).symm, NNReal.coe_le_coe.mp ?_⟩
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  lift ε to ℝ≥0 using hε.le
  obtain ⟨f, hfleoneonK, hfle⟩ := exists_lt_rieszContentAux_add_pos Λ K (Real.toNNReal_pos.mpr hε)
  rw [rieszContentAux, Real.toNNReal_of_nonneg hε.le, ← NNReal.coe_lt_coe] at hfle
  refine ((le_iff_forall_one_lt_le_mul₀ (zero_le (Λ f))).mpr fun α hα ↦ ?_).trans hfle.le
  rw [mul_comm, ← smul_eq_mul, ← map_smul]
  set K' := f ⁻¹' Ici α⁻¹
  have hKK' : ↑K ⊆ interior K' :=
    subset_interior_iff.2 ⟨f ⁻¹' Ioi α⁻¹, isOpen_Ioi.preimage f.1.2,
      fun x hx ↦ (inv_lt_one_of_one_lt₀ hα).trans_le (hfleoneonK x hx),
      preimage_mono Ioi_subset_Ici_self⟩
  have hK'cp : IsCompact K' := .of_isClosed_subset f.2 (isClosed_Ici.preimage f.1.2) fun x hx ↦
    subset_closure ((inv_pos_of_pos <| zero_lt_one.trans hα).trans_le hx).ne'
  set hb' := hb ⟨K', hK'cp⟩
  simp only [Compacts.coe_mk, le_iInf_iff] at hb'
  exact (ENNReal.toNNReal_mono (by simp) <| hb' hKK').trans <| csInf_le'
    ⟨α • f, fun x ↦ (inv_le_iff_one_le_mul₀' (zero_lt_one.trans hα)).mp, by simp⟩

end RieszContentRegular

namespace NNRealRMK

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- `rieszContent` gives a `Content` from `Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0`. Here `rieszContent Λ` is
promoted to a measure. It will be later shown that
`∫ (x : X), f x ∂(rieszMeasure Λ hΛ) = Λ f` for all `f : C_c(X, ℝ≥0)`. -/
def rieszMeasure := (rieszContent Λ).measure

lemma le_rieszMeasure_of_isCompact_tsupport_subset {f : C_c(X, ℝ≥0)} (hf : ∀ x, f x ≤ 1)
    {K : Set X} (hK : IsCompact K) (h : tsupport f ⊆ K) : .ofNNReal (Λ f) ≤ rieszMeasure Λ K := by
  rw [← TopologicalSpace.Compacts.coe_mk K hK]
  simp only [rieszMeasure, Content.measure_eq_content_of_regular (rieszContent Λ)
    (contentRegular_rieszContent Λ)]
  simp only [rieszContent, ENNReal.ofReal_coe_nnreal, ENNReal.coe_le_coe, Content.mk_apply]
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  obtain ⟨g, hg⟩ := exists_lt_rieszContentAux_add_pos Λ ⟨K, hK⟩ hε
  apply le_trans _ hg.2.le
  apply monotone_of_nnreal Λ
  intro x
  simp only [ContinuousMap.toFun_eq_coe, CompactlySupportedContinuousMap.coe_toContinuousMap]
  by_cases hx : x ∈ tsupport f
  · exact le_trans (hf x) (hg.1 x (Set.mem_of_subset_of_mem h hx))
  · rw [image_eq_zero_of_nmem_tsupport hx]
    exact zero_le (g x)

lemma le_rieszMeasure_of_tsupport_subset {f : C_c(X, ℝ≥0)} (hf : ∀ x, f x ≤ 1) {V : Set X}
    (h : tsupport f ⊆ V) : .ofNNReal (Λ f) ≤ rieszMeasure Λ V := by
  apply le_trans _ (measure_mono h)
  apply le_rieszMeasure_of_isCompact_tsupport_subset Λ hf f.hasCompactSupport
  exact subset_rfl

end NNRealRMK



/-!
# Riesz–Markov–Kakutani representation theorem for real-linear functionals

The Riesz–Markov–Kakutani representation theorem relates linear functionals on spaces of continuous
functions on a locally compact space to measures.

There are many closely related variations of the theorem. This file contains that proof of the
version where the space is a locally compact T2 space, the linear functionals are real and the
continuous functions have compact support.

## Main definitions & statements

* `RealRMK.rieszMeasure`: the measure induced by a real linear positive functional.
* `RealRMK.integral_rieszMeasure`: the Riesz–Markov–Kakutani representation theorem for a real
  linear positive functional.

## Implementation notes

The measure is defined through `rieszContent` which is for `NNReal` using the `toNNRealLinear`
version of `Λ`.

The Riesz–Markov–Kakutani representation theorem is first proved for `Real`-linear `Λ` because
equality is proven using two inequalities by considering `Λ f` and `Λ (-f)` for all functions
`f`, yet on `C_c(X, ℝ≥0)` there is no negation.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]
-/

open scoped ENNReal
open CompactlySupported CompactlySupportedContinuousMap Filter Function Set Topology
  TopologicalSpace MeasureTheory

namespace RealRMK

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X]
  [BorelSpace X]
variable {Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ} (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)

/-- The measure induced for `Real`-linear positive functional `Λ`, defined through `toNNRealLinear`
and the `NNReal`-version of `rieszContent`. This is under the namespace `RealRMK`, while
`rieszMeasure` without namespace is for `NNReal`-linear `Λ`. -/
noncomputable def rieszMeasure := (rieszContent (toNNRealLinear Λ hΛ)).measure

/-- If `f` assumes values between `0` and `1` and the support is contained in `V`, then
`Λ f ≤ rieszMeasure V`. -/
lemma le_rieszMeasure_tsupport_subset {f : C_c(X, ℝ)} (hf : ∀ (x : X), 0 ≤ f x ∧ f x ≤ 1)
    {V : Set X} (hV : tsupport f ⊆ V) : ENNReal.ofReal (Λ f) ≤ rieszMeasure hΛ V := by
  apply le_trans _ (measure_mono hV)
  have := Content.measure_eq_content_of_regular (rieszContent (toNNRealLinear Λ hΛ))
    (contentRegular_rieszContent (toNNRealLinear Λ hΛ)) (⟨tsupport f, f.hasCompactSupport⟩)
  rw [← Compacts.coe_mk (tsupport f) f.hasCompactSupport, rieszMeasure, this, rieszContent,
    ENNReal.ofReal_eq_coe_nnreal (hΛ f fun x ↦ (hf x).1), Content.mk_apply, ENNReal.coe_le_coe]
  apply le_iff_forall_pos_le_add.mpr
  intro _ hε
  obtain ⟨g, hg⟩ := exists_lt_rieszContentAux_add_pos (toNNRealLinear Λ hΛ)
    ⟨tsupport f, f.hasCompactSupport⟩ (Real.toNNReal_pos.mpr hε)
  simp_rw [NNReal.val_eq_coe, Real.toNNReal_coe] at hg
  refine le_of_lt (lt_of_le_of_lt (monotone_of_nonneg hΛ ?_) hg.2)
  intro x
  by_cases hx : x ∈ tsupport f
  · simpa using le_trans (hf x).2 (hg.1 x hx)
  · simp [image_eq_zero_of_nmem_tsupport hx]

/-- If `f` assumes the value `1` on a compact set `K` then `rieszMeasure K ≤ Λ f`. -/
lemma rieszMeasure_le_of_eq_one {f : C_c(X, ℝ)} (hf : ∀ x, 0 ≤ f x) {K : Set X}
    (hK : IsCompact K) (hfK : ∀ x ∈ K, f x = 1) : rieszMeasure hΛ K ≤ ENNReal.ofReal (Λ f) := by
  rw [show K = Compacts.mk K hK by exact rfl, rieszMeasure,
    Content.measure_eq_content_of_regular _ (contentRegular_rieszContent (toNNRealLinear Λ hΛ))]
  apply ENNReal.coe_le_iff.mpr
  intro p hp
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_eq_ofReal_iff (hΛ f hf) NNReal.zero_le_coe] at hp
  apply csInf_le'
  rw [Set.mem_image]
  use f.nnrealPart
  simp_rw [Set.mem_setOf_eq, nnrealPart_apply, Real.one_le_toNNReal]
  refine ⟨(fun x hx ↦ Eq.ge (hfK x hx)), ?_⟩
  apply NNReal.eq
  rw [toNNRealLinear_apply, show f.nnrealPart.toReal = f by ext z; simp [hf z], hp]

omit [T2Space X] [LocallyCompactSpace X] in
/-- Given `f : C_c(X, ℝ)` such that `range f ⊆ [a, b]` we obtain a partition of the support of `f`
determined by partitioning `[a, b]` into `N` pieces. -/
lemma range_cut_partition (f : C_c(X, ℝ)) (a : ℝ) {ε : ℝ} (hε : 0 < ε) (N : ℕ)
    (hf : range f ⊆ Ioo a (a + N * ε)) : ∃ (E : Fin N → Set X), tsupport f = ⋃ j, E j ∧
    univ.PairwiseDisjoint E ∧ (∀ n : Fin N, ∀ x ∈ E n, a + ε * n < f x ∧ f x ≤ a + ε * (n + 1)) ∧
    ∀ n : Fin N, MeasurableSet (E n) := by
  let b := a + N * ε
  let y : Fin N → ℝ := fun n ↦ a + ε * (n + 1)
  -- By definition `y n` and `y m` are separated by at least `ε`.
  have hy {n m : Fin N} (h : n < m) : y n + ε ≤ y m := calc
    _ ≤ a + ε * m + ε := by
      exact add_le_add_three (by rfl) ((mul_le_mul_iff_of_pos_left hε).mpr (by norm_cast)) (by rfl)
    _ = _ := by dsimp [y]; rw [mul_add, mul_one, add_assoc]
  -- Define `E n` as the inverse image of the interval `(y n - ε, y n]`.
  let E (n : Fin N) := (f ⁻¹' Ioc (y n - ε) (y n)) ∩ (tsupport f)
  use E
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The sets `E n` are a partition of the support of `f`.
    have partition_aux : range f ⊆ ⋃ n, Ioc (y n - ε) (y n) := calc
      _ ⊆ Ioc (a + (0 : ℕ) * ε) (a + N * ε) := by
        intro _ hz
        simpa using Ioo_subset_Ioc_self (hf hz)
      _ ⊆ ⋃ i ∈ Finset.range N, Ioc (a + ↑i * ε) (a + ↑(i + 1) * ε) :=
        Ioc_subset_biUnion_Ioc N (fun n ↦ a + n * ε)
      _ ⊆ _ := by
        intro z
        simp only [Finset.mem_range, mem_iUnion, mem_Ioc, forall_exists_index, and_imp, y]
        refine fun n hn _ _ ↦ ⟨⟨n, hn⟩, ⟨by linarith, by simp_all [mul_comm ε _]⟩⟩
    simp only [E, ← iUnion_inter, ← preimage_iUnion, eq_comm (a := tsupport _), inter_eq_right]
    exact fun x _ ↦ partition_aux (mem_range_self x)
  · -- The sets `E n` are pairwise disjoint.
    intro m _ n _ hmn
    apply Disjoint.preimage
    simp_rw [mem_preimage, mem_Ioc, disjoint_left]
    intro x hx
    rw [mem_setOf_eq, and_assoc] at hx
    simp_rw [mem_setOf_eq, not_and_or, not_lt, not_le, or_assoc]
    rcases (by omega : m < n ∨ n < m) with hc | hc
    · left
      exact le_trans hx.2.1 (le_tsub_of_add_le_right (hy hc))
    · right; left
      exact lt_of_le_of_lt (le_tsub_of_add_le_right (hy hc)) hx.1
  · -- Upper and lower bound on `f x` follow from the definition of `E n` .
    intro _ _ hx
    simp only [mem_inter_iff, mem_preimage, mem_Ioc, E, y] at hx
    constructor <;> linarith
  · exact fun _ ↦ (f.1.measurable measurableSet_Ioc).inter measurableSet_closure

omit [LocallyCompactSpace X] in
/-- Given a set `E`, a function `f : C_c(X, ℝ)`, `0 < ε` and `∀ x ∈ E, f x < c`, there exists an
open set `V` such that `E ⊆ V` and the sets are similar in measure and `∀ x ∈ V, f x < c`. -/
lemma exists_open_approx (f : C_c(X, ℝ)) {ε : ℝ} (hε : 0 < ε) (E : Set X) {μ : Content X}
    (hμ : μ.outerMeasure E ≠ ∞) (hμ' : MeasurableSet E) {c : ℝ} (hfE : ∀ x ∈ E, f x < c):
    ∃ (V : Opens X), E ⊆ V ∧ (∀ x ∈ V, f x < c) ∧ μ.measure V ≤ μ.measure E + ENNReal.ofReal ε := by
  have hε' := ne_of_gt <| Real.toNNReal_pos.mpr hε
  obtain ⟨V₁ : Opens X, hV₁⟩ := Content.outerMeasure_exists_open μ hμ hε'
  let V₂ : Opens X := ⟨(f ⁻¹' Iio c), IsOpen.preimage f.1.2 isOpen_Iio⟩
  use V₁ ⊓ V₂
  refine ⟨subset_inter hV₁.1 hfE, ?_, ?_⟩
  · intro x hx
    suffices ∀ x ∈ V₂.carrier, f x < c from this x (mem_of_mem_inter_right hx)
    exact fun _ a ↦ a
  · calc
      _ ≤ μ.measure V₁ := by simp [measure_mono]
      _ = μ.outerMeasure V₁ := Content.measure_apply μ (V₁.2.measurableSet)
      _ ≤ μ.outerMeasure E + ε.toNNReal := hV₁.2
      _ = _ := by rw [Content.measure_apply μ hμ']; congr;

/-- Choose `N` sufficiently large such that a particular quantity is small. -/
private lemma exists_nat_large (a' b' : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ (N : ℕ), 0 < N ∧
    a' / N * (b' + a' / N) ≤ ε := by
  have A : Tendsto (fun (N : ℝ) ↦ a' / N * (b' + a' / N)) atTop (𝓝 (0 * (b' + 0))) := by
    apply Tendsto.mul
    · exact Tendsto.div_atTop tendsto_const_nhds tendsto_id
    · exact Tendsto.add tendsto_const_nhds (Tendsto.div_atTop tendsto_const_nhds tendsto_id)
  have B := A.comp tendsto_natCast_atTop_atTop
  simp only [add_zero, zero_mul] at B
  obtain ⟨N, hN, h'N⟩ := (((tendsto_order.1 B).2 _ hε ).and (Ici_mem_atTop 1)).exists
  exact ⟨N, h'N, hN.le⟩

/-- The main estimate in the proof of the Riesz-Markov-Kakutani: `Λ f` is bounded above by the
integral of `f` with respect to the `rieszMeasure` associated to `Λ`. -/
private lemma integral_riesz_aux (f : C_c(X, ℝ)) : Λ f ≤ ∫ x, f x ∂(rieszMeasure hΛ) := by
  let μ := rieszMeasure hΛ
  let K := tsupport f
  -- Suffices to show that `Λ f ≤ ∫ x, f x ∂μ + ε` for arbitrary `ε`.
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  -- Choose an interval `(a, b)` which contains the range of `f`.
  obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, a < b ∧ range f ⊆ Ioo a b := by
    obtain ⟨r, hr⟩ := (Metric.isCompact_iff_isClosed_bounded.mp
      (HasCompactSupport.isCompact_range f.2 f.1.2)).2.subset_ball_lt 0 0
    exact ⟨-r, r, by linarith, hr.2.trans_eq (by simp [Real.ball_eq_Ioo])⟩
  -- Choose `N` positive and sufficiently large such that `ε'` is sufficiently small
  obtain ⟨N, hN, hε'⟩ := exists_nat_large (b - a) (2 * (μ K).toReal + |a| + b) hε
  let ε' := (b - a) / N
  replace hε' : 0 < ε' ∧  ε' * (2 * (μ K).toReal + |a| + b + ε') ≤ ε :=
    ⟨div_pos (sub_pos.mpr hab.1) (Nat.cast_pos'.mpr hN), hε'⟩
  -- Take a partition of the support of `f` into sets `E` by partitioning the range.
  obtain ⟨E, hE⟩ := range_cut_partition f a hε'.1 N (by field_simp [ε', ← mul_div_assoc,
    mul_div_cancel_left₀, hab.2])
  -- Introduce notation for the partition of the range.
  let y : Fin N → ℝ := fun n ↦ a + ε' * (n + 1)
  -- The measure of each `E n` is finite.
  have hE' (n : Fin N) : μ (E n) ≠ ∞ := by
    have h : E n ⊆ tsupport f := by rw [hE.1]; exact subset_iUnion _ _
    refine lt_top_iff_ne_top.mp ?_
    apply lt_of_le_of_lt <| measure_mono h
    dsimp [μ]
    rw [rieszMeasure, show f = f.toFun by rfl, Content.measure_apply _ f.2.measurableSet]
    exact Content.outerMeasure_lt_top_of_isCompact _ f.2
  -- Define sets `V` which are open approximations to the sets `E`
  obtain ⟨V, hV⟩ : ∃ V : Fin N → Opens X, ∀ n, E n ⊆ (V n) ∧ (∀ x ∈ V n, f x < y n + ε') ∧
      μ (V n) ≤ μ (E n) + ENNReal.ofReal (ε' / N) := by
    have h_ε' := (div_pos hε'.1 (Nat.cast_pos'.mpr hN))
    have h n x (hx : x ∈ E n) := lt_add_of_le_of_pos ((hE.2.2.1 n x hx).right) hε'.1
    have h' n := Eq.trans_ne
      (Content.measure_apply (rieszContent (toNNRealLinear Λ hΛ)) (hE.2.2.2 n)).symm (hE' n)
    choose V hV using fun n ↦ exists_open_approx f h_ε' (E n) (h' n) (hE.2.2.2 n) (h n)
    exact ⟨V, hV⟩
  -- Define a partition of unity subordinated to the sets `V`
  obtain ⟨g, hg⟩ : ∃ (g : Fin N → C_c(X, ℝ)), (∀ n, tsupport (g n) ⊆ (V n).carrier) ∧
    EqOn (∑ n : Fin N, (g n)) 1 (tsupport f.toFun) ∧ (∀ n x, (g n) x ∈ Icc 0 1) ∧
    ∀ n, HasCompactSupport (g n) := by
    have : tsupport f ⊆ ⋃ n, (V n).carrier := calc
      _ = ⋃ j, E j := hE.1
      _ ⊆ _ := by gcongr with n; exact (hV n).1
    obtain ⟨g', hg⟩ := exists_continuous_sum_one_of_isOpen_isCompact (fun n ↦ (V n).2) f.2 this
    exact ⟨fun n ↦ ⟨g' n, hg.2.2.2 n⟩, hg⟩
  -- The proof is completed by a chain of inequalities.
  calc Λ f
    _ = Λ (∑ n, g n • f) := ?_
    _ = ∑ n, Λ (g n • f) := by simp
    _ ≤ ∑ n, Λ ((y n + ε') • g n) := ?_
    _ = ∑ n, (y n + ε') * Λ (g n) := by simp
    -- That `y n + ε'` can be negative is bad in the inequalities so we artifically include `|a|`.
    _ = ∑ n, (|a| + y n + ε') * Λ (g n) - |a| * ∑ n, Λ (g n) :=
      by simp [add_assoc, add_mul |a|, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ∑ n, (|a| + y n + ε') * ((μ (E n)).toReal + ε' / N) - |a| * ∑ n, Λ (g n) := ?_
    _ ≤ ∑ n, (|a| + y n + ε') * ((μ (E n)).toReal + ε' / N) - |a| * (μ K).toReal := ?_
    _ = ∑ n, (y n - ε') * (μ (E n)).toReal +
      2 * ε' * (μ K).toReal + ε' / N * ∑ n, (|a| + y n + ε') := ?_
    _ ≤ ∫ (x : X), f x ∂μ + 2 * ε' * (μ K).toReal + ε' / N * ∑ n, (|a| + y n + ε') := ?_
    _ ≤ ∫ (x : X), f x ∂μ + ε' * (2 * (μ K).toReal + |a| + b + ε') := ?_
    _ ≤ ∫ (x : X), f x ∂μ + ε := by simp [hε'.2]
  · -- Equality since `∑ i : Fin N, (g i)` is equal to unity on the support of `f`
    congr; ext x
    simp only [coe_sum, coe_smulc, smul_eq_mul, Finset.sum_apply, coe_mul, Pi.mul_apply,
      ← Finset.sum_mul, ← Finset.sum_apply]
    by_cases hx : x ∈ tsupport f
    · simp [hg.2.1 hx]
    · simp [image_eq_zero_of_nmem_tsupport hx]
  · -- Use that `f ≤ y n + ε'` on `V n`
    gcongr with n hn
    apply monotone_of_nonneg hΛ
    intro x
    by_cases hx : x ∈ tsupport (g n)
    · rw [smul_eq_mul, mul_comm]
      apply mul_le_mul_of_nonneg_right ?_ (hg.2.2.1 n x).1
      exact le_of_lt <| (hV n).2.1 x <| mem_of_subset_of_mem (hg.1 n) hx
    · simp [image_eq_zero_of_nmem_tsupport hx]
  · -- Use that `Λ (g n) ≤ μ (V n)).toReal ≤ μ (E n)).toReal + ε' / N`
    gcongr with n hn
    · calc
        _ ≤ |a| + a := neg_le_iff_add_nonneg'.mp <| neg_abs_le a
        _ ≤ |a| + a + ε' * (n + 1) := (le_add_iff_nonneg_right (|a| + a)).mpr <| Left.mul_nonneg
          (le_of_lt hε'.1) <| Left.add_nonneg (Nat.cast_nonneg' n) (zero_le_one' ℝ)
        _ ≤ _ := by rw [← add_assoc, le_add_iff_nonneg_right]; exact le_of_lt hε'.1
    · calc
        _ ≤ (μ (V n)).toReal := by
          apply (ENNReal.ofReal_le_iff_le_toReal _).mp
          · exact le_rieszMeasure_tsupport_subset hΛ (fun x ↦ hg.2.2.1 n x) (hg.1 n)
          · rw [← lt_top_iff_ne_top]
            apply lt_of_le_of_lt (hV n).2.2
            rw [WithTop.add_lt_top]
            exact ⟨WithTop.lt_top_iff_ne_top.mpr (hE' n), ENNReal.ofReal_lt_top⟩
        _ ≤ _ := by
          rw [← ENNReal.toReal_ofReal (div_nonneg (le_of_lt hε'.1) (Nat.cast_nonneg _))]
          apply ENNReal.toReal_le_add (hV n).2.2
          · exact hE' n
          · exact ENNReal.ofReal_ne_top
  · -- Use that `μ K ≤ Λ (∑ n, g n)`
    gcongr
    rw [Eq.symm (map_sum Λ g _)]
    have h x : 0 ≤ (∑ n, g n) x := by simpa using Fintype.sum_nonneg fun n ↦ (hg.2.2.1 n x).1
    apply ENNReal.toReal_le_of_le_ofReal
    · exact hΛ (∑ n, g n) (fun x ↦ h x)
    · have h' x (hx : x ∈ K) : (∑ n, g n) x = 1 := by simp [hg.2.1 hx]
      refine rieszMeasure_le_of_eq_one hΛ h f.2 h'
  · -- Rearrange the sums
    have (n : Fin N) : (|a| + y n + ε') * (μ (E n)).toReal =
        (|a| + 2 * ε') * (μ (E n)).toReal + (y n - ε') * (μ (E n)).toReal := by linarith
    simp_rw [mul_add, this]
    have : ∑ i, (μ (E i)).toReal = (μ K).toReal := by
      suffices h : μ K = ∑ i, (μ (E i)) by
        rw [h]; exact Eq.symm <| ENNReal.toReal_sum <| fun n _ ↦ hE' n
      dsimp [K]; rw [hE.1]
      rw [measure_iUnion (fun m n hmn ↦ hE.2.1 trivial trivial hmn) hE.2.2.2]
      exact tsum_fintype fun b ↦ μ (E b)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, this, ← Finset.sum_mul]
    linarith
  · -- Use that `y n - ε' ≤ f x` on `E n`
    gcongr
    have h : ∀ n, (y n - ε') * (μ (E n)).toReal ≤ ∫ x in (E n), f x ∂μ := by
      intro n
      apply setIntegral_ge_of_const_le (hE.2.2.2 n) (hE' n)
      · intro x hx
        dsimp [y]; linarith [(hE.2.2.1 n x hx).1]
      · apply Integrable.integrableOn
        dsimp [μ, rieszMeasure]
        exact Continuous.integrable_of_hasCompactSupport f.1.2 f.2
    calc
      _ ≤ ∑ n, ∫ (x : X) in E n, f x ∂μ := Finset.sum_le_sum fun i a ↦ h i
      _ = ∫ x in (⋃ n, E n), f x ∂μ := by
        refine Eq.symm <| integral_fintype_iUnion hE.2.2.2 (fun _ _ ↦ hE.2.1 trivial trivial) ?_
        dsimp [μ, rieszMeasure]
        exact fun _ ↦
          Integrable.integrableOn <| Continuous.integrable_of_hasCompactSupport f.1.2 f.2
      _ = ∫ x in tsupport f, f x ∂μ := by simp_rw [hE.1]
      _ = _ := setIntegral_tsupport
  · -- Rough bound of the sum
    have h : ∑ n : Fin N, y n ≤ N * b := by
      have (n : Fin N) := calc y n
        _ ≤ a + ε' * N := by simp_all [y, show (n : ℝ) + 1 ≤ N by norm_cast; omega]
        _ = b := by field_simp [ε', ← mul_div_assoc, mul_div_cancel_left₀]
      have : ∑ n, y n ≤ ∑ n, b := Finset.sum_le_sum (fun n ↦ fun _ ↦ this n)
      simp_all
    simp only [add_assoc, add_le_add_iff_left, Finset.sum_add_distrib, Finset.sum_add_distrib,
               Fin.sum_const, Fin.sum_const, nsmul_eq_mul, ← add_assoc, mul_add, ← mul_assoc]
    simpa [show (N : ℝ) ≠ 0 by simp [hN.ne.symm], mul_comm _ ε', div_eq_mul_inv, mul_assoc]
      using (mul_le_mul_iff_of_pos_left hε'.1).mpr <| (inv_mul_le_iff₀ (Nat.cast_pos'.mpr hN)).mpr h

/-- The **Riesz-Markov-Kakutani representation theorem**: given a positive linear functional `Λ`,
the integral of `f` with respect to the `rieszMeasure` associated to `Λ` is equal to `Λ f`. -/
theorem integral_rieszMeasure (f : C_c(X, ℝ)) : ∫ x, f x ∂(rieszMeasure hΛ) = Λ f := by
  -- We apply the result `Λ f ≤ ∫ x, f x ∂(rieszMeasure hΛ)` to `f` and `-f`.
  apply le_antisymm
  -- prove the inequality for `- f`
  · calc
      _ = - ∫ x, (-f) x ∂(rieszMeasure hΛ) := by simpa using integral_neg' (-f)
      _ ≤ - Λ (-f) := neg_le_neg (integral_riesz_aux hΛ (-f))
      _ = Λ (- -f) := Eq.symm (LinearMap.map_neg Λ (- f))
      _ = _ := by rw [neg_neg]
  -- prove the inequality for `f`
  · exact integral_riesz_aux hΛ f

end RealRMK

