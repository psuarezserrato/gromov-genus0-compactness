/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

/-!
# Task F05: Subsequence and Diagonal Bookkeeping

This module formalizes strictly monotone index extraction maps $\sigma : \mathbb{N} \to \mathbb{N}$
and Cantor diagonal extraction for countably many nested subsequences, following standard analysis
and `gromov_compactness.pdf` §2.3 & §5 (Task `F05`).

## Key Definitions
- `SubseqMap`: The subtype of strictly monotone index functions $\sigma : \mathbb{N} \to \mathbb{N}$.
- `SubseqMap.id`: The identity subsequence.
- `SubseqMap.comp`: Composition of subsequences $\sigma_1 \circ \sigma_2$.
- `subseq_le`: Proof that $n \le \sigma(n)$ for all $n \in \mathbb{N}$.
- `IsSubsequenceOf`: Relation stating $\sigma_2$ is a refinement / sub-subsequence of $\sigma_1$.
- `countable_diagonal_extraction`: The Cantor diagonal subsequence theorem.
-/

namespace GromovCompactness.Bookkeeping

/-- A strictly increasing subsequence extraction map $\sigma : \mathbb{N} \to \mathbb{N}$. -/
def SubseqMap := { σ : ℕ → ℕ // StrictMono σ }

namespace SubseqMap

/-- The identity subsequence map $\mathrm{id}_{\mathbb{N}}$. -/
def id : SubseqMap := ⟨_root_.id, strictMono_id⟩

/-- Composition of two subsequence extraction maps $\sigma_1 \circ \sigma_2$. -/
def comp (σ₁ σ₂ : SubseqMap) : SubseqMap :=
  ⟨σ₁.1 ∘ σ₂.1, σ₁.2.comp σ₂.2⟩

/-- Any strictly monotone sequence on $\mathbb{N}$ satisfies $n \le \sigma(n)$ for all $n$. -/
theorem id_le (σ : SubseqMap) (n : ℕ) : n ≤ σ.1 n :=
  σ.2.id_le n

end SubseqMap

/-- Predicate asserting that $\sigma_2$ is a sub-subsequence of $\sigma_1$
via an intermediate strictly monotone map $\tau : \mathbb{N} \to \mathbb{N}$. -/
def IsSubsequenceOf (σ₂ σ₁ : SubseqMap) : Prop :=
  ∃ (τ : SubseqMap), σ₂ = σ₁.comp τ

/-- Transitivity of subsequence refinement. -/
theorem subsequence_trans (σ₁ σ₂ σ₃ : SubseqMap)
    (h21 : IsSubsequenceOf σ₂ σ₁) (h32 : IsSubsequenceOf σ₃ σ₂) :
    IsSubsequenceOf σ₃ σ₁ := by
  rcases h21 with ⟨τ₁, rfl⟩
  rcases h32 with ⟨τ₂, rfl⟩
  use τ₁.comp τ₂
  rfl

/-- Subsequence refinement along nested chains across any offset `d`. -/
theorem isSubsequenceOf_add (σ_family : ℕ → SubseqMap)
    (h_nested : ∀ k, IsSubsequenceOf (σ_family (k + 1)) (σ_family k)) (k d : ℕ) :
    IsSubsequenceOf (σ_family (k + d)) (σ_family k) := by
  induction d with
  | zero =>
    use SubseqMap.id
    exact Subtype.ext rfl
  | succ d ih =>
    exact subsequence_trans (σ_family k) (σ_family (k + d)) (σ_family (k + d + 1)) ih (h_nested (k + d))

/-- Cantor diagonal extraction for a countable family of nested subsequences:
Given a sequence of subsequences $\sigma_k$ where $\sigma_{k+1}$ refines $\sigma_k$,
there exists a diagonal subsequence $\sigma_{\mathrm{diag}}$ that is eventually a sub-subsequence
of every $\sigma_k$. -/
theorem countable_diagonal_extraction (σ_family : ℕ → SubseqMap)
    (h_nested : ∀ k, IsSubsequenceOf (σ_family (k + 1)) (σ_family k)) :
    ∃ (σ_diag : SubseqMap), ∀ k, ∃ N, ∀ n ≥ N, ∃ m, σ_diag.1 n = (σ_family k).1 m := by
  let diag_fun : ℕ → ℕ := fun n => (σ_family n).1 n
  have h_mono : StrictMono diag_fun := by
    apply strictMono_nat_of_lt_succ
    intro n
    dsimp [diag_fun]
    rcases h_nested n with ⟨τ, hτ⟩
    have h_eval : (σ_family (n + 1)).1 (n + 1) = (σ_family n).1 (τ.1 (n + 1)) := by
      rw [hτ]
      rfl
    rw [h_eval]
    have h_lt : n < τ.1 (n + 1) := by
      have h_le := τ.id_le (n + 1)
      omega
    exact (σ_family n).2 h_lt
  let σ_diag : SubseqMap := ⟨diag_fun, h_mono⟩
  use σ_diag
  intro k
  use k
  intro n hn
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = k + d := Nat.exists_eq_add_of_le hn
  have h_sub : IsSubsequenceOf (σ_family (k + d)) (σ_family k) :=
    isSubsequenceOf_add σ_family h_nested k d
  rcases h_sub with ⟨τ, hτ⟩
  use τ.1 (k + d)
  dsimp [σ_diag, diag_fun]
  rw [hτ]
  rfl

/-- Tendsto compatibility along extracted subsequences. -/
theorem tendsto_subseq_comp {β : Type*} [TopologicalSpace β]
    (f : ℕ → β) (b : β) (σ : SubseqMap)
    (h : Tendsto f atTop (nhds b)) :
    Tendsto (f ∘ σ.1) atTop (nhds b) := by
  exact h.comp σ.2.tendsto_atTop

end GromovCompactness.Bookkeeping
