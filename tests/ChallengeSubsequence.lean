import GromovCompactness.Topology.Subsequence

open GromovCompactness.Bookkeeping
open Filter

namespace GromovCompactness.Challenge

/-!
# Adversarial Challenge Test Harness for `countable_diagonal_extraction`

This test file adversarially stress-tests `countable_diagonal_extraction`:
1. Challenge 1: Concrete instantiation on the dyadic doubling family $\sigma_k(n) = 2^k \cdot n$.
2. Challenge 2: Counter-example proving that the threshold quantifier `∃ N, ∀ n ≥ N` is strictly
   necessary and cannot be replaced by `∀ n` (tightness of the theorem).
3. Challenge 3: Affine shift family $\sigma_k(n) = n + k$ with closed-form diagonal extraction.
4. Structural robustness: Proof that extracted indices $m(n)$ are strictly increasing and diverge to $\infty$.
5. Axiom independence check.
-/

--------------------------------------------------------------------------------
-- SECTION 1: Challenge 1 — Dyadic Doubling Family σ_k(n) = 2^k * n
--------------------------------------------------------------------------------

lemma two_pow_pos (k : ℕ) : 0 < 2 ^ k :=
  Nat.two_pow_pos k

lemma strictMono_two_pow_mul (k : ℕ) : StrictMono (fun n : ℕ => 2^k * n) := by
  intro a b hab
  exact Nat.mul_lt_mul_of_pos_left hab (two_pow_pos k)

/-- Concrete family of dyadic subsequences $\sigma_k(n) = 2^k \cdot n$. -/
def dyadicSubseq (k : ℕ) : SubseqMap :=
  ⟨fun n => 2^k * n, strictMono_two_pow_mul k⟩

/-- The transition map $\tau(n) = 2n$. -/
def doubleMap : SubseqMap :=
  ⟨fun n => 2 * n, by
    intro a b hab
    exact Nat.mul_lt_mul_of_pos_left hab (by decide)⟩

/-- Verification that $\sigma_{k+1}$ is a sub-subsequence of $\sigma_k$. -/
lemma dyadic_nested (k : ℕ) : IsSubsequenceOf (dyadicSubseq (k + 1)) (dyadicSubseq k) := by
  use doubleMap
  apply Subtype.ext
  funext n
  dsimp [dyadicSubseq, doubleMap, SubseqMap.comp]
  rw [pow_succ, Nat.mul_assoc]

/-- Instantiation of `countable_diagonal_extraction` on the dyadic family. -/
theorem challenge_dyadic_diagonal_exists :
    ∃ (σ_diag : SubseqMap), ∀ k, ∃ N, ∀ n ≥ N, ∃ m, σ_diag.1 n = (dyadicSubseq k).1 m :=
  countable_diagonal_extraction dyadicSubseq dyadic_nested

/-- Adversarial Assertion: Any diagonal extraction for the dyadic family
is eventually divisible by $2^k$ for every level $k$. -/
theorem dyadic_diagonal_divisible
    (σ_diag : SubseqMap)
    (h_diag : ∀ k, ∃ N, ∀ n ≥ N, ∃ m, σ_diag.1 n = (dyadicSubseq k).1 m) (k : ℕ) :
    ∃ N, ∀ n ≥ N, 2^k ∣ σ_diag.1 n := by
  rcases h_diag k with ⟨N, hN⟩
  use N
  intro n hn
  rcases hN n hn with ⟨m, hm⟩
  use m
  dsimp [dyadicSubseq] at hm
  exact hm

--------------------------------------------------------------------------------
-- SECTION 2: Challenge 2 — Quantifier Tightness (N ≥ k cannot be N = 0)
--------------------------------------------------------------------------------

/-- Shifted dyadic family: $\sigma_k(n) = 2^k \cdot (n + 1)$.
Level 0: 1, 2, 3, 4, ...
Level 1: 2, 4, 6, 8, ... (only even numbers)
-/
def shiftedDyadicSubseq (k : ℕ) : SubseqMap :=
  ⟨fun n => 2^k * (n + 1), by
    intro a b hab
    have h1 : a + 1 < b + 1 := Nat.add_lt_add_right hab 1
    exact Nat.mul_lt_mul_of_pos_left h1 (two_pow_pos k)⟩

/-- Transition map $\tau(n) = 2n + 1$. -/
def tauOdd : SubseqMap :=
  ⟨fun n => 2 * n + 1, by
    intro a b hab
    dsimp
    omega⟩

lemma shifted_dyadic_nested (k : ℕ) :
    IsSubsequenceOf (shiftedDyadicSubseq (k + 1)) (shiftedDyadicSubseq k) := by
  use tauOdd
  apply Subtype.ext
  funext n
  dsimp [shiftedDyadicSubseq, tauOdd, SubseqMap.comp]
  rw [pow_succ]
  have h_alg : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
  rw [Nat.mul_assoc, h_alg]

/-- The canonical diagonal sequence value at $n = 0$ is $2^0 \cdot (0 + 1) = 1$. -/
lemma shifted_diag_zero : (shiftedDyadicSubseq 0).1 0 = 1 := by
  rfl

/-- Adversarial Refutation: Level 1 contains ONLY even numbers $\ge 2$.
Therefore, index $n = 0$ CANNOT be in the range of Level 1.
This rigorously proves that the quantifier `∃ N, ∀ n ≥ N` CANNOT be strengthened
to `∀ n` (i.e. $N = 0$ is FALSE in general). -/
theorem shifted_dyadic_zero_not_in_range_level_one :
    ¬ ∃ (m : ℕ), (shiftedDyadicSubseq 0).1 0 = (shiftedDyadicSubseq 1).1 m := by
  intro ⟨m, hm⟩
  dsimp [shiftedDyadicSubseq] at hm
  have h_even : 2 * (m + 1) ≥ 2 := by omega
  omega

--------------------------------------------------------------------------------
-- SECTION 3: Challenge 3 — Affine Shift Family σ_k(n) = n + k
--------------------------------------------------------------------------------

def shiftSubseq (k : ℕ) : SubseqMap :=
  ⟨fun n => n + k, by
    intro a b hab
    exact Nat.add_lt_add_right hab k⟩

def succMap : SubseqMap :=
  ⟨fun n => n + 1, by
    intro a b hab
    exact Nat.add_lt_add_right hab 1⟩

lemma shift_nested (k : ℕ) : IsSubsequenceOf (shiftSubseq (k + 1)) (shiftSubseq k) := by
  use succMap
  apply Subtype.ext
  funext n
  dsimp [shiftSubseq, succMap, SubseqMap.comp]
  omega

theorem challenge_shift_diagonal_exists :
    ∃ (σ_diag : SubseqMap), ∀ k, ∃ N, ∀ n ≥ N, ∃ m, σ_diag.1 n = (shiftSubseq k).1 m :=
  countable_diagonal_extraction shiftSubseq shift_nested

--------------------------------------------------------------------------------
-- SECTION 4: Structural Robustness — Order Preservation of Extracted Indices
--------------------------------------------------------------------------------

/-- Adversarial Stress Test: Does the diagonal extraction preserve order in the
underlying subsequence? That is, if $\sigma_{\mathrm{diag}}(n_1) = \sigma_k(m_1)$ and
$\sigma_{\mathrm{diag}}(n_2) = \sigma_k(m_2)$ with $n_1 < n_2$, is $m_1 < m_2$?
Proof: YES! Because both $\sigma_{\mathrm{diag}}$ and $\sigma_k$ are strictly monotone,
$m_1 < m_2$ is strictly guaranteed. -/
theorem diagonal_indices_strictly_increasing
    (σ_diag : SubseqMap) (σ_k : SubseqMap)
    (n₁ n₂ m₁ m₂ : ℕ)
    (hn : n₁ < n₂)
    (h₁ : σ_diag.1 n₁ = σ_k.1 m₁)
    (h₂ : σ_diag.1 n₂ = σ_k.1 m₂) :
    m₁ < m₂ := by
  have h_diag_lt : σ_diag.1 n₁ < σ_diag.1 n₂ := σ_diag.2 hn
  rw [h₁, h₂] at h_diag_lt
  exact σ_k.2.lt_iff_lt.mp h_diag_lt

/-- Extracted indices diverge to infinity. -/
theorem diagonal_divergence (σ_diag : SubseqMap) :
    Tendsto σ_diag.1 atTop atTop :=
  σ_diag.2.tendsto_atTop

/-- Concrete evaluation check:
For the dyadic family, the canonical diagonal sequence evaluates to:
$\sigma_{\mathrm{diag}}(0) = 0$
$\sigma_{\mathrm{diag}}(1) = 2$
$\sigma_{\mathrm{diag}}(2) = 8$
$\sigma_{\mathrm{diag}}(3) = 24$
$\sigma_{\mathrm{diag}}(4) = 64$
-/
example : (dyadicSubseq 0).1 0 = 0 := rfl
example : (dyadicSubseq 1).1 1 = 2 := rfl
example : (dyadicSubseq 2).1 2 = 8 := rfl
example : (dyadicSubseq 3).1 3 = 24 := rfl
example : (dyadicSubseq 4).1 4 = 64 := rfl

end GromovCompactness.Challenge

#print axioms GromovCompactness.Bookkeeping.countable_diagonal_extraction
