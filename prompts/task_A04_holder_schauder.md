# Single-Lemma Lean 4.16.0 Prompts: Part 14A-1, Part 14A-2 & Part 14A-3 (Pure `ℂ` Cauchy–Riemann Derivative Identities)

To avoid any `iteratedFDeriv` / `ContinuousMultilinearMap` typeclass issues in the external model, these three single-lemma prompts work purely with `f : ℂ → ℂ`, `fderiv ℝ f z 1`, `fderiv ℝ f z Complex.I`, and `cauchyRiemann f z`.

---

## Prompt 1: Part 14A-1 (`fderiv_I_eq_of_cauchyRiemann`)

```markdown
Write a complete, self-contained Lean 4 (`v4.16.0` / Mathlib `v4.16.0`) file with **zero `sorry`** that proves **only** the single lemma `fderiv_I_eq_of_cauchyRiemann` below.

### Target Code Template

```lean
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

open Complex

namespace GromovCompactness.Analysis

noncomputable def cauchyRiemann (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)

theorem fderiv_I_eq_of_cauchyRiemann (f : ℂ → ℂ) (z : ℂ) :
    fderiv ℝ f z Complex.I =
      Complex.I * fderiv ℝ f z 1 - 2 * Complex.I * cauchyRiemann f z := by
  -- Hint:
  -- 1. `dsimp [cauchyRiemann]`
  -- 2. `have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I`
  -- 3. `linear_combination -(fderiv ℝ f z Complex.I) * hI`
  sorry

end GromovCompactness.Analysis
```
```

---

## Prompt 2: Part 14A-2 (`norm_fderiv_I_le_of_cauchyRiemann`)

```markdown
Write a complete, self-contained Lean 4 (`v4.16.0` / Mathlib `v4.16.0`) file with **zero `sorry`** that proves **only** the single lemma `norm_fderiv_I_le_of_cauchyRiemann` below, assuming `fderiv_I_eq_of_cauchyRiemann` as an `axiom`.

### Target Code Template

```lean
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Complex

namespace GromovCompactness.Analysis

noncomputable def cauchyRiemann (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)

axiom fderiv_I_eq_of_cauchyRiemann (f : ℂ → ℂ) (z : ℂ) :
    fderiv ℝ f z Complex.I =
      Complex.I * fderiv ℝ f z 1 - 2 * Complex.I * cauchyRiemann f z

theorem norm_fderiv_I_le_of_cauchyRiemann (f : ℂ → ℂ) (z : ℂ) :
    ‖fderiv ℝ f z Complex.I‖ ≤
      ‖fderiv ℝ f z 1‖ + 2 * ‖cauchyRiemann f z‖ := by
  -- Hint:
  -- 1. `rw [fderiv_I_eq_of_cauchyRiemann]`
  -- 2. Apply `norm_sub_le` and simplify `‖Complex.I * _‖` and `‖2 * Complex.I * _‖` using `norm_mul` and `Complex.norm_I`.
  sorry

end GromovCompactness.Analysis
```
```

---

## Prompt 3: Part 14A-3 (`norm_fderiv_I_sub_le_of_cauchyRiemann`)

```markdown
Write a complete, self-contained Lean 4 (`v4.16.0` / Mathlib `v4.16.0`) file with **zero `sorry`** that proves **only** the single lemma `norm_fderiv_I_sub_le_of_cauchyRiemann` below, assuming `fderiv_I_eq_of_cauchyRiemann` as an `axiom`.

### Target Code Template

```lean
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Complex

namespace GromovCompactness.Analysis

noncomputable def cauchyRiemann (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)

axiom fderiv_I_eq_of_cauchyRiemann (f : ℂ → ℂ) (z : ℂ) :
    fderiv ℝ f z Complex.I =
      Complex.I * fderiv ℝ f z 1 - 2 * Complex.I * cauchyRiemann f z

theorem norm_fderiv_I_sub_le_of_cauchyRiemann (f : ℂ → ℂ) (z w : ℂ) :
    ‖fderiv ℝ f z Complex.I - fderiv ℝ f w Complex.I‖ ≤
      ‖fderiv ℝ f z 1 - fderiv ℝ f w 1‖ +
      2 * ‖cauchyRiemann f z - cauchyRiemann f w‖ := by
  -- Hint:
  -- 1. `rw [fderiv_I_eq_of_cauchyRiemann f z, fderiv_I_eq_of_cauchyRiemann f w]`
  -- 2. Group the difference as `Complex.I * (fderiv ℝ f z 1 - fderiv ℝ f w 1) - 2 * Complex.I * (cauchyRiemann f z - cauchyRiemann f w)` by `ring`.
  -- 3. Apply `norm_sub_le`, `norm_mul`, and `Complex.norm_I`.
  sorry

end GromovCompactness.Analysis
```
```
