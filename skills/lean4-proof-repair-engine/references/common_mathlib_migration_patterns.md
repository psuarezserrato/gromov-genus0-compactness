# Common Mathlib 3 to Mathlib 4 Migration Patterns in Topology & Geometry

Quick reference guide for identifiers, tactic syntax, and conventions translated between Mathlib 3 and Mathlib 4.

---

## 1. Metric Space and Neighborhoods

| Mathlib 3 Pattern | Mathlib 4 Pattern | Notes |
|-------------------|-------------------|-------|
| `metric.ball x r` | `Metric.ball x r` | Capitalized namespace |
| `metric.closed_ball x r` | `Metric.closedBall x r` | camelCase for terms/sets |
| `dist_triangle` | `dist_triangle` | Unchanged |
| `complete_space` | `CompleteSpace` | UpperCamelCase for typeclasses |
| `metric_space` | `MetricSpace` | UpperCamelCase for typeclasses |

---

## 2. Hofer's Lemma

| Aspect | Lean 3 | Lean 4 |
|--------|--------|--------|
| Module | `analysis.hofer` | `Mathlib.Analysis.Hofer` |
| Lemma | `hofer` | `Mathlib.Analysis.Hofer.hofer` |
| Hypothesis Order | `(hf : continuous f) (x : X) (hε : 0 < ε)` | `(f : X → ℝ) (x : X) (ε : ℝ) (hε : 0 < ε) (hf : Continuous f) (hfx : 0 ≤ f x)` |

---

## 3. Tactic Syntax Migration

| Mathlib 3 Tactic | Mathlib 4 Tactic | Notes |
|------------------|------------------|-------|
| `rcases h with ⟨a, b⟩` | `obtain ⟨a, b⟩ := h` | `obtain` preferred in Lean 4 |
| `linarith` | `linarith` | Retained |
| `ring` | `ring` | Retained |
| `positivity` | `positivity` | Closes non-negative bounds |
| `sorry` | `sorry` | Standard first-pass stub |

---

## License & Citation

Licensed under the **GNU Affero General Public License v3.0 (AGPLv3)** for non-commercial use — see [LICENSE.md](https://github.com/psuarezserrato/Turing-recursive/blob/main/LICENSE.md) ([local copy](LICENSE.md)) for details:

> This project is licensed under non-commercial use. If you wish to use this software in a commercial product, service, or enterprise environment, please contact the developer to purchase a commercial license or negotiate royalty terms.

Authored by **Pablo Suárez-Serrato** (November 2026).
