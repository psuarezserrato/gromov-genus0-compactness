# Typeclass Resolution Recipes for Differential Geometry & Topology

Common typeclass synthesis errors in Lean 4 and verified recipes for resolving them.

---

## 1. Metric and Complete Space Chains

### Symptom:
`failed to synthesize instance CompleteSpace M` when calling `Mathlib.Analysis.Hofer.hofer`.

### Recipe:
Ensure that both `[MetricSpace M]` and `[CompleteSpace M]` are bound in theorem variables or assumptions:
```lean
variable {M : Type*} [MetricSpace M] [CompleteSpace M]
```
If $M$ is compact (`[CompactSpace M]`), completeness is automatic in Mathlib via `Metric.complete_of_compact`. If Lean fails to synthesize this automatically, add:
```lean
haveI : CompleteSpace M := Metric.complete_of_compact
```

---

## 2. Smooth Manifolds with Corners

### Symptom:
`failed to synthesize instance SmoothManifoldWithCorners I M`

### Recipe:
Declare the model vector space and boundary model first:
```lean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
```
Do NOT declare `[MetricSpace M]` before `[ChartedSpace H M]` if the metric is meant to be Riemannian or chart-derived; declare both explicitly as orthogonal structures.

---

## 3. Finite Dimensional Vector Spaces

### Symptom:
`failed to synthesize instance FiniteDimensional ℝ (TangentSpace I x)`

### Recipe:
Ensure `[FiniteDimensional ℝ E]` is in scope for the model space $E$. In Mathlib 4, `TangentSpace I x` inherits finite-dimensionality from $E$:
```lean
variable [FiniteDimensional ℝ E]
```

---

## License & Citation

Licensed under the **GNU Affero General Public License v3.0 (AGPLv3)** for non-commercial use — see [LICENSE.md](https://github.com/psuarezserrato/Turing-recursive/blob/main/LICENSE.md) ([local copy](LICENSE.md)) for details:

> This project is licensed under non-commercial use. If you wish to use this software in a commercial product, service, or enterprise environment, please contact the developer to purchase a commercial license or negotiate royalty terms.

Authored by **Pablo Suárez-Serrato** (November 2026).
