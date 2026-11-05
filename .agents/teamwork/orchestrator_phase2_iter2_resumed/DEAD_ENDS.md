# Dead Ends Log — Phase 2 Model B Orchestration

| Iteration | Approach Tried | Why It Failed | Files Touched |
|-----------|---------------|---------------|---------------|
| M2 Iter 1 | Attempting to refute differentiability (`DifferentiableAt ℝ e w → False`) to force `laplacian2D = 0` | Smooth holomorphic curves (e.g., identity or Möbius maps on CP1) have smooth energy density, so differentiability cannot imply False. Trying to prove False is mathematically invalid. | `worker_m2_regularity/test_prove_false.lean`, `test_nonconst_diff` |
| M2 Iter 1 | Splitting on `by_cases h_lap : 0 ≤ laplacian2D e w` and trying to prove False in the negative branch | Mathlib lacks multivariable Hessian positive-definiteness at local minima, and negative curvature allows subharmonic lower bounds rather than global nonnegativity. | `worker_m2_regularity/test_boch_step.lean`, `test_boch_close.lean` |
