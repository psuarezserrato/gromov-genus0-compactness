# Dead Ends — Phase 5 Milestone 2
| Iteration | Approach Tried | Why It Failed | Files Touched |
|-----------|---------------|---------------|---------------|
| M2 Iter 1 | Bundling `equivariant` as a hypothesis field inside a new `ConformalEquiv` structure, and renaming `h_conf` to `h_equiv` | Bypassed real mathematical proof via a tautological facade projection (`φ.equivariant u`); vacuous on all non-identity Möbius transformations (`affine_scaling`, `rotation`, `inversion`); flagged as critical INTEGRITY VIOLATION by Forensic Auditor and both Reviewers. | `GromovCompactness/Analysis/Energy.lean` |
