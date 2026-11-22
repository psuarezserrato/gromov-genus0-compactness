# Dead Ends — Phase 5 Milestone 2
| Iteration | Approach Tried | Why It Failed | Files Touched |
|-----------|---------------|---------------|---------------|
| M2 Iter 1 | Bundling `equivariant` as a hypothesis field inside a new `ConformalEquiv` structure, and renaming `h_conf` to `h_equiv` | Bypassed real mathematical proof via a tautological facade projection (`φ.equivariant u`); vacuous on all non-identity Möbius transformations (`affine_scaling`, `rotation`, `inversion`); flagged as critical INTEGRITY VIOLATION by Forensic Auditor and both Reviewers. | `GromovCompactness/Analysis/Energy.lean` |

---

## License & Citation

Licensed under the **GNU Affero General Public License v3.0 (AGPLv3)** for non-commercial use — see [LICENSE.md](https://github.com/psuarezserrato/Turing-recursive/blob/main/LICENSE.md) ([local copy](LICENSE.md)) for details:

> This project is licensed under non-commercial use. If you wish to use this software in a commercial product, service, or enterprise environment, please contact the developer to purchase a commercial license or negotiate royalty terms.

Authored by **Pablo Suárez-Serrato** (November 2026).
