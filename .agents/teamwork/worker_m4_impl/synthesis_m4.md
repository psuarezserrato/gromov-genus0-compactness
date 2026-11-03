# Milestone 4 Synthesis Blueprint: Phase 1 Foundations Completion

## Goal
Integrate verified zero-sorry solutions from Explorers 1, 2, and 3 into the remaining Phase 1 foundation modules:
1. `GromovCompactness/Analysis/Energy.lean` (Task F03)
2. `GromovCompactness/Topology/SmoothLocal.lean` (Task F04)
3. `GromovCompactness/Topology/SphereTree.lean` (Task F06)

All implementations must be 100% zero-sorry, zero-admit, facade-free, and depend strictly on standard Mathlib4 axioms `[propext, Classical.choice, Quot.sound]`.

---

## 1. Task F03: Energy.lean
Source: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_energy/ScratchEnergy.lean`

Key elements to apply:
- Modernized typeclasses: `[IsManifold I ∞ M]` (replacing deprecated `SmoothManifoldWithCorners`), `[CompactSpace M]`, `[ClosedTameTarget I M]`.
- Basis vectors `e1`, `e2` and complex equivalence lemmas `c_equiv_1`, `c_equiv_I`, `J_CP1_e1`, `J_CP1_e2`.
- Pointwise densities: `riemannianEnergyDensity`, `symplecticAreaDensity`, and the fundamental equivalence theorem `energy_density_eq_omega` (Riemannian Dirichlet density = pullback $\omega$ area density).
- Stereographic measure pushforward `chartPush`:
  - `energyMeasureExtended (u : CP1 → M) : Measure CP1` via `chartPush` of Lebesgue measure on $\mathbb{C}$ with density.
  - `energyMeasure (u : CP1 → M) (A : Set CP1) : ℝ := (energyMeasureExtended I u A).toReal`.
  - `pullbackOmegaMeasureExtended` and `pullbackOmegaMeasure`.
- Verified theorems:
  - `energy_nonneg`
  - `energy_eq_pullback_omega` (Proved for $J$-holomorphic curves)
  - `energy_additive` (Proved on disjoint measurable sets)
  - `energy_point_null` (Proved for all points $p \in \mathbb{CP}^1$, including north pole and finite points)
  - `energy_circle_null` (Proved for all circles `circle_at a r`)
  - `energy_conformal_invariant` (Equivariant transformation under `MoebiusFrame`)
  - `toReal_volume_ball` and `continuous_volume_ball`
  - `EnergyBoundedSequence` structure

---

## 2. Task F04: SmoothLocal.lean
Source: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_smooth/ScratchSmoothLocal.lean`

Key elements to apply:
- Modernized typeclasses: `[IsManifold I ∞ M]`, `[CompactSpace M]`, `[T2Space M]`. Explicit model arguments for `JHolomorphicOn (I := I) (I_dom := I_CP1)`.
- Core definition `CoreSmoothLocalConvergesOn`:
  - Pointwise convergence on compact subsets $K \subseteq \Omega$.
  - Differential convergence in `EuclideanSpace ℝ (Fin 2) →L[ℝ] E`.
  - Higher iterated Fréchet derivatives in local charts.
  - Target almost complex structure coupling $J(u_n z)(du_n(z) v) \to J(u_{\lim} z)(du_{\lim}(z) v)$.
- Frame-invariant definition `SmoothLocalConvergesOn`:
  - Quantified over finite lists of converging Möbius frames.
- Verified theorems:
  - `smooth_local_limit_unique` (Pointwise uniqueness in Hausdorff target)
  - `smooth_local_restriction` (Restriction to open subdomains)
  - `smooth_local_jhol_closure` (Closure of Cauchy-Riemann equation under $C^\infty_{\mathrm{loc}}$ limits)
  - `smooth_local_comp_moebius` (Stability under composition with converging Möbius frames)
  - `SmoothLocalConvergesVarying` definition on exhausting domains.

---

## 3. Task F06: SphereTree.lean
Source: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_tree/ScratchSphereTree.lean`

Key elements to apply:
- Modernized typeclasses and automatic synthesis:
  - `attribute [instance] SphereTree.fintypeV SphereTree.nonemptyV`
  - `[IsManifold I ∞ M]`, `[CompactSpace M]`, `[ClosedTameTarget I M]`
  - Explicit model arguments for `JHolomorphicOn (I := I) (I_dom := I_CP1)`
  - Fix implicit parameter syntax in `is_ghost_component` and `is_principal_component`.
- Verified theorems:
  - `tree_degree_sum` (Handshake lemma for trees: $\sum_{v \in V} \operatorname{deg}(v) = 2(|V| - 1)$)
  - `tree_degree_ge_one` (Degrees in connected graphs with $|V| > 1$ are $\ge 1$)
  - `ghost_components_bound` (Theorem 1 / Task F06: $G \le P - 2$ and $|V| \le 2P - 2$ via degree sum partitioning and `omega`)
  - `graft_trees` with `graftAdj`, `graftNodePoint`, `graft_node_distinct`, and complete zero-sorry proof of `IsTree` (bridge parity in $\mathbb{Z}/2\mathbb{Z}$ and cycle retraction).
  - `sphereTreeTotalEnergy` definition.

---

## 4. Verification Steps
1. Apply the implementations to the three target files.
2. Build all 7 Phase 1 modules:
   ```bash
   lake build GromovCompactness.LibraryAudit \
              GromovCompactness.Geometry.Target \
              GromovCompactness.Geometry.Sphere \
              GromovCompactness.Topology.Subsequence \
              GromovCompactness.Analysis.Energy \
              GromovCompactness.Topology.SmoothLocal \
              GromovCompactness.Topology.SphereTree
   ```
   Must exit with code 0.
3. Check 0 sorries/admits across all files:
   ```bash
   grep -nE "(sorry|admit|axiom )" \
     GromovCompactness/Analysis/Energy.lean \
     GromovCompactness/Topology/SmoothLocal.lean \
     GromovCompactness/Topology/SphereTree.lean
   ```
   Must return 0 matches.
4. Check standard axioms only `[propext, Classical.choice, Quot.sound]`.
