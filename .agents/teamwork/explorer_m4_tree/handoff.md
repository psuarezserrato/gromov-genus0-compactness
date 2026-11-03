# Technical Exploration Report: Task F06 Labelled Trees and Ghost Components Bound

## 1. Observation
1. **Existing File Inspection**:
   - Inspected `GromovCompactness/Topology/SphereTree.lean` (131 lines).
   - Found 3 unproven placeholders (`sorry`):
     - Line 93: `tree_degree_sum` (Euler characteristic degree sum formula).
     - Line 116: `ghost_components_bound` (Topological bound $G \le P - 2$ and $|V| \le 2P - 2$).
     - Line 128: `graft_trees` (Combinatorial tree grafting operation).
   - Found syntax, deprecation, and type mismatch issues in `SphereTree.lean`:
     - Line 38: Used deprecated `[SmoothManifoldWithCorners I M]` which is an error in current Mathlib toolchain; must be `[IsManifold I ∞ M]`.
     - Line 64: `is_jhol : ∀ (v : tree.V), JHolomorphicOn I (map v) Set.univ` failed because `@JHolomorphicOn` has two explicit model arguments: `(I : ModelWithCorners ℝ E H)` and `(I_dom : ModelWithCorners ℝ E_dom H_dom)`. For spheres, this must be `JHolomorphicOn I I_CP1 (map v) Set.univ`.
     - Line 81 & 85: `is_ghost_component` and `is_principal_component` were written with `(lim : StableSphereTreeLimit I M)` as if `M` were explicit, but `M` is an implicit variable of `StableSphereTreeLimit`, causing `error: function expected at StableSphereTreeLimit`.
     - Line 106-107: `(let _ := lim.tree.fintypeV; h_multivertex : 1 < Fintype.card lim.tree.V)` is invalid Lean 4 grammar for a parameter binder, causing syntax parse errors.

2. **Mathlib Inventory**:
   - `Mathlib.Combinatorics.SimpleGraph.Acyclic`:
     - `SimpleGraph.IsTree`: `isConnected ∧ IsAcyclic`.
     - `SimpleGraph.IsTree.card_edgeFinset`: `Finset.card G.edgeFinset + 1 = Fintype.card V`.
   - `Mathlib.Combinatorics.SimpleGraph.DegreeSum`:
     - `SimpleGraph.sum_degrees_eq_twice_card_edges`: `∑ v, G.degree v = 2 * #G.edgeFinset`.
   - `Mathlib.Combinatorics.SimpleGraph.Finite`:
     - `SimpleGraph.degree_pos_iff_exists_adj`: `0 < G.degree v ↔ ∃ w, G.Adj v w`.
   - `Mathlib.Combinatorics.SimpleGraph.Path`:
     - `SimpleGraph.Walk.map_isCycle_iff_of_injective`: `Function.Injective f → ((p.map f).IsCycle ↔ p.IsCycle)`.
   - `Mathlib.Data.Finset.Card`:
     - `Finset.filter_card_add_filter_neg_card_eq_card`: `#(s.filter p) + #(s.filter fun a ↦ ¬ p a) = #s`.
     - `Finset.sum_filter_add_sum_filter_not`: Splitting sums over partitioned predicates.

3. **Compilation Results**:
   - Created standalone verified solution in:
     `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_tree/ScratchSphereTree.lean`.
   - Command: `lake env lean .agents/teamwork/explorer_m4_tree/ScratchSphereTree.lean`.
   - Result: Exit code 0, 0 compiler warnings, 0 `sorry`, `#print axioms` verifies standard axioms only: `[propext, Classical.choice, Quot.sound]`.

---

## 2. Logic Chain

### 2.1 Instance Registration (`attribute [instance] SphereTree.fintypeV SphereTree.nonemptyV`)
- Rather than inserting repeated `let _ := tree.fintypeV` and `haveI` binders inside every theorem signature and proof, registering `attribute [instance] SphereTree.fintypeV SphereTree.nonemptyV` makes `Fintype tree.V` and `Nonempty tree.V` automatically synthesized whenever `tree : SphereTree` is in scope.
- This eliminates all binder syntax errors while simplifying every subsequent declaration.

### 2.2 Proof of `tree_degree_sum`
1. For any `tree : SphereTree`, `tree.is_tree : tree.adj.IsTree`.
2. By `tree.is_tree.card_edgeFinset`:
   `tree.adj.edgeFinset.card + 1 = Fintype.card tree.V`.
   Hence `tree.adj.edgeFinset.card = Fintype.card tree.V - 1`.
3. By `tree.adj.sum_degrees_eq_twice_card_edges`:
   `∑ v : tree.V, tree.adj.degree v = 2 * tree.adj.edgeFinset.card`.
4. Substituting edge card yields `2 * (Fintype.card tree.V - 1)`, proved cleanly in 4 lines by `rw [h_sum]; congr 1; omega`.

### 2.3 Proof of `ghost_components_bound`
1. **Lower Bound on Vertex Degrees (`tree_degree_ge_one`)**:
   - In any connected graph with `1 < Fintype.card V`, for any vertex $v$, there exists $w \ne v$ (since otherwise `Fintype.card V ≤ 1`).
   - By connectedness, there exists a walk $p$ from $v$ to $w$.
   - Since $v \ne w$, $p$ cannot be `nil`, so $p = \text{cons } h\ q$ where $h : \text{tree.adj.Adj } v\ u$.
   - By `degree_pos_iff_exists_adj`, $0 < \operatorname{deg}(v)$, hence $1 \le \operatorname{deg}(v)$.
2. **Partitioning Vertices**:
   - Let $s_{\text{ghost}} = \{ v \mid \text{is\_ghost\_component } v \}$ and $s_{\text{prin}} = \{ v \mid \text{is\_principal\_component } v \}$.
   - By `Fintype.card_subtype`, $G = |s_{\text{ghost}}|$ and $P = |s_{\text{prin}}|$.
   - Since $\text{is\_principal\_component } v \iff \neg \text{is\_ghost\_component } v$, by `Finset.filter_card_add_filter_neg_card_eq_card`:
     $$|V| = G + P.$$
3. **Partitioning the Degree Sum**:
   - By `Finset.sum_filter_add_sum_filter_not`:
     $$\sum_{v \in V} \operatorname{deg}(v) = \sum_{v \in s_{\text{ghost}}} \operatorname{deg}(v) + \sum_{v \in s_{\text{prin}}} \operatorname{deg}(v).$$
   - For $v \in s_{\text{ghost}}$, stability condition `lim.stable v` guarantees $3 \le \operatorname{deg}(v)$, so:
     $$\sum_{v \in s_{\text{ghost}}} \operatorname{deg}(v) \ge 3 \cdot |s_{\text{ghost}}| = 3G.$$
   - For $v \in s_{\text{prin}}$, `tree_degree_ge_one` guarantees $1 \le \operatorname{deg}(v)$, so:
     $$\sum_{v \in s_{\text{prin}}} \operatorname{deg}(v) \ge 1 \cdot |s_{\text{prin}}| = P.$$
   - Thus $\sum_{v \in V} \operatorname{deg}(v) \ge 3G + P$.
4. **Conclusion**:
   - Combining with `tree_degree_sum`:
     $$3G + P \le 2(|V| - 1) = 2(G + P - 1) = 2G + 2P - 2.$$
   - Subtracting $2G + P$ from both sides gives $G \le P - 2$.
   - Then $|V| = P + G \le P + (P - 2) = 2P - 2$.
   - Lean's `omega` discharges both inequalities simultaneously.

### 2.4 Construction and Tree Proof for `graft_trees`
1. **Definition of Grafting**:
   - Vertices: Disjoint sum $V_1 \oplus V_2$ (`Sum T₁.V T₂.V`).
   - Adjacency `graftAdj`: Preserves internal edges in $T_1$ and $T_2$, and adds a single undirected bridge edge $e_{\text{bridge}} = s(\text{Sum.inl } v_1, \text{Sum.inr } v_2)$.
   - Nodal points: `graftNodePoint` maps internal edges to their original nodal points, and assigns $p_1$ on component $v_1$ facing $v_2$, and $p_2$ on component $v_2$ facing $v_1$.
   - Distinctness `graft_node_distinct`: Pairwise distinctness is preserved because $p_1$ is assumed distinct from existing incident nodes of $v_1$ (`hp₁`), and $p_2$ is distinct from existing incident nodes of $v_2$ (`hp₂`).
2. **Proof that the Grafted Graph is a Tree (`graft_is_tree`)**:
   - **Connectedness (`graft_connected`)**: Walks between vertices in $V_1$ map via `graftHomInl`; walks in $V_2$ map via `graftHomInr`; walks between $x_1 \in V_1$ and $y_2 \in V_2$ are formed by concatenating walk $x_1 \rightsquigarrow v_1$, bridge edge $(v_1, v_2)$, and walk $v_2 \rightsquigarrow y_2$.
   - **Parity of Bridge Crossings (`walk_bridge_count_parity`)**:
     - Define bicoloring `isRight : V₁ ⊕ V₂ → Bool` (`Sum.inl _ ↦ false`, `Sum.inr _ ↦ true`).
     - Prove `isRight x ≠ isRight y ↔ s(x, y) = e_{\text{bridge}}` along any adjacent step.
     - By induction on walks, in $\mathbb{Z}/2\mathbb{Z}$:
       $$\operatorname{count}(e_{\text{bridge}}, p.\text{edges}) \equiv (\text{if } \text{isRight}(x) = \text{isRight}(y) \text{ then } 0 \text{ else } 1) \pmod 2.$$
   - **Bridge Avoidance for Cycles (`cycle_not_mem_bridge`)**:
     - For any closed walk $p : x \rightsquigarrow x$, $\text{isRight}(x) = \text{isRight}(x)$, so the count of $e_{\text{bridge}}$ is even.
     - If $p$ is a cycle, its edge list has no duplicates (`hp.isTrail.edges_nodup`), so any edge appears at most 1 time.
     - Since $\operatorname{count} \le 1$ and $\operatorname{count} \equiv 0 \pmod 2$, $\operatorname{count} = 0$.
     - Hence no cycle can ever traverse the bridge edge!
   - **Acyclicity (`graft_is_acyclic`)**:
     - Any cycle $c$ in the graft avoids $e_{\text{bridge}}$, so all its vertices must lie entirely in `Sum.inl` or entirely in `Sum.inr`.
     - Construct explicit retraction functions `walkOfInl` and `walkOfInr` mapping bridge-avoiding walks back into $T_1$ and $T_2$.
     - By `walkOfInl_map` / `walkOfInr_map` and `SimpleGraph.Walk.map_isCycle_iff_of_injective`, $c$ would induce a cycle in $T_1$ or $T_2$, contradicting $T_1.\text{is\_tree.IsAcyclic}$ and $T_2.\text{is\_tree.IsAcyclic}$.
   - Therefore, the grafted graph is connected and acyclic: `(graftAdj T₁ T₂ v₁ v₂).IsTree`.

---

## 3. Caveats
1. **Hypotheses on `graft_trees`**:
   - In `SphereTree.lean:125`, the skeleton omitted hypotheses that $p_1$ and $p_2$ are not already incident nodes of $v_1$ and $v_2$.
   - As documented in the docstring ("identifying a designated smooth point on $T_1$ with a smooth point on $T_2$"), smooth points are by definition non-nodal points. Without `hp₁` and `hp₂`, `node_distinct` cannot mathematically hold if $p_1$ happens to coincide with an existing nodal attachment point.
   - The verified solution in `ScratchSphereTree.lean` correctly incorporates `hp₁` and `hp₂`.
2. **Analysis/Energy Import Dependency**:
   - `GromovCompactness/Analysis/Energy.lean` currently fails to compile because line 38 contains the deprecated binder `[SmoothManifoldWithCorners I M]`.
   - In `ScratchSphereTree.lean`, `sphereTreeTotalEnergy` is defined using an abstract energy functional parameter. Once `Energy.lean` line 38 is remediated by the Energy team (`[SmoothManifoldWithCorners I M]` $\to$ `[IsManifold I ∞ M]`), `sphereTreeTotalEnergy` in `SphereTree.lean` will immediately connect to `totalEnergy`.

---

## 4. Conclusion
- Task F06 is fully solved, machine-checked, facade-free, and verified with zero sorry.
- All declarations in `ScratchSphereTree.lean` compile with exit code 0 and depend solely on standard Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`).
- The worker implementing Task F06 can directly transfer the code from `ScratchSphereTree.lean` into `GromovCompactness/Topology/SphereTree.lean`.

---

## 5. Verification Method

### 5.1 Verification Commands
To independently verify the complete scratch file:
```bash
cd /Users/pablosuarez/Desktop/SympTopAutoForm
lake env lean .agents/teamwork/explorer_m4_tree/ScratchSphereTree.lean
```
Expected output:
```
'GromovCompactness.tree_degree_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'GromovCompactness.ghost_components_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'GromovCompactness.graft_trees' depends on axioms: [propext, Classical.choice, Quot.sound]
'GromovCompactness.sphereTreeTotalEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Exit code: `0`.

### 5.2 Verification Script
Run the following one-liner to verify exit code and axiom soundness:
```bash
lake env lean .agents/teamwork/explorer_m4_tree/ScratchSphereTree.lean && echo "VERIFICATION SUCCESS: 0 SORRY, CLEAN EXIT CODE 0"
```
