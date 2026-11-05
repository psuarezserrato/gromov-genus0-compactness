# Dispatch Task: Milestone 3 Explorer 2 (P0-11 Core Call-Graph Wiring Components 1–4)

## Identity & Role
You are `explorer_m3_2` (`teamwork_explorer`).
Working directory: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_2`.

Path to ORIGINAL_REQUEST.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md`

## Mission & Scope
Investigate and design machine-checked Lean 4 blueprints for **Task P0-11 (`core_wiring_plan.md` / Task `G03-W` Components 1–4)**:
1. **Component 1 (`Stabilize.lean` & `GenusZero.lean` — `G02 ↔ G03`)**:
   - In `GromovCompactness/Compactness/Stabilize.lean`:
     * Enrich the conclusion of `stabilize_prestable_tree` (and base cases `stabilize_prestable_tree_of_stable_root`, `stabilize_prestable_tree_of_nonconst_root`) so it returns all 5 fields of `CompactnessWitness` (`σ`, `frames`, `smooth_conv`, `frame_collapse`, and `energy_conv`), forwarding `pdata.frame_collapse` and `pdata.energy_ident`.
     * Prove `stabilize_prestable_tree` **with zero direct `sorry`** via well-founded induction on `Fintype.card pdata.tree.V` using `prune_degree_one_root` (`deg = 1`), `suppress_degree_two_root` (`deg = 2`), and `stabilize_prestable_tree_of_stable_root` (`deg ≥ 3` or non-constant).
   - In `GromovCompactness/Compactness/GenusZero.lean`:
     * Prove `gromov_compactness_core` (`G03`) **with zero direct `sorry`** by calling `assemble_prestable_limit` (`G01`) and `stabilize_prestable_tree` (`G02`) and packaging `CompactnessWitness`.
     * Prove the second branch of `gromov_subsequence_alternative` **with zero direct `sorry`** using `CompactSpace M` and `gromov_compactness_core`.
2. **Component 2 (`Assembly.lean` — `G01 ↔ C02 + C03 + B07`)**:
   - In `GromovCompactness/Compactness/Assembly.lean`:
     * Wire `assemble_prestable_limit` (`G01`) so it explicitly calls `exists_concentration_data` (`C02`), `defect_measure_identity` (`C03`), `prestable_limit_singleton` (when $S = \emptyset$), and `resolve_single_defect_tree` (`B07`, when $S \ne \emptyset$), reducing any remaining obligation strictly to the leaf tree-grafting helper.
3. **Component 3 (`LocalTree.lean` — `B07 ↔ B06 + B05 + B04`)**:
   - In `GromovCompactness/Bubbling/LocalTree.lean`:
     * Wire `resolve_single_defect_tree` (`B07`) **with zero direct `sorry`** using `energy_rank_induction`, `local_defect_tree_of_empty_children` ($q = \emptyset$), `child_rank_strict_decrease` (`B06`), and `exists_one_level_decomposition` (`B04`), reducing the non-empty child step to a named leaf helper `graft_child_defect_trees`.
4. **Component 4 (`Measures.lean` — `C01` Weak-* Compactness)**:
   - In `GromovCompactness/Bubbling/Measures.lean`:
     * Prove `weak_energy_measure_compactness` (`C01`) **with zero direct `sorry`** using weak-* sequential compactness / Banach-Alaoglu on compact spaces, and wire `C01` directly into `C02` (`exists_concentration_data`).

Deliver a structured Hard Handoff report in `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_2/handoff.md` with compilable code blueprints, and message the orchestrator (`8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0`).


## 2026-11-05T05:59:04Z
Your working directory is /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_2.
You are explorer_m3_2 (teamwork_explorer).

Path to ORIGINAL_REQUEST.md: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md

Read your full task dispatch in /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_2/DISPATCH.md.

Mission:
Investigate and author machine-checked Lean 4 blueprints for P0-11 Core Call-Graph Wiring Components 1–4 (core_wiring_plan.md / Task G03-W):
1. Component 1: In Stabilize.lean (G02), enrich stabilize_prestable_tree to return all 5 CompactnessWitness fields, and prove via well-founded induction with ZERO direct sorry; in GenusZero.lean (G03), prove gromov_compactness_core and gromov_subsequence_alternative with ZERO direct sorry.
2. Component 2: In Assembly.lean (G01), wire assemble_prestable_limit to call C02, C03, and B07 directly.
3. Component 3: In LocalTree.lean (B07), wire resolve_single_defect_tree with ZERO direct sorry using energy_rank_induction and B04/B06.
4. Component 4: In Measures.lean (C01), prove weak_energy_measure_compactness with ZERO direct sorry and wire into C02.

Deliver your report in .agents/teamwork/explorer_m3_2/handoff.md and message the orchestrator (8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0).
