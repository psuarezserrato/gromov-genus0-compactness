# Handoff Report: Fast Kernel Axiom Census Tool (P0-6)

## 1. Observation

1. **`tests/ReportAxiomCensus.lean` bottleneck**:
   - In `tests/ReportAxiomCensus.lean:17`, the census loop executes:
     ```lean
     let axs ← liftCoreM <| Lean.collectAxioms n
     ```
   - In `Lean/Util/CollectAxioms.lean:40-43`, `Lean.collectAxioms` is defined as:
     ```lean
     def collectAxioms [Monad m] [MonadEnv m] (constName : Name) : m (Array Name) := do
       let env ← getEnv
       let (_, s) := ((CollectAxioms.collect constName).run env).run {}
       pure s.axioms
     ```
   - On each of the 1,575 project constants, it initializes a brand new state `{}` (`visited := {}`, `axioms := #[]`) and traverses down into 609,976 environment constants, re-traversing identical Mathlib subtrees millions of times.
   - Result: Execution takes ~12 minutes (~720 seconds).

2. **Lean CLI argument behavior**:
   - Running `lake env lean tests/ReportAxiomCensus.lean -- GromovCompactness` outputs verbatim:
     ```
     stderr: Expected exactly one file name
     code: 1
     ```
   - Lean without `--run` strictly enforces a single file argument and does not allow positional CLI parameters after `--`.

3. **Environment variable accessibility in `CommandElabM`**:
   - `IO.getEnv "MODULE_PREFIX"` evaluates cleanly inside custom commands during elaboration (`elab "#cmd" : command => do ...`).

4. **Empirical benchmarking of memoized traversal**:
   - Benchmarking the single memoized traversal state `MemoAxioms.State` over all declarations in `GromovCompactness` yielded:
     ```
     Total elapsed: 4614 ms
     declarations clean=1194 sorry-dependent=54; theorems clean=748 sorry-dependent=48
     Total memoized constants: 46003
     ```
   - This matches `COMPLETION_PLAN.md:35-36` verbatim:
     `| Constants depending only on standard axioms | 1,194 (748 theorems), incl. compiler-generated |`
     `| Constants depending on sorryAx | 54 (48 theorems) |`
   - Scoped run on dirty module `GromovCompactness.Extensions.Automorphisms`:
     - Elapsed time: `2962 ms` (< 3 seconds)
     - Total declarations in scope: `41` (theorems: `21`)
     - Clean declarations: `35` (theorems: `15`)
     - Sorry-dependent: `6` (theorems: `6`)
     - Verbatim dirty declarations:
       - `GromovCompactness.Extensions.ghost_component_pure_automorphism_trivial`
       - `GromovCompactness.Extensions.pure_component_automorphisms_finite`
       - `GromovCompactness.Extensions.nonconstant_component_automorphism_finite`
       - `GromovCompactness.Extensions.stability_iff_finite_automorphisms`
       - `GromovCompactness.Extensions.moebius_three_point_rigidity`
       - `GromovCompactness.Extensions.full_automorphisms_finite_iff_pure_finite`
     - Process exit code: `1` (via `throwError`).
   - Scoped run on clean module `GromovCompactness.Extensions.Homology`:
     - Elapsed time: `3110 ms` (< 3.2 seconds)
     - Total declarations in scope: `40` (theorems: `18`)
     - Clean: `40` (theorems: `18`)
     - Sorry-dependent: `0`
     - Output: `STATUS: CLEAN (0 sorryAx dependencies)`
     - Process exit code: `0`.

---

## 2. Logic Chain

1. **Bottleneck Mechanism** (from Observation 1):
   Because `Lean.collectAxioms` starts with an empty `visited` set for each declaration, analyzing 1,575 project declarations requires traversing millions of constant references across Mathlib's deep hierarchy. The computation is dominated by redundant graph traversals.

2. **Memoization Sufficiency & Soundness** (from Observation 4):
   A constant's transitively depended axioms are invariant across traversals. By caching the collected axioms for each constant in a persistent map `memo : Lean.NameMap (Array Name)` across the entire run:
   - Every Mathlib/Core constant is traversed at most once.
   - For all 1,575 project declarations, traversal completes in **4.614 seconds** (a **156x speedup**), well below the 3-minute threshold.
   - Cycle safety is achieved by pre-inserting `c` into `s.visited` before exploring children. Since Lean axioms cannot participate in mutual inductive type definitions, breaking back-edges by returning `#[]` never suppresses an axiom.

3. **Execution Protocol & Exit Code** (from Observations 2, 3, 4):
   Because `lean <file>` does not accept positional arguments after `--`, scoping must be supplied via environment variable `MODULE_PREFIX` or `PHASE_MODULE` (defaulting to `GromovCompactness`).
   Inside `#phase_axiom_census`:
   - If `dirty.isEmpty && nonstandard.isEmpty`, the command completes successfully, yielding process exit code `0`.
   - If `dirty.size > 0`, it prints all dirty constant names and executes `throwError`, causing `lean` to terminate with process exit code `1`.

---

## 3. Caveats

1. **Clean compilation prerequisite**: `lake env lean tests/PhaseAxiomCensus.lean` requires `GromovCompactness` to be compiled (`lake build GromovCompactness` exit code 0). If the project does not compile, Lean fails at the `import GromovCompactness` line.
2. **Module namespace vs declaration name**: Filtering is performed via `targetPrefix.isPrefixOf modName` using `env.header.moduleNames[idx.toNat]!`. This accurately captures all declarations physically authored within the targeted module, regardless of whether a declaration is opened in a sub-namespace.

---

## 4. Conclusion

1. Task P0-6 is fully designed, benchmarked, and verified.
2. Replacing `Lean.collectAxioms` with a memoized DAG collector `MemoAxioms.collect` reduces census runtime from 12 minutes to **4.6 seconds** (full library) and **2.9 seconds** (scoped submodules).
3. The implementation cleanly distinguishes clean vs dirty declarations, prints exact names of all sorryAx-dependent constants, and returns exit code 0 on clean scopes and 1 on failures.
4. The complete, drop-in Lean 4 source code for `tests/PhaseAxiomCensus.lean` and `tools/phase_axiom_census.sh` is provided in `analysis.md` §6.

---

## 5. Verification Method

1. **Verify scoped clean execution (Homology)**:
   ```bash
   MODULE_PREFIX=GromovCompactness.Extensions.Homology lake env lean tests/PhaseAxiomCensus.lean
   echo "Exit code: $?"
   # Expected output: STATUS: CLEAN, Exit code: 0
   ```
2. **Verify scoped dirty execution (Automorphisms)**:
   ```bash
   MODULE_PREFIX=GromovCompactness.Extensions.Automorphisms lake env lean tests/PhaseAxiomCensus.lean
   echo "Exit code: $?"
   # Expected output: STATUS: FAILED (6 sorryAx dependencies), lists 6 contracts (#30, #31, #32, #33, #34, #35), Exit code: 1
   ```
3. **Verify library-wide baseline execution**:
   ```bash
   lake env lean tests/PhaseAxiomCensus.lean
   echo "Exit code: $?"
   # Expected output: 1194 clean, 54 sorryAx-dependent, Exit code: 1
   ```
4. **Invalidation condition**:
   The design is invalidated if runtime exceeds 180 seconds or if the list of 54 dirty declarations diverges from `ReportAxiomCensus.lean`.
