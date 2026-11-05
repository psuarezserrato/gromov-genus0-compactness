import GromovCompactness
open Lean Elab Command

namespace MemoAxioms

/-- Persistent traversal state memoizing the collected axioms of visited constants. -/
structure State where
  visited : Lean.NameSet := {}
  memo    : Lean.NameMap (Array Name) := {}

abbrev M := ReaderT Environment (StateM State)

/-- Extract all constant names referenced directly by a ConstantInfo. -/
def getDirectConstants (ci : ConstantInfo) : Array Name := Id.run do
  let mut consts : Lean.NameSet := {}
  let addExpr (e : Expr) (s : Lean.NameSet) : Lean.NameSet :=
    e.getUsedConstants.foldl (init := s) fun acc c => acc.insert c
  consts := addExpr ci.type consts
  match ci with
  | .defnInfo v   => consts := addExpr v.value consts
  | .thmInfo v    => consts := addExpr v.value consts
  | .opaqueInfo v => consts := addExpr v.value consts
  | .inductInfo v =>
    for c in v.ctors do
      consts := consts.insert c
  | _ => pure ()
  return consts.toArray

/-- Collect all axioms transitively depended on by constant `c`, with cycle-safety and memoization. -/
partial def collect (c : Name) : M (Array Name) := do
  let s ← get
  if let some axs := s.memo.find? c then
    return axs
  if s.visited.contains c then
    -- Active cycle detected (e.g. mutual inductive / ctor types); return empty safely.
    return #[]
  modify fun st => { st with visited := st.visited.insert c }
  let env ← read
  let some ci := env.find? c | return #[]
  let axs ← match ci with
    | .axiomInfo _ => pure #[c]
    | .quotInfo _  => pure #[]
    | _ => do
      let direct := getDirectConstants ci
      let mut res : Lean.NameSet := {}
      for d in direct do
        let dAxs ← collect d
        for a in dAxs do
          res := res.insert a
      pure res.toArray
  modify fun st => { st with memo := st.memo.insert c axs }
  return axs

/-- Collect all constants transitively referenced by a root constant via iterative BFS traversal. -/
def getTransitiveClosure (root : Name) (env : Environment) : Lean.NameSet := Id.run do
  let mut visited : Lean.NameSet := {}
  let mut queue : Array Name := #[root]
  while !queue.isEmpty do
    let c := queue.back!
    queue := queue.pop
    if visited.contains c then
      continue
    visited := visited.insert c
    let some ci := env.find? c | continue
    let direct := getDirectConstants ci
    for d in direct do
      if !visited.contains d then
        queue := queue.push d
  return visited

/-- Check whether a declaration contains a direct sorryAx in its proof or definition value. -/
def hasDirectSorry (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo v   => v.value.getUsedConstants.contains ``sorryAx
  | .thmInfo v    => v.value.getUsedConstants.contains ``sorryAx
  | .opaqueInfo v => v.value.getUsedConstants.contains ``sorryAx
  | _             => false

end MemoAxioms

/--
Mechanical Call-Graph Wiring and Direct-Sorry Audit Command (Task P0-11 / Component 5).
Verifies:
1. `GromovCompactness.gromov_compactness_genus_zero` transitively references the core contract chain:
   `gromov_compactness_core`, `stabilize_prestable_tree`, `assemble_prestable_limit`,
   `exists_concentration_data`, `defect_measure_identity`, `resolve_single_defect_tree`,
   `TargetThresholds`, `nonlinear_elliptic_bootstrap`, `puncture_sobolev_extension`.
2. Target intermediate reduction theorems have ZERO direct sorry in their proof bodies:
   `gromov_compactness_core`, `gromov_subsequence_alternative`, `stabilize_prestable_tree`,
   `resolve_single_defect_tree`, `weak_energy_measure_compactness`, `removal_of_singularities`.
-/
elab "#audit_wiring" : command => do
  let env ← getEnv
  let startTime ← IO.monoMsNow
  
  let root := `GromovCompactness.gromov_compactness_genus_zero
  let some _ := env.find? root |
    throwError m!"Wiring audit failed: root declaration '{root}' not found in environment"

  logInfo m!"=================================================="
  logInfo m!"Starting Mechanical Call-Graph Wiring Audit (#audit_wiring)"
  logInfo m!"Root declaration: {root}"
  logInfo m!"=================================================="

  -- 1. Transitive Call Graph Reachability
  let deps := MemoAxioms.getTransitiveClosure root env
  logInfo m!"[Graph] Transitive dependency closure size: {deps.size} constants"

  let requiredConnections : List (Name × String) := [
    (`GromovCompactness.gromov_compactness_core, "Core compactness theorem (G03)"),
    (`GromovCompactness.Assembly.stabilize_prestable_tree, "Master stabilization theorem (G02)"),
    (`GromovCompactness.Assembly.assemble_prestable_limit, "Global prestable limit assembly (G01)"),
    (`GromovCompactness.Compactness.exists_concentration_data, "Concentration data extraction (C02)"),
    (`GromovCompactness.Compactness.defect_measure_identity, "Defect measure identity (C03)"),
    (`GromovCompactness.Bubbling.resolve_single_defect_tree, "Single defect tree resolution (B07)"),
    (`GromovCompactness.Analysis.TargetThresholds, "Universal bubbling threshold bundle (B01)"),
    (`GromovCompactness.Analysis.nonlinear_elliptic_bootstrap, "Nonlinear elliptic bootstrap (A05)"),
    (`GromovCompactness.Analysis.puncture_sobolev_extension, "Puncture Sobolev extension (A11)")
  ]

  let mut missingConnections : List Name := []
  for (target, desc) in requiredConnections do
    if deps.contains target then
      logInfo m!"[PASS] Connected: {target} ({desc})"
    else
      logError m!"[FAIL] Missing call-graph link: {target} ({desc})"
      missingConnections := target :: missingConnections

  -- 2. Zero Direct Sorry in Target Proof Bodies
  let zeroSorryTargets : List (Name × String) := [
    (`GromovCompactness.gromov_compactness_core, "gromov_compactness_core (G03)"),
    (`GromovCompactness.gromov_subsequence_alternative, "gromov_subsequence_alternative (G03 alternative)"),
    (`GromovCompactness.Assembly.stabilize_prestable_tree, "stabilize_prestable_tree (G02)"),
    (`GromovCompactness.Bubbling.resolve_single_defect_tree, "resolve_single_defect_tree (B07)"),
    (`GromovCompactness.Compactness.weak_energy_measure_compactness, "weak_energy_measure_compactness (C01)"),
    (`GromovCompactness.Analysis.removal_of_singularities, "removal_of_singularities (A12)")
  ]

  let mut directSorryFound : List Name := []
  for (target, desc) in zeroSorryTargets do
    if let some ci := env.find? target then
      if MemoAxioms.hasDirectSorry ci then
        logError m!"[FAIL] Direct sorry in proof body: {target} ({desc})"
        directSorryFound := target :: directSorryFound
      else
        logInfo m!"[PASS] Zero direct sorry in proof body: {target} ({desc})"
    else
      logError m!"[FAIL] Target declaration not found: {target} ({desc})"
      directSorryFound := target :: directSorryFound

  let endTime ← IO.monoMsNow
  let elapsedMs := endTime - startTime
  logInfo m!"=================================================="
  logInfo m!"Audit completed in {elapsedMs} ms"

  if !missingConnections.isEmpty || !directSorryFound.isEmpty then
    logInfo m!"STATUS: WIRING AUDIT FAILED ({missingConnections.length} missing connections, {directSorryFound.length} direct sorry bodies)"
    logInfo m!"=================================================="
    throwError m!"Wiring audit failed: {missingConnections.length} missing connections, {directSorryFound.length} direct sorry bodies"
  else
    logInfo m!"STATUS: WIRING AUDIT PASSED"
    logInfo m!"All 9 core contracts verified in transitive call graph of {root}"
    logInfo m!"All 6 intermediate theorems verified with 0 direct sorry in proof bodies"
    logInfo m!"=================================================="

/--
Fast, module-scoped kernel axiom census command (Task P0-6).
Scans declarations matching `MODULE_PREFIX` (or `PHASE_MODULE`, default `GromovCompactness`).
Prints exact sorryAx-dependent declarations and throws an error on failure (exit code 1).
-/
elab "#phase_axiom_census" : command => do
  let env ← getEnv
  let envVar ← IO.getEnv "MODULE_PREFIX"
  let envVar2 ← IO.getEnv "PHASE_MODULE"
  let rawPrefix := (envVar.orElse fun () => envVar2).getD "GromovCompactness"
  let prefixStr := rawPrefix.trim
  if prefixStr.isEmpty then
    logInfo m!"=================================================="
    logInfo m!"STATUS: ERROR (empty module prefix)"
    logInfo m!"=================================================="
    throwError m!"Phase axiom census failed: module prefix cannot be empty"

  let targetPrefix := prefixStr.toName
  if targetPrefix.isAnonymous then
    logInfo m!"=================================================="
    logInfo m!"STATUS: ERROR (anonymous module prefix)"
    logInfo m!"=================================================="
    throwError m!"Phase axiom census failed: module prefix cannot be empty or anonymous"

  let startTime ← IO.monoMsNow
  let mut clean : Nat := 0
  let mut dirty : Array Name := #[]
  let mut thmClean : Nat := 0
  let mut thmDirty : Nat := 0
  let mut nonstandard : Array (Name × Name) := #[]
  let mut state : MemoAxioms.State := {}

  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless targetPrefix.isPrefixOf modName do continue
    if n.isInternal then continue
    let (axs, nextState) := (MemoAxioms.collect n env).run state
    state := nextState
    let isThm := match ci with | .thmInfo _ => true | _ => false
    if axs.contains ``sorryAx then
      dirty := dirty.push n
      if isThm then thmDirty := thmDirty + 1
    else
      clean := clean + 1
      if isThm then thmClean := thmClean + 1
    for a in axs do
      unless a == ``sorryAx || a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        nonstandard := nonstandard.push (n, a)

  let endTime ← IO.monoMsNow
  let elapsedMs := endTime - startTime
  let total := clean + dirty.size

  logInfo m!"=================================================="
  logInfo m!"Phase Axiom Census: scope={targetPrefix}"
  logInfo m!"Elapsed time: {elapsedMs} ms"
  logInfo m!"Total declarations in scope: {total} (theorems: {thmClean + thmDirty})"
  logInfo m!"Clean declarations: {clean} (theorems: {thmClean})"
  logInfo m!"Sorry-dependent: {dirty.size} (theorems: {thmDirty})"

  for (n, a) in nonstandard do
    logError m!"NONSTANDARD AXIOM: {a} in {n}"

  if total == 0 then
    logInfo m!"STATUS: ERROR (0 declarations found for prefix {targetPrefix})"
    logInfo m!"=================================================="
    throwError m!"Phase axiom census failed: 0 declarations found for prefix {targetPrefix}"
  else if !nonstandard.isEmpty then
    logInfo m!"STATUS: FAILED ({nonstandard.size} nonstandard axiom occurrences)"
    for (n, a) in nonstandard do
      logInfo m!"  - {n} uses nonstandard axiom {a}"
    logInfo m!"=================================================="
    throwError m!"Phase axiom census failed: found {nonstandard.size} declarations with nonstandard axioms in scope {targetPrefix}"
  else if !dirty.isEmpty then
    logInfo m!"STATUS: FAILED ({dirty.size} sorryAx dependencies)"
    for d in dirty do
      logInfo m!"  - {d}"
    logInfo m!"=================================================="
    throwError m!"Phase axiom census failed: found {dirty.size} declarations depending on sorryAx in scope {targetPrefix}"
  else
    logInfo m!"STATUS: CLEAN (0 sorryAx dependencies)"
    logInfo m!"All declarations depend strictly on standard axioms: [propext, Classical.choice, Quot.sound]"
    logInfo m!"=================================================="

#audit_wiring
#phase_axiom_census
