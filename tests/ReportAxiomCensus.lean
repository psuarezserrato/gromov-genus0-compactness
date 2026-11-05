import GromovCompactness
open Lean Elab Command

/-- Census: for every theorem/def in the `GromovCompactness` namespace (from project modules),
report whether it transitively depends on `sorryAx`. -/
elab "#sorry_census" : command => do
  let env ← getEnv
  let mut clean : Nat := 0
  let mut dirty : Array Name := #[]
  let mut thmClean : Nat := 0
  let mut thmDirty : Nat := 0
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`GromovCompactness).isPrefixOf modName do continue
    if n.isInternal then continue
    let axs ← liftCoreM <| Lean.collectAxioms n
    let isThm := match ci with | .thmInfo _ => true | _ => false
    if axs.contains ``sorryAx then
      dirty := dirty.push n
      if isThm then thmDirty := thmDirty + 1
    else
      clean := clean + 1
      if isThm then thmClean := thmClean + 1
    for a in axs do
      unless a == ``sorryAx || a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        logInfo m!"NONSTANDARD AXIOM {a} in {n}"
  logInfo m!"declarations clean={clean} sorry-dependent={dirty.size}; theorems clean={thmClean} sorry-dependent={thmDirty}"

#sorry_census

#print axioms GromovCompactness.gromov_compactness_genus_zero
#print axioms GromovCompactness.gromov_compactness_component_bounds
#print axioms GromovCompactness.Topology.component_count_bounds
