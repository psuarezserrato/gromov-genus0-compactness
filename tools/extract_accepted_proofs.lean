import GromovCompactness
import Lean.Data.Json
open Lean Meta

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

end MemoAxioms

/--
Exports metadata for all clean verified theorems in GromovCompactness to a JSONL file.
-/
def exportManifest (outPath : String) : MetaM Unit := do
  let env ← getEnv
  let mut thms : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`GromovCompactness).isPrefixOf modName do continue
    if n.isInternal then continue
    match ci with
    | .thmInfo _ => thms := thms.push n
    | _ => pure ()

  let mut state : MemoAxioms.State := {}
  let mut cleanRecords : Array (Name × Array Name) := #[]
  let mut dirtyCount : Nat := 0

  for n in thms do
    let (axs, nextState) := (MemoAxioms.collect n env).run state
    state := nextState
    if axs.contains ``sorryAx then
      dirtyCount := dirtyCount + 1
    else
      let sortedAxs := axs.qsort (fun a b => a.toString < b.toString)
      cleanRecords := cleanRecords.push (n, sortedAxs)

  IO.println s!"Total GromovCompactness theorems: {thms.size} (Clean: {cleanRecords.size}, Dirty: {dirtyCount})"
  
  let handle ← IO.FS.Handle.mk outPath IO.FS.Mode.write
  for (n, axs) in cleanRecords do
    let some ci := env.find? n | continue
    let docOpt ← findDocString? env n
    let rangesOpt ← findDeclarationRanges? n
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    let typeFmt ← ppExpr ci.type
    let usedConsts := ci.value?.map (fun v => v.getUsedConstants) |>.getD #[]
    
    let (startLine, endLine) := match rangesOpt with
      | some r => (r.range.pos.line, r.range.endPos.line)
      | none => (0, 0)
    
    let j := Json.mkObj [
      ("name", Json.str n.toString),
      ("module", Json.str modName.toString),
      ("doc", Json.str (docOpt.getD "")),
      ("type", Json.str (toString typeFmt)),
      ("start_line", Json.num startLine),
      ("end_line", Json.num endLine),
      ("premises", Json.arr (usedConsts.map (fun c => Json.str c.toString))),
      ("axioms", Json.arr (axs.map (fun a => Json.str a.toString)))
    ]
    handle.putStrLn j.compress
  handle.flush
  IO.println s!"Exported {cleanRecords.size} clean theorem records to {outPath}."

def main (args : List String) : IO Unit := do
  let outPath := args.head?.getD "data/raw_accepted_theorems.jsonl"
  let env ← importModules #[{ module := `GromovCompactness }] {}
  let coreCtx : Core.Context := { fileName := "extract", fileMap := FileMap.ofString "" }
  let coreState : Core.State := { env := env }
  let metaCtx : Meta.Context := {}
  let metaState : Meta.State := {}
  let ((_, _), _) ← (exportManifest outPath).run metaCtx metaState |>.toIO coreCtx coreState
