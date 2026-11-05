import GromovCompactness
import Lean.Data.Json
open Lean Meta

/--
Export public Mathlib and GromovCompactness declarations (theorems, definitions, structures)
with their docstrings and types to a JSONL file.
-/
def exportDecls (outPath : String) : MetaM Unit := do
  let env ← getEnv
  let handle ← IO.FS.Handle.mk outPath IO.FS.Mode.write
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`Mathlib).isPrefixOf modName || (`GromovCompactness).isPrefixOf modName do continue
    
    -- Filter out recursors and boilerplate internal projections
    let s := n.toString
    if s.endsWith ".rec" || s.endsWith ".casesOn" || s.endsWith ".recOn" ||
       s.endsWith ".brecOn" || s.endsWith ".noConfusion" || s.endsWith ".injEq" then
      continue
    
    let kind := match ci with
      | .thmInfo _ => "thm"
      | .defnInfo _ => "def"
      | .inductInfo _ => "inductive"
      | _ => "other"
    if kind == "other" then continue

    let docOpt ← findDocString? env n
    let typeFmt ← ppExpr ci.type
    let j := Json.mkObj [
      ("name", Json.str s),
      ("module", Json.str modName.toString),
      ("kind", Json.str kind),
      ("doc", Json.str (docOpt.getD "")),
      ("type", Json.str (toString typeFmt))
    ]
    handle.putStrLn j.compress
    count := count + 1
  handle.flush
  IO.println s!"Exported {count} declarations to {outPath}."

def main (args : List String) : IO Unit := do
  let outPath := args.head?.getD "data/mathlib_project_declarations.jsonl"
  let env ← importModules #[{ module := `GromovCompactness }] {}
  let coreCtx : Core.Context := { fileName := "export_decls", fileMap := FileMap.ofString "" }
  let coreState : Core.State := { env := env }
  let metaCtx : Meta.Context := {}
  let metaState : Meta.State := {}
  let ((_, _), _) ← (exportDecls outPath).run metaCtx metaState |>.toIO coreCtx coreState
