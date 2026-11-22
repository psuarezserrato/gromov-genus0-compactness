/-
Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
Released under the GNU Affero General Public License v3.0 (AGPLv3) for non-commercial use;
see LICENSE.md for details.
This project is licensed under non-commercial use. If you wish to use this software in a
commercial product, service, or enterprise environment, please contact the developer to purchase
a commercial license or negotiate royalty terms.
Authors: Pablo Suárez-Serrato (November 2026)
-/

import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.LibraryAudit
import Lean

open Lean Elab Command

def standardAxioms : List Name :=
  [`propext, `Classical.choice, `Quot.sound]

def getAxioms (env : Environment) (name : Name) : Array Name :=
  let (_, s) := (CollectAxioms.collect name env).run {}
  s.axioms

elab "#audit_all_axioms" : command => do
  let env ← getEnv
  let mut count := 0
  let mut badCount := 0
  for (name, _) in env.constants do
    if name.toString.startsWith "GromovCompactness" then
      let axioms := getAxioms env name
      let nonStd := axioms.filter (fun ax => !standardAxioms.contains ax)
      if !nonStd.isEmpty then
        logError m!"Declaration {name} depends on non-standard axioms: {nonStd.toList}"
        badCount := badCount + 1
      count := count + 1
  logInfo m!"Audit complete: Checked {count} declarations in namespace GromovCompactness. Non-standard axiom violations: {badCount}"
  if badCount > 0 then
    throwError "Integrity violation: non-standard axioms detected!"

#audit_all_axioms
