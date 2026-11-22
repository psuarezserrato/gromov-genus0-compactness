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

open Lean Meta

def checkAxioms (env : Environment) (modName : Name) : IO Unit := do
  IO.println s!"Checking declarations in module {modName}:"
  let standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]
  for (name, cinfo) in env.constants do
    if name.getPrefix == modName || (`GromovCompactness).isPrefixOf name then
      let (_, axioms) := collectAxioms name |>.run env
      let nonStandard := axioms.toList.filter (fun ax => !standardAxioms.contains ax)
      if !nonStandard.isEmpty then
        IO.println s!"VIOLATION: Declaration '{name}' depends on non-standard axioms: {nonStandard}"
      else
        IO.println s!"PASS: '{name}' axioms: {axioms.toList}"

def main : IO Unit := do
  let env ← importModules #[{ module := `GromovCompactness.Geometry.Sphere }] {}
  let standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  let mut violations := 0
  for (name, _) in env.constants do
    if (`GromovCompactness).isPrefixOf name then
      count := count + 1
      let (_, axioms) := collectAxioms name |>.run env
      let nonStandard := axioms.toList.filter (fun ax => !standardAxioms.contains ax)
      if !nonStandard.isEmpty then
        violations := violations + 1
        IO.println s!"VIOLATION: '{name}' depends on non-standard axioms: {nonStandard}"
      else
        IO.println s!"'{name}' depends on: {axioms.toList}"
  IO.println s!"Checked {count} GromovCompactness declarations. Total non-standard axiom violations: {violations}."

