import tests.ChallengePhase2ModelA
import Lean

open Lean

def checkPureAxioms (declName : Name) : MetaM Unit := do
  let axs ← Lean.collectAxioms declName
  let standard : List Name := [`propext, `Classical.choice, `Quot.sound]
  for ax in axs do
    if !standard.contains ax then
      throwError s!"INTEGRITY FAILURE: Declaration {declName} depends on non-standard axiom {ax}!"
  IO.println s!"[PASS] {declName} depends only on standard axioms: {axs.toList}"

def runAudit : MetaM Unit := do
  IO.println "=== FORENSIC TEST AXIOM INTEGRITY AUDIT (auditor1_m5_iter2) ==="
  let pureDecls : List Name := [
    `VerifyChallengeQueries.challenge_query_B01_reduction,
    `VerifyChallengeQueries.challenge_query_B02
  ]
  for d in pureDecls do
    checkPureAxioms d

#eval runAudit
