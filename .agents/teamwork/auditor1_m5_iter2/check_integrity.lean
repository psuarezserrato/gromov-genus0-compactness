import GromovCompactness
import GromovCompactness.Analysis.HoferRescaling
import Lean

open Lean

def checkPureAxioms (declName : Name) : MetaM Unit := do
  let env ← getEnv
  let axioms := env.find? declName
  let axs ← Lean.collectAxioms declName
  let standard : List Name := [`propext, `Classical.choice, `Quot.sound]
  for ax in axs do
    if !standard.contains ax then
      throwError s!"INTEGRITY FAILURE: Declaration {declName} depends on non-standard axiom {ax}!"
  IO.println s!"[PASS] {declName} depends only on standard axioms: {axs.toList}"

def runAudit : MetaM Unit := do
  IO.println "=== FORENSIC AXIOM INTEGRITY AUDIT (auditor1_m5_iter2) ==="
  let pureDecls : List Name := [
    `GromovCompactness.Analysis.tendsto_one_div_succ_zero,
    `GromovCompactness.Analysis.tendsto_dist_zero_of_le_inv_succ,
    `GromovCompactness.Analysis.tendsto_scale_zero_of_le_inv_succ,
    `GromovCompactness.Analysis.energyMeasure_disk_at_zero,
    `GromovCompactness.Analysis.antitone_closedBall_inv_succ,
    `GromovCompactness.Analysis.tendsto_measure_closedBall_inv_succ,
    `GromovCompactness.Analysis.atom_iff_concentration,
    `GromovCompactness.Analysis.has_energy_defect_iff_concentration,
    `GromovCompactness.Analysis.card_le_of_atoms,
    `GromovCompactness.Analysis.finite_atoms_of_bounded_measure,
    `GromovCompactness.Analysis.atoms_card_le,
    `GromovCompactness.Analysis.exists_target_thresholds_of_modules,
    `GromovCompactness.Analysis.rescaled_curve,
    `GromovCompactness.Analysis.hofer_gradient_rescaling,
    `GromovCompactness.Analysis.hofer_rescaling_ball_inclusion,
    `GromovCompactness.Analysis.hofer_rescaling_calibration,
    `GromovCompactness.Analysis.hofer_rescaling_gradient_bound,
    `GromovCompactness.Analysis.hofer_single_step,
    `GromovCompactness.Analysis.ivt_radial_energy_of_continuous,
    `GromovCompactness.Analysis.test_radial_ivt,
    `GromovCompactness.Analysis.exists_calibrated_rescaling_of_ivt,
    `GromovCompactness.Analysis.exists_calibrated_rescaling,
    `GromovCompactness.Analysis.bubble_energy_ge_sphere_gap,
    `GromovCompactness.Bubbling.exists_target_thresholds_of_modules,
    `GromovCompactness.Bubbling.exists_calibrated_rescaling_of_ivt,
    `GromovCompactness.Bubbling.exists_calibrated_rescaling,
    `GromovCompactness.Bubbling.bubble_energy_ge_sphere_gap
  ]
  for d in pureDecls do
    checkPureAxioms d

#eval runAudit
