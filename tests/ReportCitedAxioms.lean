import GromovCompactness
open Lean Elab Command

/-- For each given short name, find project declarations whose last name component matches,
and report whether they depend on `sorryAx`. -/
elab "#check_cited " ids:ident* : command => do
  let env ← getEnv
  for id in ids do
    let short := id.getId.toString
    let mut found := false
    for (n, _) in env.constants.toList do
      let some idx := env.getModuleIdxFor? n | continue
      let modName := env.header.moduleNames[idx.toNat]!
      unless (`GromovCompactness).isPrefixOf modName do continue
      if n.isInternal then continue
      match n with
      | .str _ s =>
        if s == short then
          found := true
          let axs ← liftCoreM <| Lean.collectAxioms n
          let tag := if axs.contains ``sorryAx then "SORRY" else "CLEAN"
          logInfo m!"{tag} {n} {axs.toList}"
      | _ => pure ()
    unless found do logInfo m!"NOTFOUND {short}"

#check_cited metric_symm metric_pos_def metric_J_invariant jholomorphic_coordinate_invariance
  exists_unique_moebius_three_points affine_scaling_toHomeo_ne_id countable_diagonal_extraction
  tree_degree_sum ghost_components_bound hofer_gradient_rescaling exists_target_thresholds_of_modules
  exists_target_thresholds exists_calibrated_rescaling_of_ivt exists_calibrated_rescaling
  energy_rank_strict_decrease child_rank_strict_decrease child_mass_le_parent_sub_h
  ghost_component_branches ghost_bubble_degree_ge_three card_q_floor_le ghost_branching
  concentration_singular_set_properties card_S_floor_le defect_measure_total_mass
  component_count_bounds component_count_bounds_marked principal_components_energy_bound
  crossRatioC_translation crossRatioC_scaling moduli_space_t2 energy_nonneg
  gromov_compactness_component_bounds gromov_compactness_genus_zero gromov_compactness_core
  tendsto_integral limsup_closed_le
