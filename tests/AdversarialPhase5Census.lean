/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Master Adversarial Challenger 1 (challenger_m5_1)
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Data.Fintype.Card
import GromovCompactness
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Topology.SphereTree
import GromovCompactness.Analysis.Energy
import GromovCompactness.Extensions.VaryingJ
import GromovCompactness.Extensions.Automorphisms

open Lean Elab Command
open scoped Manifold ContDiff Topology Classical
open Metric Set GromovCompactness Classical
open GromovCompactness.Extensions

namespace GromovCompactness.AdversarialPhase5Census

/-!
# Master Empirical Adversarial Challenge Suite: Phase 5 Deliverables

This test suite executes empirical adversarial verification across:
1. `Target.lean`: Smoothness, closedness, and non-degeneracy of (M, ω, J); refuting non-closed forms.
2. `Energy.lean`: Spherical Jacobian factor, positive energy for non-constant smooth maps,
   zero energy for constant maps, quadratic trace vs volume scaling cancellation, conformal invariance.
3. `Sphere.lean` & `SphereTree.lean`: Möbius frames, tree degree sums, ghost component bounds,
   acyclic tree grafting.
4. `VaryingJ.lean`: Symmetrized metric properties, Riemannian-symplectic area density identity,
   uniform threshold existence.
5. `Automorphisms.lean`: 3-point Möbius rigidity, necessity of 3 points (counterexample with 2 points),
   ghost component triviality, equivalence of full and pure automorphism finiteness.
6. `#run_adversarial_phase5_census`: Sensitivity testing and exhaustive axiom census audit.
-/

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [tgt : ClosedTameTarget I M]

/- =========================================================================
   1. TARGET GEOMETRY & REFINEMENT OF PREDICATES (Target.lean)
   ========================================================================= -/

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev F2 := E3 →L[ℝ] E3 →L[ℝ] ℝ

noncomputable def L_proj0 : E3 →L[ℝ] ℝ := ContinuousLinearMap.proj 0
noncomputable def e0_vec : E3 := WithLp.equiv 2 _ !₂[1, 0, 0]
noncomputable def e1_vec : E3 := WithLp.equiv 2 _ !₂[0, 1, 0]
noncomputable def e2_vec : E3 := WithLp.equiv 2 _ !₂[0, 0, 1]

lemma L_proj0_e0 : L_proj0 e0_vec = 1 := rfl
lemma L_proj0_e1 : L_proj0 e1_vec = 0 := rfl
lemma L_proj0_e2 : L_proj0 e2_vec = 0 := rfl

/-- Adversarial Probe 1.1: The cyclic exterior derivative of an explicit non-closed form is strictly non-zero. -/
theorem adversarial_omega_closed_refutes_nonclosed_form
    (b_form : F2)
    (hB : b_form e1_vec e2_vec = 1)
    (y : E3) :
    let form_omega : E3 →L[ℝ] F2 := ContinuousLinearMap.smulRight L_proj0 b_form
    let dω_y := fderiv ℝ (⇑form_omega) y
    dω_y e1_vec e2_vec e0_vec + dω_y e2_vec e0_vec e1_vec + dω_y e0_vec e1_vec e2_vec ≠ 0 := by
  intro form_omega dω_y
  have hd : dω_y = form_omega := by
    dsimp [dω_y, form_omega]
    exact (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := E3) (F := F2) form_omega (x := y)).fderiv
  rw [hd]
  dsimp [ContinuousLinearMap.smulRight, form_omega]
  rw [L_proj0_e1, L_proj0_e2, L_proj0_e0]
  simp [hB]

/-- Adversarial Probe 1.2: CP1 Target structure has strictly positive-definite metric on all non-zero vectors. -/
theorem adversarial_CP1_metric_pos_def (z : CP1) (v : TangentSpace I_CP1 z) (hv : v ≠ 0) :
    0 < ClosedTameTarget.metric I_CP1 z v v :=
  metric_pos_def I_CP1 z v hv

/-- Adversarial Probe 1.3: CP1 Target almost-complex structure satisfies J² = -id. -/
theorem adversarial_J_CP1_sq_identity (v : EuclideanSpace ℝ (Fin 2)) :
    J_CP1 (J_CP1 v) = -v :=
  J_CP1_sq v

/- =========================================================================
   2. ENERGY MEASURE, NON-CONSTANT MAPS, & CONFORMAL INVARIANCE (Energy.lean)
   ========================================================================= -/

/-- Adversarial Probe 2.1: The spherical Jacobian (2/(1+|w|²))² is strictly positive everywhere. -/
theorem adversarial_sphericalJacobian_pos (w : ℂ) :
    0 < sphericalJacobian w :=
  sphericalJacobian_pos w

/-- Adversarial Probe 2.2: Spherical Jacobian takes exact value 4 at origin. -/
theorem adversarial_sphericalJacobian_origin :
    sphericalJacobian 0 = 4 := by
  dsimp [sphericalJacobian]
  norm_num

/-- Adversarial Probe 2.3: Concrete non-constant smooth map on CP1 has strictly positive total energy. -/
theorem adversarial_concrete_nonconstant_positive_energy :
    0 < totalEnergy I_CP1 (id : CP1 → CP1) :=
  concrete_nonconstant_map_positive_energy

/-- Adversarial Probe 2.4: Concrete non-constant smooth map on CP1 has finite total energy. -/
theorem adversarial_concrete_nonconstant_finite_energy :
    energyMeasureExtended I_CP1 (id : CP1 → CP1) Set.univ < ⊤ :=
  concrete_nonconstant_map_finite_energy

/-- Adversarial Probe 2.5: Dilation trace scaling factor l² perfectly cancels volume dilation l⁻². -/
theorem adversarial_dilation_cancellation (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal (l ^ 2) * ENNReal.ofReal (l⁻¹ ^ 2) = 1 :=
  dilation_factor_cancellation l hl

/-- Adversarial Probe 2.6: Unconditional conformal invariance of energy under identity frame. -/
theorem adversarial_energy_conformal_invariant_id (u : CP1 → M) (A : Set CP1) :
    energyMeasure I (u ∘ MoebiusFrame.id.toHomeo) (MoebiusFrame.id.toHomeo ⁻¹' A) = energyMeasure I u A :=
  energy_conformal_invariant_id I u A

/- =========================================================================
   3. SPHERE TREES, DEGREE SUMS, & GHOST COMPONENT BOUNDS (SphereTree.lean)
   ========================================================================= -/

/-- Adversarial Probe 3.1: Tree degree sum identity ∑ deg(v) = 2(|V| - 1). -/
theorem adversarial_tree_degree_sum (tree : SphereTree) :
    ∑ v : tree.V, tree.adj.degree v = 2 * (Fintype.card tree.V - 1) :=
  tree_degree_sum tree

/-- Adversarial Probe 3.2: Ghost components bound G ≤ P - 2 and |V| ≤ 2P - 2. -/
theorem adversarial_ghost_components_bound
    (lim : StableSphereTreeLimit I (M := M))
    (P G : ℕ)
    (h_multivertex : 1 < Fintype.card lim.tree.V)
    (h_P : P = Fintype.card { v : lim.tree.V // is_principal_component I lim v })
    (h_G : G = Fintype.card { v : lim.tree.V // is_ghost_component I lim v }) :
    G ≤ P - 2 ∧ Fintype.card lim.tree.V ≤ 2 * P - 2 :=
  ghost_components_bound I lim P G h_multivertex h_P h_G

/-- Adversarial Probe 3.3: In any stable tree limit, a ghost component requires at least 3 principal components.
Specifically, if G ≥ 1, then P ≥ 3 and |V| ≥ 4. -/
theorem adversarial_ghost_requires_at_least_three_principal
    (lim : StableSphereTreeLimit I (M := M))
    (P G : ℕ)
    (h_multivertex : 1 < Fintype.card lim.tree.V)
    (h_P : P = Fintype.card { v : lim.tree.V // is_principal_component I lim v })
    (h_G : G = Fintype.card { v : lim.tree.V // is_ghost_component I lim v })
    (h_ghost_exists : 1 ≤ G) :
    3 ≤ P ∧ 4 ≤ Fintype.card lim.tree.V := by
  have ⟨h_gp, _⟩ := ghost_components_bound I lim P G h_multivertex h_P h_G
  have hP : 3 ≤ P := by omega
  have hV_eq : Fintype.card lim.tree.V = G + P := by
    have h_card_G : G = (Finset.univ.filter (is_ghost_component I lim)).card := by
      rw [h_G, Fintype.card_subtype]
    have h_card_P : P = (Finset.univ.filter (is_principal_component I lim)).card := by
      rw [h_P, Fintype.card_subtype]
    have h_prin_eq : Finset.univ.filter (is_principal_component I lim) =
        Finset.univ.filter (fun v => ¬ is_ghost_component I lim v) := by
      ext v; simp [is_principal_component]
    have h_sum_cards : (Finset.univ.filter (is_ghost_component I lim)).card +
        (Finset.univ.filter (is_principal_component I lim)).card = Fintype.card lim.tree.V := by
      rw [h_prin_eq, Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ]
    rw [h_card_G, h_card_P, h_sum_cards]
  have hV : 4 ≤ Fintype.card lim.tree.V := by omega
  exact ⟨hP, hV⟩

/- =========================================================================
   4. VARYING J GEOMETRY & ENERGY IDENTITIES (VaryingJ.lean)
   ========================================================================= -/

/-- Adversarial Probe 4.1: Symmetrized metric g_J is positive definite for any tamed J. -/
theorem adversarial_symmetrizedMetric_pos_def
    («ω» : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x)
    (h_tame : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < «ω» x v (J x v))
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < symmetrizedMetric I «ω» J x v v :=
  symmetrizedMetric_pos_def I «ω» J h_tame x v hv

/-- Adversarial Probe 4.2: Symmetrized metric g_J is J-invariant. -/
theorem adversarial_symmetrizedMetric_J_invariant
    («ω» : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (h_skew : ∀ (x : M) (v w : TangentSpace I x), «ω» x v w = - «ω» x w v)
    (J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x)
    (h_J_sq : ∀ (x : M) (v : TangentSpace I x), J x (J x v) = -v)
    (x : M) (v w : TangentSpace I x) :
    symmetrizedMetric I «ω» J x (J x v) (J x w) = symmetrizedMetric I «ω» J x v w :=
  symmetrizedMetric_J_invariant I «ω» h_skew J h_J_sq x v w

/-- Adversarial Probe 4.3: UniformTargetThresholds is inhabited for any varying almost complex sequence. -/
theorem adversarial_exists_uniform_target_thresholds
    (varying_J : VaryingAlmostComplexStructures I (M := M)) :
    Nonempty (UniformTargetThresholds I (M := M) varying_J) :=
  exists_uniform_target_thresholds I varying_J

/- =========================================================================
   5. AUTOMORPHISMS & 3-POINT RIGIDITY (Automorphisms.lean)
   ========================================================================= -/

/-- Adversarial Probe 5.1: 3-point Möbius rigidity: any Möbius matrix fixing 3 projective points is projectively trivial. -/
theorem adversarial_moebius_three_point_rigidity (M_mat : MoebiusMatrix) (v₁ v₂ v₃ : ℂ × ℂ)
    (h12 : ¬ ProjEquiv v₁ v₂) (h13 : ¬ ProjEquiv v₁ v₃) (h23 : ¬ ProjEquiv v₂ v₃)
    (hfix1 : ProjEquiv (M_mat.act v₁) v₁)
    (hfix2 : ProjEquiv (M_mat.act v₂) v₂)
    (hfix3 : ProjEquiv (M_mat.act v₃) v₃) :
    PglEquiv M_mat MoebiusMatrix.id :=
  moebius_three_point_rigidity M_mat v₁ v₂ v₃ h12 h13 h23 hfix1 hfix2 hfix3

/-- Standard projective points [1:0] and [0:1]. -/
def p_inf : ℂ × ℂ := (1, 0)
def p_zero : ℂ × ℂ := (0, 1)

/-- Adversarial Probe 5.2: 2-point fixed hypothesis is STRICTLY INSUFFICIENT for rigidity.
Counterexample: The matrix diag(2, 1) fixes [1:0] and [0:1], but is NOT projectively equivalent to id! -/
theorem adversarial_two_point_rigidity_fails :
    let M2 : MoebiusMatrix := ⟨2, 0, 0, 1, by norm_num⟩
    (¬ ProjEquiv p_inf p_zero) ∧
    ProjEquiv (M2.act p_inf) p_inf ∧
    ProjEquiv (M2.act p_zero) p_zero ∧
    ¬ PglEquiv M2 MoebiusMatrix.id := by
  intro M2
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [ProjEquiv, p_inf, p_zero]
    intro h
    norm_num at h
  · dsimp [M2, MoebiusMatrix.act, ProjEquiv, p_inf]
    ring
  · dsimp [M2, MoebiusMatrix.act, ProjEquiv, p_zero]
    ring
  · intro h
    have h_eval := h (1, 1)
    dsimp [PglEquiv, ProjEquiv, M2, MoebiusMatrix.act, MoebiusMatrix.id] at h_eval
    ring_nf at h_eval
    norm_num at h_eval

/-- Adversarial Probe 5.3: Equivalence of full automorphism finiteness and pure componentwise automorphism finiteness. -/
theorem adversarial_full_automorphisms_finite_iff_pure_finite
    (lim : StableSphereTreeLimit I (M := M)) :
    Finite (StableMapAutomorphism I lim) ↔ Finite (PureComponentAutomorphism I lim) :=
  full_automorphisms_finite_iff_pure_finite I lim

/-- Adversarial Probe 5.4: Pure componentwise automorphisms of a stable map are finite. -/
theorem adversarial_pure_component_automorphisms_finite
    (lim : StableSphereTreeLimit I (M := M))
    (h_ghost_triv : ∀ (v : lim.tree.V) (_h_ghost : is_ghost_component I lim v)
      (aut : PureComponentAutomorphism I lim), (aut.1.frame v).toHomeo = Homeomorph.refl CP1)
    (h_ghost_fin : ∀ (v : lim.tree.V), is_ghost_component I lim v →
      Finite { ϕ : MoebiusFrame // ϕ.toHomeo = Homeomorph.refl CP1 })
    (h_prin_fin : ∀ (v : lim.tree.V), is_principal_component I lim v →
      Finite { ϕ : MoebiusFrame // ∀ z, lim.map v (ϕ.toHomeo z) = lim.map v z }) :
    Finite (PureComponentAutomorphism I lim) :=
  pure_component_automorphisms_finite I lim h_ghost_triv h_ghost_fin h_prin_fin

end GromovCompactness.AdversarialPhase5Census

/- =========================================================================
   6. MECHANICAL CALL-GRAPH WIRING & SENSITIVITY TESTING (#audit_wiring)
   ========================================================================= -/

namespace WiringAuditMemo

structure State where
  visited : Lean.NameSet := {}
  memo    : Lean.NameMap (Array Name) := {}

abbrev M := ReaderT Environment (StateM State)

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

def hasDirectSorry (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo v   => v.value.getUsedConstants.contains ``sorryAx
  | .thmInfo v    => v.value.getUsedConstants.contains ``sorryAx
  | .opaqueInfo v => v.value.getUsedConstants.contains ``sorryAx
  | _             => false

end WiringAuditMemo

def dummy_clean_decl : Nat := 42
def dummy_direct_sorry_decl : Nat := by sorry
def dummy_transitive_sorry_decl : Nat := dummy_direct_sorry_decl + 1

elab "#run_adversarial_phase5_census" : command => do
  let env ← getEnv
  logInfo m!"=================================================="
  logInfo m!"Starting Adversarial Sensitivity Tests on Wiring & Axioms"
  logInfo m!"=================================================="

  -- 1. Test hasDirectSorry oracle sensitivity
  let some ciClean := env.find? `dummy_clean_decl | throwError "Clean dummy decl missing"
  let some ciSorry := env.find? `dummy_direct_sorry_decl | throwError "Sorry dummy decl missing"
  let some ciTrans := env.find? `dummy_transitive_sorry_decl | throwError "Transitive dummy decl missing"

  if WiringAuditMemo.hasDirectSorry ciClean then
    throwError "[FAIL] hasDirectSorry incorrectly flagged clean decl!"
  logInfo m!"[PASS] hasDirectSorry passed clean decl"

  if !WiringAuditMemo.hasDirectSorry ciSorry then
    throwError "[FAIL] hasDirectSorry failed to detect direct sorry!"
  logInfo m!"[PASS] hasDirectSorry detected direct sorry"

  if WiringAuditMemo.hasDirectSorry ciTrans then
    throwError "[FAIL] hasDirectSorry confused transitive sorry with direct sorry!"
  logInfo m!"[PASS] hasDirectSorry distinguished transitive from direct sorry"

  -- 2. Test Call-Graph Reachability of Root
  let root := `GromovCompactness.gromov_compactness_genus_zero
  let some _ := env.find? root | throwError m!"Root '{root}' missing"
  let deps := WiringAuditMemo.getTransitiveClosure root env
  logInfo m!"[Graph] Closure size from {root}: {deps.size} constants"

  let required := [
    `GromovCompactness.gromov_compactness_core,
    `GromovCompactness.Assembly.stabilize_prestable_tree,
    `GromovCompactness.Assembly.assemble_prestable_limit,
    `GromovCompactness.Compactness.exists_concentration_data,
    `GromovCompactness.Compactness.defect_measure_identity,
    `GromovCompactness.Bubbling.resolve_single_defect_tree,
    `GromovCompactness.Analysis.TargetThresholds,
    `GromovCompactness.Analysis.nonlinear_elliptic_bootstrap,
    `GromovCompactness.Analysis.puncture_sobolev_extension
  ]

  for target in required do
    if deps.contains target then
      logInfo m!"[PASS] Verified required connection: {target}"
    else
      throwError m!"[FAIL] Missing call graph link: {target}"

  -- 3. Verify zero direct sorry on all 6 intermediate theorems
  let intermediate := [
    `GromovCompactness.gromov_compactness_core,
    `GromovCompactness.gromov_subsequence_alternative,
    `GromovCompactness.Assembly.stabilize_prestable_tree,
    `GromovCompactness.Bubbling.resolve_single_defect_tree,
    `GromovCompactness.Compactness.weak_energy_measure_compactness,
    `GromovCompactness.Analysis.removal_of_singularities
  ]

  for target in intermediate do
    let some ci := env.find? target | throwError m!"Intermediate decl {target} missing"
    if WiringAuditMemo.hasDirectSorry ci then
      throwError m!"[FAIL] Intermediate decl {target} contains direct sorry!"
    logInfo m!"[PASS] Zero direct sorry in intermediate decl: {target}"

  -- 4. Exhaustive Axiom Census of all 5 Phase 5 Target Modules
  let modules := [
    `GromovCompactness.Analysis.Energy,
    `GromovCompactness.Geometry.Target,
    `GromovCompactness.Geometry.Sphere,
    `GromovCompactness.Topology.SphereTree,
    `GromovCompactness.Extensions.Automorphisms
  ]

  logInfo m!"=================================================="
  logInfo m!"Exhaustive Phase 5 Target Modules Axiom Audit"
  logInfo m!"=================================================="
  let mut totalClean : Nat := 0
  let mut totalDirty : Array Name := #[]
  let mut state : WiringAuditMemo.State := {}

  for modPrefix in modules do
    let mut modClean : Nat := 0
    let mut modDirty : Array Name := #[]
    for (n, _) in env.constants.toList do
      let some idx := env.getModuleIdxFor? n | continue
      let modName := env.header.moduleNames[idx.toNat]!
      unless modPrefix.isPrefixOf modName do continue
      if n.isInternal then continue
      let (axs, nextState) := (WiringAuditMemo.collect n env).run state
      state := nextState
      if axs.contains ``sorryAx then
        modDirty := modDirty.push n
      else
        modClean := modClean + 1

    logInfo m!"Module: {modPrefix} -> clean: {modClean}, sorry: {modDirty.size}"
    if !modDirty.isEmpty then
      for d in modDirty do
        logError m!"  - [DIRTY] {d}"
      totalDirty := totalDirty ++ modDirty
    else
      logInfo m!"[PASS] Module {modPrefix} is 100% CLEAN!"
    totalClean := totalClean + modClean

  logInfo m!"=================================================="
  logInfo m!"Phase 5 Audit Summary: clean = {totalClean}, sorry = {totalDirty.size}"
  if !totalDirty.isEmpty then
    throwError m!"Phase 5 Module Audit Failed: {totalDirty.size} sorry dependencies found!"
  logInfo m!"STATUS: ALL 5 PHASE 5 TARGET MODULES ARE 100% CLEAN (0 sorryAx)"
  logInfo m!"=================================================="

#run_adversarial_phase5_census
