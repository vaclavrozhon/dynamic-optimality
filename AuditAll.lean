import DynamicOptimalityResults
import DynamicOptimality
import Splay
import ChaCha
import ChaChaPaper20261030
import Greedy
import MultiSplay
import Lean

set_option stderrAsMessages false

/-! Focused legacy namespace audit, including public and private declarations.
`make audit` uses these endpoint diagnostics in the complete registered-module
audit, which also covers modules outside these imports and other namespaces.
The imported axiom summaries avoid rereading proof bodies under memory
pressure. Keep this file outside the module system so private declarations
remain included. Progress goes directly to stderr for long-running audits. -/

open Lean in
run_cmd do
  Lean.Elab.Command.liftIO <| IO.eprintln "Imports loaded; checking public endpoints."

#print axioms DynamicOptimality.ChaCha.execution
#print axioms DynamicOptimality.ChaCha.online
#print axioms DynamicOptimality.ChaCha.competitive
#print axioms DynamicOptimality.ChaCha.competitor_bound
#print axioms DynamicOptimality.ChaCha.All.execution
#print axioms DynamicOptimality.ChaCha.All.online
#print axioms DynamicOptimality.ChaCha.All.competitive
#print axioms DynamicOptimality.ChaCha.All.competitor_bound
#print axioms DynamicOptimality.ChaCha.All.third_log_competitive
#print axioms MultiSplay.Online.execution
#print axioms MultiSplay.Online.online
#print axioms MultiSplay.Online.first_cost_eq_classical
#print axioms MultiSplay.Online.first_classical_transcript
#print axioms MultiSplay.Online.run_classical
#print axioms MultiSplay.Online.comparator_estimate
#print axioms MultiSplay.Online.composed_bound
#print axioms MultiSplay.Online.competitive
#print axioms MultiSplay.Online.competitive_expanded
#print axioms MultiSplay.Online.competitive_logarithmic
#print axioms MultiSplay.Online.competitive_generic_logarithmic
#print axioms MultiSplay.Online.competitive_generic_shifted
#print axioms MultiSplay.admissible_egTargetFactor
#print axioms DynamicOptimality.Results.splay
#print axioms DynamicOptimality.Results.splay_refined
#print axioms DynamicOptimality.Results.greedy
#print axioms DynamicOptimality.Results.chacha
#print axioms DynamicOptimality.Results.multisplay
#print axioms DynamicOptimality.Results.bst_models_equivalent
#print axioms DynamicOptimality.BSTModel.competitive_iff
#print axioms DynamicOptimality.ModelCosts.geometry_iff_hull
#print axioms DynamicOptimality.Geometry.to_hullExecution
#print axioms DynamicOptimality.OnlineModel.Normalization.pointer_cost_le_from_state
#print axioms DynamicOptimality.Geometry.OnlineSearch.run_cost_le
#print axioms DynamicOptimality.Geometry.greedy_cost_geometric
#print axioms Splay.Accounting.LogHeightNormalForm.exists_structuralLogHeightComparisonTrace
#print axioms Splay.Accounting.LogHeightNormalForm.additiveStructuralHypothesis
#print axioms DynamicOptimality.Geometry.ReferenceClosure.row_card_le
#print axioms DynamicOptimality.Geometry.ReferenceClosure.closePoints_satisfied
#print axioms DynamicOptimality.Geometry.ReferenceClosure.closePoints_card_add_rows_le
#print axioms DynamicOptimality.Geometry.ReferenceClosure.execution_referenceClosure
#print axioms DynamicOptimality.Geometry.ReferenceClosure.closePoints_interval_closed
#print axioms DynamicOptimality.Geometry.ReferenceClosure.GuardCounterexample.guarded_not_satisfied
#print axioms DynamicOptimality.Results.chacha_splay
#print axioms ChaCha.Paper20261030.SplayAuxiliary.All.execution
#print axioms ChaCha.Paper20261030.SplayAuxiliary.All.ordinary_active
#print axioms ChaCha.Separation.explicit_third_log_separation
#print axioms DynamicOptimality.Funnel.convex_composition
#print axioms DynamicOptimality.Results.funnel_shuffle
#print axioms DynamicOptimality.Funnel.wordCount_sublist
#print axioms MultiSplay.Obstructions.IntervalProjection.restriction_not_splay
#print axioms MultiSplay.Obstructions.Classical.classical_potential_obstruction
#print axioms ChaCha.Entropy.residual_shared_OPT
#print axioms ChaCha.Entropy.primary_expectation
#print axioms ChaCha.Entropy.exists_entropy_residual_lower_bound
#print axioms DynamicOptimality.Geometry.execution_map_monotone
#print axioms DynamicOptimality.ColoredWalks.exists_colored_embedding
#print axioms DynamicOptimality.ColoredWalks.exists_colored_pointer_tree
#print axioms DynamicOptimality.Results.geometric_online
#print axioms DynamicOptimality.GeometricOnlineSimulation.dyadicSplitTrees
#print axioms DynamicOptimality.Geometry.OnlineStrategy.exists_onlineBST
#print axioms DynamicOptimality.Geometry.OnlineGreedy.exists_onlineBST
#print axioms DynamicOptimality.MultiFinger.simulationBound
#print axioms DynamicOptimality.ColoredWalks.shuffle_OPT_bound
#print axioms DynamicOptimality.ColoredWalks.shuffle_from_initial
#print axioms DynamicOptimality.Results.colored_shuffle

open Lean in
run_cmd do
  let env ← getEnv
  let prefixes := #[`DynamicOptimality, `Splay, `ChaCha,
    `Greedy, `GreedyForest, `GreedyMerge, `MultiSplay]
  let mut targets : Array Name := #[]
  for (name, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf (privateToUserName name)) then
      targets := targets.push name
  Lean.Elab.Command.liftIO <| IO.eprintln s!"Starting namespace audit: {targets.size} declarations."
  let mut count : Nat := 0
  let mut unexpected : Array (Name × Array Name) := #[]
  for name in targets do
    let axioms ← Lean.collectAxioms name
    if axioms.any (fun ax => ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound) then
      unexpected := unexpected.push (name, axioms)
    count := count + 1
    if count % 2000 == 0 then
      Lean.Elab.Command.liftIO <| IO.eprintln s!"Axiom audit progress: {count}/{targets.size}."
  logInfo m!"Audited shared, splay, Greedy, Cha-Cha, and MultiSplay declarations: {count}"
  logInfo m!"Declarations using nonstandard axioms: {unexpected}"
  unless unexpected.isEmpty do
    throwError "Nonstandard axiom dependency in the shared development"
