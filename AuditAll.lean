import DynamicOptimalityResults
import DynamicOptimality
import Splay
import TangoSquared
import TangoSquaredPaper20261030
import Greedy
import MultiSplay
import Lean

set_option stderrAsMessages false

/-! Audit public and private declarations using Lean's standard collector.
The imported axiom summaries avoid rereading proof bodies under memory
pressure. Keep this file outside the module system so private declarations
remain included. Progress goes directly to stderr for long-running audits. -/

open Lean in
run_cmd do
  Lean.Elab.Command.liftIO <| IO.eprintln "Imports loaded; checking public endpoints."

#print axioms DynamicOptimality.Tango2.execution
#print axioms DynamicOptimality.Tango2.online
#print axioms DynamicOptimality.Tango2.competitive
#print axioms DynamicOptimality.Tango2.competitor_bound
#print axioms DynamicOptimality.Tango2.All.execution
#print axioms DynamicOptimality.Tango2.All.online
#print axioms DynamicOptimality.Tango2.All.competitive
#print axioms DynamicOptimality.Tango2.All.competitor_bound
#print axioms DynamicOptimality.Tango2.All.third_log_competitive
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
#print axioms DynamicOptimality.Results.multisplay
#print axioms DynamicOptimality.Results.bst_models_equivalent
#print axioms DynamicOptimality.BSTModel.competitive_iff
#print axioms DynamicOptimality.ModelCosts.geometry_iff_hull
#print axioms DynamicOptimality.Geometry.to_hullExecution
#print axioms DynamicOptimality.OnlineModel.Normalization.pointer_cost_le_from_state
#print axioms DynamicOptimality.Geometry.OnlineSearch.run_cost_le
#print axioms DynamicOptimality.Geometry.greedy_cost_geometric

open Lean in
run_cmd do
  let env ← getEnv
  let prefixes := #[`DynamicOptimality, `Splay, `TangoSquared,
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
  logInfo m!"Audited shared, splay, Greedy, Tango², and MultiSplay declarations: {count}"
  logInfo m!"Declarations using nonstandard axioms: {unexpected}"
  unless unexpected.isEmpty do
    throwError "Nonstandard axiom dependency in the shared development"
