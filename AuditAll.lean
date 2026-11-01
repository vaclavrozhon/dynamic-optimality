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
