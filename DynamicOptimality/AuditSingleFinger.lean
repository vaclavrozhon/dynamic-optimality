import DynamicOptimality.SingleFinger.DequePopMax
import DynamicOptimality.SingleFinger.SourceDequeJoin
import DynamicOptimality.SingleFinger.SourceReflection
import DynamicOptimality.SingleFinger.SourceCompile
import DynamicOptimality.SingleFinger.TendonPotential
import DynamicOptimality.SingleFinger.Skeleton

/-! Private audit of the single-finger construction dependencies.
The imported declarations do not yet include the multifinger simulator.
-/

#print axioms DynamicOptimality.SingleFinger.Deque.pop_min
#print axioms DynamicOptimality.SingleFinger.Deque.pop_max
#print axioms DynamicOptimality.SingleFinger.SourceDeque.pop_min
#print axioms DynamicOptimality.SingleFinger.SourceDeque.pop_max
#print axioms DynamicOptimality.SingleFinger.SourceDequeJoin.execute
#print axioms DynamicOptimality.SingleFinger.SourceCompile.compile_steps
#print axioms DynamicOptimality.SingleFinger.TendonPotential.merge_releases
#print axioms DynamicOptimality.SingleFinger.TendonPotential.grow_one
#print axioms DynamicOptimality.SingleFinger.BoundedScan.find
#print axioms DynamicOptimality.SingleFinger.Skeleton.Hand.branching_bound
#print axioms DynamicOptimality.SingleFinger.Skeleton.Hand.contains_vertex

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut unexpected : Array (Name × Array Name) := #[]
  for (name, _) in env.constants.toList do
    if (`DynamicOptimality.SingleFinger).isPrefixOf name then
      count := count + 1
      let axioms ← Lean.collectAxioms name
      if axioms.any (fun ax => ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound) then
        unexpected := unexpected.push (name,axioms)
  logInfo m!"Audited single-finger declarations: {count}"
  logInfo m!"Declarations using nonstandard axioms: {unexpected}"
  unless unexpected.isEmpty do
    throwError "Nonstandard axiom dependency in the single-finger modules"
