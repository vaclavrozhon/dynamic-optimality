import Splay.Accounting.ArticleRequestUnbroken
import Splay.Accounting.ArticleInitializedExecution

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST Splay.Assumptions.NormalForm

/-- Restoring the two true boundary priorities completes the actual
request's preservation proof. -/
theorem ArticleCompleteRequest.preservesUnbroken {n : ℕ} {params : Interface.Parameters}
    {comparison before after : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
    (request : ArticleCompleteRequest params comparison before after key kinds initial)
    (comparisonRoot : comparison.HasRoot key.val) {execution : SplayExecution key.val before after}
    {zig zigZig zigZag : ℕ} (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (zero : Interface.GrowingPassCountZero initial.toInterface)
    (unbroken : PassedBlocksUnbroken (Snapshot.ofTree comparison).withTruePriority before initial) :
    PassedBlocksUnbroken (Snapshot.ofTree comparison).withTruePriority after request.final :=
  request.restoration.preservesUnbroken request.stage.setup.temporarySnapshot rfl
    (request.stage.preservesUnbroken comparisonRoot transcript zero unbroken)

theorem ArticleMacro.preservesUnbroken {n : ℕ} {params : Interface.Parameters}
    {before after : ArticleCheckpoint n} (step : ArticleMacro params before after)
    (zero : Interface.GrowingPassCountZero before.state.toInterface)
    (unbroken : PassedBlocksUnbroken (Snapshot.ofTree before.comparison).withTruePriority before.splay before.state) :
    PassedBlocksUnbroken (Snapshot.ofTree after.comparison).withTruePriority after.splay after.state := by
  cases step with
  | rotation represented rotation execution =>
    exact execution.preservesUnbroken _ represented.view_eq unbroken
  | request represented root execution transcript request =>
    exact request.preservesUnbroken root transcript.transcript zero unbroken

/-- The invariant follows the chronological sequence of actual comparison
rotations and requests, with growing-counter validity propagated by its trace. -/
theorem ArticleMacroHistory.preservesUnbroken {n : ℕ} {params : Interface.Parameters}
    {first last : ArticleCheckpoint n} (history : ArticleMacroHistory params first last)
    (zero : Interface.GrowingPassCountZero first.state.toInterface)
    (unbroken : PassedBlocksUnbroken (Snapshot.ofTree first.comparison).withTruePriority first.splay first.state) :
    PassedBlocksUnbroken (Snapshot.ofTree last.comparison).withTruePriority last.splay last.state := by
  induction history with
  | done => exact unbroken
  | next head tail ih => exact ih (head.trace.growingPassCountZero zero) (head.preservesUnbroken zero unbroken)

/-- The initialized chronological construction has the geometric invariant
without any caller-supplied unbroken certificate. -/
theorem ArticleInitializedExecution.passedBlocksUnbroken {n : ℕ} {params : Interface.Parameters}
    {bounds : Splay.Assumptions.NormalForm.StructuralBounds} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses} {tree : BST 0 n}
    (run : ArticleInitializedExecution params bounds comparison tree) :
    PassedBlocksUnbroken (Snapshot.ofTree comparison.finalTree).withTruePriority run.finalTree run.final := by
  apply run.execution.history.preservesUnbroken
  · intro id block found growing
    have found' : (canonicalState (Snapshot.ofTree comparison.initialTree).withTruePriority tree).toInterface.blocks[id]? = some block := found
    obtain ⟨rich, richFound, blockEq⟩ := Option.map_eq_some_iff.mp (by
      simpa only [State.toInterface, List.getElem?_map] using found')
    have member := List.mem_of_getElem? richFound
    obtain ⟨placement, _, richEq⟩ := List.mem_map.mp member
    subst rich
    subst block
    rfl
  · exact canonicalState_passedBlocksUnbroken _ _

end Splay.Accounting
