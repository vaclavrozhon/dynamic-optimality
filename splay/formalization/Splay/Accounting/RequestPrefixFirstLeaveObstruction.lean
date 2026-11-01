import Splay.Accounting.BoundaryPairingMoveComposition
import Splay.Accounting.RequestStartBoundaryLineage

namespace Splay.Accounting

open Splay.Lazy
open Splay.Lazy.Canonical
open Splay.Rank
open Splay.Tree.BST

namespace ShiftAtomicBoundaryPairing

/--
Two otherwise valid boundary macros may use the same loser in succession.
For the second move, the first macro's delete is then a genuine prior leave.

This is the local kernel-checked reason why a macro embedded later in a
request must carry a request-prefix first-leave invariant.  The invariant
cannot be recovered from the second macro's own event shape.
-/
theorem repeatedLoser_has_prior_leave
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {beforeTree middleTree afterTree : BST 0 n}
    {initial : State n}
    {firstSlot secondSlot : PairingSlot}
    {firstWinner secondWinner loser : Interface.Element n}
    (first :
      Certificate (params := params) (snapshot := snapshot)
        (beforeTree := beforeTree) (afterTree := middleTree)
        initial firstSlot firstWinner loser)
    (second :
      Certificate (params := params) (snapshot := snapshot)
        (beforeTree := middleTree) (afterTree := afterTree)
        first.transition.final secondSlot secondWinner loser) :
    let combined := first.transition.trans second.transition
    let secondMove := second.move.prepend first.transition.trace
    ∃ prior,
      prior ∈
          (eraseOperations combined.events).take
            secondMove.deleteOperationIndex ∧
        operationLeavesElement prior loser := by
  let combined := first.transition.trans second.transition
  let secondMove := second.move.prepend first.transition.trace
  refine ⟨.delete first.move.source loser, ?_, ?_⟩
  · have firstDeleteMember :
        .delete first.move.source loser ∈
          eraseOperations first.transition.events := by
      have selectedMember :=
        List.get_mem
          (eraseOperations first.transition.events)
          ⟨first.move.deleteOperationIndex,
            first.move.deleteAt.operationIndex_lt⟩
      rw [first.move.deleteAt.operation_eq_get] at selectedMember
      rw [first.move_loser] at selectedMember
      exact selectedMember
    change
      .delete first.move.source loser ∈
        (eraseOperations
          (first.transition.events ++ second.transition.events)).take
          ((eraseOperations first.transition.events).length +
            second.move.deleteOperationIndex)
    rw [second.delete_operation_index, Nat.add_zero,
      eraseOperations_append, List.take_append]
    simpa using firstDeleteMember
  · simp [operationLeavesElement]

/--
The obstruction is inhabited for every ordinary endpoint for which the
shift-atomic constructor applies: execute its legal boundary macro twice.
-/
theorem exists_repeatedLoser_prior_leave
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {beforeTree afterTree : BST 0 n}
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree)
    (initialAtomic : initial.ShiftAtomic)
    (firstSlot secondSlot : PairingSlot)
    (winner loser : Interface.Element n)
    (afterParent :
      canonicalParent snapshot afterTree loser = some winner) :
    ∃ first :
        Certificate (params := params) (snapshot := snapshot)
          (beforeTree := beforeTree) (afterTree := afterTree)
          initial firstSlot winner loser,
      ∃ second :
          Certificate (params := params) (snapshot := snapshot)
            (beforeTree := afterTree) (afterTree := afterTree)
            first.transition.final secondSlot winner loser,
        let combined := first.transition.trans second.transition
        let secondMove := second.move.prepend first.transition.trace
        ∃ prior,
          prior ∈
              (eraseOperations combined.events).take
                secondMove.deleteOperationIndex ∧
            operationLeavesElement prior loser := by
  obtain ⟨first⟩ :=
    exists_certificate initialRepresents initialAtomic
      firstSlot winner loser afterParent
  obtain ⟨second⟩ :=
    exists_certificate first.transition.final_represents
      first.finalAtomic secondSlot winner loser afterParent
  exact
    ⟨first, second,
      repeatedLoser_has_prior_leave first second⟩

end ShiftAtomicBoundaryPairing

end Splay.Accounting
