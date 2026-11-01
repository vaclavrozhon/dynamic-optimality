import Splay.Accounting.ShiftAtomicBoundaryPairing

namespace Splay.Lazy.Trace.VisibleStepAt

/-- A visible occurrence in a suffix survives an arbitrary trace prefix. -/
theorem prepend
    {n : ℕ} {params : Interface.Parameters}
    {initial middle final before after : State n}
    {prefixEvents suffixEvents : List (Event n)}
    (prefixTrace : Trace params initial prefixEvents middle)
    {suffixTrace : Trace params middle suffixEvents final}
    {operationIndex eventIndex : ℕ}
    {operation : Interface.Operation n}
    (occurrence :
      Trace.VisibleStepAt suffixTrace operationIndex eventIndex
        before operation after) :
    Trace.VisibleStepAt (prefixTrace.append suffixTrace)
      ((eraseOperations prefixEvents).length + operationIndex)
      (prefixEvents.length + eventIndex)
      before operation after := by
  induction prefixTrace with
  | nil _ =>
      simpa [eraseOperations] using occurrence
  | @cons first middle final event events head tail ih =>
      cases event with
      | operation headOperation =>
          have transported :=
            Trace.VisibleStepAt.visibleTail head
              (tail.append suffixTrace) (ih occurrence)
          convert transported using 1 <;>
            simp [eraseOperations, Event.operations] <;> omega
      | silent =>
          have transported :=
            Trace.VisibleStepAt.silentTail head
              (tail.append suffixTrace) (ih occurrence)
          convert transported using 1 <;>
            simp [eraseOperations, Event.operations] <;> omega

/-- A visible occurrence in a prefix survives appending any trace suffix. -/
theorem append
    {n : ℕ} {params : Interface.Parameters}
    {initial middle final before after : State n}
    {prefixEvents suffixEvents : List (Event n)}
    {prefixTrace : Trace params initial prefixEvents middle}
    (suffixTrace : Trace params middle suffixEvents final)
    {operationIndex eventIndex : ℕ}
    {operation : Interface.Operation n}
    (occurrence :
      Trace.VisibleStepAt prefixTrace operationIndex eventIndex
        before operation after) :
    Trace.VisibleStepAt (prefixTrace.append suffixTrace)
      operationIndex eventIndex before operation after := by
  induction occurrence with
  | head step tail =>
      exact .head step (tail.append suffixTrace)
  | visibleTail head tail occurrence ih =>
      exact
        .visibleTail head (tail.append suffixTrace)
          (ih suffixTrace)
  | silentTail head tail occurrence ih =>
      exact
        .silentTail head (tail.append suffixTrace)
          (ih suffixTrace)

end Splay.Lazy.Trace.VisibleStepAt

namespace Splay.Accounting

open Splay.Lazy

namespace BoundaryPairingMove

/-- Transport a boundary move through an arbitrary rich trace prefix. -/
def prepend
    {n : ℕ} {params : Interface.Parameters}
    {initial middle final : State n}
    {prefixEvents suffixEvents : List (Event n)}
    (prefixTrace : Trace params initial prefixEvents middle)
    {suffixTrace : Trace params middle suffixEvents final}
    (move : BoundaryPairingMove suffixTrace) :
    BoundaryPairingMove (prefixTrace.append suffixTrace) where
  slot := move.slot
  winner := move.winner
  loser := move.loser
  source := move.source
  deleteOperationIndex :=
    (eraseOperations prefixEvents).length + move.deleteOperationIndex
  deleteEventIndex := prefixEvents.length + move.deleteEventIndex
  deleteBefore := move.deleteBefore
  deleteAfter := move.deleteAfter
  deleteAt := move.deleteAt.prepend prefixTrace
  destination := move.destination
  insertOperationIndex :=
    (eraseOperations prefixEvents).length + move.insertOperationIndex
  insertEventIndex := prefixEvents.length + move.insertEventIndex
  insertBefore := move.insertBefore
  insertAfter := move.insertAfter
  insertAt := move.insertAt.prepend prefixTrace
  delete_before_insert := Nat.add_lt_add_left
    move.delete_before_insert prefixEvents.length
  destinationBlock := move.destinationBlock
  destinationFound := move.destinationFound
  destinationCreator := move.destinationCreator

/-- Transport a boundary move through an arbitrary rich trace suffix. -/
def append
    {n : ℕ} {params : Interface.Parameters}
    {initial middle final : State n}
    {prefixEvents suffixEvents : List (Event n)}
    {prefixTrace : Trace params initial prefixEvents middle}
    (suffixTrace : Trace params middle suffixEvents final)
    (move : BoundaryPairingMove prefixTrace) :
    BoundaryPairingMove (prefixTrace.append suffixTrace) where
  slot := move.slot
  winner := move.winner
  loser := move.loser
  source := move.source
  deleteOperationIndex := move.deleteOperationIndex
  deleteEventIndex := move.deleteEventIndex
  deleteBefore := move.deleteBefore
  deleteAfter := move.deleteAfter
  deleteAt := move.deleteAt.append suffixTrace
  destination := move.destination
  insertOperationIndex := move.insertOperationIndex
  insertEventIndex := move.insertEventIndex
  insertBefore := move.insertBefore
  insertAfter := move.insertAfter
  insertAt := move.insertAt.append suffixTrace
  delete_before_insert := move.delete_before_insert
  destinationBlock := move.destinationBlock
  destinationFound := move.destinationFound
  destinationCreator := move.destinationCreator

@[simp]
theorem prepend_slot
    {n : ℕ} {params : Interface.Parameters}
    {initial middle final : State n}
    {prefixEvents suffixEvents : List (Event n)}
    (prefixTrace : Trace params initial prefixEvents middle)
    {suffixTrace : Trace params middle suffixEvents final}
    (move : BoundaryPairingMove suffixTrace) :
    (move.prepend prefixTrace).slot = move.slot :=
  rfl

@[simp]
theorem append_slot
    {n : ℕ} {params : Interface.Parameters}
    {initial middle final : State n}
    {prefixEvents suffixEvents : List (Event n)}
    {prefixTrace : Trace params initial prefixEvents middle}
    (suffixTrace : Trace params middle suffixEvents final)
    (move : BoundaryPairingMove prefixTrace) :
    (move.append suffixTrace).slot = move.slot :=
  rfl

end BoundaryPairingMove

end Splay.Accounting
