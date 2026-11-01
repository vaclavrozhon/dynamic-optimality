import Splay.Lazy.TraceOccurrence
import Splay.Interface.ActivitySlot

namespace Splay.Lazy

namespace Trace

/--
An actual visible rich step indexed simultaneously by its position among
visible interface operations and by its position among all rich events.

Silent events advance only `eventIndex`; visible events advance both indices.
This is the missing chronological bridge between `eraseOperations events`
and the intermediate rich states hidden inside the original trace proof.
-/
inductive VisibleStepAt {n : ℕ} {params : Interface.Parameters} :
    {initial final : State n} → {events : List (Event n)} →
      Trace params initial events final →
        ℕ → ℕ → State n → Interface.Operation n → State n → Prop
  | head {before middle final : State n}
      {operation : Interface.Operation n} {events : List (Event n)}
      (step : Step params before (.operation operation) middle)
      (tail : Trace params middle events final) :
      VisibleStepAt (.cons step tail) 0 0 before operation middle
  | visibleTail {initial middle final : State n}
      {headOperation : Interface.Operation n} {events : List (Event n)}
      (headStep : Step params initial (.operation headOperation) middle)
      (tailTrace : Trace params middle events final)
      {operationIndex eventIndex : ℕ}
      {before after : State n} {operation : Interface.Operation n}
      (occurrence :
        VisibleStepAt tailTrace operationIndex eventIndex
          before operation after) :
      VisibleStepAt (.cons headStep tailTrace)
        operationIndex.succ eventIndex.succ before operation after
  | silentTail {initial middle final : State n}
      {events : List (Event n)}
      (headStep : Step params initial .silent middle)
      (tailTrace : Trace params middle events final)
      {operationIndex eventIndex : ℕ}
      {before after : State n} {operation : Interface.Operation n}
      (occurrence :
        VisibleStepAt tailTrace operationIndex eventIndex
          before operation after) :
      VisibleStepAt (.cons headStep tailTrace)
        operationIndex eventIndex.succ before operation after

namespace VisibleStepAt

/-- The selected rich endpoints form the exact selected visible step. -/
theorem step {n : ℕ} {params : Interface.Parameters}
    {initial final before after : State n}
    {events : List (Event n)} {trace : Trace params initial events final}
    {operationIndex eventIndex : ℕ}
    {operation : Interface.Operation n}
    (occurrence :
      VisibleStepAt trace operationIndex eventIndex
        before operation after) :
    Step params before (.operation operation) after := by
  induction occurrence with
  | head step _ => exact step
  | visibleTail _ _ _ ih => exact ih
  | silentTail _ _ _ ih => exact ih

/-- The visible index lies inside the erased operation list. -/
theorem operationIndex_lt {n : ℕ} {params : Interface.Parameters}
    {initial final before after : State n}
    {events : List (Event n)} {trace : Trace params initial events final}
    {operationIndex eventIndex : ℕ}
    {operation : Interface.Operation n}
    (occurrence :
      VisibleStepAt trace operationIndex eventIndex
        before operation after) :
    operationIndex < (eraseOperations events).length := by
  induction occurrence with
  | head _ _ =>
      simp [eraseOperations, Event.operations]
  | visibleTail _ _ _ ih =>
      simpa [eraseOperations, Event.operations] using Nat.succ_lt_succ ih
  | silentTail _ _ _ ih =>
      simpa [eraseOperations, Event.operations] using ih

/-- The rich-event index lies inside the un-erased event list. -/
theorem eventIndex_lt {n : ℕ} {params : Interface.Parameters}
    {initial final before after : State n}
    {events : List (Event n)} {trace : Trace params initial events final}
    {operationIndex eventIndex : ℕ}
    {operation : Interface.Operation n}
    (occurrence :
      VisibleStepAt trace operationIndex eventIndex
        before operation after) :
    eventIndex < events.length := by
  induction occurrence with
  | head _ _ => simp
  | visibleTail _ _ _ ih =>
      simpa only [List.length_cons, Nat.succ_lt_succ_iff] using ih
  | silentTail _ _ _ ih =>
      simpa only [List.length_cons, Nat.succ_lt_succ_iff] using ih

/-- Looking up the erased list recovers the selected operation. -/
theorem operation_eq_get {n : ℕ} {params : Interface.Parameters}
    {initial final before after : State n}
    {events : List (Event n)} {trace : Trace params initial events final}
    {operationIndex eventIndex : ℕ}
    {operation : Interface.Operation n}
    (occurrence :
      VisibleStepAt trace operationIndex eventIndex
        before operation after) :
    (eraseOperations events).get
        ⟨operationIndex, occurrence.operationIndex_lt⟩ =
      operation := by
  induction occurrence with
  | head _ _ => rfl
  | visibleTail _ _ occurrence ih => exact ih
  | silentTail _ _ occurrence ih => exact ih

/-- Looking up the rich event list recovers the selected visible event. -/
theorem event_eq_get {n : ℕ} {params : Interface.Parameters}
    {initial final before after : State n}
    {events : List (Event n)} {trace : Trace params initial events final}
    {operationIndex eventIndex : ℕ}
    {operation : Interface.Operation n}
    (occurrence :
      VisibleStepAt trace operationIndex eventIndex
        before operation after) :
    events.get ⟨eventIndex, occurrence.eventIndex_lt⟩ =
      .operation operation := by
  induction occurrence with
  | head _ _ => rfl
  | visibleTail _ _ occurrence ih => exact ih
  | silentTail _ _ occurrence ih => exact ih

/-- The selected rich step induces its exact interface step. -/
theorem toInterface {n : ℕ} {params : Interface.Parameters}
    {initial final before after : State n}
    {events : List (Event n)} {trace : Trace params initial events final}
    {operationIndex eventIndex : ℕ}
    {operation : Interface.Operation n}
    (occurrence :
      VisibleStepAt trace operationIndex eventIndex
        before operation after) :
    Interface.Step params before.toInterface operation after.toInterface :=
  occurrence.step.interfaceStep_of_operation

end VisibleStepAt

/--
Every erased-operation position comes from one actual visible rich event and
retains its actual rich before/after states.
-/
theorem exists_visibleStepAt {n : ℕ} {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    (trace : Trace params initial events final)
    (operationIndex : Fin (eraseOperations events).length) :
    ∃ eventIndex before operation after,
      VisibleStepAt trace operationIndex.val eventIndex
        before operation after := by
  induction trace with
  | nil _ =>
      exact Fin.elim0 operationIndex
  | @cons before middle after event events head tail ih =>
      cases event with
      | operation headOperation =>
          rcases operationIndex with ⟨position, inBounds⟩
          cases position with
          | zero =>
              exact
                ⟨0, before, headOperation, middle,
                  .head head tail⟩
          | succ position =>
              have tailBounds :
                  position < (eraseOperations events).length := by
                simpa [eraseOperations, Event.operations] using inBounds
              obtain
                  ⟨eventIndex, stepBefore, operation, stepAfter,
                    occurrence⟩ :=
                ih ⟨position, tailBounds⟩
              exact
                ⟨eventIndex.succ, stepBefore, operation, stepAfter,
                  .visibleTail head tail occurrence⟩
      | silent =>
          let tailIndex : Fin (eraseOperations events).length :=
            ⟨operationIndex.val, by
              simpa [eraseOperations, Event.operations] using
                operationIndex.isLt⟩
          obtain
              ⟨eventIndex, stepBefore, operation, stepAfter, occurrence⟩ :=
            ih tailIndex
          refine
            ⟨eventIndex.succ, stepBefore, operation, stepAfter, ?_⟩
          simpa only [tailIndex] using
            (VisibleStepAt.silentTail head tail occurrence)

end Trace

end Splay.Lazy

namespace Splay.Interface.ActivitySlot

/--
An activity slot in an erased legal rich trace selects the actual visible
rich `pass` event and proves its tuple valid in the exact projected pre-state.
-/
theorem exists_richPairingValid
    {n : ℕ} {params : Parameters}
    {initial final : Splay.Lazy.State n}
    {events : List (Splay.Lazy.Event n)}
    (slot : ActivitySlot (Splay.Lazy.eraseOperations events))
    (trace : Splay.Lazy.Trace params initial events final) :
    ∃ eventIndex before after sourceBlock,
      Splay.Lazy.Trace.VisibleStepAt trace
          slot.operationIndex.val eventIndex before
          (.pass slot.source slot.matching) after ∧
        before.toInterface.block? slot.source = some sourceBlock ∧
        PairingValid before.toInterface slot.source sourceBlock
          slot.pairing := by
  obtain ⟨eventIndex, before, operation, after, occurrence⟩ :=
    trace.exists_visibleStepAt slot.operationIndex
  have indexEq :
      (⟨slot.operationIndex.val, occurrence.operationIndex_lt⟩ :
        Fin (Splay.Lazy.eraseOperations events).length) =
        slot.operationIndex :=
    Fin.ext rfl
  have operationEq :
      operation = .pass slot.source slot.matching := by
    rw [← occurrence.operation_eq_get, indexEq]
    exact slot.operation_eq
  subst operation
  have legalStep := occurrence.toInterface
  cases legalStep.2.1 with
  | pass sourceFound matchingValid _ _ =>
      exact
        ⟨eventIndex, before, after, _, occurrence, sourceFound,
          matchingValid.2.2.2.1
            slot.pairing slot.pairing_mem_matching⟩

end Splay.Interface.ActivitySlot
