import Splay.Lazy.Trace

namespace Splay.Lazy

namespace Trace

/--
An occurrence of one primitive event at a concrete chronological position in
a rich trace.

`Trace` itself hides intermediate states in its proof.  `StepAt` exposes just
the two endpoints of one selected event without replacing the trace by a
second, potentially unrelated, list of states.
-/
inductive StepAt {n : ℕ} {params : Interface.Parameters} :
    {initial final : State n} → {events : List (Event n)} →
      Trace params initial events final →
        ℕ → State n → Event n → State n → Prop
  | head {before middle final : State n} {event : Event n}
      {events : List (Event n)}
      (step : Step params before event middle)
      (tail : Trace params middle events final) :
      StepAt (.cons step tail) 0 before event middle
  | tail {initial middle final : State n} {headEvent : Event n}
      {events : List (Event n)}
      (headStep : Step params initial headEvent middle)
      (tailTrace : Trace params middle events final)
      {index : ℕ} {before after : State n} {event : Event n}
      (occurrence : StepAt tailTrace index before event after) :
      StepAt (.cons headStep tailTrace) index.succ before event after

namespace StepAt

/-- The selected endpoints really form the selected primitive rich step. -/
theorem step {n : ℕ} {params : Interface.Parameters}
    {initial final before after : State n}
    {events : List (Event n)} {trace : Trace params initial events final}
    {index : ℕ} {event : Event n}
    (occurrence : StepAt trace index before event after) :
    Step params before event after := by
  induction occurrence with
  | head step _ => exact step
  | tail _ _ _ ih => exact ih

/-- A selected chronological position is necessarily inside the event list. -/
theorem index_lt {n : ℕ} {params : Interface.Parameters}
    {initial final before after : State n}
    {events : List (Event n)} {trace : Trace params initial events final}
    {index : ℕ} {event : Event n}
    (occurrence : StepAt trace index before event after) :
    index < events.length := by
  induction occurrence with
  | head _ _ => simp
  | tail _ _ _ ih =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff]
      exact ih

/-- The event named by an occurrence is the event stored at that list index. -/
theorem event_eq_get {n : ℕ} {params : Interface.Parameters}
    {initial final before after : State n}
    {events : List (Event n)} {trace : Trace params initial events final}
    {index : ℕ} {event : Event n}
    (occurrence : StepAt trace index before event after) :
    events.get ⟨index, occurrence.index_lt⟩ = event := by
  induction occurrence with
  | head _ _ => rfl
  | tail _ _ occurrence ih =>
      exact ih

end StepAt

/--
Every position in a rich trace has actual before/after states and an actual
`StepAt` witness.  This is the basic bridge from list-indexed accounting
objects to the proof-indexed structural execution.
-/
theorem exists_stepAt {n : ℕ} {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    (trace : Trace params initial events final)
    (index : Fin events.length) :
    ∃ before event after,
      StepAt trace index.val before event after := by
  induction trace with
  | nil _ =>
      exact Fin.elim0 index
  | @cons before middle after event events head tail ih =>
      rcases index with ⟨position, inBounds⟩
      cases position with
      | zero =>
          exact ⟨before, event, middle, .head head tail⟩
      | succ position =>
          have tailBounds : position < events.length := by
            simpa only [List.length_cons, Nat.succ_lt_succ_iff] using
              inBounds
          obtain ⟨stepBefore, stepEvent, stepAfter, occurrence⟩ :=
            ih ⟨position, tailBounds⟩
          exact
            ⟨stepBefore, stepEvent, stepAfter,
              .tail head tail occurrence⟩

/-- An actual visible interface operation at a chronological rich-trace slot. -/
def OperationAt {n : ℕ} {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    (trace : Trace params initial events final)
    (index : ℕ) (before : State n)
    (operation : Interface.Operation n) (after : State n) : Prop :=
  StepAt trace index before (.operation operation) after

namespace OperationAt

/-- A selected visible occurrence induces the exact abstract interface step. -/
theorem toInterface {n : ℕ} {params : Interface.Parameters}
    {initial final before after : State n}
    {events : List (Event n)} {trace : Trace params initial events final}
    {index : ℕ} {operation : Interface.Operation n}
    (occurrence : OperationAt trace index before operation after) :
    Interface.Step params before.toInterface operation after.toInterface :=
  occurrence.step.interfaceStep_of_operation

/-- A selected visible operation lies inside the rich event list. -/
theorem index_lt {n : ℕ} {params : Interface.Parameters}
    {initial final before after : State n}
    {events : List (Event n)} {trace : Trace params initial events final}
    {index : ℕ} {operation : Interface.Operation n}
    (occurrence : OperationAt trace index before operation after) :
    index < events.length :=
  StepAt.index_lt occurrence

end OperationAt

end Trace

end Splay.Lazy
