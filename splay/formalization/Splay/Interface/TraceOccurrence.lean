import Splay.Interface.Model

namespace Splay.Interface

namespace Trace

/--
An operation occurrence at one concrete chronological position of an
interface trace.

The endpoints hidden by `Trace` remain the actual endpoints of that very
trace proof.  In particular, this relation cannot be witnessed with states
from a second execution of the same operation list.
-/
inductive StepAt {n : ℕ} {params : Parameters} :
    {initial final : State n} → {operations : List (Operation n)} →
      Trace params initial operations final →
        ℕ → State n → Operation n → State n → Prop
  | head {before middle final : State n} {operation : Operation n}
      {operations : List (Operation n)}
      (step : Step params before operation middle)
      (tail : Trace params middle operations final) :
      StepAt (.cons step tail) 0 before operation middle
  | tail {initial middle final : State n} {headOperation : Operation n}
      {operations : List (Operation n)}
      (headStep : Step params initial headOperation middle)
      (tailTrace : Trace params middle operations final)
      {index : ℕ} {before after : State n} {operation : Operation n}
      (occurrence : StepAt tailTrace index before operation after) :
      StepAt (.cons headStep tailTrace) index.succ before operation after

namespace StepAt

/-- The selected endpoints form the selected legal interface step. -/
theorem step {n : ℕ} {params : Parameters}
    {initial final before after : State n}
    {operations : List (Operation n)}
    {trace : Trace params initial operations final}
    {index : ℕ} {operation : Operation n}
    (occurrence : StepAt trace index before operation after) :
    Step params before operation after := by
  induction occurrence with
  | head step _ => exact step
  | tail _ _ _ ih => exact ih

/-- A selected chronological position lies inside the operation list. -/
theorem index_lt {n : ℕ} {params : Parameters}
    {initial final before after : State n}
    {operations : List (Operation n)}
    {trace : Trace params initial operations final}
    {index : ℕ} {operation : Operation n}
    (occurrence : StepAt trace index before operation after) :
    index < operations.length := by
  induction occurrence with
  | head _ _ => simp
  | tail _ _ _ ih =>
      simpa only [List.length_cons, Nat.succ_lt_succ_iff] using ih

/-- The operation named by an occurrence is stored at that list position. -/
theorem operation_eq_get {n : ℕ} {params : Parameters}
    {initial final before after : State n}
    {operations : List (Operation n)}
    {trace : Trace params initial operations final}
    {index : ℕ} {operation : Operation n}
    (occurrence : StepAt trace index before operation after) :
    operations.get ⟨index, occurrence.index_lt⟩ = operation := by
  induction occurrence with
  | head _ _ => rfl
  | tail _ _ occurrence ih => exact ih

end StepAt

/--
Every operation-list position exposes actual before/after states from the
given trace proof.
-/
theorem exists_stepAt {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (trace : Trace params initial operations final)
    (index : Fin operations.length) :
    ∃ before operation after,
      StepAt trace index.val before operation after := by
  induction trace with
  | nil _ =>
      exact Fin.elim0 index
  | @cons before middle after operation operations head tail ih =>
      rcases index with ⟨position, inBounds⟩
      cases position with
      | zero =>
          exact ⟨before, operation, middle, .head head tail⟩
      | succ position =>
          have tailBounds : position < operations.length := by
            simpa only [List.length_cons, Nat.succ_lt_succ_iff] using
              inBounds
          obtain ⟨stepBefore, stepOperation, stepAfter, occurrence⟩ :=
            ih ⟨position, tailBounds⟩
          exact
            ⟨stepBefore, stepOperation, stepAfter,
              .tail head tail occurrence⟩

end Trace

end Splay.Interface
