import Splay.Lazy.Model

namespace Splay.Lazy

/--
One primitive event in a rich lazy-interval execution.

Visible events are exact abstract-interface operations. Silent events cover
changes intentionally erased by that interface, such as transferring a
shrinking interval's current owner or applying a rank update whose uniform gap
shift is absorbed by the interval gap.
-/
inductive Event (n : ℕ)
  | operation (operation : Interface.Operation n)
  | silent
  deriving Repr

namespace Event

/-- Erase a rich event to zero or one abstract-interface operations. -/
def operations {n : ℕ} : Event n → List (Interface.Operation n)
  | .operation op => [op]
  | .silent => []

end Event

/-- Concatenated abstract operations exported by a rich event sequence. -/
def eraseOperations {n : ℕ} (events : List (Event n)) :
    List (Interface.Operation n) :=
  events.flatMap Event.operations

/--
One valid rich step.

For a visible event, the projections have exactly the corresponding interface
effect. A silent event must leave the complete interface projection unchanged.
Both endpoints satisfy the transient owner/order/gap invariant.
-/
def Step {n : ℕ} (params : Interface.Parameters)
    (before : State n) (event : Event n) (after : State n) : Prop :=
  before.Valid params ∧
    after.Valid params ∧
      match event with
      | .operation op =>
          Interface.Effect params before.toInterface op after.toInterface
      | .silent =>
          before.toInterface = after.toInterface

/-- A finite rich execution, including interface-invisible structural steps. -/
inductive Trace {n : ℕ} (params : Interface.Parameters) :
    State n → List (Event n) → State n → Prop
  | nil {state : State n} (valid : state.Valid params) :
      Trace params state [] state
  | cons {before middle after : State n} {event : Event n}
      {events : List (Event n)}
      (head : Step params before event middle)
      (tail : Trace params middle events after) :
      Trace params before (event :: events) after

namespace Step

theorem before_valid {n : ℕ} {params : Interface.Parameters}
    {before after : State n} {event : Event n}
    (step : Step params before event after) :
    before.Valid params :=
  step.1

theorem after_valid {n : ℕ} {params : Interface.Parameters}
    {before after : State n} {event : Event n}
    (step : Step params before event after) :
    after.Valid params :=
  step.2.1

theorem interfaceStep_of_operation {n : ℕ}
    {params : Interface.Parameters} {before after : State n}
    {operation : Interface.Operation n}
    (step : Step params before (.operation operation) after) :
    Interface.Step params before.toInterface operation after.toInterface :=
  ⟨step.1.toInterface, step.2.2, step.2.1.toInterface⟩

theorem projection_eq_of_silent {n : ℕ}
    {params : Interface.Parameters} {before after : State n}
    (step : Step params before .silent after) :
    before.toInterface = after.toInterface :=
  step.2.2

end Step

namespace Trace

/--
Every rich trace erases to a genuine trace of the abstract pairing interface.
-/
theorem toInterface {n : ℕ} {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    (trace : Trace params initial events final) :
    Interface.Trace params initial.toInterface
      (eraseOperations events) final.toInterface := by
  induction trace with
  | nil valid =>
      exact Interface.Trace.nil valid.toInterface
  | @cons before middle after event events head tail ih =>
      cases event with
      | operation operation =>
          simp only [eraseOperations, List.flatMap_cons, Event.operations,
            List.singleton_append]
          exact Interface.Trace.cons head.interfaceStep_of_operation ih
      | silent =>
          simp only [eraseOperations, List.flatMap_cons, Event.operations,
            List.nil_append]
          rw [head.projection_eq_of_silent]
          exact ih

/-- The first state of any rich trace is transient-valid. -/
theorem initial_valid {n : ℕ} {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    (trace : Trace params initial events final) :
    initial.Valid params := by
  cases trace with
  | nil valid => exact valid
  | cons head _ => exact head.before_valid

/-- The final state of any rich trace is transient-valid. -/
theorem final_valid {n : ℕ} {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    (trace : Trace params initial events final) :
    final.Valid params := by
  induction trace with
  | nil valid => exact valid
  | cons _ _ ih => exact ih

end Trace

end Splay.Lazy
