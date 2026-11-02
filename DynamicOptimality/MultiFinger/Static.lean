import DynamicOptimality.ColoredWalks.EmbeddingMetric
import Mathlib.Data.Finset.Basic

/-! Persistent fingers in a fixed instance of the shared raw BST.
A request costs one, and moving any chosen finger costs the actual number
of adjacent edges. The definition is a benchmark execution, not a second
ordinary-BST optimum and not a claimed simulation theorem. -/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR
open ColoredWalks

variable {α : Type*}

structure Configuration (reference : RawTree α) (count : Nat) where
  finger : Fin count → Pointer.Cursor α
  valid : ∀ index, (finger index).tree = reference

def Configuration.update {reference : RawTree α} {count : Nat}
    (state : Configuration reference count) (index : Fin count) (cursor : Pointer.Cursor α)
    (valid : cursor.tree = reference) : Configuration reference count :=
  ⟨Function.update state.finger index cursor,by
    intro other
    by_cases same : other = index
    · subst other; simpa using valid
    · simpa [same] using state.valid other⟩

/-- One static edge move with a chosen persistent finger. Bookkeeping
which finger moves is free; the actual move still has unit cost. -/
inductive Step {reference : RawTree α} {count : Nat} :
    Configuration reference count → Configuration reference count → Prop
  | move (state : Configuration reference count) (index : Fin count) (next : Pointer.Cursor α)
      (actual : Pointer.Step (state.finger index) next)
      (same : next.tree = reference) :
      Step state (state.update index next same)

inductive Execution {reference : RawTree α} {count : Nat} :
    Configuration reference count → List α → Configuration reference count → Nat → Prop
  | done (state : Configuration reference count) : Execution state [] state 0
  | move {before middle after : Configuration reference count} {word : List α} {cost : Nat}
      (step : Step before middle) (rest : Execution middle word after cost) :
      Execution before word after (cost+1)
  | serve {before after : Configuration reference count} {word : List α} {cost : Nat}
      (index : Fin count) (key : α) (found : (before.finger index).focus.rootKey = some key)
      (rest : Execution before word after cost) : Execution before (key::word) after (cost+1)

 theorem Execution.append {reference : RawTree α} {count : Nat}
    {before middle after : Configuration reference count} {first last : List α} {a b : Nat}
    (front : Execution before first middle a) (back : Execution middle last after b) :
    Execution before (first++last) after (a+b) := by
  induction front with
  | done => simpa using back
  | move step rest ih => simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Execution.move step (ih back)
  | serve index key found rest ih =>
    simpa only [List.cons_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Execution.serve index key found (ih back)

 theorem Execution.length_le {reference : RawTree α} {count : Nat}
    {before after : Configuration reference count} {word : List α} {cost : Nat}
    (run : Execution before word after cost) : word.length ≤ cost := by
  induction run with
  | done => simp
  | move _ _ ih => exact Nat.le_trans ih (Nat.le_succ _)
  | serve _ _ _ _ ih => simpa only [List.length_cons] using Nat.add_le_add_right ih 1

 theorem Configuration.move_path {reference : RawTree α} {count : Nat}
    (state : Configuration reference count) (index : Fin count) {next : Pointer.Cursor α} {cost : Nat}
    (path : Moves (state.finger index) next cost) :
    ∃ after : Configuration reference count,
      after.finger index = next ∧ (∀ other, other ≠ index → after.finger other = state.finger other) ∧
      Execution state [] after cost := by
  generalize startEq : state.finger index = start at path
  induction path generalizing state with
  | refl cursor => exact ⟨state,startEq,by intros; rfl,.done state⟩
  | @step first middle last cost move same rest ih =>
    have valid : middle.tree = reference := same.symm.trans (startEq ▸ state.valid index)
    let current := state.update index middle valid
    have atMiddle : current.finger index = middle := by simp [current,Configuration.update]
    obtain ⟨after,atLast,others,trace⟩ := ih current atMiddle
    refine ⟨after,atLast,?_,?_⟩
    · intro other different
      rw [others other different]
      simp [current,Configuration.update,different]
    · have step : Step state current := .move state index middle (startEq ▸ move) valid
      exact .move step trace

end DynamicOptimality.MultiFinger
