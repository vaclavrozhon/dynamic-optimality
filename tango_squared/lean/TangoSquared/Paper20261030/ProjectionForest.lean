import TangoSquared.Paper20261030.PackedExecution
import TangoSquared.Paper20261030.PackedRearrangements

/-!
# Sequential execution in a forest with one cursor per color

A forest instruction acts at one specified color's current cursor. All
other cursors remain unchanged. A finite batch is serialized into these
instructions, with the sum of the individual costs. This model is an
intermediate step: it has constantly many disjoint routing trees and has
not yet been compiled into the ordinary single-cursor BST.
-/

namespace TangoSquared.Paper20261030.ProjectionForest

open ColoredStorage SourcePointer

variable {α ρ C : Type*} [DecidableEq C]

abbrev State (C α ρ : Type*) := C → Option (Cursor α (List ρ))
abbrev Observation (C ρ : Type*) := C × List ρ

inductive Trace : State C α ρ → List (Observation C ρ) → State C α ρ → Nat → Prop
  | nil (state) : Trace state [] state 0
  | step {state final q before after reads cost}
      (atCursor : state q = some before) (move : SourcePointer.Step before after)
      (rest : Trace (Function.update state q (some after)) reads final cost) :
      Trace state reads final (cost+1)
  | read {state final q cursor reads cost} (atCursor : state q = some cursor)
      (rest : Trace state reads final cost) :
      Trace state ((q,cursor.focus.rootRecord)::reads) final (cost+1)

theorem Trace.append {before middle after : State C α ρ} {xs ys : List (Observation C ρ)} {m n : Nat}
    (first : Trace before xs middle m) (last : Trace middle ys after n) :
    Trace before (xs++ys) after (m+n) := by
  induction first with
  | nil => simpa using last
  | step atCursor move rest ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Trace.step atCursor move (ih last)
  | read atCursor rest ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Trace.read atCursor (ih last)

theorem run_at (q : C) (state : State C α ρ)
    {before after : Cursor α (List ρ)} {reads : List (List ρ)} {cost : Nat}
    (atCursor : state q = some before) (execution : SourcePointer.Trace before reads after cost) :
    Trace state (reads.map (fun records => (q,records))) (Function.update state q (some after)) cost := by
  induction execution generalizing state with
  | nil before =>
    have unchanged : Function.update state q (some before) = state := by
      rw [← atCursor,Function.update_eq_self]
    rw [unchanged]
    exact .nil _
  | step move rest ih =>
    have next := ih (Function.update state q _) (Function.update_self _ _ _)
    simpa only [Function.update_idem] using Trace.step atCursor move next
  | read rest ih => exact .read atCursor (ih state atCursor)

def LocalTrace : Option (Cursor α (List ρ)) → Option (Cursor α (List ρ)) → Nat → Prop
  | none,none,cost => cost = 0
  | some before,some after,cost => ∃ reads, SourcePointer.Trace before reads after cost
  | _,_,_ => False

def mix (selected : Finset C) (before after : State C α ρ) : State C α ρ :=
  fun q => if q ∈ selected then after q else before q

theorem batch (selected : Finset C) (before after : State C α ρ) (costs : C → Nat)
    (traces : ∀ q ∈ selected, LocalTrace (before q) (after q) (costs q)) :
    ∃ reads, Trace before reads (mix selected before after) (∑ q ∈ selected, costs q) := by
  induction selected using Finset.induction_on with
  | empty =>
    have same : mix ∅ before after = before := by funext q; simp [mix]
    rw [same,Finset.sum_empty]
    exact ⟨[],Trace.nil before⟩
  | @insert q selected absent ih =>
    obtain ⟨firstReads,first⟩ := ih (fun i hi => traces i (Finset.mem_insert_of_mem hi))
    have current : mix selected before after q = before q := by simp [mix,absent]
    have update : Function.update (mix selected before after) q (after q) = mix (insert q selected) before after := by
      funext i
      by_cases eq : i = q
      · subst i; simp [mix]
      · simp [mix,eq]
    have localTrace := traces q (Finset.mem_insert_self q selected)
    cases old : before q with
    | none =>
      cases fresh : after q with
      | none =>
        have zero : costs q = 0 := by simpa only [old,fresh,LocalTrace] using localTrace
        have same : mix (insert q selected) before after = mix selected before after := by
          rw [← update,fresh,← old,← current,Function.update_eq_self]
        refine ⟨firstReads,?_⟩
        simpa only [Finset.sum_insert absent,zero,Nat.zero_add,same] using first
      | some cursor => simp only [old,fresh,LocalTrace] at localTrace
    | some initial =>
      cases fresh : after q with
      | none => simp only [old,fresh,LocalTrace] at localTrace
      | some final =>
        obtain ⟨reads,trace⟩ : ∃ reads, SourcePointer.Trace initial reads final (costs q) := by
          simpa only [old,fresh,LocalTrace] using localTrace
        have last := run_at q (mix selected before after) (current.trans old) trace
        rw [← fresh,update] at last
        refine ⟨firstReads ++ reads.map (fun records => (q,records)),?_⟩
        simpa only [Finset.sum_insert absent,Nat.add_comm] using first.append last

theorem batch_all [Fintype C] (before after : State C α ρ) (costs : C → Nat)
    (traces : ∀ q, LocalTrace (before q) (after q) (costs q)) :
    ∃ reads, Trace before reads after (∑ q, costs q) := by
  have same : mix Finset.univ before after = after := by funext q; simp [mix]
  simpa only [same] using batch Finset.univ before after costs (fun q _ => traces q)

end TangoSquared.Paper20261030.ProjectionForest
