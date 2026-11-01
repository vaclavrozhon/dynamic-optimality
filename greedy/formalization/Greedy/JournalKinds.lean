import Greedy.JournalBatches

/-! Entry classification and journals containing only ordinary entries. -/

namespace Greedy.EntryJournal

open WeightedMemory (State)
variable {Record : Type*} [Fintype Record] [DecidableEq Record]

def internal (_state : State Record) : Action Record → ℤ
  | .entry _ _ .internal => 1
  | _ => 0

def IsOrdinary : Action Record → Prop
  | .change _ _ => True
  | .entry _ _ kind => kind = .ordinary

def OrdinaryOnly (actions : List (Action Record)) : Prop := ∀ action ∈ actions, IsOrdinary action

@[simp] theorem ordinaryOnly_append (first second : List (Action Record)) :
    OrdinaryOnly (first ++ second) ↔ OrdinaryOnly first ∧ OrdinaryOnly second := by
  simp only [OrdinaryOnly, List.mem_append, or_imp, forall_and]

theorem ordinaryOnly_batch (target : Record → ℤ) : OrdinaryOnly (batch target) := by
  intro action member
  obtain ⟨record, _, rfl⟩ := List.mem_map.mp member
  trivial

theorem ordinaryOnly_total_zero (weight : State Record → Action Record → ℤ)
    (changeZero : ∀ state record value, weight state (.change record value) = 0)
    (entryZero : ∀ state record creator, weight state (.entry record creator .ordinary) = 0)
    (state : State Record) (actions : List (Action Record)) (ordinary : OrdinaryOnly actions) :
    total weight state actions = 0 := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      have head := ordinary action (by simp)
      have tail := ih (step state action) (fun action member => ordinary action (by simp [member]))
      rw [total, tail, add_zero]
      cases action with
      | change record value => exact changeZero ..
      | entry record creator kind =>
          have equal : kind = .ordinary := head
          subst kind
          exact entryZero ..

theorem ordinaryOnly_internal_zero (state : State Record) (actions : List (Action Record))
    (ordinary : OrdinaryOnly actions) : total internal state actions = 0 :=
  ordinaryOnly_total_zero internal (by intros; rfl) (by intros; rfl) state actions ordinary

theorem ordinaryOnly_boundary_zero (state : State Record) (actions : List (Action Record))
    (ordinary : OrdinaryOnly actions) : total boundary state actions = 0 :=
  ordinaryOnly_total_zero boundary (by intros; rfl) (by intros; rfl) state actions ordinary

end Greedy.EntryJournal
