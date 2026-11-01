import Greedy.CreditPrograms
import Greedy.MembershipPointer
import Greedy.RestorationMemory

/-! Label batches and administrative actions with exact membership annotations. -/

namespace Greedy.WinnerCredit

open EntryJournal

variable {Record Ticket : Type*} [Fintype Record] [DecidableEq Record] [DecidableEq Ticket]

def Administrative (actions : List (Action Record Ticket)) : Prop :=
  ∀ action ∈ actions, match action with
  | .change _ _ => True
  | .entry _ _ kind _ => kind = .ordinary
  | .win _ _ => False

theorem administrative_append (first second : List (Action Record Ticket)) :
    Administrative (first ++ second) ↔ Administrative first ∧ Administrative second := by
  simp only [Administrative, List.mem_append, or_imp, forall_and]

theorem Administrative.legal {actions : List (Action Record Ticket)} (admin : Administrative actions)
    (state : State Record Ticket) : Legal state actions := by
  induction actions generalizing state with
  | nil => trivial
  | cons action rest ih =>
      have head := admin action (List.mem_cons_self)
      have tail := ih (fun next member => admin next (List.mem_cons_of_mem _ member)) (step state action)
      cases action with
      | change => exact ⟨trivial, tail⟩
      | entry => exact ⟨trivial, tail⟩
      | win => exact False.elim head

theorem Administrative.paired {actions : List (Action Record Ticket)} (admin : Administrative actions) : Paired actions := by
  induction actions with
  | nil => exact .nil
  | cons action rest ih =>
      have head := admin action (List.mem_cons_self)
      have tail := ih (fun next member => admin next (List.mem_cons_of_mem _ member))
      cases action with
      | change record label => exact .change record label tail
      | entry record creator kind ticket => exact head ▸ Paired.ordinary record creator ticket tail
      | win => exact False.elim head

theorem Administrative.remaining_zero {actions : List (Action Record Ticket)} (admin : Administrative actions) (ticket : Ticket) :
    remaining actions ticket = 0 := by
  induction actions with
  | nil => rfl
  | cons action rest ih =>
      have head := admin action (List.mem_cons_self)
      have tail := ih (fun next member => admin next (List.mem_cons_of_mem _ member))
      cases action <;> simp_all only [remaining]

def relabel (target : Record → ℤ) (records : List Record) : List (Action Record Ticket) :=
  records.map (fun record => .change record (target record))

noncomputable def batch (target : Record → ℤ) : List (Action Record Ticket) := relabel target Finset.univ.toList

theorem relabel_erases (target : Record → ℤ) (records : List Record) :
    erase (relabel (Ticket := Ticket) target records) = EntryJournal.relabel target records := by
  induction records with
  | nil => rfl
  | cons record rest ih => simp only [relabel, List.map_cons, erase, List.flatMap_cons, eraseOne, List.singleton_append] at *; exact congrArg (List.cons _) ih

theorem relabel_ticket (target : Record → ℤ) (records : List Record) (state : State Record Ticket) :
    (run state (relabel target records)).ticket = state.ticket := by
  induction records generalizing state with
  | nil => rfl
  | cons record rest ih => exact ih (step state (.change record (target record)))

theorem batch_erases (target : Record → ℤ) : erase (batch (Ticket := Ticket) target) = EntryJournal.batch target :=
  relabel_erases target Finset.univ.toList

theorem batch_ticket (target : Record → ℤ) (state : State Record Ticket) :
    (run state (batch target)).ticket = state.ticket := relabel_ticket target Finset.univ.toList state

theorem batch_administrative (target : Record → ℤ) : Administrative (batch (Ticket := Ticket) target) := by
  intro action member
  obtain ⟨record, _, rfl⟩ := List.mem_map.mp member
  trivial

end Greedy.WinnerCredit
