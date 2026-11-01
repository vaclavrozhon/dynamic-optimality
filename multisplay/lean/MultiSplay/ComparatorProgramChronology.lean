import MultiSplay.ComparatorGenuineHistory
import MultiSplay.ClassicalSwitchHistory
import MultiSplay.ComparatorGapProgram

/-! # Composing comparator services in the actual switch chronology

This reusable induction retains each service's exact output forest and
persistent memory. The invariant and its concrete local service are explicit
parameters here; the actual comparator instantiates them separately.
-/

namespace MultiSplay.ComparatorHistory

open DynamicOptimality (RawTree)
open TangoSquared (DepthTree)
open TangoSquared.Primary (Key)
open EndpointEncoding ClassicalSwitch CommonForest
open Secondary (Row)

def advance (memory : Row → Bool) : List (State × Key) → Row → Bool
  | [] => memory
  | entry :: rest => advance (update entry memory) rest

theorem advance_append (memory : Row → Bool) (first rest : List (State × Key)) :
    advance memory (first ++ rest) = advance (advance memory first) rest := by
  induction first generalizing memory with
  | nil => rfl
  | cons entry first ih => exact ih (update entry memory)

theorem runCost_append {a b : Nat} (reference : DepthTree a b) (memory : Row → Bool)
    (first rest : List (State × Key)) :
    runCost reference memory (first ++ rest) =
      runCost reference memory first + runCost reference (advance memory first) rest := by
  induction first generalizing memory with
  | nil => simp [runCost,advance]
  | cons entry first ih => simp only [List.cons_append,runCost,advance,ih,Nat.add_assoc]

def Service {a b : Nat} (secondary : DepthTree a b) (reference : RawTree Nat) (scale : Nat)
    (invariant : State → (Row → Bool) → List (RawTree Nat) → Prop) : Prop :=
  ∀ state memory before owner,
    invariant state memory before → referenceAt reference owner ≠ .empty →
    ∃ after work, invariant (toggle state owner) (update (state,owner) memory) after ∧
      Program before (eventWord reference state owner) after work ∧
      work ≤ scale * (eventCost secondary memory (state,owner) + 1)

theorem service_schedule {a b : Nat} (secondary : DepthTree a b) (reference : RawTree Nat)
    (scale : Nat) (invariant : State → (Row → Bool) → List (RawTree Nat) → Prop)
    (service : Service secondary reference scale invariant)
    (state : State) (memory : Row → Bool) (before : List (RawTree Nat)) (owners : List Key)
    (valid : invariant state memory before)
    (real : ∀ owner ∈ owners, referenceAt reference owner ≠ .empty) :
    ∃ after work,
      invariant (applySwitches state owners) (advance memory (schedule state owners)) after ∧
      Program before ((schedule state owners).flatMap fun entry => eventWord reference entry.1 entry.2) after work ∧
      work ≤ scale * (owners.length + runCost secondary memory (schedule state owners)) := by
  induction owners generalizing state memory before with
  | nil => exact ⟨before,0,valid,.nil _,by simp [runCost,schedule]⟩
  | cons owner rest ih =>
      obtain ⟨middle,headWork,headValid,headRun,headBound⟩ := service state memory before owner valid
        (real owner (by simp))
      obtain ⟨after,tailWork,tailValid,tailRun,tailBound⟩ := ih (toggle state owner)
        (update (state,owner) memory) middle headValid (fun next member => real next (by simp [member]))
      refine ⟨after,headWork+tailWork,tailValid,headRun.append tailRun,?_⟩
      simp only [List.length_cons,schedule,runCost]
      nlinarith

theorem service_history {a b : Nat} (secondary : DepthTree a b) (reference : RawTree Nat)
    (scale : Nat) (invariant : State → (Row → Bool) → List (RawTree Nat) → Prop)
    (service : Service secondary reference scale invariant)
    (state : State) (memory : Row → Bool) (before : List (RawTree Nat)) (addresses : List Key)
    (valid : invariant state memory before)
    (real : ∀ address ∈ addresses, referenceAt reference address ≠ .empty) :
    ∃ after work,
      invariant (addresses.foldl nodeStep state) (advance memory (history state addresses)) after ∧
      Program before (historyWord reference state addresses) after work ∧
      work ≤ scale * ((actualHistory state addresses).length +
        runCost secondary memory (history state addresses)) := by
  induction addresses generalizing state memory before with
  | nil => exact ⟨before,0,valid,.nil _,by simp [actualHistory,runCost,history]⟩
  | cons address rest ih =>
      have ownerReal : ∀ owner ∈ actualEmissions state address, referenceAt reference owner ≠ .empty := by
        intro owner member
        exact referenceAt_prefix_nonempty (real address (by simp)) (actual_prefix member)
      obtain ⟨middle,headWork,headValid,headRun,headBound⟩ :=
        service_schedule secondary reference scale invariant service state memory before
          (actualEmissions state address) valid ownerReal
      rw [actualEmissions_state] at headValid
      obtain ⟨after,tailWork,tailValid,tailRun,tailBound⟩ := ih (nodeStep state address)
        (advance memory (schedule state (actualEmissions state address))) middle headValid
          (fun next member => real next (by simp [member]))
      refine ⟨after,headWork+tailWork,?_,headRun.append tailRun,?_⟩
      · simpa only [List.foldl_cons,history,advance_append] using tailValid
      · simp only [actualHistory,List.length_append,history,runCost_append]
        nlinarith

/-- The subselected genuine history is charged against the already proved
actual ledger with its original initial bits, never against reset bits. -/
theorem service_history_le_actual {a b : Nat} (secondary : DepthTree a b) (reference : RawTree Nat)
    (scale : Nat) (invariant : State → (Row → Bool) → List (RawTree Nat) → Prop)
    (service : Service secondary reference scale invariant)
    (state : State) (memory : Row → Bool) (before : List (RawTree Nat)) (addresses : List Key)
    (valid : invariant state memory before)
    (real : ∀ address ∈ addresses, referenceAt reference address ≠ .empty) :
    ∃ after work,
      Program before (historyWord reference state addresses) after work ∧
      work ≤ scale * ((actualHistory state addresses).length +
        Secondary.actualLedger secondary memory state addresses) := by
  obtain ⟨after,work,_,run,paid⟩ := service_history secondary reference scale invariant service
    state memory before addresses valid real
  exact ⟨after,work,run,paid.trans (Nat.mul_le_mul_left _
    (Nat.add_le_add_left (runCost_history_le_actual secondary memory state addresses) _))⟩

end MultiSplay.ComparatorHistory
