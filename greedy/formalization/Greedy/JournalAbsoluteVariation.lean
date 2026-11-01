import Greedy.JournalVariation
import Greedy.JournalBatches
import Greedy.SparseCreatorSum

/-! Match sparse vector variation with the same chronological entry journal. -/

namespace Greedy.EntryJournal

open WeightedMemory (State)
open scoped BigOperators

variable {Record : Type*} [Fintype Record] [DecidableEq Record]

def absoluteChange (state : State Record) : Action Record → ℤ
  | .change record value => |value - state.label record|
  | .entry _ _ _ => 0

theorem absoluteChange_eq (state : State Record) (action : Action Record) :
    absoluteChange state action = positiveChange state action + negativeChange state action := by
  cases action with
  | change record value =>
      simp only [absoluteChange, positiveChange, negativeChange, encode, WeightedMemory.positiveChange]
      by_cases nonnegative : 0 ≤ value - state.label record
      · rw [abs_of_nonneg nonnegative]; omega
      · rw [abs_of_neg (by omega : value - state.label record < 0)]; omega
  | entry => rfl

theorem total_absolute_eq (state : State Record) (actions : List (Action Record)) :
    total absoluteChange state actions = total positiveChange state actions + total negativeChange state actions := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      simp only [total, absoluteChange_eq, ih]
      omega

theorem relabel_absolute (state : State Record) (target : Record → ℤ)
    (records : List Record) (distinct : records.Nodup) :
    total absoluteChange state (relabel target records) = ∑ record ∈ records.toFinset, |target record - state.label record| := by
  induction records generalizing state with
  | nil => simp [relabel, total]
  | cons record rest ih =>
      have fresh := (List.nodup_cons.mp distinct).1
      have tail := ih (step state (.change record (target record))) (List.nodup_cons.mp distinct).2
      simp only [relabel, List.map_cons, total]
      rw [show List.map (fun record => Action.change record (target record)) rest = relabel target rest from rfl,
        tail, List.toFinset_cons, Finset.sum_insert (by simpa using fresh)]
      congr 1
      apply Finset.sum_congr rfl
      intro key member
      have different : key ≠ record := by intro equal; subst key; exact fresh (List.mem_toFinset.mp member)
      simp [step, encode, WeightedMemory.step, different]

theorem batch_absolute (state : State Record) (target : Record → ℤ) :
    total absoluteChange state (batch target) = ∑ record, |target record - state.label record| := by
  rw [batch, relabel_absolute state target _ (Finset.nodup_toList _), Finset.toList_toFinset]

end Greedy.EntryJournal

namespace Greedy.LabelHistory

open scoped BigOperators

variable {Record : Type*} [Fintype Record] [DecidableEq Record]

theorem variation_update (history : History Record) (time : ℕ) (target : Record → ℤ) :
    variation (update history time target) = variation history + ∑ record, |target record - current history record| := by
  simp [variation, update]

theorem update_batch_variation (history : History Record) (time : ℕ) (state : WeightedMemory.State Record)
    (target : Record → ℤ) (agree : current history = state.label) :
    variation (update history time target) = variation history +
      EntryJournal.total EntryJournal.absoluteChange state (EntryJournal.batch target) := by
  rw [variation_update, agree, EntryJournal.batch_absolute]

theorem update_single_variation (history : History Record) (time : ℕ) (state : WeightedMemory.State Record)
    (record : Record) (value : ℤ) (agree : current history = state.label) :
    variation (update history time (Function.update state.label record value)) = variation history +
      EntryJournal.absoluteChange state (.change record value) := by
  rw [variation_update, agree]
  congr 1
  classical
  rw [Finset.sum_eq_single record]
  · simp [EntryJournal.absoluteChange]
  · intro other _ different
    simp [Function.update_of_ne different]
  · simp

end Greedy.LabelHistory
