import Mathlib

/-!
# Sparse, timestamped histories of actual label changes

A change stamped `t` occurs after entries stamped `t` have read their
labels. Thus `value t` includes precisely changes with stamp smaller than
`t`. A vector batch records the difference between its target and the
current labels. No artificial entry times are introduced by serialization.
-/

namespace Greedy.LabelHistory

structure Change (Record : Type*) where
  time : ℕ
  delta : Record → ℤ

structure History (Record : Type*) where
  initial : Record → ℤ
  changes : List (Change Record)

variable {Record : Type*}

def value (history : History Record) (time : ℕ) (record : Record) : ℤ :=
  history.initial record + (history.changes.map (fun change => if change.time < time then change.delta record else 0)).sum

def current (history : History Record) (record : Record) : ℤ :=
  history.initial record + (history.changes.map (fun change => change.delta record)).sum

def Before (history : History Record) (clock : ℕ) : Prop :=
  ∀ change ∈ history.changes, change.time < clock

def update (history : History Record) (time : ℕ) (target : Record → ℤ) : History Record :=
  { history with changes := history.changes ++ [⟨time, fun record => target record - current history record⟩] }

@[simp] theorem current_initial (label : Record → ℤ) : current ⟨label, []⟩ = label := by
  funext record
  simp [current]

@[simp] theorem value_initial (label : Record → ℤ) (time : ℕ) : value ⟨label, []⟩ time = label := by
  funext record
  simp [value]

theorem current_eq_value (history : History Record) (clock : ℕ) (before : Before history clock) :
    current history = value history clock := by
  funext record
  unfold current value
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro change member
  simp [before change member]

@[simp] theorem current_update (history : History Record) (time : ℕ) (target : Record → ℤ) :
    current (update history time target) = target := by
  funext record
  simp [current, update]
  ring

theorem value_update (history : History Record) (time : ℕ) (target : Record → ℤ) (query : ℕ) (record : Record) :
    value (update history time target) query record = value history query record +
      if time < query then target record - current history record else 0 := by
  simp [value, update]
  ring

theorem update_preserves_past (history : History Record) (time : ℕ) (target : Record → ℤ)
    (query : ℕ) (past : query ≤ time) : value (update history time target) query = value history query := by
  funext record
  rw [value_update]
  simp [show ¬time < query by omega]

theorem update_before (history : History Record) (clock : ℕ) (target : Record → ℤ)
    (before : Before history clock) : Before (update history clock target) (clock+1) := by
  intro change member
  rcases List.mem_append.mp member with old | fresh
  · exact (before change old).trans_le (by omega)
  · have same := List.mem_singleton.mp fresh
    subst change
    simp

theorem Before.mono {history : History Record} {clock : ℕ} (before : Before history clock)
    (later : ℕ) (bound : clock ≤ later) : Before history later :=
  fun change member => (before change member).trans_le bound

/-- Any immutable snapshot no later than this batch is preserved exactly. -/
theorem snapshot_preserved (history : History Record) (clock : ℕ) (target : Record → ℤ)
    (record : Record) (joined : ℕ) (stored : ℤ) (past : joined ≤ clock)
    (snapshot : stored = value history joined record) : stored = value (update history clock target) joined record := by
  rw [update_preserves_past history clock target joined past]
  exact snapshot

/-- An entry made immediately before the batch stores the actual current
label and keeps that same historical value after the batch. -/
theorem current_snapshot (history : History Record) (clock : ℕ) (target : Record → ℤ)
    (before : Before history clock) (record : Record) :
    current history record = value (update history clock target) clock record := by
  rw [update_preserves_past history clock target clock (le_refl _)]
  exact congrFun (current_eq_value history clock before) record

open scoped BigOperators

/-- Finite sums of stored differences use the original joined timestamps.
This is the sparse counterpart of the dense telescope in `ForestLedger`. -/
theorem difference (history : History Record) (record : Record) (first last : ℕ) :
    value history last record - value history first record =
      (history.changes.map (fun change =>
        ((if change.time < last then (1 : ℤ) else 0) -
          (if change.time < first then (1 : ℤ) else 0)) * change.delta record)).sum := by
  unfold value
  have pointwise (change : Change Record) :
      ((if change.time < last then (1 : ℤ) else 0) - (if change.time < first then (1 : ℤ) else 0)) * change.delta record =
        (if change.time < last then change.delta record else 0) -
          (if change.time < first then change.delta record else 0) := by
    split_ifs <;> ring
  simp_rw [pointwise]
  have subtract (changes : List (Change Record)) :
      (changes.map (fun change => (if change.time < last then change.delta record else 0) -
        (if change.time < first then change.delta record else 0))).sum =
      (changes.map (fun change => if change.time < last then change.delta record else 0)).sum -
        (changes.map (fun change => if change.time < first then change.delta record else 0)).sum := by
    induction changes with
    | nil => simp
    | cons change rest ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [subtract]
  ring

end Greedy.LabelHistory
