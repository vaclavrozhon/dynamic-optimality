import Greedy.EntryJournal

/-!
# Simultaneous label batches in the chronological entry journal

A batch writes every selected record once and preserves all saved creator
memories. Its positive variation is exactly the sum of the positive
endpoint differences. Thus a batch that only increases labels at selected
ports pays once per port, even when it changes many other labels.
-/

namespace Greedy.EntryJournal

open scoped BigOperators
open WeightedMemory (State)

variable {Record : Type*} [Fintype Record] [DecidableEq Record]

@[simp] theorem run_append (state : State Record) (first second : List (Action Record)) :
    run state (first ++ second) = run (run state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons action rest ih => exact ih (step state action)

@[simp] theorem total_append (weight : State Record → Action Record → ℤ)
    (state : State Record) (first second : List (Action Record)) :
    total weight state (first ++ second) = total weight state first + total weight (run state first) second := by
  induction first generalizing state with
  | nil => simp [total, run]
  | cons action rest ih => simp only [total, run, List.cons_append, ih]; omega

@[simp] theorem valid_append (K : ℤ) (state : State Record) (first second : List (Action Record)) :
    Valid K state (first ++ second) ↔ Valid K state first ∧ Valid K (run state first) second := by
  induction first generalizing state with
  | nil => simp [Valid, run]
  | cons action rest ih => simp only [List.cons_append, Valid, run, ih, and_assoc]

def relabel (target : Record → ℤ) (records : List Record) : List (Action Record) :=
  records.map (fun record => .change record (target record))

theorem relabel_valid (K : ℤ) (state : State Record) (target : Record → ℤ)
    (records : List Record) (bounded : ∀ record ∈ records, 1 ≤ target record ∧ target record ≤ K) :
    Valid K state (relabel target records) := by
  induction records generalizing state with
  | nil => trivial
  | cons record rest ih =>
      exact ⟨bounded record (by simp), ih _ (fun key member => bounded key (by simp [member]))⟩

theorem run_relabel (state : State Record) (target : Record → ℤ) (records : List Record) :
    run state (relabel target records) =
      ⟨fun record => if record ∈ records then target record else state.label record, state.memory⟩ := by
  induction records generalizing state with
  | nil => simp [relabel, run]
  | cons record rest ih =>
      change run (step state (.change record (target record))) (relabel target rest) = _
      rw [ih]
      congr 1
      funext key
      by_cases same : key = record <;> by_cases member : key ∈ rest <;>
        simp [step, encode, WeightedMemory.step, same, member]

theorem relabel_positive (state : State Record) (target : Record → ℤ)
    (records : List Record) (distinct : records.Nodup) :
    total positiveChange state (relabel target records) =
      ∑ record ∈ records.toFinset, max 0 (target record - state.label record) := by
  induction records generalizing state with
  | nil => simp [relabel, total]
  | cons record rest ih =>
      have fresh := (List.nodup_cons.mp distinct).1
      have tail := ih (step state (.change record (target record))) (List.nodup_cons.mp distinct).2
      simp only [relabel, List.map_cons, total] at ⊢
      rw [show List.map (fun record => Action.change record (target record)) rest = relabel target rest from rfl,
        tail, List.toFinset_cons, Finset.sum_insert (by simpa using fresh)]
      congr 1
      apply Finset.sum_congr rfl
      intro key member
      have different : key ≠ record := by intro equal; subst key; exact fresh (List.mem_toFinset.mp member)
      simp [step, encode, WeightedMemory.step, different]

theorem relabel_zero (weight : State Record → Action Record → ℤ)
    (zero : ∀ state record value, weight state (.change record value) = 0)
    (state : State Record) (target : Record → ℤ) (records : List Record) :
    total weight state (relabel target records) = 0 := by
  induction records generalizing state with
  | nil => rfl
  | cons record rest ih =>
      change weight state (.change record (target record)) +
        total weight (step state (.change record (target record))) (relabel target rest) = 0
      rw [zero, ih, add_zero]

noncomputable def batch (target : Record → ℤ) : List (Action Record) :=
  relabel target (Finset.univ.toList)

@[simp] theorem run_batch (state : State Record) (target : Record → ℤ) :
    run state (batch target) = ⟨target, state.memory⟩ := by
  rw [batch, run_relabel]
  simp

@[simp] theorem batch_positive (state : State Record) (target : Record → ℤ) :
    total positiveChange state (batch target) = ∑ record, max 0 (target record - state.label record) := by
  rw [batch, relabel_positive state target _ (Finset.nodup_toList _), Finset.toList_toFinset]

theorem batch_valid (K : ℤ) (state : State Record) (target : Record → ℤ)
    (bounded : ∀ record, 1 ≤ target record ∧ target record ≤ K) :
    Valid K state (batch target) :=
  relabel_valid K state target _ (fun record _ => bounded record)

theorem batch_positive_le_ports (K : ℤ) (state : State Record) (target : Record → ℤ)
    (ports : Finset Record) (oldBound : Bounded K state)
    (newBound : ∀ record, 1 ≤ target record ∧ target record ≤ K)
    (free : ∀ record, record ∉ ports → target record ≤ state.label record) :
    total positiveChange state (batch target) ≤ (K - 1) * ports.card := by
  rw [batch_positive]
  have pointwise : ∀ record, max 0 (target record - state.label record) ≤
      if record ∈ ports then K - 1 else 0 := by
    intro record
    have old := oldBound record
    have current := newBound record
    by_cases member : record ∈ ports
    · simp only [member, ↓reduceIte]; omega
    · have decrease := free record member
      simp only [member, ↓reduceIte]; omega
  calc
    _ ≤ ∑ record, if record ∈ ports then K - 1 else 0 := Finset.sum_le_sum (fun record _ => pointwise record)
    _ = (K - 1) * ports.card := by simp; ring

end Greedy.EntryJournal
