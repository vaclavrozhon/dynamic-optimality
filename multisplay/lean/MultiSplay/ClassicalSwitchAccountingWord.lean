import MultiSplay.ClassicalSwitchAccountingInventory

/-! # Every exact classical history preserves its live-key inventory -/

namespace MultiSplay.ClassicalSwitch.Accounting

open DynamicOptimality (RawTree)
open TangoSquared.Primary (Key)
open EndpointEncoding CommonForest

variable {α : Type*} [DecidableEq α]

theorem leftWord_safe (lower upper : Boundary α) (old incoming : List α) (pivot : α) :
    Safe (leftWord lower upper old incoming pivot) := by
  intro key
  cases lower <;> cases upper <;>
    simp only [leftWord, leftToRightWord, noLowerWord, noUpperWord, noGuardsWord, SafeAt, eventChange] <;>
    split_ifs <;> norm_num

theorem leftWord_balanced (lower upper : Boundary α) (old incoming : List α) (pivot : α) :
    Balanced (leftWord lower upper old incoming pivot) := by
  intro key
  cases lower <;> cases upper <;>
    simp only [leftWord, leftToRightWord, noLowerWord, noUpperWord, noGuardsWord, change,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, eventChange] <;>
    split_ifs <;> norm_num

@[simp] theorem eventChange_mirror (event : Event α) (key : α) :
    eventChange event.mirror key = eventChange event key := by cases event <;> rfl

theorem safeAt_mirror (word : List (Event α)) (key : α) (level : Int) :
    SafeAt key level (word.map Event.mirror) ↔ SafeAt key level word := by
  induction word generalizing level with
  | nil => rfl
  | cons event rest ih => simp [SafeAt, ih]

theorem change_mirror (word : List (Event α)) (key : α) :
    change (word.map Event.mirror) key = change word key := by
  simp [change, List.map_map, Function.comp_def]

theorem word_safe (oldSide : Bool) (lower upper : Boundary α) (old incoming : List α) (pivot : α) :
    Safe (word oldSide lower upper old incoming pivot) := by
  cases oldSide with
  | false => exact leftWord_safe lower upper old incoming pivot
  | true =>
      intro key
      exact (safeAt_mirror _ key 0).mpr
        (leftWord_safe upper.reflect lower.reflect old.reverse incoming.reverse pivot key)

theorem word_balanced (oldSide : Bool) (lower upper : Boundary α) (old incoming : List α) (pivot : α) :
    Balanced (word oldSide lower upper old incoming pivot) := by
  cases oldSide with
  | false => exact leftWord_balanced lower upper old incoming pivot
  | true =>
      intro key
      rw [word, if_pos rfl, change_mirror]
      exact leftWord_balanced upper.reflect lower.reflect old.reverse incoming.reverse pivot key

theorem eventWord_safe (reference : RawTree α) (state : State) (owner : Key) :
    Safe (eventWord reference state owner) := by
  unfold eventWord
  split
  · intro key; exact Int.le_refl _
  · exact word_safe _ _ _ _ _ _

theorem eventWord_balanced (reference : RawTree α) (state : State) (owner : Key) :
    Balanced (eventWord reference state owner) := by
  unfold eventWord
  split
  · intro key; rfl
  · exact word_balanced _ _ _ _ _ _

theorem schedule_safe_balanced (reference : RawTree α) (state : State) (owners : List Key) :
    Safe ((schedule state owners).flatMap fun entry => eventWord reference entry.1 entry.2) ∧
    Balanced ((schedule state owners).flatMap fun entry => eventWord reference entry.1 entry.2) := by
  induction owners generalizing state with
  | nil => exact ⟨fun _ => Int.le_refl _,fun _ => rfl⟩
  | cons owner rest ih =>
      have headSafe := eventWord_safe reference state owner
      have headBalanced := eventWord_balanced reference state owner
      obtain ⟨tailSafe,tailBalanced⟩ := ih (toggle state owner)
      exact ⟨headSafe.append headBalanced tailSafe,headBalanced.append tailBalanced⟩

theorem history_safe_balanced (reference : RawTree α) (state : State) (addresses : List Key) :
    Safe (historyWord reference state addresses) ∧ Balanced (historyWord reference state addresses) := by
  induction addresses generalizing state with
  | nil => exact ⟨fun _ => Int.le_refl _,fun _ => rfl⟩
  | cons address rest ih =>
      obtain ⟨headSafe,headBalanced⟩ := schedule_safe_balanced reference state (actualEmissions state address)
      obtain ⟨tailSafe,tailBalanced⟩ := ih (nodeStep state address)
      exact ⟨headSafe.append headBalanced tailSafe,headBalanced.append tailBalanced⟩

/-- Distinctness is derived for the actual supplied trace. It need not be
included as an invariant field of the physical algorithm. -/
theorem history_distinct {reference : RawTree α} {state : State} {addresses : List Key}
    {before after : List (RawTree α)} {cost : Nat}
    (run : SplayTrace before (historyWord reference state addresses) after cost)
    (unique : UniqueKeys before) :
    DistinctSplayTrace before (historyWord reference state addresses) after cost :=
  trace_distinct_of_safe run unique (history_safe_balanced reference state addresses).1

end MultiSplay.ClassicalSwitch.Accounting
