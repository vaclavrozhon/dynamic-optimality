import MultiSplay.ClassicalSwitchHistory
import MultiSplay.ForestSplayRun

/-!
# The live-key inventory during the exact classical word

A split temporarily removes its pivot from the analytical forest; its matching
raw join reinserts it. Therefore uniqueness at intermediate checkpoints does
not follow from an unchanged key multiset. The inventory below records these
removals and insertions, and proves that a word whose every prefix has a
nonpositive balance cannot introduce a duplicate key.
-/

namespace MultiSplay.ClassicalSwitch.Accounting

open DynamicOptimality (RawTree)
open TangoSquared.MTR.Tree (inorder)
open CommonForest

variable {α : Type*} [DecidableEq α]

def eventChange : Event α → α → Int
  | .search _ _, _ => 0
  | .split _ pivot _, key => if key = pivot then -1 else 0
  | .join _ pivot _, key => if key = pivot then 1 else 0

def change (word : List (Event α)) (key : α) : Int :=
  (word.map (fun event => eventChange event key)).sum

def SafeAt (key : α) (level : Int) : List (Event α) → Prop
  | [] => level ≤ 0
  | event::rest => level ≤ 0 ∧ SafeAt key (level + eventChange event key) rest

def Safe (word : List (Event α)) : Prop := ∀ key, SafeAt key 0 word

def Balanced (word : List (Event α)) : Prop := ∀ key, change word key = 0

theorem change_append (first rest : List (Event α)) (key : α) :
    change (first ++ rest) key = change first key + change rest key := by
  simp [change, List.sum_append]

theorem SafeAt.initial {key : α} {level : Int} {word : List (Event α)}
    (safe : SafeAt key level word) : level ≤ 0 := by
  cases word with
  | nil => exact safe
  | cons => exact safe.1

theorem SafeAt.mono {key : α} {lower upper : Int} {word : List (Event α)}
    (safe : SafeAt key upper word) (le : lower ≤ upper) : SafeAt key lower word := by
  induction word generalizing lower upper with
  | nil => exact le.trans safe
  | cons event rest ih => exact ⟨le.trans safe.1, ih safe.2 (by omega)⟩

theorem SafeAt.append {key : α} {level : Int} {first rest : List (Event α)}
    (head : SafeAt key level first) (tail : SafeAt key (level + change first key) rest) :
    SafeAt key level (first ++ rest) := by
  induction first generalizing level with
  | nil => simpa [change] using tail
  | cons event first ih =>
      exact ⟨head.1,ih head.2 (by simpa [change, Int.add_assoc] using tail)⟩

theorem SafeAt.suffix {key : α} {level : Int} {first rest : List (Event α)}
    (safe : SafeAt key level (first ++ rest)) : SafeAt key (level + change first key) rest := by
  induction first generalizing level with
  | nil => simpa [change] using safe
  | cons event first ih => simpa [change, Int.add_assoc] using ih safe.2

theorem Safe.append {first rest : List (Event α)}
    (head : Safe first) (balanced : Balanced first) (tail : Safe rest) : Safe (first ++ rest) := by
  intro key
  exact (head key).append (by simpa [balanced key] using tail key)

theorem Balanced.append {first rest : List (Event α)}
    (head : Balanced first) (tail : Balanced rest) : Balanced (first ++ rest) := by
  intro key
  rw [change_append, head key, tail key, Int.add_zero]

def liveCount (forest : List (RawTree α)) (key : α) : Int :=
  (forest.flatMap inorder).count key

theorem liveCount_append (first rest : List (RawTree α)) (key : α) :
    liveCount (first ++ rest) key = liveCount first key + liveCount rest key := by
  simp [liveCount, List.flatMap_append, List.count_append]

theorem unique_iff (forest : List (RawTree α)) :
    UniqueKeys forest ↔ ∀ key, liveCount forest key ≤ 1 := by
  constructor
  · intro unique key
    have bound := List.nodup_iff_count_le_one.mp unique key
    unfold liveCount
    exact_mod_cast bound
  · intro bounded
    apply List.nodup_iff_count_le_one.mpr
    intro key
    have bound := bounded key
    unfold liveCount at bound
    exact_mod_cast bound

theorem step_inventory {before after : List (RawTree α)} {word : List (Event α)} {cost : Nat}
    (step : Step Auxiliary.Splay idle before word after cost) (key : α) :
    liveCount after key = liveCount before key + change word key := by
  induction step with
  | search execution => simp [liveCount, change, eventChange, execution.inorder_eq]
  | @split pivot a left right work execution =>
      by_cases same : key = pivot <;>
        simp [liveCount, change, eventChange, execution.inorder_eq, inorder, List.count_append, same, eq_comm] <;> omega
  | join left right pivot =>
      by_cases same : key = pivot <;>
        simp [liveCount, change, eventChange, inorder, List.count_append, same, eq_comm] <;> omega
  | prepare execution => obtain ⟨rfl,rfl⟩ := execution; simp [change]
  | context step front back ih => simp only [liveCount_append]; omega
  | reorder order =>
      have counts := (order.flatMap_right inorder).count_eq key
      simp only [change, List.map_nil, List.sum_nil, Int.add_zero]
      unfold liveCount
      exact_mod_cast counts.symm

/-- Bounded prefix inventories prove distinctness at every checkpoint of the
supplied actual trace, including intermediate splits, joins, and permutations. -/
theorem trace_distinct {before after : List (RawTree α)} {word : List (Event α)} {cost : Nat}
    (run : SplayTrace before word after cost)
    (bounded : ∀ key, SafeAt key (liveCount before key - 1) word) :
    DistinctSplayTrace before word after cost := by
  have unique : UniqueKeys before := (unique_iff before).mpr (fun key => by
    have initial := (bounded key).initial
    omega)
  induction run with
  | nil => exact .nil _ unique
  | @cons before middle after first rest head tail step remaining ih =>
      have next : ∀ key, SafeAt key (liveCount middle key - 1) rest := by
        intro key
        have safe := (bounded key).suffix
        have inventory := step_inventory step key
        convert safe using 1 <;> omega
      exact .cons unique step (ih next ((unique_iff middle).mpr (fun key => by
        have initial := (next key).initial
        omega)))

theorem trace_distinct_of_safe {before after : List (RawTree α)} {word : List (Event α)} {cost : Nat}
    (run : SplayTrace before word after cost) (unique : UniqueKeys before) (safe : Safe word) :
    DistinctSplayTrace before word after cost := by
  apply trace_distinct run
  intro key
  exact (safe key).mono (by have bound := (unique_iff before).mp unique key; omega)

end MultiSplay.ClassicalSwitch.Accounting
