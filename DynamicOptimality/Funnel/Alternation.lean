import Mathlib.Data.List.Basic
import Mathlib.Tactic.SplitIfs

/-! # Side changes and deletion of path entries

Deleting one entry removes at most two adjacent changes. Conversely, deleting
entries cannot create more changes than were present before. The statements
are for arbitrary labels and therefore also apply to the two search sides.
-/

namespace DynamicOptimality.Funnel

variable {α : Type*} [DecidableEq α]

def changeStep : Option α → α → Nat
  | none, _ => 0
  | some a, b => if a = b then 0 else 1

def changesFrom (previous : Option α) : List α → Nat
  | [] => 0
  | a :: rest => changeStep previous a + changesFrom (some a) rest

def changes (word : List α) : Nat := changesFrom none word

theorem changeStep_le (previous : Option α) (a : α) : changeStep previous a ≤ 1 := by
  cases previous with
  | none => simp [changeStep]
  | some p => simp only [changeStep]; split_ifs <;> omega

theorem changeStep_triangle (previous : Option α) (a b : α) :
    changeStep previous b ≤ changeStep previous a + changeStep (some a) b := by
  cases previous with
  | none => simp [changeStep]
  | some p =>
    by_cases pa : p = a
    · subst p
      simp [changeStep]
    · by_cases ab : a = b
      · subst b
        simp [changeStep]
      · have bound := changeStep_le (some p) b
        simp only [changeStep,pa,ab,↓reduceIte] at bound ⊢
        omega

theorem changesFrom_triangle (previous : Option α) (a : α) (word : List α) :
    changesFrom previous word ≤ changeStep previous a + changesFrom (some a) word := by
  cases word with
  | nil => simp [changesFrom]
  | cons b word =>
    simp only [changesFrom]
    have triangle := changeStep_triangle previous a b
    omega

theorem changesFrom_insert_le (previous : Option α) (a : α) (word : List α) :
    changesFrom previous (a :: word) ≤ changesFrom previous word + 2 := by
  cases word with
  | nil =>
    have bound := changeStep_le previous a
    simp only [changesFrom,Nat.add_zero]
    omega
  | cons b word =>
    simp only [changesFrom]
    have first := changeStep_le previous a
    have second := changeStep_le (some a) b
    omega

theorem changesFrom_sublist {small large : List α} (sublist : small.Sublist large)
    (previous : Option α) : changesFrom previous small ≤ changesFrom previous large := by
  induction sublist generalizing previous with
  | slnil => simp [changesFrom]
  | @cons small large a sublist ih =>
    have triangle := changesFrom_triangle previous a small
    have bound := ih (some a)
    simp only [changesFrom]
    omega
  | cons_cons a sublist ih =>
    simp only [changesFrom]
    exact Nat.add_le_add_left (ih (some a)) _

/-- An entry can be responsible for at most two changes. The additive form
avoids truncated subtraction and includes empty lists. -/
theorem changesFrom_deletion_bound {small large : List α} (sublist : small.Sublist large)
    (previous : Option α) :
    changesFrom previous large + 2 * small.length ≤ changesFrom previous small + 2 * large.length := by
  induction sublist generalizing previous with
  | slnil => simp [changesFrom]
  | @cons small large a sublist ih =>
    have inserted := changesFrom_insert_le previous a large
    have bound := ih previous
    simp only [List.length_cons]
    omega
  | cons_cons a sublist ih =>
    have bound := ih (some a)
    simp only [changesFrom,List.length_cons]
    omega

theorem changes_sublist {small large : List α} (sublist : small.Sublist large) :
    changes small ≤ changes large := changesFrom_sublist sublist none

theorem changes_deletion_bound {small large : List α} (sublist : small.Sublist large) :
    changes large + 2 * small.length ≤ changes small + 2 * large.length :=
  changesFrom_deletion_bound sublist none

end DynamicOptimality.Funnel
