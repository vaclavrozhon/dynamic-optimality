import DynamicOptimality.Funnel.Alternation
import Mathlib.Data.Finset.Card

/-! # Monotone paths have one run per distinct label -/

namespace DynamicOptimality.Funnel

variable {α : Type*} [LinearOrder α]

theorem changes_cons_cons (a b : α) (rest : List α) :
    changes (a :: b :: rest) = (if a = b then 0 else 1) + changes (b :: rest) := by
  simp [changes,changesFrom,changeStep]

theorem changes_add_one_eq_card (a : α) (rest : List α)
    (sorted : (a :: rest).Pairwise (· ≤ ·)) :
    changes (a :: rest) + 1 = (a :: rest).toFinset.card := by
  induction rest generalizing a with
  | nil => simp [changes,changesFrom,changeStep]
  | cons b rest ih =>
    obtain ⟨aBefore,tailSorted⟩ := List.pairwise_cons.mp sorted
    have tailAccount := ih b tailSorted
    by_cases same : a = b
    · subst a
      simpa only [changes_cons_cons,ite_true,Nat.zero_add,List.toFinset_cons,Finset.insert_idem] using tailAccount
    · have ab : a < b := lt_of_le_of_ne (aBefore b (by simp)) same
      have absent : a ∉ (b :: rest).toFinset := by
        intro member
        have occurs := List.mem_toFinset.mp member
        rcases List.mem_cons.mp occurs with equal | occurs
        · exact same equal
        · have ba : b ≤ a := (List.pairwise_cons.mp tailSorted).1 a occurs
          exact (not_le_of_gt ab) ba
      rw [changes_cons_cons,if_neg same,List.toFinset_cons,Finset.card_insert_of_notMem absent]
      omega

theorem changes_anchored_le_card (parent : α) (word : List α)
    (sorted : word.Pairwise (· ≤ ·)) :
    changesFrom (some parent) word ≤ word.toFinset.card := by
  cases word with
  | nil => simp [changesFrom]
  | cons a word =>
    have account := changes_add_one_eq_card a word sorted
    have step := changeStep_le (some parent) a
    simp only [changes,changesFrom,changeStep,Nat.zero_add] at account
    simp only [changesFrom]
    omega

theorem changes_anchored_le_card_decreasing (parent : α) (word : List α)
    (sorted : word.Pairwise (· ≥ ·)) :
    changesFrom (some parent) word ≤ word.toFinset.card :=
  changes_anchored_le_card (α := OrderDual α) parent word sorted

end DynamicOptimality.Funnel
