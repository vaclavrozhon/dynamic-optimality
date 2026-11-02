import DynamicOptimality.Funnel.RunCounts

/-! # Accounting for the prefix before the first own label -/

namespace DynamicOptimality.Funnel

variable {α : Type*} [DecidableEq α]

theorem changesFrom_le_changes_add_one (previous : Option α) (word : List α) :
    changesFrom previous word ≤ changes word + 1 := by
  cases word with
  | nil => simp [changesFrom,changes]
  | cons a word =>
    have step := changeStep_le previous a
    simp only [changes,changesFrom,changeStep,Nat.zero_add]
    simp only [changeStep] at step
    omega

theorem changesFrom_append_le (previous : Option α) (before after : List α) :
    changesFrom previous (before ++ after) ≤ changesFrom previous before + changes after + 1 := by
  induction before generalizing previous with
  | nil => simpa only [List.nil_append,changesFrom,Nat.zero_add] using
      changesFrom_le_changes_add_one previous after
  | cons a before ih =>
    have bound := ih (some a)
    simp only [List.cons_append,changesFrom]
    omega

theorem changes_append_le (before after : List α) :
    changes (before ++ after) ≤ changes before + changes after + 1 :=
  changesFrom_append_le none before after

/-- The own suffix can introduce at most one label beyond its foreign run
representatives. Keeping the prefix term on both sides avoids subtraction. -/
theorem prefix_suffix_run_account (own : α) (before after : List α)
    (foreign : ∀ a ∈ before, a ≠ own)
    (startsOwn : after = [] ∨ ∃ rest, after = own :: rest) :
    (before ++ after).toFinset.card + ownRuns (fun a => decide (a = own)) false after +
        (runHeads before).length ≤
      before.toFinset.card + (runHeads (before ++ after)).length + 1 := by
  rcases startsOwn with rfl | ⟨rest,rfl⟩
  · simp [ownRuns]
  · have cards := Finset.card_union_le before.toFinset (own :: rest).toFinset
    rw [← List.toFinset_append] at cards
    have suffix := distinct_add_ownRuns_le own (own :: rest)
    rw [runHeads_append_foreign before own rest foreign,List.length_append]
    omega

end DynamicOptimality.Funnel
