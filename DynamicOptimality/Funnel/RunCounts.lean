import DynamicOptimality.Funnel.RunCompression
import DynamicOptimality.Funnel.UniformForeign
import Mathlib.Data.Finset.Card

/-! # Run counts and distinct interval labels -/

namespace DynamicOptimality.Funnel

variable {α : Type*} [DecidableEq α]

@[simp] theorem mem_runHeads (a : α) (word : List α) : a ∈ runHeads word ↔ a ∈ word := by
  constructor
  · intro member
    exact (runHeads_sublist word).subset member
  · intro member
    induction word with
    | nil => simp at member
    | cons b word ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact List.mem_of_head? (by simp only [head_runHeads,List.head?_cons])
      · have tail := ih member
        simp only [runHeads,prependRun]
        split_ifs
        · exact tail
        · exact List.mem_cons_of_mem _ tail

theorem runHeads_length_cons (a : α) (rest : List α) :
    (runHeads (a :: rest)).length = changes (a :: rest) + 1 := by
  induction rest generalizing a with
  | nil => simp [runHeads,prependRun,changes,changesFrom,changeStep]
  | cons b rest ih =>
    rw [runHeads_cons]
    by_cases same : b = a
    · subst b
      simp only [List.head?_cons,ite_true,ih,changes,changesFrom,changeStep,ite_true,
        Nat.zero_add]
    · simp only [List.head?_cons,Option.some.injEq,same,↓reduceIte,List.length_cons,ih,
        changes,changesFrom,changeStep,Ne.symm same,↓reduceIte,Nat.zero_add]
      omega

theorem runHeads_length_le (word : List α) : (runHeads word).length ≤ changes word + 1 := by
  cases word with
  | nil => simp [runHeads,changes,changesFrom]
  | cons a rest => exact (runHeads_length_cons a rest).le

theorem runHeads_append_foreign (before : List α) (own : α) (after : List α)
    (foreign : ∀ a ∈ before, a ≠ own) :
    runHeads (before ++ own :: after) = runHeads before ++ runHeads (own :: after) := by
  induction before with
  | nil => rfl
  | cons a before ih =>
    have aForeign := foreign a (by simp)
    have tailForeign : ∀ b ∈ before, b ≠ own := fun b hb => foreign b (List.mem_cons_of_mem _ hb)
    cases before with
    | nil =>
      simp [runHeads_cons,runHeads,prependRun,head_runHeads,Ne.symm aForeign]
    | cons b before =>
      change runHeads (a :: ((b :: before) ++ own :: after)) =
        runHeads (a :: b :: before) ++ runHeads (own :: after)
      rw [runHeads_cons a ((b :: before) ++ own :: after),runHeads_cons a (b :: before)]
      simp only [List.cons_append,List.head?_cons,Option.some.injEq]
      by_cases same : b = a
      · simp only [same,ite_true]
        simpa only [same,List.cons_append] using ih tailForeign
      · simp only [same,ite_false]
        simpa only [List.cons_append] using congrArg (fun rest => a :: rest) (ih tailForeign)

theorem ownRuns_duplicate (keep : α → Bool) (previous : Bool) (a : α) (rest : List α) :
    ownRuns keep previous (a :: a :: rest) = ownRuns keep previous (a :: rest) := by
  simp only [ownRuns]
  cases kept : keep a <;> cases previous <;> simp_all

theorem count_runHeads (own : α) (word : List α) :
    (runHeads word).count own = ownRuns (fun a => decide (a = own)) false word := by
  induction word with
  | nil => rfl
  | cons a word ih =>
    cases word with
    | nil => simp [runHeads,prependRun,ownRuns,List.count_cons]
    | cons b word =>
      rw [runHeads_cons]
      by_cases same : b = a
      · subst b
        simp only [List.head?_cons,ite_true,ih,ownRuns_duplicate]
      · simp only [List.head?_cons,Option.some.injEq,same,↓reduceIte,List.count_cons,ih]
        by_cases aOwn : a = own
        · subst a
          simp [ownRuns,same,Nat.add_comm]
        · by_cases bOwn : b = own
          · subst b
            simp [ownRuns,aOwn]
          · simp [ownRuns,aOwn,bOwn]

theorem ownRuns_map {β : Type*} (label : β → α) (own : α) (previous : Bool) (word : List β) :
    ownRuns (fun a => decide (a = own)) previous (word.map label) =
      ownRuns (fun a => decide (label a = own)) previous word := by
  induction word generalizing previous with
  | nil => rfl
  | cons a word ih => simp only [List.map_cons,ownRuns,ih]

/-- All labels except the own label need a foreign run representative. -/
theorem distinct_add_ownRuns_le (own : α) (word : List α) :
    word.toFinset.card + ownRuns (fun a => decide (a = own)) false word ≤
      (runHeads word).length + 1 := by
  let foreign := (runHeads word).filter (fun a => decide (a ≠ own))
  have subset : word.toFinset ⊆ insert own foreign.toFinset := by
    intro a member
    have occurs : a ∈ runHeads word := (mem_runHeads a word).mpr (List.mem_toFinset.mp member)
    by_cases same : a = own
    · exact Finset.mem_insert.mpr (Or.inl same)
    · exact Finset.mem_insert.mpr (Or.inr (List.mem_toFinset.mpr
        (List.mem_filter.mpr ⟨occurs,decide_eq_true same⟩)))
  have cards := (Finset.card_le_card subset).trans (Finset.card_insert_le own foreign.toFinset)
  have length := List.toFinset_card_le foreign
  have account : foreign.length + (runHeads word).count own = (runHeads word).length := by
    have split := List.length_eq_countP_add_countP (l := runHeads word) (fun a => a == own)
    simpa [foreign,List.count_eq_countP,List.countP_eq_length_filter,beq_iff_eq,
      Bool.not_eq_true,ne_eq,Nat.add_comm] using split.symm
  rw [count_runHeads] at account
  omega

end DynamicOptimality.Funnel
