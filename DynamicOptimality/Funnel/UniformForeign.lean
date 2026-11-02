import DynamicOptimality.Funnel.Alternation

/-! # Removing outside keys of one search side

When all foreign entries of a path lie on the same side of the query, only
entry into or exit from a block of own entries can create extra side changes.
Each such block pays at most two changes, independent of its length.
-/

namespace DynamicOptimality.Funnel

variable {α β : Type*} [DecidableEq β]

def ownRuns (keep : α → Bool) (previousOwn : Bool) : List α → Nat
  | [] => 0
  | a :: rest => (if keep a = true ∧ previousOwn = false then 1 else 0) +
      ownRuns keep (keep a) rest

/-- A scan invariant keeps the last own side separately from the last physical
side. Leaving an own block needs at most one pending unit of credit. -/
theorem uniform_foreign_scan (keep : α → Bool) (label : α → β) (foreign : β)
    (word : List α) (uniform : ∀ a ∈ word, keep a = false → label a = foreign)
    (previousOwn : Bool) (ownPrevious : Option β) :
    changesFrom (if previousOwn then ownPrevious else some foreign) (word.map label) ≤
      changesFrom ownPrevious ((word.filter keep).map label) +
        2 * ownRuns keep previousOwn word + (if previousOwn then 1 else 0) := by
  induction word generalizing previousOwn ownPrevious with
  | nil => simp [changesFrom,ownRuns]
  | cons a word ih =>
    have tailUniform : ∀ b ∈ word, keep b = false → label b = foreign :=
      fun b hb => uniform b (List.mem_cons_of_mem _ hb)
    cases kept : keep a with
    | true =>
      have recurse := ih tailUniform true (some (label a))
      cases previousOwn <;>
        simp only [List.map_cons,List.filter_cons,kept,↓reduceIte,changesFrom,ownRuns,
          Bool.false_eq_true,Bool.true_eq_false,and_self,and_false,and_true,↓reduceIte] at recurse ⊢
      · have step := changeStep_le (some foreign) (label a)
        omega
      · omega
    | false =>
      have same := uniform a (by simp) kept
      have recurse := ih tailUniform false ownPrevious
      cases previousOwn <;>
        simp only [List.map_cons,List.filter_cons,kept,Bool.false_eq_true,↓reduceIte,
          changesFrom,ownRuns,false_and,↓reduceIte,same,changeStep,ite_true] at recurse ⊢
      · omega
      · have step := changeStep_le ownPrevious foreign
        simp only [changeStep] at step
        omega

theorem uniform_foreign_changes (keep : α → Bool) (label : α → β) (foreign : β)
    (word : List α) (uniform : ∀ a ∈ word, keep a = false → label a = foreign) :
    changes (word.map label) ≤ changes ((word.filter keep).map label) +
      2 * ownRuns keep false word := by
  have scan := uniform_foreign_scan keep label foreign word uniform false none
  have start := changesFrom_triangle (α := β) none foreign (word.map label)
  simp only [Bool.false_eq_true,↓reduceIte,changesFrom,changeStep,Nat.zero_add,Nat.add_zero,
    changes] at scan start ⊢
  omega

end DynamicOptimality.Funnel
