import ChaCha.Paper20261030.PhysicalSecondaryAccess

/-! Finite sequences of charged, root-returning visits in the existing
decorated source-pointer model. Each request has an actual trace reaching
and reading its named original leaf. Budgets are upper bounds. -/

namespace ChaCha.Paper20261030.SourcePointer

open ColoredStorage

variable {α ρ : Type*}

inductive Services : Source α ρ → List α → Source α ρ → Nat → Prop
  | nil (tree : Source α ρ) (budget : Nat) : Services tree [] tree budget
  | cons {before middle after : Source α ρ} {key : α} {requests : List α} {firstCost lastCost budget : Nat}
      (first : VisitsLeaf key before middle firstCost) (rest : Services middle requests after lastCost)
      (bound : firstCost+lastCost ≤ budget) : Services before (key :: requests) after budget

theorem Services.mono {before after : Source α ρ} {requests : List α} {small large : Nat}
    (execution : Services before requests after small) (bound : small ≤ large) :
    Services before requests after large := by
  cases execution with
  | nil => exact .nil _ _
  | cons first rest cost => exact .cons first rest (cost.trans bound)

theorem Services.rearranges {before after : Source α ρ} {requests : List α} {budget : Nat}
    (execution : Services before requests after budget) : Rearranges before after budget := by
  induction execution with
  | nil => exact rearranges_refl _ _
  | cons first rest bound ih => exact (first.rearranges.trans ih).mono bound

end ChaCha.Paper20261030.SourcePointer
