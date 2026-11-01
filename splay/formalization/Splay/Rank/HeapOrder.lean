import Splay.Rank.Basic

namespace Splay.Rank

/--
A bottom-to-top heap-view chain: every next heavy path has strictly smaller
rank than the preceding one.
-/
def IsHeapAncestorChain {α : Type*} (rank : α → ℕ) (chain : List α) : Prop :=
  chain.IsChain fun child parent => rank parent < rank child

/--
A heavy path of rank `R` has at most `R + 1` heap ancestors, counting itself.

This is the numerical argument from `setup.tex`, isolated from the later
concrete heap-view representation.
-/
theorem heapAncestorChain_length_le_rank_succ
    {α : Type*} (rank : α → ℕ) (path : α) (ancestors : List α)
    (hChain : IsHeapAncestorChain rank (path :: ancestors)) :
    (path :: ancestors).length ≤ rank path + 1 := by
  induction ancestors generalizing path with
  | nil =>
      simp
  | cons parent ancestors ih =>
      have hStep :
          rank parent < rank path ∧
            IsHeapAncestorChain rank (parent :: ancestors) := by
        simpa [IsHeapAncestorChain] using hChain
      have hTail := ih parent hStep.2
      simp only [List.length_cons] at hTail ⊢
      omega

end Splay.Rank
