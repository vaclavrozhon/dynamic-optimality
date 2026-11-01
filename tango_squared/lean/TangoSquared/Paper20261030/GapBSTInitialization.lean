import TangoSquared.Paper20261030.GapBSTAccess
import DynamicOptimality.PointerInitialization

/-! Initializing the gap encoding from any equal-key ordinary BST and
then compiling a complete source service sequence. An empty request word
needs no initialization and leaves the given initial tree unchanged. -/

namespace TangoSquared.Paper20261030.GapBST

open ColoredStorage

variable {α ρ : Type*}

theorem services_from_tree (before : MTR.Tree α) {source target : Source α ρ}
    (word : before.inorder = source.shape.leaves) {requests : List α} {budget : Nat}
    (execution : SourcePointer.Services source requests target budget) :
    ∃ (after : MTR.Tree α) (cost : Nat), after.inorder = before.inorder ∧
      MTR.Pointer.Execution before requests after cost ∧ cost ≤ budget+3*requests.length+18*before.size := by
  by_cases empty : requests = []
  · subst requests
    exact ⟨before,0,rfl,.nil _,Nat.zero_le _⟩
  · obtain ⟨cost,run,bound⟩ := services execution
    have initialWord : before.inorder = (encode source).inorder := word.trans (encode_word source).symm
    obtain ⟨initialCost,initialTrace,initialBound⟩ := DynamicOptimality.initialize_pointer _ _ initialWord []
    have full := DynamicOptimality.prepend_pointer_initialization initialTrace run empty
    have finalWord : (encode target).inorder = before.inorder :=
      (encode_word target).trans (execution.rearranges.leaves.symm.trans word.symm)
    exact ⟨encode target,initialCost+cost,finalWord,full,by omega⟩

end TangoSquared.Paper20261030.GapBST
