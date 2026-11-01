import Splay.Accounting.ArticleBoundaryPhases

namespace Splay.Accounting

open Splay.Lazy Splay.Rank Splay.Tree.BST

/-- The two boundary phases together pay every selected loser whose
original shrinking residence contains at most twelve elements. -/
theorem ArticleBoundaryPhasesExecution.smallCredit
    {n key cutoff : ℕ} {snapshot : Snapshot n} {before : BST 0 n} {groups : List ℕ}
    {params : Interface.Parameters} {initial : Lazy.State n}
    {batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups}
    (execution : ArticleBoundaryPhasesExecution params initial batches)
    (marked : Interface.Element n → Bool)
    (small : ∀ pairing ∈ execution.firstAllocation.matching ++ execution.secondAllocation.matching,
      marked pairing.loser = true → ∃ (id : Interface.BlockId) (source : Lazy.Block n),
        initial.blocks[id]? = some source ∧ source.mode = .shrinking ∧
          pairing.loser ∈ source.elements ∧ source.elements.length ≤ 12) :
    Interface.boundaryCredit cutoff execution.final.toInterface +
      ((execution.firstAllocation.matching ++ execution.secondAllocation.matching).filter
        fun pairing => marked pairing.loser).length ≤
          Interface.boundaryCredit cutoff initial.toInterface := by
  have firstPaid := execution.first.smallCredit cutoff marked
    (fun pairing member => small pairing (List.mem_append_left _ member))
  have secondPaid := execution.second.smallCredit cutoff marked (by
    intro pairing member selected
    obtain ⟨oldId, old, oldFound, _, oldMember, oldSmall⟩ :=
      small pairing (List.mem_append_right _ member) selected
    obtain ⟨nextId, next, nextFound, shrinking, nextMember⟩ := execution.second.sources pairing member
    have sublist := execution.first.shrinkingRefines.elements_sublist_of_common_element
      execution.first.trace.initial_valid oldFound oldMember nextFound shrinking nextMember
    exact ⟨nextId, next, nextFound, shrinking, nextMember, sublist.length_le.trans oldSmall⟩)
  simp only [List.filter_append, List.length_append, final]
  omega

end Splay.Accounting
