import Splay.Accounting.ArticleGlobalPairingFold

namespace Splay.Accounting.ArticleSourceMacroChain

open Splay.Lazy ArticleBatchDestinationAllocation

/-- Every pairing in the chain, with its actual destination identifier. -/
def matching {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (chain : ArticleSourceMacroChain params state) : List (Interface.Pairing n) :=
  chain.batches.flatMap fun batch => batch.firstMatching ++ batch.secondMatching

/-- The final heap is the simultaneous reparenting of all actual losers.
This is an endpoint statement about the same trace used in the cost proof. -/
theorem view_reparented {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (chain : ArticleSourceMacroChain params state)
    (disjoint : chain.batches.Pairwise
      (Function.onFun List.Disjoint ArticleSourceLoserBatch.sourceElements)) :
    ∃ after : BatchReparentedView state.view chain.matching,
      after.view = chain.final.view := by
  induction chain with
  | nil state stable =>
      exact ⟨BatchReparentedView.nil state.view stable.2.2.1, rfl⟩
  | cons head tail ih =>
      have parts := List.pairwise_cons.mp disjoint
      obtain ⟨first, firstView⟩ := head.view_reparented
      obtain ⟨second, secondView⟩ := ih parts.2
      have distinct : ∀ a ∈ head.batch.firstMatching ++ head.batch.secondMatching,
          ∀ b ∈ tail.matching, a.loser ≠ b.loser := by
        intro a aMember b bMember equal
        obtain ⟨batch, batchMember, pairingMember⟩ := List.mem_flatMap.mp bMember
        have separated := parts.1 batch batchMember
        have aInside := head.batch.loser_mem_source a.loser
          (List.mem_map.mpr ⟨a, aMember, rfl⟩)
        have bInside := batch.loser_mem_source b.loser
          (List.mem_map.mpr ⟨b, pairingMember, rfl⟩)
        exact List.disjoint_left.mp separated aInside (equal ▸ bInside)
      let last := first.append (second.transportSource firstView) distinct
      exact ⟨last, secondView⟩

end Splay.Accounting.ArticleSourceMacroChain
