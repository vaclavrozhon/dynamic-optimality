import Splay.Accounting.ArticleTemporaryPreparation
import Splay.Accounting.ArticleRelocationUnbroken
import Splay.Lazy.CanonicalInitializationTrace

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

/-- The actual canonical initialization has not passed any block yet. -/
theorem canonicalState_passedBlocksUnbroken {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) :
    PassedBlocksUnbroken snapshot tree (canonicalState snapshot tree) := by
  intro block member positive
  obtain ⟨placement, _, rfl⟩ := List.mem_map.mp member
  exact positive rfl |>.elim

theorem ArticleRequestPreparation.preservesUnbroken {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n} {before : BST 0 n} {key : Fin n} {initial : Lazy.State n}
    (preparation : ArticleRequestPreparation params snapshot before key initial)
    (unbroken : PassedBlocksUnbroken snapshot before initial) :
    PassedBlocksUnbroken snapshot before preparation.final :=
  unbroken.refine preparation.passRefines

/-- Lowering the two isolated boundary priorities respects every old heap
edge. Thus the actual temporary-rank preparation preserves full cross-side
unbrokenness, including its attachment-order information. -/
theorem ArticleTemporaryPreparation.preservesUnbroken {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n} {before : BST 0 n} {key : Fin n} {initial : Lazy.State n}
    (setup : ArticleTemporaryPreparation params snapshot before key initial)
    (unbroken : PassedBlocksUnbroken snapshot.withTruePriority before initial) :
    PassedBlocksUnbroken setup.temporarySnapshot before setup.final := by
  have prepared := setup.preparation.preservesUnbroken unbroken
  have edgeOrder : ∀ edge ∈ fullEdges snapshot.withTruePriority before,
      setup.temporarySnapshot.rank edge.owner < setup.temporarySnapshot.rank edge.child := by
    intro edge member
    rw [← setup.lowered_rank]
    apply setup.lowered_trace_stable.2.2.2.1
    change setup.preparation.final.view.parent edge.child = some edge.owner
    rw [setup.preparation.represents.view_eq]
    exact canonicalParent_eq_some_of_mem_fullEdges snapshot.withTruePriority before edge member
  have temporary := (prepared.of_edge_order edgeOrder).absorbRankUpdate setup.loweredView
    (setup.preparation.final.isolatedRankBlockShift setup.loweredView)
  exact temporary.refine (State.PassRefinement.of_blocks_eq rfl)

end Splay.Accounting
