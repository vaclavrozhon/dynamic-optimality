import Splay.Accounting.ArticleRelocationUnbroken
import Splay.Accounting.ArticleGapPotential
import Splay.Lazy.IsolatedRankTransport

namespace Splay.Accounting

open Splay.Rank Splay.Tree Splay.Lazy Splay.Lazy.Canonical JunctionBendReduction

/-- A complete canonical rank change, including finite preparation, whole
block relocation and final numerical-rank restoration. -/
structure ArticleCanonicalRankChange {n : ℕ} (params : Interface.Parameters)
    (initial : Lazy.State n) (after : Snapshot n) (tree : BST 0 n) (birthBudget : ℕ) where
  events : List (Event n)
  final : Lazy.State n
  trace : Trace params initial events final
  represents : final.Represents params after tree
  births : final.blocks.length ≤ initial.blocks.length + birthBudget
  noInserts : Interface.totalInserts (eraseOperations events) = 0
  noIncreases : Interface.totalIncreases (eraseOperations events) = 0
  preservesUnbroken : ∀ before, initial.view = canonicalHeapView before tree →
    PassedBlocksUnbroken before tree initial → PassedBlocksUnbroken after tree final

namespace ArticleCanonicalRankChange

def withBudget {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    {after : Snapshot n} {tree : BST 0 n} {budget larger : ℕ}
    (execution : ArticleCanonicalRankChange params initial after tree budget) (bound : budget ≤ larger) :
    ArticleCanonicalRankChange params initial after tree larger where
  events := execution.events
  final := execution.final
  trace := execution.trace
  represents := execution.represents
  births := execution.births.trans (Nat.add_le_add_left bound _)
  noInserts := execution.noInserts
  noIncreases := execution.noIncreases
  preservesUnbroken := execution.preservesUnbroken

/-- All geometric and rank-update premises are discharged from finite
exceptions, actual junction cuts, and unchanged child orders outside the
chosen owner support. No heap promotions or interface inserts are needed. -/
theorem exists_of_support {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    (before after : Snapshot n) (tree : BST 0 n)
    (represented : initial.Represents params before tree)
    (changed owners : Finset (Element n))
    (rootEq : (canonicalHeapView after tree).root = (canonicalHeapView before tree).root)
    (ordinary : ∀ element ∉ changed, after.rank element = before.rank element)
    (changedOwners : changed ⊆ owners)
    (otherOrders : ∀ owner ∉ owners, ∀ side,
      (canonicalHeapView after tree).topDown owner side = (canonicalHeapView before tree).topDown owner side)
    (minimumChanges : before.MinimumChangesFrom after changed)
    (support : affectedOwnerSupport before after changed tree ⊆ owners) :
    Nonempty (ArticleCanonicalRankChange params initial after tree
      (5 * (junctionExceptionsFrom before after tree (Nat.le_refl n) ∪ changed).card +
        2 * owners.card + 4 * owners.card * (relocationCutsFrom before after tree (Nat.le_refl n)).card)) := by
  classical
  let selected := junctionExceptionsFrom before after tree (Nat.le_refl n) ∪ changed
  let cuts := relocationCutsFrom before after tree (Nat.le_refl n)
  obtain ⟨preparation⟩ := ArticleRelocationPreparation.exists_preparation represented.stable selected owners cuts
  let target := canonicalHeapView after tree
  let transient := target.withRank preparation.final.view.rank
  let relocated := preparation.final.relocateBlocks transient
  have geometry : preparation.final.RelocationGeometry transient :=
    preparation.canonical_relocationGeometry represented.view_eq Finset.subset_union_left (Finset.Subset.refl _) rootEq otherOrders
  have prefixes : ∀ block ∈ preparation.final.blocks, block.mode = .growing →
      ∃ suffix, transient.topDown block.owner block.side = block.elements ++ suffix :=
    preparation.canonical_growing_prefixes represented.view_eq otherOrders
  have root : transient.root = preparation.final.view.root := by
    change target.root = preparation.final.view.root
    rw [preparation.view_eq, represented.view_eq]
    exact rootEq
  have relocationTrace : Trace params preparation.final [.silent] relocated :=
    State.relocateBlocks_trace preparation.stable.1 geometry
  have relocationPrepared : relocated.RankPrepared params :=
    State.relocateBlocks_rankPrepared preparation.stable.rankPrepared geometry root prefixes
  have isolated : relocated.IsolatedRanks changed :=
    (preparation.isolatedRanks Finset.subset_union_right changedOwners).relocateBlocks transient
  have same : relocated.view.SameStructure target := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have unchanged : ∀ element ∉ changed, target.rank element = relocated.view.rank element := by
    intro element outside
    change after.rank element = preparation.final.view.rank element
    rw [preparation.view_eq, represented.view_eq]
    exact ordinary element outside
  let final := relocated.absorbRankUpdate target (relocated.isolatedRankBlockShift target)
  obtain ⟨rankTrace, finalStable⟩ := relocationPrepared.absorbRankUpdate_trace_stable
    (isolated.compatible relocationPrepared.valid same unchanged) (canonicalHeapView_heapOrdered after tree)
  refine ⟨{
    events := (preparation.events ++ [.silent]) ++ [.silent]
    final := final
    trace := (preparation.trace.append relocationTrace).append rankTrace
    represents := ⟨finalStable, rfl⟩
    births := ?_
    noInserts := ?_
    noIncreases := ?_
    preservesUnbroken := by
      intro oldSnapshot oldView oldUnbroken
      have ranks : before.rank = oldSnapshot.rank := congrArg HeapView.rank (represented.view_eq.symm.trans oldView)
      have preparedUnbroken := preparation.relocated_unbroken represented.view_eq
        Finset.subset_union_left (Finset.Subset.refl _) minimumChanges support geometry
        (oldUnbroken.of_rank_eq ranks)
      exact preparedUnbroken.absorbRankUpdate target (relocated.isolatedRankBlockShift target)
  }⟩
  · have bound := preparation.births
    have lengthEq : final.blocks.length = preparation.final.blocks.length := by
      simp [final, relocated, State.absorbRankUpdate]
    rw [lengthEq]
    dsimp only [selected, cuts] at bound
    omega
  · simp only [eraseOperations_append, Interface.totalInserts_append,
      show eraseOperations ([.silent] : List (Event n)) = [] from rfl, preparation.noInserts]
    rfl
  · simp only [eraseOperations_append, Interface.totalIncreases_append,
      show eraseOperations ([.silent] : List (Event n)) = [] from rfl, preparation.noIncreases]
    rfl

theorem gap_le {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    {after : Snapshot n} {tree : BST 0 n} {budget : ℕ}
    (execution : ArticleCanonicalRankChange params initial after tree budget) (stable : initial.Stable params) :
    geometricGapPotential execution.final ≤ geometricGapPotential initial :=
  geometricGapPotential_le_of_no_increases stable execution.represents.stable execution.trace execution.noIncreases

end ArticleCanonicalRankChange
end Splay.Accounting
