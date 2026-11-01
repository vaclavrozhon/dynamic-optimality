import Splay.Accounting.ArticleTemporaryCanonicalEndpoint
import Splay.Lazy.IsolatedRankTransport

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

/-- Pairings retain shrinking singletons for both boundary vertices and
leave all four of their own growing intervals empty. -/
theorem ArticlePairingStage.boundaries_isolated {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {before : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
    (stage : ArticlePairingStage params snapshot before key kinds initial) :
    let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
    stage.final.IsolatedRanks {selection.left, selection.right} := by
  classical
  dsimp only
  let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
  apply State.IsolatedRanks.of_singleton_blocks stage.stable.1
  · intro block member growing ownerMarked
    have ownerEq : block.owner = selection.left ∨ block.owner = selection.right := by simpa using ownerMarked
    have empty : ArticleGrowingOwnerEmpty stage.final block.owner := by
      rcases ownerEq with left | right
      · rw [left]
        exact stage.boundaryEmpty .left
      · rw [right]
        exact stage.boundaryEmpty .right
    obtain ⟨id, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨lt, equal⟩ := List.getElem?_eq_some_iff.mp found
    let index : Fin stage.final.blocks.length := ⟨id, lt⟩
    have atSide : ArticleGrowingEmptyAt stage.final block.owner block.side := by
      cases block.side with
      | left => exact empty.1
      | right => exact empty.2
    have result := atSide index
    dsimp only at result
    rw [show stage.final.blocks.get index = block from equal] at result
    exact result growing rfl rfl
  · intro element marked
    have atBoundary : element = selection.left ∨ element = selection.right := by simpa using marked
    rcases atBoundary with left | right
    · subst element
      exact stage.boundary_singleton .left
    · subst element
      exact stage.boundary_singleton .right

namespace ArticleTemporaryTransferStage

variable {n : ℕ} {params : Interface.Parameters} {comparison : BST 0 n}
  {before : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
  (stage : ArticleTemporaryTransferStage params (Snapshot.ofTree comparison) before key kinds initial)

/-- Both boundary ranks remain isolated at the actual canonical splay
endpoint, after all pairing operations and both whole-block transfers. -/
theorem canonical_boundaries_isolated (after : BST 0 n) :
    let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection stage.setup.temporarySnapshot before key
    (stage.canonicalFinal after).IsolatedRanks {selection.left, selection.right} :=
  (stage.pairing.boundaries_isolated.transferBothSides stage.leftGeometry stage.rightGeometry stage.pairing.stable.2.2.1).replaceView _

/-- Install the fixed true doubled rank function on the existing temporary
heap structure. Junctions will subsequently restore its numerical heap order. -/
noncomputable def restoredRankView (after : BST 0 n) : HeapView n :=
  { (stage.canonicalFinal after).view with rank := (Snapshot.ofTree comparison).withTruePriority.rank }

noncomputable def restoredRanks (after : BST 0 n) : Lazy.State n :=
  (stage.canonicalFinal after).absorbRankUpdate (stage.restoredRankView after)
    ((stage.canonicalFinal after).isolatedRankBlockShift (stage.restoredRankView after))

/-- The true rank restoration is one actual silent event and preserves all
rank-prepared invariants. This deliberately does not claim heap order before
the remaining heavy-path junctions have been performed. -/
theorem restoredRanks_trace_rankPrepared (comparisonRoot : comparison.HasRoot key.val)
    {after : BST 0 n} {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag) :
    Trace params (stage.canonicalFinal after) [.silent] (stage.restoredRanks after) ∧
      (stage.restoredRanks after).RankPrepared params := by
  let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection stage.setup.temporarySnapshot before key
  have same : (stage.canonicalFinal after).view.SameStructure (stage.restoredRankView after) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  apply (stage.canonical_boundaries_isolated after).trace_rankPrepared
    (stage.canonical_represents comparisonRoot transcript).stable.rankPrepared (stage.restoredRankView after) same
  intro element outside
  have notBoundaries : element ≠ selection.left ∧ element ≠ selection.right := by simpa using outside
  change (Snapshot.ofTree comparison).withTruePriority.rank element = stage.setup.temporarySnapshot.rank element
  rw [stage.setup.temporarySnapshot_eq_comparison comparison key comparisonRoot]
  exact (twoBoundaryTemporaryRank_eq_truePriority (Snapshot.ofTree comparison) selection.left selection.right element notBoundaries).symm

/-- Restore both true ranks after the complete canonical prefix in the same
actual event sequence. -/
theorem restoredRanks_trace (comparisonRoot : comparison.HasRoot key.val)
    {after : BST 0 n} {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag) :
    Trace params initial ((stage.events ++ [.silent]) ++ [.silent]) (stage.restoredRanks after) :=
  (stage.canonical_trace comparisonRoot transcript).append (stage.restoredRanks_trace_rankPrepared comparisonRoot transcript).1

/-- The restored rank function is exactly the fixed doubled comparison rank. -/
@[simp]
theorem restoredRanks_rank (after : BST 0 n) :
    (stage.restoredRanks after).view.rank = (Snapshot.ofTree comparison).withTruePriority.rank := rfl

/-- Rank absorption never changes an interface value. -/
@[simp]
theorem restoredRanks_value (after : BST 0 n) :
    (stage.restoredRanks after).value = (stage.canonicalFinal after).value := rfl

/-- The true rank update preserves the geometric gap potential even though
its intermediate heap still awaits structural junctions. -/
theorem restoredRanks_gap_eq (comparisonRoot : comparison.HasRoot key.val)
    {after : BST 0 n} {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag) :
    geometricGapPotential (stage.restoredRanks after) = geometricGapPotential (stage.canonicalFinal after) := by
  have prepared := (stage.restoredRanks_trace_rankPrepared comparisonRoot transcript).2
  have stable := (stage.canonical_represents comparisonRoot transcript).stable
  rw [geometricGapPotential_eq prepared.complete prepared.valuesRealizeGaps,
    geometricGapPotential_eq stable.2.1 stable.2.2.2.2.2]
  rfl

end ArticleTemporaryTransferStage

end Splay.Accounting
