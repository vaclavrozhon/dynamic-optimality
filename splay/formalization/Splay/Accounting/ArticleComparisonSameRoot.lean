import Splay.Accounting.ComparisonRotationSupport
import Splay.Accounting.ComparisonCellRankUpdate
import Splay.Accounting.ArticleCanonicalRankChange

namespace Splay.Accounting

open Splay.Rank Splay.Tree Splay.Lazy Splay.Lazy.Canonical JunctionBendReduction

def articleComparisonOwnerBudget (depth : ℕ) : ℕ := 5 + (depth + 2) * (2 * (depth + 1) + 1)

def articleComparisonBirthBudget (depth : ℕ) : ℕ :=
  30 + 2 * articleComparisonOwnerBudget depth + 4 * articleComparisonOwnerBudget depth * (depth + 12)

/-- A comparison rotation retaining the root is implemented using a bounded
number of real interval preparations, one block relocation and one numeric
rank update. The construction works for arbitrary represented lazy blocks. -/
theorem exists_articleComparisonSameRoot {n depth : ℕ} {params : Interface.Parameters}
    {before after splay : BST 0 n} (rotation : BST.RotationAt depth before after)
    {initial : Lazy.State n} (represented : initial.Represents params (Snapshot.ofTree before).withTruePriority splay)
    (rootEq : (canonicalHeapView (Snapshot.ofTree after).withTruePriority splay).root =
      (canonicalHeapView (Snapshot.ofTree before).withTruePriority splay).root) :
    Nonempty (ArticleCanonicalRankChange params initial (Snapshot.ofTree after).withTruePriority splay
      (articleComparisonBirthBudget depth)) := by
  classical
  obtain ⟨profile⟩ := rotation.exists_cutProfile
  obtain ⟨changed, changedCard, changes⟩ := ComparisonRotationJunctionBound.RotationAt.exists_doubledMinimumChangeSupport rotation
  let oldSnapshot := (Snapshot.ofTree before).withTruePriority
  let newSnapshot := (Snapshot.ofTree after).withTruePriority
  let selected := junctionExceptionsFrom oldSnapshot newSnapshot splay (Nat.le_refl n)
  let structuralOwners := affectedOwnerSupport oldSnapshot newSnapshot changed splay
  let borderOwners := borderCutOwners oldSnapshot profile.cutSet profile.border
  let owners := structuralOwners ∪ borderOwners
  let cuts := relocationCutsFrom oldSnapshot newSnapshot splay (Nat.le_refl n) ∪ profile.cutSet
  obtain ⟨preparation⟩ := ArticleRelocationPreparation.exists_preparation represented.stable selected owners cuts
  have otherOrders : ∀ owner ∉ owners, ∀ side,
      (canonicalHeapView newSnapshot splay).topDown owner side = (canonicalHeapView oldSnapshot splay).topDown owner side := by
    intro owner outside side
    exact topDown_eq_of_not_mem_affectedOwnerSupport changes splay
      (fun inside => outside (Finset.mem_union_left _ inside)) side
  let target := canonicalHeapView newSnapshot splay
  let transient := target.withRank preparation.final.view.rank
  let relocated := preparation.final.relocateBlocks transient
  have geometry : preparation.final.RelocationGeometry transient :=
    preparation.canonical_relocationGeometry represented.view_eq (Finset.Subset.refl _) Finset.subset_union_left rootEq otherOrders
  have prefixes : ∀ block ∈ preparation.final.blocks, block.mode = .growing →
      ∃ suffix, transient.topDown block.owner block.side = block.elements ++ suffix :=
    preparation.canonical_growing_prefixes represented.view_eq otherOrders
  have root : transient.root = preparation.final.view.root := by
    change target.root = preparation.final.view.root
    rw [preparation.view_eq, represented.view_eq]
    exact rootEq
  have relocationTrace : Trace params preparation.final [.silent] relocated :=
    State.relocateBlocks_trace preparation.stable.1 geometry
  have ready : relocated.RankPrepared params :=
    State.relocateBlocks_rankPrepared preparation.stable.rankPrepared geometry root prefixes
  have compatible : relocated.RankUpdateCompatible target (relocated.isolatedRankBlockShift target) :=
    comparison_relocated_rankCompatible profile preparation represented.view_eq Finset.subset_union_right Finset.subset_union_right ready.valid
  obtain ⟨rankTrace, finalStable⟩ := ready.absorbRankUpdate_trace_stable compatible (canonicalHeapView_heapOrdered newSnapshot splay)
  let final := relocated.absorbRankUpdate target (relocated.isolatedRankBlockShift target)
  have junctions := ComparisonRotationJunctionBound.RotationAt.doubled_junctionCount_le_one rotation (splay := splay)
  change junctionCount oldSnapshot newSnapshot splay ≤ 1 at junctions
  have selectedBound : selected.card ≤ 6 := by
    have bound := junctionExceptionsFrom_card_le oldSnapshot newSnapshot splay (Nat.le_refl n)
    change selected.card ≤ 6 * junctionCount oldSnapshot newSnapshot splay at bound
    omega
  have ownersBound : owners.card ≤ articleComparisonOwnerBudget depth := by
    have structural := ComparisonRotationJunctionBound.RotationAt.doubled_affectedOwners_card_le rotation (splay := splay) changedCard
    have border := profile.before_borderOwners_card_le
    have unionBound := Finset.card_union_le structuralOwners borderOwners
    change structuralOwners.card ≤ 5 at structural
    change borderOwners.card ≤ (depth + 2) * (2 * (depth + 1) + 1) at border
    dsimp only [owners, articleComparisonOwnerBudget]
    omega
  have cutsBound : cuts.card ≤ depth + 12 := by
    have structural := relocationCutsFrom_card_le oldSnapshot newSnapshot splay (Nat.le_refl n)
    change (relocationCutsFrom oldSnapshot newSnapshot splay (Nat.le_refl n)).card ≤
      10 * junctionCount oldSnapshot newSnapshot splay at structural
    have shifted := profile.cutSet_card_le
    have unionBound := Finset.card_union_le (relocationCutsFrom oldSnapshot newSnapshot splay (Nat.le_refl n)) profile.cutSet
    dsimp only [cuts]
    omega
  refine ⟨{
    events := (preparation.events ++ [.silent]) ++ [.silent]
    final := final
    trace := (preparation.trace.append relocationTrace).append rankTrace
    represents := ⟨finalStable, rfl⟩
    births := ?_
    noInserts := ?_
    noIncreases := ?_
    preservesUnbroken := by
      intro oldSnapshot' oldView oldUnbroken
      have ranks : oldSnapshot.rank = oldSnapshot'.rank := congrArg HeapView.rank (represented.view_eq.symm.trans oldView)
      have preparedUnbroken := preparation.relocated_unbroken represented.view_eq
        (Finset.Subset.refl _) Finset.subset_union_left changes Finset.subset_union_left geometry
        (oldUnbroken.of_rank_eq ranks)
      exact preparedUnbroken.absorbRankUpdate target (relocated.isolatedRankBlockShift target)
  }⟩
  · have lengthEq : final.blocks.length = preparation.final.blocks.length := by
      simp [final, relocated, State.absorbRankUpdate]
    rw [lengthEq]
    have budgetBound : 5 * selected.card + 2 * owners.card + 4 * owners.card * cuts.card ≤ articleComparisonBirthBudget depth := by
      unfold articleComparisonBirthBudget
      calc
        _ ≤ 5 * 6 + 2 * articleComparisonOwnerBudget depth + 4 * articleComparisonOwnerBudget depth * (depth + 12) := by gcongr
        _ = _ := rfl
    have actual := preparation.births
    omega
  · simp only [eraseOperations_append, Interface.totalInserts_append,
      show eraseOperations ([.silent] : List (Event n)) = [] from rfl, preparation.noInserts]
    rfl
  · simp only [eraseOperations_append, Interface.totalIncreases_append,
      show eraseOperations ([.silent] : List (Event n)) = [] from rfl, preparation.noIncreases]
    rfl

/-- Doubling priorities retains the actual canonical root. -/
theorem canonicalRoot_withTruePriority_eq {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) :
    canonicalRoot snapshot.withTruePriority tree = canonicalRoot snapshot tree := by
  apply canonicalRoot_eq_of_rank_eq_zero
  change truePriority (snapshot.rank (canonicalRoot snapshot tree)) = 0
  rw [rank_canonicalRoot_eq_zero]
  rfl

/-- In particular every positive-depth comparison rotation has the fully
constructed bounded macro without a root-agreement hypothesis. -/
theorem exists_articleComparisonNonroot {n depth : ℕ} {params : Interface.Parameters}
    {before after splay : BST 0 n} (rotation : BST.RotationAt depth.succ before after)
    {initial : Lazy.State n} (represented : initial.Represents params (Snapshot.ofTree before).withTruePriority splay) :
    Nonempty (ArticleCanonicalRankChange params initial (Snapshot.ofTree after).withTruePriority splay
      (articleComparisonBirthBudget depth.succ)) := by
  apply exists_articleComparisonSameRoot rotation represented
  change canonicalRoot _ splay = canonicalRoot _ splay
  rw [canonicalRoot_withTruePriority_eq, canonicalRoot_withTruePriority_eq]
  exact canonicalRoot_eq_of_rotationAt_depth_succ rotation splay

end Splay.Accounting
