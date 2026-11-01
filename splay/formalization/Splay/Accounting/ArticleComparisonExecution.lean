import Splay.Accounting.ArticleComparisonSameRoot
import Splay.Lazy.RootSwapExecution

namespace Splay.Accounting

open Splay.Rank Splay.Tree Splay.Lazy Splay.Lazy.Canonical JunctionBendReduction

def articleFullComparisonBirthBudget (depth : ℕ) : ℕ :=
  41 + 2 * (articleComparisonOwnerBudget depth + 1) +
    4 * (articleComparisonOwnerBudget depth + 1) * (depth + 12)

/-- A complete comparison-tree rotation on arbitrary represented intervals,
with explicit constant costs for bounded rotation depth. -/
structure ArticleComparisonExecution {n : ℕ} (params : Interface.Parameters) (initial : Lazy.State n)
    (comparison splay : BST 0 n) (depth : ℕ) where
  final : Lazy.State n
  events : List (Event n)
  trace : Trace params initial events final
  represents : final.Represents params (Snapshot.ofTree comparison).withTruePriority splay
  births : final.blocks.length ≤ initial.blocks.length + articleFullComparisonBirthBudget depth
  inserts : Interface.totalInserts (eraseOperations events) ≤ 1
  increases : Interface.totalIncreases (eraseOperations events) ≤ 3 * params.valueBound
  preservesUnbroken : ∀ before, initial.view = canonicalHeapView before splay →
    PassedBlocksUnbroken before splay initial →
      PassedBlocksUnbroken (Snapshot.ofTree comparison).withTruePriority splay final

/-- Construct the root-changing branch, including actual deletion of the
new root and actual insertion of the old root after true ranks are installed. -/
theorem exists_articleComparisonRootChange {n depth : ℕ} {params : Interface.Parameters}
    {before after splay : BST 0 n} (rotation : BST.RotationAt depth before after)
    {initial : Lazy.State n} (represented : initial.Represents params (Snapshot.ofTree before).withTruePriority splay)
    (rootsNe : (canonicalHeapView (Snapshot.ofTree after).withTruePriority splay).root ≠ initial.view.root) :
    Nonempty (ArticleComparisonExecution params initial after splay depth) := by
  classical
  obtain ⟨profile⟩ := rotation.exists_cutProfile
  obtain ⟨changed, changedCard, changes⟩ := ComparisonRotationJunctionBound.RotationAt.exists_doubledMinimumChangeSupport rotation
  let oldSnapshot := (Snapshot.ofTree before).withTruePriority
  let newSnapshot := (Snapshot.ofTree after).withTruePriority
  let target := canonicalHeapView newSnapshot splay
  let insertOwner := (target.parent initial.view.root).getD target.root
  let selected := junctionExceptionsFrom oldSnapshot newSnapshot splay (Nat.le_refl n) ∪ {initial.view.root, target.root}
  let structuralOwners := affectedOwnerSupport oldSnapshot newSnapshot changed splay
  let borderOwners := borderCutOwners oldSnapshot profile.cutSet profile.border
  let owners := (structuralOwners ∪ borderOwners) ∪ {insertOwner}
  let cuts := relocationCutsFrom oldSnapshot newSnapshot splay (Nat.le_refl n) ∪ profile.cutSet
  obtain ⟨preparation⟩ := ArticleRelocationPreparation.exists_preparation represented.stable selected owners cuts
  have fullView := preparation.view_eq.trans represented.view_eq
  have sameRoot : preparation.final.view.root = initial.view.root := congrArg HeapView.root preparation.view_eq
  have rootAssigned : target.root ∈ preparation.final.allElements := by
    apply (preparation.stable.2.1 target.root).mpr
    apply preparation.final.view.parent_ne_none_of_ne_root
    simpa only [sameRoot] using rootsNe
  obtain ⟨source, sourceMember, sourceContains⟩ := State.mem_allElements_iff.mp rootAssigned
  obtain ⟨sourceId, sourceFound⟩ := List.mem_iff_getElem?.mp sourceMember
  obtain ⟨sourceShrinking, sourceSingleton⟩ := preparation.singletons target.root
    (Finset.mem_union_right _ (by simp)) source sourceMember sourceContains
  have otherOrders : ∀ owner ∉ owners, ∀ side,
      target.topDown owner side = (canonicalHeapView oldSnapshot splay).topDown owner side := by
    intro owner outside side
    exact topDown_eq_of_not_mem_affectedOwnerSupport changes splay
      (fun inside => outside (Finset.mem_union_left _ (Finset.mem_union_left _ inside))) side
  have borderSubset : borderOwners ⊆ owners := by
    intro element member
    exact Finset.mem_union_left _ (Finset.mem_union_right _ member)
  have shiftedEq {first second : Element n} (same : SameCutCell profile.cutSet first second) :
      preparation.final.numericRankShift target first = preparation.final.numericRankShift target second := by
    unfold State.numericRankShift
    rw [preparation.view_eq, represented.view_eq]
    exact profile.doubled_shift_eq same
  obtain ⟨checkpoint⟩ := State.RootSwapCheckpoint.exists_of_prepared preparation.stable target sourceFound sourceShrinking sourceSingleton
    (fun block member _shrinking nonempty rootOutside =>
      preparation.canonical_block_segment represented.view_eq Finset.subset_union_left Finset.subset_union_left otherOrders member nonempty rootOutside)
    (preparation.canonical_growing_prefixes represented.view_eq otherOrders)
    (by
      intro block member growing element inside
      exact (shiftedEq (preparation.growing_owner_sameCell oldSnapshot splay represented.view_eq profile.border
        (fun cut member => (profile.border_spec cut member).1) borderSubset member growing inside)).symm)
    (by
      intro block member _shrinking first firstIn second secondIn
      exact shiftedEq (preparation.all_blocks_sameCell oldSnapshot splay represented.view_eq profile.border
        (fun cut member => (profile.border_spec cut member).1) borderSubset Finset.subset_union_right member first firstIn second secondIn))
    (by
      intro block member growing ownerEq
      apply preparation.empty block member growing
      apply Finset.mem_union_right
      rw [sameRoot] at ownerEq
      exact Finset.mem_singleton.mpr ownerEq)
  obtain ⟨swap⟩ := checkpoint.finish (canonicalHeapView_heapOrdered newSnapshot splay) (by simpa only [sameRoot] using rootsNe)
  have junctions := ComparisonRotationJunctionBound.RotationAt.doubled_junctionCount_le_one rotation (splay := splay)
  change junctionCount oldSnapshot newSnapshot splay ≤ 1 at junctions
  have selectedBound : selected.card ≤ 8 := by
    have exceptions := junctionExceptionsFrom_card_le oldSnapshot newSnapshot splay (Nat.le_refl n)
    change (junctionExceptionsFrom oldSnapshot newSnapshot splay (Nat.le_refl n)).card ≤ 6 * junctionCount oldSnapshot newSnapshot splay at exceptions
    have unionBound := Finset.card_union_le (junctionExceptionsFrom oldSnapshot newSnapshot splay (Nat.le_refl n)) {initial.view.root, target.root}
    have pairBound : ({initial.view.root, target.root} : Finset (Element n)).card ≤ 2 := by simpa using Finset.card_insert_le initial.view.root {target.root}
    change (junctionExceptionsFrom oldSnapshot newSnapshot splay (Nat.le_refl n) ∪ {initial.view.root, target.root}).card ≤ 8
    omega
  have ownersBound : owners.card ≤ articleComparisonOwnerBudget depth + 1 := by
    have structural := ComparisonRotationJunctionBound.RotationAt.doubled_affectedOwners_card_le rotation (splay := splay) changedCard
    have border := profile.before_borderOwners_card_le
    have unionBound := Finset.card_union_le structuralOwners borderOwners
    have singletonBound := Finset.card_union_le (structuralOwners ∪ borderOwners) {insertOwner}
    change structuralOwners.card ≤ 5 at structural
    change borderOwners.card ≤ (depth + 2) * (2 * (depth + 1) + 1) at border
    simp only [Finset.card_singleton] at singletonBound
    dsimp only [owners, articleComparisonOwnerBudget]
    omega
  have cutsBound : cuts.card ≤ depth + 12 := by
    have structural := relocationCutsFrom_card_le oldSnapshot newSnapshot splay (Nat.le_refl n)
    change (relocationCutsFrom oldSnapshot newSnapshot splay (Nat.le_refl n)).card ≤ 10 * junctionCount oldSnapshot newSnapshot splay at structural
    have shifted := profile.cutSet_card_le
    have unionBound := Finset.card_union_le (relocationCutsFrom oldSnapshot newSnapshot splay (Nat.le_refl n)) profile.cutSet
    dsimp only [cuts]
    omega
  refine ⟨{
    final := swap.final
    events := preparation.events ++ swap.events
    trace := preparation.trace.append swap.trace
    represents := ⟨swap.stable, swap.view_eq⟩
    births := ?_
    inserts := by rw [eraseOperations_append, Interface.totalInserts_append, preparation.noInserts, swap.inserts]
    increases := by rw [eraseOperations_append, Interface.totalIncreases_append, preparation.noIncreases, Nat.zero_add]; exact swap.increases
    preservesUnbroken := by
      intro oldSnapshot' oldView oldUnbroken
      have ranks : oldSnapshot.rank = oldSnapshot'.rank := congrArg HeapView.rank (represented.view_eq.symm.trans oldView)
      have preparedUnbroken := (oldUnbroken.of_rank_eq ranks).refine preparation.passRefines
      intro block member positive
      by_cases large : 1 < block.elements.length
      · obtain ⟨old, oldMember, elements, counter⟩ := swap.largeOrigin block member large
        have oldPositive : old.passCount ≠ 0 := by simpa only [← counter] using positive
        have structural := swap.stable.1.2 block member
        apply preparation.prepared_block_unbroken represented.view_eq Finset.subset_union_left
          Finset.subset_union_left changes
          (fun _ inside => Finset.mem_union_left _ (Finset.mem_union_left _ inside))
          oldMember (preparedUnbroken old oldMember oldPositive) elements
        · intro element inside
          have parent := structural.parent_eq inside
          rw [swap.view_eq] at parent
          exact parent
        · intro element inside
          have side := structural.side_eq inside
          rw [swap.view_eq] at side
          exact side
      · cases elements : block.elements with
        | nil => exact canonicalBlockCrossSideUnbroken_of_elements_nil newSnapshot splay block elements
        | cons first rest =>
            have restEmpty : rest = [] := by
              apply List.length_eq_zero_iff.mp
              simp only [elements, List.length_cons] at large
              omega
            exact canonicalBlockCrossSideUnbroken_of_elements_singleton newSnapshot splay block first
              (by simp only [elements, restEmpty])
  }⟩
  have bound : 5 * selected.card + 2 * owners.card + 4 * owners.card * cuts.card + 1 ≤ articleFullComparisonBirthBudget depth := by
    unfold articleFullComparisonBirthBudget
    calc
      _ ≤ 5 * 8 + 2 * (articleComparisonOwnerBudget depth + 1) +
          4 * (articleComparisonOwnerBudget depth + 1) * (depth + 12) + 1 := by gcongr
      _ = _ := by ring
  have preparationBound := preparation.births
  have swapBound := swap.births
  omega

/-- Every genuine comparison rotation now has the bounded non-atomic
realization, including both root and contextual rotations. -/
theorem ArticleComparisonExecution.exists_of_rotation {n depth : ℕ} {params : Interface.Parameters}
    {before after splay : BST 0 n} (rotation : BST.RotationAt depth before after)
    {initial : Lazy.State n} (represented : initial.Represents params (Snapshot.ofTree before).withTruePriority splay) :
    Nonempty (ArticleComparisonExecution params initial after splay depth) := by
  classical
  by_cases rootEq : (canonicalHeapView (Snapshot.ofTree after).withTruePriority splay).root = initial.view.root
  · obtain ⟨execution⟩ := exists_articleComparisonSameRoot rotation represented (by simpa only [represented.view_eq] using rootEq)
    refine ⟨{
      final := execution.final
      events := execution.events
      trace := execution.trace
      represents := execution.represents
      births := ?_
      inserts := by rw [execution.noInserts]; omega
      increases := by rw [execution.noIncreases]; omega
      preservesUnbroken := execution.preservesUnbroken
    }⟩
    have budget : articleComparisonBirthBudget depth ≤ articleFullComparisonBirthBudget depth := by
      unfold articleComparisonBirthBudget articleFullComparisonBirthBudget
      gcongr <;> omega
    exact execution.births.trans (Nat.add_le_add_left budget _)
  · exact exists_articleComparisonRootChange rotation represented rootEq

end Splay.Accounting
