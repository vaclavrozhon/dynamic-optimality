import Splay.Accounting.ArticleCanonicalRelocation
import Splay.Accounting.JunctionUnbrokenPreservation
import Splay.Lazy.CanonicalRankOrder

namespace Splay.Accounting

open Splay.Rank Splay.Tree Splay.Lazy Splay.Lazy.Canonical JunctionBendReduction

/-- A block which has already participated in a pass is geometrically
unbroken. The first pass of a newly converted growing block is exempt. -/
def PassedBlocksUnbroken {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (state : Lazy.State n) : Prop :=
  ∀ block ∈ state.blocks, block.passCount ≠ 0 → canonicalBlockCrossSideUnbroken snapshot tree block

/-- Any priority change respecting all old light edges preserves their
full attachment data and hence the geometric invariant. -/
theorem PassedBlocksUnbroken.of_edge_order {n : ℕ} {first second : Snapshot n} {tree : BST 0 n}
    {state : Lazy.State n} (unbroken : PassedBlocksUnbroken first tree state)
    (edgeOrder : ∀ edge ∈ fullEdges first tree, second.rank edge.owner < second.rank edge.child) :
    PassedBlocksUnbroken second tree state := by
  have edgesEq : fullEdges second tree = fullEdges first tree :=
    treeEdges_eq_of_edge_order first second tree (Nat.le_refl n) 0 edgeOrder
  have rootEq : canonicalRoot second tree = canonicalRoot first tree :=
    subtreeOwner_eq_of_edge_order first second tree (Nat.le_refl n) 0 edgeOrder
  have incomingEq : ∀ element, incomingEdge? second tree element = incomingEdge? first tree element := by
    intro element
    cases lookup : incomingEdge? first tree element with
    | none =>
        rw [incomingEdge?_eq_none_iff] at lookup ⊢
        exact lookup.trans rootEq.symm
    | some edge =>
        have spec := incomingEdge?_some_mem first tree lookup
        have member : edge ∈ fullEdges second tree := by rw [edgesEq]; exact spec.1
        simpa only [spec.2] using incomingEdge_eq_some_of_mem_fullEdges second tree member
  intro block member positive
  have old := unbroken block member positive
  simpa only [canonicalBlockCrossSideUnbroken, canonicalParent, canonicalSide,
    ChildBetween, ChildStrictlyAbove, incomingEq] using old

/-- The rank cap stored in a snapshot is immaterial to the geometric invariant. -/
theorem PassedBlocksUnbroken.of_rank_eq {n : ℕ} {first second : Snapshot n} {tree : BST 0 n}
    {state : Lazy.State n} (unbroken : PassedBlocksUnbroken first tree state)
    (ranks : second.rank = first.rank) : PassedBlocksUnbroken second tree state := by
  apply unbroken.of_edge_order
  intro edge member
  rw [ranks]
  exact mem_treeEdges_rank_lt first tree (Nat.le_refl n) member

theorem PassedBlocksUnbroken.refine {n : ℕ} {snapshot : Snapshot n} {tree : BST 0 n}
    {before after : Lazy.State n} (unbroken : PassedBlocksUnbroken snapshot tree before)
    (refinement : before.PassRefinement after) : PassedBlocksUnbroken snapshot tree after := by
  intro block member positive
  obtain ⟨old, oldMember, owner, side, sublist, counter⟩ := refinement block member positive
  exact canonicalBlockCrossSideUnbroken_mono
    (unbroken old oldMember (by simpa only [← counter] using positive)) owner side
    (fun _ inside => sublist.mem inside)

theorem PassedBlocksUnbroken.absorbRankUpdate {n : ℕ} {snapshot : Snapshot n} {tree : BST 0 n}
    {state : Lazy.State n} (unbroken : PassedBlocksUnbroken snapshot tree state)
    (view : HeapView n) (shift : Block n → ℤ) :
    PassedBlocksUnbroken snapshot tree (state.absorbRankUpdate view shift) := by
  intro block member positive
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  exact canonicalBlockCrossSideUnbroken_mono (unbroken old oldMember positive) rfl rfl (fun _ inside => inside)

namespace ArticleRelocationPreparation

/-- A prepared block remains unbroken at any valid target placement with
its original payload. This also applies after a root-changing partial
relocation, where the new root's singleton has already been deleted. -/
theorem prepared_block_unbroken {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    {selected owners changed : Finset (Element n)} {cuts : Finset ℕ}
    {before after : Snapshot n} {tree : BST 0 n}
    (execution : ArticleRelocationPreparation params initial selected owners cuts)
    (viewEq : initial.view = canonicalHeapView before tree)
    (exceptions : junctionExceptionsFrom before after tree (Nat.le_refl n) ⊆ selected)
    (cutSubset : relocationCutsFrom before after tree (Nat.le_refl n) ⊆ cuts)
    (changes : before.MinimumChangesFrom after changed)
    (support : affectedOwnerSupport before after changed tree ⊆ owners)
    {block next : Block n} (member : block ∈ execution.final.blocks)
    (oldUnbroken : canonicalBlockCrossSideUnbroken before tree block)
    (elements : next.elements = block.elements)
    (newParents : ∀ element ∈ next.elements, canonicalParent after tree element = some next.owner)
    (newSides : ∀ element ∈ next.elements, canonicalSide after tree element = next.side) :
    canonicalBlockCrossSideUnbroken after tree next := by
  have fullView := execution.view_eq.trans viewEq
  have oldStructural := execution.stable.1.2 block member
  have oldParents : ∀ element ∈ block.elements, canonicalParent before tree element = some block.owner := by
    intro element inside
    have parent := oldStructural.parent_eq inside
    rw [fullView] at parent
    exact parent
  by_cases empty : next.elements = []
  · exact canonicalBlockCrossSideUnbroken_of_elements_nil after tree next empty
  by_cases exceptional : ∃ element ∈ block.elements, element ∈ selected
  · obtain ⟨element, inside, marked⟩ := exceptional
    have singleton := (execution.singletons element marked block member inside).2
    exact canonicalBlockCrossSideUnbroken_of_elements_singleton after tree next element (elements.trans singleton)
  have ordinary : ∀ element ∈ block.elements,
      element ∉ junctionExceptionsFrom before after tree (Nat.le_refl n) :=
    fun element inside marked => exceptional ⟨element, inside, exceptions marked⟩
  have firstMember : next.elements.headD next.owner ∈ next.elements := by
    cases payload : next.elements with
    | nil => exact (empty payload).elim
    | cons first rest => simp
  have firstOld : next.elements.headD next.owner ∈ block.elements := elements ▸ firstMember
  have sameSide : next.side = block.side := by
    have sideEq := canonicalSide_eq_of_not_mem_junctionExceptions before after tree
      (oldParents _ firstOld) (ordinary _ firstOld)
    have oldSide := oldStructural.side_eq firstOld
    rw [fullView] at oldSide
    exact (newSides _ firstMember).symm.trans (sideEq.trans oldSide)
  by_cases marked : block.owner ∈ owners
  · apply canonicalBlockCrossSideUnbroken_of_sameCutCell before after tree oldUnbroken
      (by intro element inside; exact elements ▸ inside) sameSide
    · simpa only [elements] using oldParents
    · exact newParents
    · simpa only [elements] using ordinary
    · intro first firstIn last lastIn
      rw [elements] at firstIn lastIn
      exact (execution.cells block member marked first firstIn last lastIn).mono
        (fun cut inJunction => cutSubset (Finset.mem_union_left _ inJunction))
  · have outside : block.owner ∉ affectedOwnerSupport before after changed tree := fun inside => marked (support inside)
    have otherParents := parent_iff_of_not_mem_affectedOwnerSupport changes tree outside
    have ownerEq : next.owner = block.owner :=
      Option.some.inj ((newParents _ firstMember).symm.trans ((otherParents _).mpr (oldParents _ firstOld)))
    exact canonicalBlockCrossSideUnbroken_mono
      (canonicalBlockCrossSideUnbroken_of_not_mem_affectedOwnerSupport changes tree block outside
        (fun element inside => (otherParents _).mpr (oldParents element inside)) oldUnbroken) ownerEq sameSide
      (fun _ inside => elements ▸ inside)

/-- The actual preparation and simultaneous relocation preserve every
already-passed block, including all unrelated owners. -/
theorem relocated_unbroken {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    {selected owners changed : Finset (Element n)} {cuts : Finset ℕ}
    {before after : Snapshot n} {tree : BST 0 n}
    (execution : ArticleRelocationPreparation params initial selected owners cuts)
    (viewEq : initial.view = canonicalHeapView before tree)
    (exceptions : junctionExceptionsFrom before after tree (Nat.le_refl n) ⊆ selected)
    (cutSubset : relocationCutsFrom before after tree (Nat.le_refl n) ⊆ cuts)
    (changes : before.MinimumChangesFrom after changed)
    (support : affectedOwnerSupport before after changed tree ⊆ owners)
    (geometry : execution.final.RelocationGeometry
      ((canonicalHeapView after tree).withRank execution.final.view.rank))
    (unbroken : PassedBlocksUnbroken before tree initial) :
    PassedBlocksUnbroken after tree
      (execution.final.relocateBlocks ((canonicalHeapView after tree).withRank execution.final.view.rank)) := by
  let target := (canonicalHeapView after tree).withRank execution.final.view.rank
  have prepared := unbroken.refine execution.passRefines
  intro next nextMember nextPositive
  obtain ⟨block, member, rfl⟩ := List.mem_map.mp nextMember
  change (block.relocated execution.final.view target).passCount ≠ 0 at nextPositive
  have positive : block.passCount ≠ 0 := by
    have counter := congrArg Interface.Block.passCount (block.relocated_toInterface execution.final.view target)
    change (block.relocated execution.final.view target).passCount = block.passCount at counter
    simpa only [counter] using nextPositive
  have nextStructural := Block.relocated_structurallyValid (execution.stable.1.2 block member) geometry.ranks
    (geometry.segments block member) (geometry.growingRaw block member)
  exact execution.prepared_block_unbroken viewEq exceptions cutSubset changes support member
    (prepared block member positive) (Block.relocated_elements _ _ _)
    (fun _ inside => nextStructural.parent_eq inside) (fun _ inside => nextStructural.side_eq inside)

end ArticleRelocationPreparation
end Splay.Accounting
