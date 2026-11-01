import Splay.Accounting.JunctionUnbrokenCorridor
import Splay.Accounting.JunctionOwnerSupport

namespace Splay.Accounting.JunctionBendReduction

open Splay.Rank Splay.Tree Splay.Lazy Splay.Lazy.Canonical

/-- A new intervening child has an old intervening child on the same side.
Only the two endpoints need to avoid the finite junction exceptions. -/
theorem exists_old_intervening_child_of_sameCutCell {n : ℕ}
    (before after : Snapshot n) (tree : BST 0 n)
    {first middle last oldOwner newOwner : Element n}
    (firstOrdinary : first ∉ junctionExceptionsFrom before after tree (Nat.le_refl n))
    (lastOrdinary : last ∉ junctionExceptionsFrom before after tree (Nat.le_refl n))
    (sameCell : SameCutCell (junctionCutsFrom before after tree (Nat.le_refl n)) first last)
    (firstParent : canonicalParent before tree first = some oldOwner)
    (lastParent : canonicalParent before tree last = some oldOwner)
    (firstNextParent : canonicalParent after tree first = some newOwner)
    (middleParent : canonicalParent after tree middle = some newOwner)
    (above : ChildStrictlyAbove after tree first middle)
    (below : ChildStrictlyAbove after tree middle last) :
    ∃ oldMiddle, canonicalParent before tree oldMiddle = some oldOwner ∧
      canonicalSide before tree oldMiddle = canonicalSide after tree middle ∧
      ChildStrictlyAbove before tree first oldMiddle ∧
      ChildStrictlyAbove before tree oldMiddle last := by
  obtain ⟨firstNew, middleNew, firstLookup, middleLookup, above⟩ := above
  obtain ⟨middleNew', lastNew, middleLookup', lastLookup, below⟩ := below
  have middleEq : middleNew' = middleNew := Option.some.inj (middleLookup'.symm.trans middleLookup)
  subst middleNew'
  have firstNewSpec := incomingEdge?_some_mem after tree firstLookup
  have middleNewSpec := incomingEdge?_some_mem after tree middleLookup
  have lastNewSpec := incomingEdge?_some_mem after tree lastLookup
  obtain ⟨firstOld, firstOldMember, firstChild, firstBranch, firstKey, firstDepth, firstSide⟩ :=
    exists_edge_same_attachment_side_of_not_mem_exceptions after before tree (Nat.le_refl n) 0
      firstNewSpec.1 (by simpa only [firstNewSpec.2, junctionExceptionsFrom_comm after before] using firstOrdinary)
  obtain ⟨lastOld, lastOldMember, lastChild, lastBranch, lastKey, lastDepth, lastSide⟩ :=
    exists_edge_same_attachment_side_of_not_mem_exceptions after before tree (Nat.le_refl n) 0
      lastNewSpec.1 (by simpa only [lastNewSpec.2, junctionExceptionsFrom_comm after before] using lastOrdinary)
  have firstOldChild : firstOld.child = first := firstChild.trans firstNewSpec.2
  have lastOldChild : lastOld.child = last := lastChild.trans lastNewSpec.2
  have firstOldLookup : incomingEdge? before tree first = some firstOld := by
    simpa only [firstOldChild] using incomingEdge_eq_some_of_mem_fullEdges before tree firstOldMember
  have lastOldLookup : incomingEdge? before tree last = some lastOld := by
    simpa only [lastOldChild] using incomingEdge_eq_some_of_mem_fullEdges before tree lastOldMember
  have firstOwner : firstOld.owner = oldOwner := by
    simpa only [canonicalParent, firstOldLookup, Option.map_some, Option.some.injEq] using firstParent
  have lastOwner : lastOld.owner = oldOwner := by
    simpa only [canonicalParent, lastOldLookup, Option.map_some, Option.some.injEq] using lastParent
  have firstNewOwner : firstNew.owner = newOwner := by
    simpa only [canonicalParent, firstLookup, Option.map_some, Option.some.injEq] using firstNextParent
  have middleNewOwner : middleNew.owner = newOwner := by
    simpa only [canonicalParent, middleLookup, Option.map_some, Option.some.injEq] using middleParent
  obtain ⟨old, oldMember, oldOwnerEq, oldBranch, oldKey, oldDepth, oldSide⟩ :=
    exists_old_between_edge_of_sameCutCell before after tree (Nat.le_refl n) 0
      firstOldMember lastOldMember (firstOwner.trans lastOwner.symm)
      (by rw [firstOldChild]; exact fun member => firstOrdinary (Finset.mem_union_right _ member))
      (by simpa only [firstOldChild, lastOldChild] using sameCell)
      firstNewSpec.1 firstKey.symm middleNewSpec.1 (middleNewOwner.trans firstNewOwner.symm)
      (by simpa only [edgeStrictlyAbove, firstDepth, firstBranch] using above)
      (by simpa only [edgeStrictlyAbove, lastDepth, lastBranch] using below)
  have oldLookup := incomingEdge_eq_some_of_mem_fullEdges before tree oldMember
  refine ⟨old.child, ?_, ?_, ?_, ?_⟩
  · exact (canonicalParent_eq_some_of_mem_fullEdges before tree old oldMember).trans
      (congrArg some (oldOwnerEq.trans firstOwner))
  · simp only [canonicalSide, oldLookup, middleLookup, oldSide]
  · exact ⟨firstOld, old, firstOldLookup, oldLookup, by
      simpa only [edgeStrictlyAbove, firstDepth, firstBranch, oldDepth, oldBranch] using above⟩
  · exact ⟨old, lastOld, oldLookup, lastOldLookup, by
      simpa only [edgeStrictlyAbove, lastDepth, lastBranch, oldDepth, oldBranch] using below⟩

/-- Relocating an ordinary block within one junction-cut cell preserves its
cross-side unbrokenness. The owner may change and the payload may shrink. -/
theorem canonicalBlockCrossSideUnbroken_of_sameCutCell {n : ℕ}
    (before after : Snapshot n) (tree : BST 0 n) {old next : Lazy.Block n}
    (unbroken : canonicalBlockCrossSideUnbroken before tree old)
    (subset : ∀ element ∈ next.elements, element ∈ old.elements)
    (sameSide : next.side = old.side)
    (oldParents : ∀ element ∈ next.elements, canonicalParent before tree element = some old.owner)
    (newParents : ∀ element ∈ next.elements, canonicalParent after tree element = some next.owner)
    (ordinary : ∀ element ∈ next.elements,
      element ∉ junctionExceptionsFrom before after tree (Nat.le_refl n))
    (cells : ∀ first ∈ next.elements, ∀ last ∈ next.elements,
      SameCutCell (junctionCutsFrom before after tree (Nat.le_refl n)) first last) :
    canonicalBlockCrossSideUnbroken after tree next := by
  intro first firstMember last lastMember middle middleParent opposite between
  have oriented : ∀ first ∈ next.elements, ∀ last ∈ next.elements,
      ChildStrictlyAbove after tree first middle → ChildStrictlyAbove after tree middle last → False := by
    intro first firstMember last lastMember above below
    obtain ⟨oldMiddle, oldParent, oldSide, oldAbove, oldBelow⟩ :=
      exists_old_intervening_child_of_sameCutCell before after tree
        (ordinary first firstMember) (ordinary last lastMember) (cells first firstMember last lastMember)
        (oldParents first firstMember) (oldParents last lastMember) (newParents first firstMember)
        middleParent above below
    exact unbroken first (subset first firstMember) last (subset last lastMember) oldMiddle oldParent
      (by simpa only [oldSide, ← sameSide] using opposite) (Or.inl ⟨oldAbove, oldBelow⟩)
  rcases between with ⟨above, below⟩ | ⟨above, below⟩
  · exact oriented first firstMember last lastMember above below
  · exact oriented last lastMember first firstMember above below

/-- The full incoming edge, including its attachment data, is unchanged
at owners outside the actual finite support. -/
theorem incomingEdge_eq_of_parent_not_mem_affectedOwnerSupport {n : ℕ}
    {before after : Snapshot n} {changed : Finset (External n)}
    (changes : before.MinimumChangesFrom after changed) (tree : BST 0 n)
    {owner child : External n} (outside : owner ∉ affectedOwnerSupport before after changed tree)
    (parent : canonicalParent after tree child = some owner) :
    incomingEdge? before tree child = incomingEdge? after tree child := by
  classical
  obtain ⟨edge, lookup, ownerEq⟩ := Option.map_eq_some_iff.mp parent
  have edgeSpec := incomingEdge?_some_mem after tree lookup
  have oldMember : edge ∈ fullEdges before tree := by
    rcases new_edge_owner_cases changes tree (Nat.le_refl n) 0 edgeSpec.1 with
      old | junction | ⟨oldEdge, oldMember, sameOwner, marked⟩
    · exact old
    · exact (outside (Finset.mem_union_right _ (Finset.mem_union_left _ (ownerEq ▸ junction)))).elim
    · apply False.elim
      apply outside
      apply Finset.mem_union_right
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨oldEdge.child, marked, ?_⟩
      rw [canonicalParent_eq_some_of_mem_fullEdges before tree oldEdge oldMember]
      exact sameOwner.trans ownerEq
  rw [lookup]
  simpa only [edgeSpec.2] using incomingEdge_eq_some_of_mem_fullEdges before tree oldMember

/-- Unrelated owners retain cross-side unbrokenness without any cuts. -/
theorem canonicalBlockCrossSideUnbroken_of_not_mem_affectedOwnerSupport {n : ℕ}
    {before after : Snapshot n} {changed : Finset (External n)}
    (changes : before.MinimumChangesFrom after changed) (tree : BST 0 n) (block : Block n)
    (outside : block.owner ∉ affectedOwnerSupport before after changed tree)
    (parents : ∀ element ∈ block.elements, canonicalParent after tree element = some block.owner)
    (unbroken : canonicalBlockCrossSideUnbroken before tree block) :
    canonicalBlockCrossSideUnbroken after tree block := by
  intro first firstMember last lastMember middle middleParent opposite between
  have firstLookup := incomingEdge_eq_of_parent_not_mem_affectedOwnerSupport changes tree outside (parents first firstMember)
  have lastLookup := incomingEdge_eq_of_parent_not_mem_affectedOwnerSupport changes tree outside (parents last lastMember)
  have middleLookup := incomingEdge_eq_of_parent_not_mem_affectedOwnerSupport changes tree outside middleParent
  apply unbroken first firstMember last lastMember middle
    ((parent_iff_of_not_mem_affectedOwnerSupport changes tree outside middle).mp middleParent)
  · simpa only [canonicalSide, middleLookup] using opposite
  · simpa only [ChildBetween, ChildStrictlyAbove, firstLookup, lastLookup, middleLookup] using between

end Splay.Accounting.JunctionBendReduction
