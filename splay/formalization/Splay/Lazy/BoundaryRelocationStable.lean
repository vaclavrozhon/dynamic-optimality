import Splay.Lazy.BoundaryRelocation
import Splay.Lazy.ComparisonRootSwapComplete

namespace Splay.Lazy

/-- Outside its new placement, a reparented element is simply erased from
its previous child order. -/
theorem HeapView.topDown_eq_erase_of_reparenting {n : ℕ} {before after : HeapView n}
    (element : Element n)
    (unchanged : ∀ queried, queried ≠ element →
      after.parent queried = before.parent queried ∧ after.side queried = before.side queried)
    (owner : Element n) (side : Side) (outside : element ∉ after.topDown owner side) :
    after.topDown owner side = (before.topDown owner side).erase element := by
  have membership : ∀ queried, queried ∈ after.topDown owner side ↔
      queried ∈ (before.topDown owner side).erase element := by
    intro queried
    by_cases equal : queried = element
    · subst queried
      simp [outside, (before.topDown_nodup owner side).not_mem_erase]
    · rw [List.mem_erase_of_ne equal]
      simp only [after.mem_topDown_iff, before.mem_topDown_iff,
        (unchanged queried equal).1, (unchanged queried equal).2]
  cases side with
  | left =>
      exact List.Pairwise.eq_of_mem_iff (after.topDown_ordered owner).1
        ((before.topDown_ordered owner).1.sublist List.erase_sublist) membership
  | right =>
      exact List.Pairwise.eq_of_mem_iff (after.topDown_ordered owner).2
        ((before.topDown_ordered owner).2.sublist List.erase_sublist) membership

namespace State.OneGrowingPerSide

/-- Two found growing blocks at the same placement have the same ID. -/
theorem blockId_eq {n : ℕ} {state : State n} (unique : state.OneGrowingPerSide)
    {firstId secondId : Interface.BlockId} {first second : Block n}
    (firstFound : state.blocks[firstId]? = some first)
    (secondFound : state.blocks[secondId]? = some second)
    (firstGrowing : first.mode = .growing) (secondGrowing : second.mode = .growing)
    (owner : first.owner = second.owner) (side : first.side = second.side) : firstId = secondId := by
  obtain ⟨firstLt, firstEq⟩ := List.getElem?_eq_some_iff.mp firstFound
  obtain ⟨secondLt, secondEq⟩ := List.getElem?_eq_some_iff.mp secondFound
  let firstIndex : Fin state.blocks.length := ⟨firstId, firstLt⟩
  let secondIndex : Fin state.blocks.length := ⟨secondId, secondLt⟩
  have firstGet : state.blocks.get firstIndex = first := firstEq
  have secondGet : state.blocks.get secondIndex = second := secondEq
  have firstProperty : (state.blocks.get firstIndex).mode = .growing ∧
      (state.blocks.get firstIndex).owner = first.owner ∧
      (state.blocks.get firstIndex).side = first.side := by rw [firstGet]; exact ⟨firstGrowing, rfl, rfl⟩
  have secondProperty : (state.blocks.get secondIndex).mode = .growing ∧
      (state.blocks.get secondIndex).owner = first.owner ∧
      (state.blocks.get secondIndex).side = first.side := by rw [secondGet]; exact ⟨secondGrowing, owner.symm, side.symm⟩
  exact congrArg Fin.val ((unique first.owner first.side).unique firstProperty secondProperty)

end State.OneGrowingPerSide

namespace BoundaryRelocation

variable {n : ℕ} {params : Interface.Parameters} {initial : State n}
  {sourceId destinationId : Interface.BlockId} {element : Element n} {afterView : HeapView n}
  (relocation : BoundaryRelocation params initial sourceId destinationId element afterView)

theorem blocks_length_eq : relocation.final.blocks.length = initial.blocks.length := by
  rw [relocation.blocks_eq]
  simp [State.insert, State.delete]

include relocation in
theorem ids_ne : destinationId ≠ sourceId := by
  intro equal
  have destinationAtSource : initial.blocks[sourceId]? = some relocation.destination :=
    (congrArg (fun id : ℕ => initial.blocks[id]?) equal).symm.trans relocation.destinationFound
  have blocksEq := Option.some.inj (relocation.sourceFound.symm.trans destinationAtSource)
  have shrinking := relocation.sourceShrinking
  rw [blocksEq, relocation.destinationGrowing] at shrinking
  contradiction

theorem complete (complete : initial.Complete) : relocation.final.Complete := by
  intro queried
  rw [relocation.assigned_iff, complete queried]
  constructor
  · intro parent
    apply relocation.final.view.parent_ne_none_of_ne_root
    intro equal
    apply parent
    rw [equal, relocation.root_eq, initial.view.root_parent]
  · intro parent
    apply initial.view.parent_ne_none_of_ne_root
    intro equal
    apply parent
    rw [equal, ← relocation.root_eq, relocation.final.view.root_parent]

theorem oneGrowingPerSide (unique : initial.OneGrowingPerSide) : relocation.final.OneGrowingPerSide := by
  unfold State.OneGrowingPerSide
  rw [relocation.blocks_eq]
  exact (unique.delete sourceId element relocation.intervalGap).insert destinationId element

/-- Every old growing block remains topmost. At the selected destination the
new element is prepended; elsewhere deletion affects only the suffix. -/
theorem growingTopmost (unique : initial.OneGrowingPerSide)
    (topmost : initial.GrowingTopmost) : relocation.final.GrowingTopmost := by
  have valid := relocation.trace.initial_valid
  have destinationLookup : relocation.final.blocks[destinationId]? =
      some (relocation.destination.inserted element) := by
    rw [relocation.blocks_eq]
    simp [State.insert, State.delete, List.getElem?_modify,
      Ne.symm relocation.ids_ne, relocation.destinationFound]
  have sourceLookup : relocation.final.blocks[sourceId]? =
      some (relocation.source.deleted element relocation.intervalGap) := by
    rw [relocation.blocks_eq]
    simp [State.insert, State.delete, List.getElem?_modify,
      relocation.ids_ne, relocation.sourceFound]
  intro id
  dsimp only
  intro growing
  let current := relocation.final.blocks.get id
  have currentGrowing : current.mode = .growing := growing
  have currentFound : relocation.final.blocks[id.val]? = some current := by simp [current]
  by_cases destination : id.val = destinationId
  · have currentEq : current = relocation.destination.inserted element := by
      rw [destination, destinationLookup] at currentFound
      exact Option.some.inj currentFound.symm
    change ∃ suffix, relocation.final.view.topDown current.owner current.side = current.elements ++ suffix
    rw [currentEq]
    exact relocation.destinationFirst
  · have notSource : id.val ≠ sourceId := by
      intro equal
      rw [equal, sourceLookup] at currentFound
      have currentEq := Option.some.inj currentFound
      rw [← currentEq] at currentGrowing
      simpa [Block.deleted, relocation.sourceShrinking] using currentGrowing
    have oldFound : initial.blocks[id.val]? = some current := by
      have transformedFound :=
        (congrArg (fun blocks : List (Block n) => blocks[id.val]?) relocation.blocks_eq).symm.trans currentFound
      simpa [State.insert, State.delete, List.getElem?_modify,
        Ne.symm destination, Ne.symm notSource] using transformedFound
    obtain ⟨oldLt, oldEq⟩ := List.getElem?_eq_some_iff.mp oldFound
    let oldId : Fin initial.blocks.length := ⟨id.val, oldLt⟩
    have oldGet : initial.blocks.get oldId = current := oldEq
    have oldGrowing : (initial.blocks.get oldId).mode = .growing := by
      rw [oldGet]
      exact currentGrowing
    obtain ⟨suffix, order⟩ := topmost oldId oldGrowing
    change initial.view.topDown (initial.blocks.get oldId).owner (initial.blocks.get oldId).side =
      (initial.blocks.get oldId).elements ++ suffix at order
    rw [oldGet] at order
    have notCurrent : element ∉ current.elements := by
      intro inside
      exact notSource (valid.blockId_eq_of_element_mem oldFound inside relocation.sourceFound relocation.elementMem)
    have outside : element ∉ relocation.final.view.topDown current.owner current.side := by
      intro inside
      have oldPlacement := relocation.final.view.mem_topDown_iff.mp inside
      obtain ⟨tail, first⟩ := relocation.destinationFirst
      have newPlacement := relocation.final.view.mem_topDown_iff.mp (by rw [first]; simp :
        element ∈ relocation.final.view.topDown relocation.destination.owner relocation.destination.side)
      have ownerEq : current.owner = relocation.destination.owner :=
        Option.some.inj (oldPlacement.1.symm.trans newPlacement.1)
      have sideEq : current.side = relocation.destination.side := oldPlacement.2.symm.trans newPlacement.2
      exact destination (unique.blockId_eq oldFound relocation.destinationFound currentGrowing
        relocation.destinationGrowing ownerEq sideEq)
    have afterOrder := HeapView.topDown_eq_erase_of_reparenting element relocation.unpaired
      current.owner current.side outside
    change ∃ suffix, relocation.final.view.topDown current.owner current.side = current.elements ++ suffix
    refine ⟨suffix.erase element, ?_⟩
    rw [afterOrder, order, List.erase_append_right _ notCurrent]

/-- The actual boundary macro ends at a stable state when its supplied
reparented view is heap ordered. -/
theorem stable (before : initial.Stable params) (ordered : afterView.HeapOrdered) :
    relocation.final.Stable params := by
  refine ⟨relocation.trace.final_valid, relocation.complete before.2.1, ?_,
    relocation.oneGrowingPerSide before.2.2.2.1,
    relocation.growingTopmost before.2.2.2.1 before.2.2.2.2.1, relocation.values⟩
  rw [relocation.view_eq]
  exact ordered

end BoundaryRelocation
end Splay.Lazy
