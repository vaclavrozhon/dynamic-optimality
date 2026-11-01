import Splay.Accounting.ShrinkingResidenceTransport
import Splay.Lazy.OutermostReparenting
import Splay.Lazy.ShrinkingRefinement

namespace Splay.Accounting

open Splay.Lazy

@[simp]
theorem operationLeavingElementsList_adjustValuesEvents {n : ℕ} (state : Lazy.State n)
    (target : Interface.Element n → ℕ) (elements : List (Interface.Element n)) :
    operationLeavingElementsList (eraseOperations (state.adjustValuesEvents target elements)) = [] := by
  induction elements generalizing state with
  | nil => rfl
  | cons element elements ih =>
      simp only [State.adjustValuesEvents_cons, eraseOperations_append,
        operationLeavingElementsList_append, operationLeavingElementsList_adjustValueEvents, ih,
        List.nil_append]

@[simp]
theorem operationLeavingElementsList_safeInsertEvents {n : ℕ} (state : Lazy.State n)
    (blockId : Interface.BlockId) (block : Lazy.Block n) (element : Interface.Element n) :
    operationLeavingElementsList (eraseOperations (state.safeInsertEvents blockId block element)) = [] := by
  simp only [State.safeInsertEvents, eraseOperations_append, operationLeavingElementsList_append,
    operationLeavingElementsList_adjustValueEvents]
  rfl

@[simp]
theorem operationLeavingElementsList_normalizedInsertEvents {n : ℕ} (state : Lazy.State n)
    (blockId : Interface.BlockId) (block : Lazy.Block n) (element : Interface.Element n) :
    operationLeavingElementsList (eraseOperations (state.normalizedInsertEvents blockId block element)) = [] := by
  simp only [State.normalizedInsertEvents, eraseOperations_append, operationLeavingElementsList_append,
    operationLeavingElementsList_adjustValueEvents, operationLeavingElementsList_safeInsertEvents,
    List.nil_append]

/-- Exactly this loser leaves; value normalization and heap replacement do
not introduce hidden residence endings. -/
theorem boundaryRelocation_leavingElements {n : ℕ} {params : Interface.Parameters}
    {initial : Lazy.State n} {sourceId destinationId : Interface.BlockId}
    {element : Interface.Element n} {view : HeapView n}
    (relocation : BoundaryRelocation params initial sourceId destinationId element view) :
    operationLeavingElementsList (eraseOperations relocation.events) = [element] := by
  rw [relocation.events_eq]
  simp only [eraseOperations_append, operationLeavingElementsList_append,
    operationLeavingElementsList_adjustValuesEvents, operationLeavingElementsList_normalizedInsertEvents]
  rfl

end Splay.Accounting

namespace Splay.Lazy.BoundaryRelocation

variable {n : ℕ} {params : Interface.Parameters} {initial : State n}
  {sourceId destinationId : Interface.BlockId} {element : Element n} {afterView : HeapView n}
  (relocation : BoundaryRelocation params initial sourceId destinationId element afterView)

/-- Boundary moves only delete from shrinking sources; their counters and
physical IDs remain fixed. -/
theorem shrinkingRefines : State.ShrinkingRefinement (fun _ => False) initial relocation.final := by
  have different := relocation.ids_ne.symm
  have destinationFound : (initial.delete sourceId element relocation.intervalGap).blocks[destinationId]? = some relocation.destination := by
    change (initial.blocks.modify sourceId (fun block => block.deleted element relocation.intervalGap))[destinationId]? = _
    rw [List.getElem?_modify]
    simp [different, relocation.destinationFound]
  exact ((initial.delete_shrinkingRefinement (fun _ => False) sourceId element relocation.intervalGap).trans
    ((initial.delete sourceId element relocation.intervalGap).insert_shrinkingRefinement (fun _ => False)
      destinationId relocation.destination element destinationFound relocation.destinationGrowing)).trans
        (State.ShrinkingRefinement.of_blocks_eq _ relocation.blocks_eq)

/-- Growing destination IDs and placements survive the boundary move.
The selected destination merely receives its new head. -/
theorem preservesGrowingPlacement {id : Interface.BlockId} {block : Block n}
    (found : initial.blocks[id]? = some block) (growing : block.mode = .growing) :
    ∃ current : Block n, relocation.final.blocks[id]? = some current ∧
      current.mode = .growing ∧ current.owner = block.owner ∧
      current.side = block.side ∧ current.creator = block.creator := by
  have notSource : sourceId ≠ id := by
    intro equal
    have atSource : initial.blocks[sourceId]? = some block := by simpa [equal] using found
    have equalBlocks := Option.some.inj (relocation.sourceFound.symm.trans atSource)
    have shrinking := relocation.sourceShrinking
    rw [equalBlocks, growing] at shrinking
    contradiction
  have detachedFound : (initial.delete sourceId element relocation.intervalGap).blocks[id]? = some block := by
    change (initial.blocks.modify sourceId fun b => b.deleted element relocation.intervalGap)[id]? = _
    rw [List.getElem?_modify]
    simp [notSource, found]
  have finalFound := congrArg (fun blocks : List (Block n) => blocks[id]?) relocation.blocks_eq
  change relocation.final.blocks[id]? =
    ((initial.delete sourceId element relocation.intervalGap).blocks.modify destinationId
      fun b => b.inserted element)[id]? at finalFound
  rw [List.getElem?_modify, detachedFound] at finalFound
  by_cases selected : destinationId = id
  · refine ⟨block.inserted element, ?_, growing, rfl, rfl, rfl⟩
    simpa [selected] using finalFound
  · exact ⟨block, by simpa [selected] using finalFound, growing, rfl, rfl, rfl⟩

/-- A growing interval of any other owner remains literally the same block. -/
theorem preservesGrowingBlock {id : Interface.BlockId} {block : Block n}
    (found : initial.blocks[id]? = some block) (growing : block.mode = .growing)
    (otherOwner : block.owner ≠ relocation.destination.owner) :
    relocation.final.blocks[id]? = some block := by
  have notSource : sourceId ≠ id := by
    intro equal
    have atSource : initial.blocks[sourceId]? = some block := by simpa [equal] using found
    have blockEq := Option.some.inj (relocation.sourceFound.symm.trans atSource)
    have shrinking := relocation.sourceShrinking
    rw [blockEq, growing] at shrinking
    contradiction
  have notDestination : destinationId ≠ id := by
    intro equal
    have atDestination : initial.blocks[destinationId]? = some block := by simpa [equal] using found
    have blockEq := Option.some.inj (relocation.destinationFound.symm.trans atDestination)
    exact otherOwner (congrArg Block.owner blockEq.symm)
  rw [relocation.blocks_eq]
  simp [State.insert, State.delete, List.getElem?_modify, notSource, notDestination, found]

/-- The endpoint is a simultaneous reparenting of the same single loser. -/
def singletonReparented (stable : relocation.final.Stable params)
    (pairing : Interface.Pairing n)
    (loser : pairing.loser = element)
    (parent : relocation.final.view.parent element = some pairing.winner)
    (side : relocation.final.view.side element = Canonical.sideOf pairing.winner element) :
    Accounting.ArticleBatchDestinationAllocation.BatchReparentedView initial.view [pairing] where
  view := relocation.final.view
  rank_eq := relocation.rank_eq
  root_eq := relocation.root_eq
  ordered := stable.2.2.1
  paired_parent := by
    intro p member
    have equal : p = pairing := by simpa using member
    subst p
    simpa [loser] using parent
  paired_side := by
    intro p member
    have equal : p = pairing := by simpa using member
    subst p
    simpa [loser] using side
  unpaired_parent := by
    intro queried outside
    exact (relocation.unpaired queried (by simpa [loser] using outside pairing (by simp))).1
  unpaired_side := by
    intro queried outside
    exact (relocation.unpaired queried (by simpa [loser] using outside pairing (by simp))).2

end Splay.Lazy.BoundaryRelocation
