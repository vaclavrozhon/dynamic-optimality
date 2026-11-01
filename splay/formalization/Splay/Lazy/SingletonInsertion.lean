import Splay.Lazy.SafeInsertCost
import Splay.Lazy.ComparisonRootSwapComplete

namespace Splay.Lazy.State

/-- Insert into an empty growing slot, immediately turn the new child into
a shrinking singleton, and restore the empty growing slot. The intermediate
singleton may lie anywhere in the owner's child order. -/
def insertSingleton {n : ℕ} (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (element : Element n) : State n :=
  ((state.insert blockId element).convert blockId (state.view.rawGap element)).create block.creator block.side

def insertSingletonEvents {n : ℕ} (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (element : Element n) : List (Event n) :=
  state.safeInsertEvents blockId block element ++
    [.operation (.convert blockId), .operation (.create block.creator)]

/-- Checked singleton insertion for arbitrary unchanged surrounding blocks.
Only their concrete segment validity after attaching the new element is
required; no atomicity of the rest of the heap is assumed. -/
theorem insertSingleton_trace {n : ℕ} {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId) (block : Block n) (element : Element n)
    (valid : state.Valid params) (found : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing) (empty : block.elements = [])
    (unassigned : element ∉ state.allElements) (gapNonnegative : 0 ≤ state.view.rawGap element)
    (afterSegment : IsSegment (block.inserted element).elements
      (state.view.attachedTopDown (state.insert blockId element).allElements block.owner block.side))
    (otherValid : ∀ id : Fin state.blocks.length, blockId ≠ id.val →
      (state.blocks.get id).StructurallyValid state.view (state.insert blockId element).allElements) :
    Trace params state (state.insertSingletonEvents blockId block element) (state.insertSingleton blockId block element) := by
  have inserted := state.safeInsert_trace blockId block element valid found growing unassigned gapNonnegative afterSegment otherValid
  have insertedFound : (state.insert blockId element).blocks[blockId]? = some (block.inserted element) := by
    simp [State.insert, List.getElem?_modify, found]
  have singleton : (block.inserted element).elements = [element] := by simp [Block.inserted, empty]
  have shrinkingGap : ((block.inserted element).converted (state.view.rawGap element)).GapValid (state.insert blockId element).view :=
    Block.singleton_shrinking_gapValid _ _ rfl element singleton rfl
  exact inserted.append ((state.insert blockId element).convertAndCreate_trace blockId (block.inserted element)
    (state.view.rawGap element) inserted.final_valid insertedFound growing shrinkingGap)

@[simp]
theorem insertSingleton_value {n : ℕ} (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (element : Element n) :
    (state.insertSingleton blockId block element).value = state.value := rfl

@[simp]
theorem insertSingleton_view {n : ℕ} (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (element : Element n) :
    (state.insertSingleton blockId block element).view = state.view := rfl

@[simp]
theorem insertSingleton_blocks_length {n : ℕ} (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (element : Element n) :
    (state.insertSingleton blockId block element).blocks.length = state.blocks.length + 1 := by
  simp [insertSingleton, State.create, State.convert, State.insert]

@[simp]
theorem insertSingletonEvents_inserts {n : ℕ} (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (element : Element n) :
    Interface.totalInserts (eraseOperations (state.insertSingletonEvents blockId block element)) = 1 := by
  rw [insertSingletonEvents, eraseOperations_append, Interface.totalInserts_append, safeInsertEvents_totalInserts]
  rfl

@[simp]
theorem insertSingletonEvents_activity {n : ℕ} (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (element : Element n) :
    Interface.totalActivity (eraseOperations (state.insertSingletonEvents blockId block element)) = 0 := by
  rw [insertSingletonEvents, eraseOperations_append, Interface.totalActivity_append, safeInsertEvents_totalActivity]
  rfl

theorem insertSingletonEvents_increases {n : ℕ} {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId) (block : Block n) (element : Element n)
    (valid : state.Valid params) :
    Interface.totalIncreases (eraseOperations (state.insertSingletonEvents blockId block element)) ≤ 3 * params.valueBound := by
  rw [insertSingletonEvents, eraseOperations_append, Interface.totalIncreases_append,
    show Interface.totalIncreases (eraseOperations ([.operation (.convert blockId), .operation (.create block.creator)] : List (Event n))) = 0 from rfl,
    Nat.add_zero]
  exact state.safeInsertEvents_totalIncreases_le blockId block element valid

/-- The selected old growing ID now holds the new shrinking singleton;
all other old blocks stay literally unchanged and one empty slot is appended. -/
theorem insertSingleton_blocks {n : ℕ} (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (element : Element n) :
    (state.insertSingleton blockId block element).blocks =
      state.blocks.modify blockId (fun current => (current.inserted element).converted (state.view.rawGap element)) ++
        [Block.emptyGrowing block.creator block.side] := by
  simp [insertSingleton, State.create, State.convert, State.insert, List.modify_modify_eq, Function.comp_def]

/-- Immediate singleton conversion restores synchronized values without
raising the newly inserted element above one. -/
theorem insertSingleton_valuesRealizeGaps {n : ℕ} (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (element : Element n)
    (values : state.ValuesRealizeGaps) (found : state.blocks[blockId]? = some block)
    (empty : block.elements = []) (elementOne : state.value element = 1) :
    (state.insertSingleton blockId block element).ValuesRealizeGaps := by
  refine ⟨values.1, ?_⟩
  intro current member queried inside
  rw [insertSingleton_blocks] at member
  rcases List.mem_append.mp member with modified | replacement
  · obtain ⟨id, currentFound⟩ := List.mem_iff_getElem?.mp modified
    rw [List.getElem?_modify] at currentFound
    split at currentFound
    next selected =>
      have original : state.blocks[id]? = some block := by simpa only [selected] using found
      rw [original] at currentFound
      have currentEq : (block.inserted element).converted (state.view.rawGap element) = current := by simpa using currentFound
      rw [← currentEq] at inside ⊢
      have atElement : queried = element := by simpa [Block.converted, Block.inserted, empty] using inside
      subst queried
      change state.value element = Analysis.transientContractedGap (state.view.rawGap element) (state.view.rawGap element)
      rw [elementOne, Analysis.transientContractedGap_self]
    next untouched =>
      have oldFound : state.blocks[id]? = some current := by simpa using currentFound
      exact values.2 current (List.mem_iff_getElem?.mpr ⟨id, oldFound⟩) queried inside
  · have atReplacement := List.mem_singleton.mp replacement
    rw [atReplacement] at inside
    simp [Block.emptyGrowing] at inside

/-- Only the selected growing slot could be temporarily inserted below old
shrinking blocks. Converting it restores topmost growing intervals globally. -/
theorem insertSingleton_growingTopmost {n : ℕ} (state : State n) (blockId : Interface.BlockId)
    (block : Block n) (element : Element n) (found : state.blocks[blockId]? = some block)
    (topmost : state.GrowingTopmost) :
    (state.insertSingleton blockId block element).GrowingTopmost := by
  intro index
  dsimp only
  intro growing
  let current := (state.insertSingleton blockId block element).blocks.get index
  have member : current ∈ (state.insertSingleton blockId block element).blocks := List.get_mem _ _
  change current.mode = .growing at growing
  change ∃ suffix, state.view.topDown current.owner current.side = current.elements ++ suffix
  rw [insertSingleton_blocks] at member
  rcases List.mem_append.mp member with modified | replacement
  · obtain ⟨id, currentFound⟩ := List.mem_iff_getElem?.mp modified
    rw [List.getElem?_modify] at currentFound
    split at currentFound
    next selected =>
      have original : state.blocks[id]? = some block := by simpa only [selected] using found
      rw [original] at currentFound
      have currentEq : (block.inserted element).converted (state.view.rawGap element) = current := by simpa using currentFound
      rw [← currentEq] at growing
      contradiction
    next untouched =>
      have oldFound : state.blocks[id]? = some current := by simpa using currentFound
      obtain ⟨lt, equal⟩ := List.getElem?_eq_some_iff.mp oldFound
      have result := topmost ⟨id, lt⟩
      change (state.blocks[id]).mode = .growing → ∃ suffix,
        state.view.topDown (state.blocks[id]).owner (state.blocks[id]).side = (state.blocks[id]).elements ++ suffix at result
      rw [equal] at result
      exact result growing
  · rw [List.mem_singleton.mp replacement]
    exact ⟨state.view.topDown block.creator block.side, by simp [Block.emptyGrowing]⟩

/-- The immediate conversion and replacement preserve one growing interval
per owner and side. The required inserted validity comes from the actual
safe-insert prefix of `insertSingleton_trace`. -/
theorem insertSingleton_oneGrowingPerSide {n : ℕ} {params : Interface.Parameters}
    (state : State n) (blockId : Interface.BlockId) (block : Block n) (element : Element n)
    (insertedValid : (state.insert blockId element).Valid params)
    (found : state.blocks[blockId]? = some block) (growing : block.mode = .growing)
    (one : state.OneGrowingPerSide) :
    (state.insertSingleton blockId block element).OneGrowingPerSide := by
  have insertedFound : (state.insert blockId element).blocks[blockId]? = some (block.inserted element) := by
    simp [State.insert, found]
  exact (state.insert blockId element).convertAndCreate_oneGrowingPerSide blockId (block.inserted element)
    (state.view.rawGap element) insertedValid insertedFound growing (one.insert blockId element)

end Splay.Lazy.State
