import Splay.Lazy.CanonicalInitializationTrace
import Splay.Accounting.FullOrderSegment

namespace Splay.Lazy

namespace State

/-- Deleting an assigned element erases precisely that occurrence from the
assigned list, even when its shrinking source contains other elements. -/
theorem delete_allElements {n : ℕ} {state : State n}
    (blockId : Interface.BlockId) (block : Block n) (element : Element n)
    (intervalGap : ℤ) (found : state.blocks[blockId]? = some block)
    (member : element ∈ block.elements) (nodup : state.allElements.Nodup) :
    (state.delete blockId element intervalGap).allElements = state.allElements.erase element := by
  rcases state with ⟨view, blocks, value⟩
  change (blocks.modify blockId fun current => current.deleted element intervalGap).flatMap
    Block.elements = (blocks.flatMap Block.elements).erase element
  change blocks[blockId]? = some block at found
  change (blocks.flatMap Block.elements).Nodup at nodup
  induction blocks generalizing blockId with
  | nil => simp at found
  | cons head tail ih =>
      change (head.elements ++ tail.flatMap Block.elements).Nodup at nodup
      have parts := List.nodup_append.mp nodup
      cases blockId with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst block
          simp only [List.modify_zero_cons, List.flatMap_cons, Block.deleted]
          rw [List.erase_append_left _ member]
      | succ blockId =>
          simp only [List.getElem?_cons_succ] at found
          have inTail : element ∈ tail.flatMap Block.elements :=
            List.mem_flatMap.mpr ⟨block, List.mem_of_getElem? found, member⟩
          have notHead : element ∉ head.elements := fun inside => parts.2.2 element inside element inTail rfl
          simp only [List.modify_succ_cons, List.flatMap_cons]
          rw [ih blockId found parts.2.1, List.erase_append_right _ notHead]

/-- Exact attached-child order after deletion; detached heap vertices do not
break the source or any other interval. -/
theorem delete_attachedTopDown {n : ℕ} {state : State n}
    (blockId : Interface.BlockId) (block : Block n) (element : Element n)
    (intervalGap : ℤ) (found : state.blocks[blockId]? = some block)
    (member : element ∈ block.elements) (nodup : state.allElements.Nodup)
    (owner : Element n) (side : Side) :
    state.view.attachedTopDown (state.delete blockId element intervalGap).allElements owner side =
      (state.view.attachedTopDown state.allElements owner side).erase element := by
  rw [delete_allElements blockId block element intervalGap found member nodup]
  have attachedNodup : (state.view.attachedTopDown state.allElements owner side).Nodup :=
    (state.view.topDown_nodup owner side).filter _
  rw [attachedNodup.erase_eq_filter]
  unfold HeapView.attachedTopDown
  rw [List.filter_filter]
  apply List.filter_congr
  intro queried _
  by_cases equal : queried = element
  · subst queried
    simp [nodup.not_mem_erase]
  · simp [List.mem_erase_of_ne equal, equal]

/-- General deletion is legal once the source's new attained gap is supplied.
Every other block retains its identity and structural validity. -/
theorem delete_step_of_gapValid {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) {blockId : Interface.BlockId} {block : Block n}
    (found : state.blocks[blockId]? = some block) (shrinking : block.mode = .shrinking)
    (element : Element n) (member : element ∈ block.elements) (intervalGap : ℤ)
    (gapValid : (block.deleted element intervalGap).GapValid state.view) :
    Step params state (.operation (.delete blockId element))
      (state.delete blockId element intervalGap) := by
  have sourceValid := valid.2 block (List.mem_of_getElem? found)
  apply state.delete_step blockId block element intervalGap valid found shrinking member
  · change IsSegment (block.elements.erase element) _
    rw [delete_attachedTopDown blockId block element intervalGap found member valid.allElements_nodup]
    exact sourceValid.isSegment.erase ((state.view.topDown_nodup _ _).filter _) member
  · exact gapValid
  · intro id different
    let other := state.blocks.get id
    have otherValid := valid.2 other (List.get_mem _ id)
    have otherFound : state.blocks[id.val]? = some other := by simp [other]
    have notOther : element ∉ other.elements := by
      intro otherMember
      exact different (valid.blockId_eq_of_element_mem found member otherFound otherMember)
    refine ⟨?_, otherValid.2⟩
    rw [delete_attachedTopDown blockId block element intervalGap found member valid.allElements_nodup]
    exact otherValid.isSegment.erase_ambient_of_not_mem notOther

/-- The recomputed source gap always exists; deletion never requires splitting
or atomizing the source. -/
theorem exists_delete_step {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) {blockId : Interface.BlockId} {block : Block n}
    (found : state.blocks[blockId]? = some block) (shrinking : block.mode = .shrinking)
    (element : Element n) (member : element ∈ block.elements) :
    ∃ intervalGap, Step params state (.operation (.delete blockId element))
      (state.delete blockId element intervalGap) := by
  obtain ⟨intervalGap, gapValid⟩ := Block.exists_gapValid_of_shrinking state.view
    (block.deleted element 0) shrinking
  exact ⟨intervalGap, delete_step_of_gapValid valid found shrinking element member intervalGap gapValid⟩

end State
end Splay.Lazy
