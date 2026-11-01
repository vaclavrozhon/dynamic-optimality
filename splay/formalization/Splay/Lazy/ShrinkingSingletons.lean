import Splay.Lazy.BlockRefinement
import Splay.Lazy.IsolatedRankUpdate

namespace Splay.Lazy.State

/-- Every occurrence of a selected element is a shrinking singleton.
The heap root may be selected without requiring a nonexistent residence. -/
def ShrinkingSingletons {n : ℕ} (state : State n) (selected : Finset (Element n)) : Prop :=
  ∀ element ∈ selected, ∀ block ∈ state.blocks, element ∈ block.elements →
    block.mode = .shrinking ∧ block.elements = [element]

namespace ShrinkingSingletons

theorem of_residences {n : ℕ} {params : Interface.Parameters} {state : State n}
    {selected : Finset (Element n)} (valid : state.Valid params)
    (residences : ∀ element ∈ selected, element ∈ state.allElements →
      ∃ (id : Interface.BlockId) (block : Block n), state.blocks[id]? = some block ∧ block.mode = .shrinking ∧ block.elements = [element]) :
    state.ShrinkingSingletons selected := by
  intro element marked other member inside
  obtain ⟨id, block, found, shrinking, singleton⟩ :=
    residences element marked (mem_allElements_iff.mpr ⟨other, member, inside⟩)
  obtain ⟨otherId, otherFound⟩ := List.mem_iff_getElem?.mp member
  have equal := valid.blockId_eq_of_element_mem found (by simp [singleton]) otherFound inside
  rw [← equal, found] at otherFound
  cases Option.some.inj otherFound
  exact ⟨shrinking, singleton⟩

/-- A refinement preserves singleton payloads; preservation of actual
growing blocks rules out changing such a singleton back to growing mode. -/
theorem refine {n : ℕ} {before after : State n} {selected : Finset (Element n)}
    (singletons : before.ShrinkingSingletons selected)
    (refines : before.BlockRefinement after)
    (growings : ∀ block ∈ after.blocks, block.mode = .growing → block ∈ before.blocks) :
    after.ShrinkingSingletons selected := by
  intro element marked block member inside
  obtain ⟨old, oldMember, _, _, sublist⟩ := refines block member
  have oldSingleton := singletons element marked old oldMember (sublist.mem inside)
  have singleton : block.elements = [element] := by
    rw [oldSingleton.2] at sublist
    rcases List.sublist_singleton.mp sublist with empty | singleton
    · simp [empty] at inside
    · exact singleton
  refine ⟨?_, singleton⟩
  cases mode : block.mode with
  | shrinking => rfl
  | growing =>
      have impossible := (singletons element marked block (growings block member mode) inside).1
      rw [mode] at impossible
      contradiction

/-- Preserving each old shrinking block at its identifier preserves every
singleton it contains, using final disjointness to identify any occurrence. -/
theorem of_shrinking_frame {n : ℕ} {params : Interface.Parameters} {before after : State n}
    {selected : Finset (Element n)} (singletons : before.ShrinkingSingletons selected)
    (complete : before.Complete) (valid : after.Valid params) (sameView : after.view = before.view)
    (frame : ∀ (id : Interface.BlockId) (block : Block n), before.blocks[id]? = some block → block.mode = .shrinking →
      after.blocks[id]? = some block) : after.ShrinkingSingletons selected := by
  apply of_residences valid
  intro element marked assigned
  have parented : after.view.parent element ≠ none := by
    obtain ⟨block, member, inside⟩ := mem_allElements_iff.mp assigned
    rw [(valid.2 block member).parent_eq inside]
    simp
  have beforeAssigned : element ∈ before.allElements := (complete element).mpr (sameView ▸ parented)
  obtain ⟨block, member, inside⟩ := mem_allElements_iff.mp beforeAssigned
  obtain ⟨id, found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨shrinking, singleton⟩ := singletons element marked block member inside
  exact ⟨id, block, frame id block found shrinking, shrinking, singleton⟩

end ShrinkingSingletons

theorem IsolatedRanks.refine {n : ℕ} {before after : State n} {selected : Finset (Element n)}
    (isolated : before.IsolatedRanks selected) (refines : before.BlockRefinement after)
    (growings : ∀ block ∈ after.blocks, block.mode = .growing → block ∈ before.blocks) :
    after.IsolatedRanks selected :=
  ⟨fun block member growing marked => isolated.growingEmpty block (growings block member growing) growing marked,
    ShrinkingSingletons.refine isolated.singleton refines growings⟩

end Splay.Lazy.State
