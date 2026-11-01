import Splay.Lazy.TwoSideTransfer

namespace Splay.Lazy.Block

@[simp] theorem sideTransferred_side {n : ℕ} (view : HeapView n)
    (source boundary : Element n) (side : Side) (block : Block n) :
    (block.sideTransferred view source boundary side).side = block.side := by
  unfold sideTransferred
  split
  next selected => exact selected.2.2.1.symm
  next => rfl

@[simp] theorem sideTransferred_passCount {n : ℕ} (view : HeapView n)
    (source boundary : Element n) (side : Side) (block : Block n) :
    (block.sideTransferred view source boundary side).passCount = block.passCount := by
  unfold sideTransferred
  split <;> rfl

@[simp] theorem sideTransferred_creator {n : ℕ} (view : HeapView n)
    (source boundary : Element n) (side : Side) (block : Block n) :
    (block.sideTransferred view source boundary side).creator = block.creator := by
  unfold sideTransferred
  split <;> rfl

theorem twoSideTransferred_owner {n : ℕ} (firstView secondView : HeapView n)
    (source left right : Element n) (block : Block n) :
    let next := (block.sideTransferred firstView source left .left).sideTransferred secondView source right .right
    next.owner = block.owner ∨
      block.owner = source ∧ next.owner = (match next.side with | .left => left | .right => right) := by
  classical
  dsimp only
  by_cases leftSelected : block.SelectedForSideTransfer source left .left
  · have firstEq : block.sideTransferred firstView source left .left =
        block.transferred left .left ((firstView.rank source : ℤ) - firstView.rank left) := by
      simp only [sideTransferred, if_pos leftSelected]
    have notRight : ¬ (block.sideTransferred firstView source left .left).SelectedForSideTransfer source right .right := by
      intro selected
      have sides := selected.2.2.1
      rw [sideTransferred_side, leftSelected.2.2.1] at sides
      contradiction
    rw [sideTransferred, if_neg notRight, firstEq]
    exact Or.inr ⟨leftSelected.2.1, rfl⟩
  · have firstEq : block.sideTransferred firstView source left .left = block := by
      simp only [sideTransferred, if_neg leftSelected]
    rw [firstEq]
    by_cases rightSelected : block.SelectedForSideTransfer source right .right
    · rw [sideTransferred, if_pos rightSelected]
      exact Or.inr ⟨rightSelected.2.1, rfl⟩
    · rw [sideTransferred, if_neg rightSelected]
      exact Or.inl rfl

end Splay.Lazy.Block

namespace Splay.Lazy.State

/-- Whole-side transfers preserve physical identity, payload, creator,
mode and pass count. The only new owners are the selected boundaries. -/
theorem transferBothSides_block_origin {n : ℕ} (state : State n) {source left right : Element n}
    (first : SideTransferGeometry state.view source left .left)
    (second : SideTransferGeometry state.view source right .right) (ordered : state.view.HeapOrdered)
    {id : Interface.BlockId} {next : Block n}
    (found : (state.transferBothSides first second ordered).blocks[id]? = some next) :
    ∃ old : Block n, state.blocks[id]? = some old ∧ next.elements = old.elements ∧
      next.side = old.side ∧ next.mode = old.mode ∧ next.passCount = old.passCount ∧ next.creator = old.creator ∧
      (next.owner = old.owner ∨ old.owner = source ∧
        next.owner = match next.side with | .left => left | .right => right) := by
  change ((state.blocks.map (Block.sideTransferred state.view source left .left)).map
    (Block.sideTransferred _ source right .right))[id]? = some next at found
  rw [List.getElem?_map, List.getElem?_map] at found
  obtain ⟨middle, middleFound, nextEq⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨old, oldFound, middleEq⟩ := Option.map_eq_some_iff.mp middleFound
  subst middle
  subst next
  exact ⟨old, oldFound, by simp, by simp, by simp, by simp, by simp,
    old.twoSideTransferred_owner _ _ source left right⟩

end Splay.Lazy.State
