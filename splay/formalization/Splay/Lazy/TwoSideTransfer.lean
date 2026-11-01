import Splay.Lazy.SideTransfer

namespace Splay.Lazy

namespace SideTransferGeometry

variable {n : ℕ} {view : HeapView n} {source left right : Element n}
  (first : SideTransferGeometry view source left .left)
  (second : SideTransferGeometry view source right .right)

/-- The right side keeps its entire transfer geometry while all left-side
intervals move. The parent and child orders on that side are unchanged. -/
noncomputable def afterLeft (ordered : view.HeapOrdered) :
    SideTransferGeometry (first.after ordered) source right .right where
  moved := second.moved
  decomposition := by
    rw [first.other_topDown ordered source .right (Or.inr (by decide)) (Or.inr (by decide))]
    exact second.decomposition
  ranks := second.ranks
  outermost := by
    intro element member child childMember
    rw [first.other_topDown ordered right .right (Or.inr (by decide)) (Or.inr (by decide))] at childMember
    exact second.outermost element member child childMember

end SideTransferGeometry

namespace State

variable {n : ℕ} (state : State n) {source left right : Element n}
  (first : SideTransferGeometry state.view source left .left)
  (second : SideTransferGeometry state.view source right .right)
  (ordered : state.view.HeapOrdered)

/-- The actual two-sided whole-block transfer, with a stable checkpoint
between its two silent primitive steps. -/
noncomputable def transferBothSides : State n :=
  (state.transferSide first ordered).transferSide (first.afterLeft second ordered) (first.after_ordered ordered)

@[simp]
theorem transferBothSides_blocks_length :
    (state.transferBothSides first second ordered).blocks.length = state.blocks.length := by
  simp [transferBothSides, transferSide]

@[simp]
theorem transferBothSides_value :
    (state.transferBothSides first second ordered).value = state.value := rfl

@[simp]
theorem transferBothSides_rank :
    (state.transferBothSides first second ordered).view.rank = state.view.rank := rfl

@[simp]
theorem transferBothSides_root :
    (state.transferBothSides first second ordered).view.root = state.view.root := rfl

/-- Each source side ends with exactly its original terminal boundary. -/
theorem transferBothSides_source_topDown :
    (state.transferBothSides first second ordered).view.topDown source .left = [left] ∧
      (state.transferBothSides first second ordered).view.topDown source .right = [right] := by
  constructor
  · change ((first.afterLeft second ordered).after (first.after_ordered ordered)).topDown source .left = _
    rw [(first.afterLeft second ordered).other_topDown _ source .left (Or.inr (by decide)) (Or.inr (by decide))]
    exact first.source_topDown ordered
  · exact (first.afterLeft second ordered).source_topDown (first.after_ordered ordered)

end State

namespace SideTransferGeometry

variable {n : ℕ} {params : Interface.Parameters} {state : State n} {source left right : Element n}
  (first : SideTransferGeometry state.view source left .left)
  (second : SideTransferGeometry state.view source right .right)
  (stable : state.Stable params)

include first second stable in
theorem afterLeft_emptyGrowingSlots (empty : second.EmptyGrowingSlots) :
    (first.afterLeft second stable.2.2.1).EmptyGrowingSlots
      (state := state.transferSide first stable.2.2.1) := by
  intro block member growing ownerEq sideEq
  obtain ⟨oldBlock, oldMember, rfl⟩ := List.mem_map.mp member
  have oldGrowing : oldBlock.mode = .growing := by simpa only [Block.sideTransferred_mode] using growing
  rw [Block.sideTransferred_of_growing _ _ _ _ _ oldGrowing] at ownerEq sideEq ⊢
  exact empty oldBlock oldMember oldGrowing ownerEq sideEq

include first second stable in
theorem afterLeft_isolatedBoundary (isolated : second.IsolatedBoundary) :
    (first.afterLeft second stable.2.2.1).IsolatedBoundary
      (state := state.transferSide first stable.2.2.1) := by
  intro block member inside
  obtain ⟨oldBlock, oldMember, rfl⟩ := List.mem_map.mp member
  rw [Block.sideTransferred_elements] at inside ⊢
  exact isolated oldBlock oldMember inside

include first second stable in
/-- Both whole-side transfers are constructed and checked in sequence. Every
required right-side invariant is transported through the actual left step. -/
theorem transferBothSides_trace_stable
    (leftEmpty : first.EmptyGrowingSlots) (leftIsolated : first.IsolatedBoundary)
    (rightEmpty : second.EmptyGrowingSlots) (rightIsolated : second.IsolatedBoundary) :
    Trace params state [.silent, .silent] (state.transferBothSides first second stable.2.2.1) ∧
      (state.transferBothSides first second stable.2.2.1).Stable params := by
  have firstStable := first.transferSide_stable stable leftEmpty leftIsolated
  have firstTrace := first.transferSide_trace stable leftEmpty leftIsolated
  have nextEmpty := first.afterLeft_emptyGrowingSlots second stable rightEmpty
  have nextIsolated := first.afterLeft_isolatedBoundary second stable rightIsolated
  have secondStable := (first.afterLeft second stable.2.2.1).transferSide_stable firstStable nextEmpty nextIsolated
  have secondTrace := (first.afterLeft second stable.2.2.1).transferSide_trace firstStable nextEmpty nextIsolated
  exact ⟨firstTrace.append secondTrace, secondStable⟩

end SideTransferGeometry
end Splay.Lazy
