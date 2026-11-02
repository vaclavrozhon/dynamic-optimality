import DynamicOptimality.MultiFinger.TendonPop

/-! Physical endpoint insertions into exact source half-tendons.
The inserted separator is an existing source key adjacent to the tendon;
these operations never add keys to the original BST universe. -/

namespace DynamicOptimality.MultiFinger.TendonContents

open ChaCha.MTR SingleFinger SearchRotation
open DynamicOptimality.GeometricOnlineSimulation.OpenDeque
open TendonSource TendonDeque

variable {α : Type*}

theorem low_push_last (layout : Right α) {cells : List (LowCell α)}
    (valid : LowValid layout cells) (gap inside : RawTree α) (key : α) :
    ∃ (after : Right α) (count : Nat), LowValid after (cells++[(gap,key)]) ∧
      Rotations (layout.fill (.node gap key inside)).tree (after.fill inside).tree count ∧
      count+after.potential ≤ layout.potential+5 := by
  obtain ⟨count,_,actual,paid⟩ := layout.append_rotations gap inside key
  exact ⟨layout.append gap key,count,valid.append gap key,actual,paid⟩

theorem high_push_first (layout : Left α) {cells : List (HighCell α)}
    (valid : HighValid layout cells) (gap inside : RawTree α) (key : α) :
    ∃ (after : Left α) (count : Nat), HighValid after ((key,gap)::cells) ∧
      Rotations (layout.fill (.node inside key gap)).tree (after.fill inside).tree count ∧
      count+after.potential ≤ layout.potential+5 := by
  obtain ⟨count,_,actual,paid⟩ := layout.prepend_rotations inside gap key
  refine ⟨layout.prepend gap key,count,?_,actual,paid⟩
  intro inner
  change (key,gap)::(layout.fill inner).cells = (key,gap)::cells
  rw [valid inner]

theorem low_push_first (layout : Right α) {cells : List (LowCell α)}
    (valid : LowValid layout cells) (gap inside : RawTree α) (key : α) :
    ∃ (after : Right α) (count : Nat), LowValid after ((gap,key)::cells) ∧
      Rotations (.node gap key (layout.fill inside).tree) (after.fill inside).tree count ∧
      count+after.potential ≤ layout.potential+5 := by
  let filled := layout.fill inside
  let pushed := SingleFinger.Deque.pushMinLayout filled key gap
  have cellsEq : pushed.cells = (key,firstGap cells inside)::afterCells cells inside := by
    simp only [pushed,SingleFinger.Deque.pushMinLayout,SingleFinger.Deque.Layout.cells,List.cons_append]
    change (key,filled.gap)::filled.cells = _
    rw [(valid inside).1,(valid inside).2]
  have term : terminal pushed = inside := by
    change trailing gap pushed.cells = inside
    rw [cellsEq,trailing,trailing_afterCells]
  obtain ⟨after,reopened,potential⟩ := open_right pushed
  rw [term] at reopened
  obtain ⟨actual,paid⟩ := MultiFinger.Deque.push_min filled key gap
  refine ⟨after,1,LowValid.of_filled after ((gap,key)::cells) (by simp) inside ?_ ?_,?_,?_⟩
  · rw [reopened]; rfl
  · rw [reopened]; exact cellsEq
  · simpa only [reopened] using actual
  · simpa only [potential,filled,Right.fill_potential] using paid

theorem high_push_last (layout : Left α) {cells : List (HighCell α)}
    (valid : HighValid layout cells) (gap inside : RawTree α) (key : α) :
    ∃ (after : Left α) (count : Nat), HighValid after (cells++[(key,gap)]) ∧
      Rotations (.node (layout.fill inside).tree key gap) (after.fill inside).tree count ∧
      count+after.potential ≤ layout.potential+5 := by
  let filled := layout.fill inside
  let pushed := SingleFinger.Deque.pushMaxLayout filled key gap
  let after := asLeft pushed
  have reopened : after.fill inside = pushed := asLeft_fill _
  have cellsEq : pushed.cells = cells++[(key,gap)] := by
    change filled.front++(filled.pivot,filled.afterGap)::(filled.back++[(key,gap)]) = _
    simpa only [SingleFinger.Deque.Layout.cells,List.append_assoc,List.cons_append] using
      congrArg (fun entries => entries++[(key,gap)]) (valid inside)
  obtain ⟨actual,paid⟩ := MultiFinger.Deque.push_max filled key gap
  refine ⟨after,1,HighValid.of_filled after (cells++[(key,gap)]) inside ?_,?_,?_⟩
  · rw [reopened]; exact cellsEq
  · simpa only [reopened] using actual
  · simpa only [after,asLeft_potential,filled,Left.fill_potential] using paid

end DynamicOptimality.MultiFinger.TendonContents
