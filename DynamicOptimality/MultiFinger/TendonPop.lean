import DynamicOptimality.MultiFinger.TendonParametric
import DynamicOptimality.MultiFinger.TendonInitialization

/-! Literal pops at either end of either source half-tendon.
All hanging subtrees in the returned queue match the remaining source
cells exactly. The unchanged open endpoint can be substituted later.
-/

namespace DynamicOptimality.MultiFinger.TendonContents

open ChaCha.MTR SingleFinger SearchRotation
open DynamicOptimality.GeometricOnlineSimulation.OpenDeque
open TendonSource TendonDeque

variable {α : Type*}

theorem afterCells_length (cells : List (LowCell α)) (inside : RawTree α) :
    (afterCells cells inside).length = cells.length := by
  induction cells <;> simp_all [afterCells]

theorem trailing_afterCells (cells : List (LowCell α)) (inside : RawTree α) :
    trailing (firstGap cells inside) (afterCells cells inside) = inside := by
  induction cells with
  | nil => rfl
  | cons cell cells ih => cases cell; exact ih

theorem high_pop_min (layout : Left α) {key : α} {gap : RawTree α} {rest : List (HighCell α)}
    (valid : HighValid layout ((key,gap)::rest)) (nonempty : rest ≠ []) (inside : RawTree α) :
    ∃ (after : Left α) (count : Nat), HighValid after rest ∧
      Rotations (layout.fill inside).tree (.node inside key (after.fill gap).tree) count ∧
      count+after.potential ≤ layout.potential+14 := by
  have enough : 2 ≤ (layout.fill inside).cells.length := by
    rw [valid inside,List.length_cons]
    have positive := List.length_pos_iff.mpr nonempty
    omega
  obtain ⟨remaining,popped,count,cells,actual,paid⟩ := MultiFinger.Deque.pop_min (layout.fill inside) enough
  rw [valid inside] at cells
  have head := (List.cons.inj cells).1
  have tail := (List.cons.inj cells).2
  have keyEq : key = popped := congrArg Prod.fst head
  have gapEq : gap = remaining.gap := congrArg Prod.snd head
  let after := asLeft remaining
  have filled : after.fill gap = remaining := by rw [gapEq]; exact asLeft_fill _
  refine ⟨after,count,HighValid.of_filled after rest gap ?_,?_,?_⟩
  · rw [filled]; exact tail.symm
  · have first : (layout.fill inside).gap = inside := rfl
    simpa only [filled,keyEq,first] using actual
  · simpa only [after,asLeft_potential,Left.fill_potential] using paid

theorem high_pop_max (layout : Left α) {key : α} {gap : RawTree α} {rest : List (HighCell α)}
    (valid : HighValid layout (rest++[(key,gap)])) (nonempty : rest ≠ []) (inside : RawTree α) :
    ∃ (after : Left α) (count : Nat), HighValid after rest ∧
      Rotations (layout.fill inside).tree (.node (after.fill inside).tree key gap) count ∧
      count+after.potential ≤ layout.potential+14 := by
  have enough : 2 ≤ (layout.fill inside).cells.length := by
    rw [valid inside,List.length_append]
    have positive := List.length_pos_iff.mpr nonempty
    simp only [List.length_cons,List.length_nil]
    omega
  obtain ⟨remaining,popped,lastGap,count,cells,sameGap,actual,paid⟩ := MultiFinger.Deque.pop_max (layout.fill inside) enough
  rw [valid inside] at cells
  obtain ⟨tail,last⟩ := List.append_inj' cells (by simp)
  have head : (key,gap) = (popped,lastGap) := by simpa using last
  have keyEq : key = popped := congrArg Prod.fst head
  have gapEq : gap = lastGap := congrArg Prod.snd head
  let after := asLeft remaining
  have initial : remaining.gap = inside := sameGap
  have filled : after.fill inside = remaining := by rw [← initial]; exact asLeft_fill _
  refine ⟨after,count,HighValid.of_filled after rest inside ?_,?_,?_⟩
  · rw [filled]; exact tail.symm
  · simpa only [filled,keyEq,gapEq] using actual
  · simpa only [after,asLeft_potential,Left.fill_potential] using paid

theorem low_pop_min (layout : Right α) {key : α} {gap : RawTree α} {rest : List (LowCell α)}
    (valid : LowValid layout ((gap,key)::rest)) (nonempty : rest ≠ []) (inside : RawTree α) :
    ∃ (after : Right α) (count : Nat), LowValid after rest ∧
      Rotations (layout.fill inside).tree (.node gap key (after.fill inside).tree) count ∧
      count+after.potential ≤ layout.potential+14 := by
  have enough : 2 ≤ (layout.fill inside).cells.length := by
    rw [(valid inside).2,afterCells_length,List.length_cons]
    have positive := List.length_pos_iff.mpr nonempty
    omega
  obtain ⟨remaining,popped,count,cells,actual,paid⟩ := MultiFinger.Deque.pop_min (layout.fill inside) enough
  have last := terminal_pop_min cells
  rw [right_terminal] at last
  rw [(valid inside).2] at cells
  change (key,firstGap rest inside)::afterCells rest inside = (popped,remaining.gap)::remaining.cells at cells
  have head := (List.cons.inj cells).1
  have tail := (List.cons.inj cells).2
  have keyEq : key = popped := congrArg Prod.fst head
  have gapEq : firstGap rest inside = remaining.gap := congrArg Prod.snd head
  obtain ⟨after,filled,potential⟩ := open_right remaining
  rw [← last] at filled
  refine ⟨after,count,LowValid.of_filled after rest nonempty inside ?_ ?_,?_,?_⟩
  · rw [filled]; exact gapEq.symm
  · rw [filled]; exact tail.symm
  · simpa only [filled,keyEq,(valid inside).1,firstGap] using actual
  · simpa only [potential,Right.fill_potential] using paid

theorem low_pop_max (layout : Right α) {key : α} {gap : RawTree α} {rest : List (LowCell α)}
    (valid : LowValid layout (rest++[(gap,key)])) (nonempty : rest ≠ []) (inside : RawTree α) :
    ∃ (after : Right α) (count : Nat), LowValid after rest ∧
      Rotations (layout.fill inside).tree (.node (after.fill gap).tree key inside) count ∧
      count+after.potential ≤ layout.potential+14 := by
  have enough : 2 ≤ (layout.fill inside).cells.length := by
    rw [(valid inside).2,afterCells_length,List.length_append]
    have positive := List.length_pos_iff.mpr nonempty
    simp only [List.length_cons,List.length_nil]
    omega
  obtain ⟨remaining,popped,lastGap,count,cells,sameGap,actual,paid⟩ := MultiFinger.Deque.pop_max (layout.fill inside) enough
  rw [(valid inside).2,afterCells_append_singleton] at cells
  obtain ⟨tail,last⟩ := List.append_inj' cells (by simp)
  have head : (key,inside) = (popped,lastGap) := by simpa using last
  have keyEq : key = popped := congrArg Prod.fst head
  have lastEq : inside = lastGap := congrArg Prod.snd head
  have first : remaining.gap = firstGap rest gap := by
    rw [sameGap,(valid inside).1,firstGap_append_singleton]
  have term : terminal remaining = gap := by
    rw [terminal,first,← tail,trailing_afterCells]
  obtain ⟨after,filled,potential⟩ := open_right remaining
  rw [term] at filled
  refine ⟨after,count,LowValid.of_filled after rest nonempty gap ?_ ?_,?_,?_⟩
  · rw [filled]; exact first
  · rw [filled]; exact tail.symm
  · simpa only [filled,keyEq,lastEq] using actual
  · simpa only [potential,Right.fill_potential] using paid

end DynamicOptimality.MultiFinger.TendonContents
