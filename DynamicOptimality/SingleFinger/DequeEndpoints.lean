import DynamicOptimality.SingleFinger.DequeRebalance

/-! Constant-cost endpoint kernels and the nonnegative deque potential.

An endpoint entering a deque is supplied as its parent. An endpoint leaving
it becomes its parent. The cursor returns to the deque pivot. This is the
interface needed when a tendon gains or loses one skeleton vertex.

`Layout` is a ghost description, not a controller register. Its cell lists
record the inorder sequence together with the untouched hanging subtrees.
The executable routines use only the two spine-length counters.
-/

namespace DynamicOptimality.SingleFinger.Deque

open ChaCha.MTR ChaCha.Paper20261030.Auxiliary LocalProgram
open Spine Counted

variable {κ α ρ : Type*}

structure Layout (κ : Type*) where
  gap : RawTree κ
  front : List (Cell κ)
  pivot : κ
  afterGap : RawTree κ
  back : List (Cell κ)

def Layout.tree (layout : Layout κ) : RawTree κ :=
  .node (rightSpine layout.gap layout.front) layout.pivot
    (leftSpine layout.afterGap layout.back)

def Layout.cells (layout : Layout κ) : List (Cell κ) :=
  layout.front++(layout.pivot,layout.afterGap)::layout.back

def potential (front back : Nat) : Nat := 4*((front-back)+(back-front))

def Layout.potential (layout : Layout κ) : Nat := Deque.potential layout.front.length layout.back.length

@[simp] theorem potential_zero : potential 0 0 = 0 := rfl

theorem potential_push_front (front back : Nat) :
    potential (front+1) back ≤ potential front back + 4 := by unfold potential; omega

theorem potential_push_back (front back : Nat) :
    potential front (back+1) ≤ potential front back + 4 := by unfold potential; omega

theorem potential_pop_front (front back : Nat) :
    potential front back ≤ potential (front+1) back + 4 := by unfold potential; omega

theorem potential_pop_back (front back : Nat) :
    potential front back ≤ potential front (back+1) + 4 := by unfold potential; omega

def pushMinLayout (layout : Layout κ) (entry : κ) (gap : RawTree κ) : Layout κ :=
  ⟨gap,(entry,layout.gap)::layout.front,layout.pivot,layout.afterGap,layout.back⟩

def pushMaxLayout (layout : Layout κ) (entry : κ) (afterGap : RawTree κ) : Layout κ :=
  ⟨layout.gap,layout.front,layout.pivot,layout.afterGap,layout.back++[(entry,afterGap)]⟩

theorem push_min (layout : Layout (Entry α ρ)) (entry : Entry α ρ) (gap : RawTree (Entry α ρ))
    (outside : List (Pointer.Frame (Entry α ρ))) (rest : Schedule) :
    Steps code (prepend .rotateLeft 1 rest) ⟨.node gap entry layout.tree,outside⟩
      rest ⟨(pushMinLayout layout entry gap).tree,outside⟩ [] 1 := by
  apply Counted.one
  rfl

theorem push_max (layout : Layout (Entry α ρ)) (entry : Entry α ρ) (afterGap : RawTree (Entry α ρ))
    (outside : List (Pointer.Frame (Entry α ρ))) (rest : Schedule) :
    Steps code (prepend .rotateRight 1 rest) ⟨.node layout.tree entry afterGap,outside⟩
      rest ⟨(pushMaxLayout layout entry afterGap).tree,outside⟩ [] 1 := by
  apply Counted.one
  simp only [Layout.tree,pushMaxLayout,leftSpine_append,leftSpine]
  rfl

theorem push_min_amortized (layout : Layout κ) (entry : κ) (gap : RawTree κ) :
    1+(pushMinLayout layout entry gap).potential ≤ layout.potential+5 := by
  have bound := potential_push_front layout.front.length layout.back.length
  simpa only [Layout.potential,pushMinLayout,List.length_cons] using (by omega :
    1 + potential (layout.front.length+1) layout.back.length ≤
      potential layout.front.length layout.back.length+5)

theorem push_max_amortized (layout : Layout κ) (entry : κ) (gap : RawTree κ) :
    1+(pushMaxLayout layout entry gap).potential ≤ layout.potential+5 := by
  have bound := potential_push_back layout.front.length layout.back.length
  simpa only [Layout.potential,pushMaxLayout,List.length_append,List.length_singleton] using (by omega :
    1 + potential layout.front.length (layout.back.length+1) ≤
      potential layout.front.length layout.back.length+5)

def popMinFast (rest : Schedule) : Schedule := prepend .rotateRight 1 (prepend .right 1 rest)
def popMaxFast (rest : Schedule) : Schedule := prepend .rotateLeft 1 (prepend .left 1 rest)

/-- Pop when the front spine contains a cell. The minimum becomes an actual
parent; no key is deleted or copied. -/
theorem pop_min_fast (gap : RawTree (Entry α ρ)) (entry : Entry α ρ)
    (nextGap : RawTree (Entry α ρ)) (front : List (Cell (Entry α ρ)))
    (pivot : Entry α ρ) (afterGap : RawTree (Entry α ρ)) (back : List (Cell (Entry α ρ)))
    (outside : List (Pointer.Frame (Entry α ρ))) (rest : Schedule) :
    Steps code (popMinFast rest)
      ⟨(Layout.mk gap ((entry,nextGap)::front) pivot afterGap back).tree,outside⟩ rest
      ⟨(Layout.mk nextGap front pivot afterGap back).tree,.right gap entry::outside⟩ [] 2 := by
  have first := Counted.one (α := α) (ρ := ρ) (action := .rotateRight)
    (before := ⟨(Layout.mk gap ((entry,nextGap)::front) pivot afterGap back).tree,outside⟩)
    rfl (prepend .right 1 rest)
  have last := Counted.one (α := α) (ρ := ρ) (action := .right)
    (before := ⟨.node gap entry (Layout.mk nextGap front pivot afterGap back).tree,outside⟩) rfl rest
  exact first.append last

theorem pop_max_fast (gap : RawTree (Entry α ρ)) (front : List (Cell (Entry α ρ)))
    (pivot : Entry α ρ) (afterGap : RawTree (Entry α ρ)) (back : List (Cell (Entry α ρ)))
    (entry : Entry α ρ) (nextGap : RawTree (Entry α ρ))
    (outside : List (Pointer.Frame (Entry α ρ))) (rest : Schedule) :
    Steps code (popMaxFast rest)
      ⟨(Layout.mk gap front pivot afterGap (back++[(entry,nextGap)])).tree,outside⟩ rest
      ⟨(Layout.mk gap front pivot afterGap back).tree,.left entry nextGap::outside⟩ [] 2 := by
  have first := Counted.one (α := α) (ρ := ρ) (action := .rotateLeft)
    (before := ⟨.node (rightSpine gap front) pivot (.node (leftSpine afterGap back) entry nextGap),outside⟩)
    rfl (prepend .left 1 rest)
  have last := Counted.one (α := α) (ρ := ρ) (action := .left)
    (before := ⟨.node (Layout.mk gap front pivot afterGap back).tree entry nextGap,outside⟩) rfl rest
  simpa only [popMaxFast,Layout.tree,leftSpine_append,leftSpine,List.nil_append] using first.append last

theorem pop_min_fast_amortized (front back : Nat) :
    2+potential front back ≤ potential (front+1) back+6 := by
  have := potential_pop_front front back
  omega

theorem pop_max_fast_amortized (front back : Nat) :
    2+potential front back ≤ potential front (back+1)+6 := by
  have := potential_pop_back front back
  omega

/-- Splitting a nonempty list at its middle supplies a realizable balanced
layout. This is used in proofs only; the executing program needs the lengths. -/
theorem middle_split (cells : List κ) (nonempty : cells ≠ []) :
    ∃ front pivot back, cells = front++pivot::back ∧
      front.length = cells.length/2 ∧
      back.length = cells.length-1-cells.length/2 := by
  let count := cells.length/2
  have positive : 0 < cells.length := by cases cells <;> simp_all
  have smaller : count < cells.length := by dsimp [count]; omega
  have nonemptyDrop : cells.drop count ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    simp only [List.length_drop,List.length_nil] at lengths
    omega
  obtain ⟨pivot,back,equal⟩ := List.exists_cons_of_ne_nil nonemptyDrop
  refine ⟨cells.take count,pivot,back,?_,?_,?_⟩
  · simpa only [equal] using (List.take_append_drop count cells).symm
  · simp only [List.length_take]
    exact Nat.min_eq_left (by omega)
  · have lengths := congrArg List.length equal
    simp only [List.length_drop,List.length_cons] at lengths
    dsimp [count] at lengths
    omega

/-- The potential stored at an exhausted side pays for the entire concrete
rebuild and the following pop, including the final pointer move. -/
theorem depleted_min_amortized {oldBack newFront newBack : Nat}
    (sameSize : oldBack = newFront+newBack)
    (balanced : newFront ≤ newBack+1 ∧ newBack ≤ newFront+1)
    (nonempty : 0 < newFront) :
    rebuildCost 0 oldBack newFront newBack + 2 + potential (newFront-1) newBack ≤
      potential 0 oldBack + 14 := by
  have bound := rebuildCost_bound (oldFront := 0) (by omega : 0+oldBack = newFront+newBack)
  unfold potential
  omega

theorem depleted_max_amortized {oldFront newFront newBack : Nat}
    (sameSize : oldFront = newFront+newBack)
    (balanced : newFront ≤ newBack+1 ∧ newBack ≤ newFront+1)
    (nonempty : 0 < newBack) :
    rebuildCost oldFront 0 newFront newBack + 2 + potential newFront (newBack-1) ≤
      potential oldFront 0 + 14 := by
  have bound := rebuildCost_bound (oldBack := 0) (by omega : oldFront+0 = newFront+newBack)
  unfold potential
  omega

end DynamicOptimality.SingleFinger.Deque
