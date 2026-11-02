import DynamicOptimality.MultiFinger.TendonContents

/-! Replacing the open subtree does not change a queue's stored cells.
These lemmas recover an open-tendon invariant from one actual closed deque
returned by the physical endpoint algorithm. No uniform choice of algorithm
witnesses over all possible inner subtrees is required. -/

namespace DynamicOptimality.MultiFinger.TendonContents

open ChaCha.MTR SingleFinger
open DynamicOptimality.GeometricOnlineSimulation.OpenDeque
open TendonSource

variable {α : Type*}

def replaceTerminal : List (Spine.Cell α) → RawTree α → List (Spine.Cell α)
  | [], _ => []
  | [(key,_)], inside => [(key,inside)]
  | cell::next::cells, inside => cell::replaceTerminal (next::cells) inside

theorem replaceTerminal_append (front : List (Spine.Cell α)) (key : α)
    (old inside : RawTree α) :
    replaceTerminal (front++[(key,old)]) inside = front++[(key,inside)] := by
  induction front with
  | nil => rfl
  | cons cell front ih =>
    cases front with
    | nil => cases cell; rfl
    | cons next front => simpa only [List.cons_append,replaceTerminal] using congrArg (cell::·) ih

theorem right_cells_replace (layout : Right α) (old inside : RawTree α) :
    replaceTerminal (layout.fill old).cells inside = (layout.fill inside).cells := by
  cases layout with
  | mk gap front pivot back =>
    cases back with
    | none => simpa only [Right.fill,SingleFinger.Deque.Layout.cells] using replaceTerminal_append front pivot old inside
    | some data =>
      rcases data with ⟨afterGap,back,last⟩
      simpa only [Right.fill,SingleFinger.Deque.Layout.cells,List.append_assoc,List.cons_append] using
        replaceTerminal_append (front++(pivot,afterGap)::back) last old inside

theorem right_gap_same (layout : Right α) (old inside : RawTree α) :
    (layout.fill inside).gap = (layout.fill old).gap := by
  cases layout with
  | mk gap front pivot back => cases back <;> rfl

theorem afterCells_replace (cells : List (LowCell α)) (old inside : RawTree α) :
    replaceTerminal (afterCells cells old) inside = afterCells cells inside := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
    cases cell
    cases cells with
    | nil => rfl
    | cons next cells =>
      simpa only [afterCells,firstGap,replaceTerminal] using congrArg ((_ , _)::·) ih

/-- One exact filled layout determines all future substitutions at the
open end, including the exact original hanging subtrees. -/
theorem LowValid.of_filled (layout : Right α) (cells : List (LowCell α))
    (nonempty : cells ≠ []) (inside : RawTree α)
    (gap : (layout.fill inside).gap = firstGap cells inside)
    (entries : (layout.fill inside).cells = afterCells cells inside) : LowValid layout cells := by
  intro other
  constructor
  · rw [right_gap_same layout inside other,gap]
    cases cells with
    | nil => exact (nonempty rfl).elim
    | cons cell cells => rfl
  · rw [← right_cells_replace layout inside other,entries,afterCells_replace]

theorem HighValid.of_filled (layout : Left α) (cells : List (HighCell α))
    (inside : RawTree α) (entries : (layout.fill inside).cells = cells) : HighValid layout cells := by
  intro other
  exact entries

end DynamicOptimality.MultiFinger.TendonContents
