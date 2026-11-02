import DynamicOptimality.SingleFinger.SourceOpenDeque
import DynamicOptimality.SingleFinger.SourceOpenLeftDeque
import DynamicOptimality.SingleFinger.SourceDequeTerminal

/-! Exact ghost output of repeated endpoint insertion. These functions are
used only in representation theorems. The executable catenation controllers
receive four integer counters, never these source cells or hanging subtrees.
-/

namespace DynamicOptimality.SingleFinger.SourceOpenDeque

open ChaCha.Paper20261030 ColoredStorage SourceSpine

variable {α ρ : Type*}

def Right.absorb (outer : Right α ρ) (gap : Source α ρ) : List (Cell α ρ) → Right α ρ
  | [] => outer
  | (entry,nextGap)::rest => (outer.append gap entry).absorb nextGap rest

theorem Right.append_backLength (outer : Right α ρ) (gap : Source α ρ) (entry : ρ) :
    (outer.append gap entry).backLength = outer.backLength+1 := by
  cases outer with | mk first front pivot back => cases back <;>
    simp [Right.append,Right.backLength,List.length_append]

theorem Right.absorb_front (outer : Right α ρ) (gap : Source α ρ) (cells : List (Cell α ρ)) :
    (outer.absorb gap cells).front = outer.front := by
  induction cells generalizing outer gap with
  | nil => rfl
  | cons cell cells ih => exact ih (outer.append gap cell.1) cell.2

theorem Right.absorb_backLength (outer : Right α ρ) (gap : Source α ρ) (cells : List (Cell α ρ)) :
    (outer.absorb gap cells).backLength = outer.backLength+cells.length := by
  induction cells generalizing outer gap with
  | nil => simp [Right.absorb]
  | cons cell cells ih =>
    simp only [Right.absorb,ih,Right.append_backLength,List.length_cons]
    omega

theorem Right.absorb_cells (outer : Right α ρ) (gap : Source α ρ) (cells : List (Cell α ρ)) :
    ((outer.absorb gap cells).fill (SourceDeque.trailing gap cells)).cells =
      (outer.fill gap).cells++cells := by
  induction cells generalizing outer gap with
  | nil => simp [Right.absorb,SourceDeque.trailing]
  | cons cell cells ih =>
    rcases cell with ⟨entry,nextGap⟩
    rw [Right.absorb,SourceDeque.trailing,ih,Right.append_fill]
    simp only [SourceDeque.pushMaxLayout,SourceDeque.Layout.cells,
      List.append_assoc,List.cons_append,List.singleton_append,List.nil_append]

def Left.absorb (outer : Left α ρ) (cells : List (Cell α ρ)) : Left α ρ :=
  { outer with front := cells++outer.front }

theorem Left.absorb_append (outer : Left α ρ) (cells : List (Cell α ρ))
    (entry : ρ) (gap : Source α ρ) :
    outer.absorb (cells++[(entry,gap)]) = (outer.prepend gap entry).absorb cells := by
  simp only [Left.absorb,Left.prepend,List.append_assoc,List.singleton_append]

theorem Left.absorb_cells (outer : Left α ρ) (gap : Source α ρ) (cells : List (Cell α ρ)) :
    ((outer.absorb cells).fill gap).cells = cells++(outer.fill gap).cells := by
  simp only [Left.absorb,Left.fill,SourceDeque.Layout.cells,List.append_assoc]

end DynamicOptimality.SingleFinger.SourceOpenDeque
