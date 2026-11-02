import DynamicOptimality.SingleFinger.SourceDequePop

/-! The unchanged final hanging subtree of a source deque. This subtree is
retained while its cells are transferred into an adjacent deque. -/

namespace DynamicOptimality.SingleFinger.SourceDeque

open ChaCha.Paper20261030 ColoredStorage SourceSpine

variable {α ρ : Type*}

def trailing (gap : Source α ρ) : List (Cell α ρ) → Source α ρ
  | [] => gap
  | (_,nextGap)::rest => trailing nextGap rest

def Layout.terminal (layout : Layout α ρ) : Source α ρ := trailing layout.gap layout.cells

theorem trailing_independent (first last : Source α ρ) {cells : List (Cell α ρ)}
    (nonempty : cells ≠ []) : trailing first cells = trailing last cells := by
  cases cells with
  | nil => exact False.elim (nonempty rfl)
  | cons cell cells => cases cell; rfl

theorem Layout.cells_nonempty (layout : Layout α ρ) : layout.cells ≠ [] := by
  simp [Layout.cells]

theorem terminal_of_pop {before after : Layout α ρ} {entry : ρ}
    (cells : before.cells = (entry,after.gap)::after.cells) : before.terminal = after.terminal := by
  simp only [Layout.terminal,cells,trailing]

end DynamicOptimality.SingleFinger.SourceDeque
