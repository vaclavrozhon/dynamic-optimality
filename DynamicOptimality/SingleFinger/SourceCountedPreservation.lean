import DynamicOptimality.SingleFinger.SourceCounted
import ChaCha.Paper20261030.SourceInorderLabels

/-! The counted kernels preserve the exact inorder word of application
records (including leaf records). This applies to every execution prefix,
not only executions obtained from the structural deque lemmas.
-/

namespace DynamicOptimality.SingleFinger.SourceCounted

open ChaCha.Paper20261030 ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ ι : Type*}

theorem nav_only (commands : Schedule) :
    code (ρ := ρ) commands = .halt ∨
      ∃ action next, code (ρ := ρ) commands = .nav action next := by
  induction commands with
  | nil => exact Or.inl rfl
  | cons head rest ih =>
    rcases head with ⟨action,count⟩
    cases count with
    | zero => exact ih
    | succ count => exact Or.inr ⟨action,prepend action count rest,rfl⟩

theorem step_inorder (label : ρ → ι) {state next : Schedule} {before after : Cursor α ρ} {entry}
    (step : Step code state before next after entry) :
    before.tree.inorderLabels label = after.tree.inorderLabels label := by
  cases step with
  | read observed =>
    rcases nav_only (ρ := ρ) state with halted | ⟨action,next,moved⟩
    · simp [observed] at halted
    · simp [observed] at moved
  | nav observed moved => exact navigate_inorderLabels label _ moved
  | write observed =>
    rcases nav_only (ρ := ρ) state with halted | ⟨action,next,moved⟩
    · simp [observed] at halted
    · simp [observed] at moved

theorem steps_inorder (label : ρ → ι) {state next : Schedule} {before after : Cursor α ρ} {reads cost}
    (run : Steps code state before next after reads cost) :
    before.tree.inorderLabels label = after.tree.inorderLabels label := by
  induction run with
  | nil => rfl
  | next first rest ih => exact (step_inorder label first).trans ih

end DynamicOptimality.SingleFinger.SourceCounted
