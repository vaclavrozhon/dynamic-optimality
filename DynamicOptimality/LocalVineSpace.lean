import DynamicOptimality.LocalVineInitialization
import DynamicOptimality.LocalProgramSize

/-! The initialization sweep's sole counter is the actual cursor depth.
It is at most the number of physical vertices throughout every execution
prefix, so it has only `n+1` possible values on an `n`-vertex input. -/

namespace DynamicOptimality.LocalVineInitialization

open TangoSquared.MTR
open TangoSquared.Paper20261030.Auxiliary
open LocalProgram

variable {α ρ : Type*}

def State.depth : State → Nat
  | .scan depth | .rotate depth | .down depth | .up depth => depth

theorem step_depth {state next : State} {before after : Metadata.Cursor α (fun _ => ρ)} {entry}
    (step : Step program state before next after entry)
    (aligned : state.depth = before.ancestors.length) : next.depth = after.ancestors.length := by
  cases step with
  | @read next cursor view instruction observed =>
    cases state with
    | scan depth =>
      simp only [program,Instruction.read.injEq] at instruction
      rw [← instruction]
      dsimp only
      split
      · split <;> simpa [State.depth] using aligned
      · simpa [State.depth] using aligned
    | rotate | down => simp [program] at instruction
    | up depth => cases depth <;> simp [program] at instruction
  | @nav next before after action instruction moved =>
    have depthChange := navigate_depth moved
    cases state with
    | scan => simp [program] at instruction
    | rotate depth =>
      simp only [program,Instruction.nav.injEq] at instruction
      obtain ⟨rfl,rfl⟩ := instruction
      simp only [State.depth] at aligned ⊢
      exact aligned.trans depthChange.symm
    | down depth =>
      simp only [program,Instruction.nav.injEq] at instruction
      obtain ⟨rfl,rfl⟩ := instruction
      simp only [State.depth] at aligned ⊢
      omega
    | up depth =>
      cases depth with
      | zero => simp [program] at instruction
      | succ depth =>
        simp only [program,Instruction.nav.injEq] at instruction
        obtain ⟨rfl,rfl⟩ := instruction
        simp only [State.depth] at aligned ⊢
        omega
  | write instruction =>
    cases state with
    | scan | rotate | down => simp [program] at instruction
    | up depth => cases depth <;> simp [program] at instruction
  | writeSize instruction =>
    cases state with
    | scan | rotate | down => simp [program] at instruction
    | up depth => cases depth <;> simp [program] at instruction

theorem prefix_depth {state last : State} {before after : Metadata.Cursor α (fun _ => ρ)} {reads cost}
    (run : Steps program state before last after reads cost) (aligned : state.depth = before.ancestors.length) :
    last.depth = after.ancestors.length := by
  induction run with
  | nil => exact aligned
  | next first rest ih => exact ih (step_depth first aligned)

theorem counter_bound (tree : RawTree (NodeRecord α (fun _ => ρ)))
    {state : State} {cursor : Metadata.Cursor α (fun _ => ρ)} {reads cost}
    (run : Steps program (.scan 0) (.atRoot tree) state cursor reads cost) : state.depth ≤ tree.size := by
  have aligned := prefix_depth run rfl
  have bound := cursor_depth_bound cursor
  have size := run.tree_size
  change tree.size = cursor.tree.size at size
  omega

end DynamicOptimality.LocalVineInitialization
