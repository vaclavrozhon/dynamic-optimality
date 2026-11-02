import ChaCha.Paper20261030.SourceProgramComposition

/-! A source program can run inside an unchanged enclosing context. The
controller and all observed records remain the same; only the inaccessible
outer ancestor suffix is appended to each actual cursor. -/

namespace ChaCha.Paper20261030.SourceLocalProgram

open ColoredStorage SourcePointer
open DynamicOptimality.LocalProgram (Move)

variable {α ρ σ : Type*}

theorem navigate_extend {action : Move} {before after : Cursor α ρ}
    (moved : navigate action before = some after) (outside : List (Frame α ρ)) :
    navigate action (before.extend outside) = some (after.extend outside) := by
  rcases before with ⟨focus,rest⟩
  cases action with
  | left => cases focus with
    | leaf => simp [navigate] at moved
    | fork => cases Option.some.inj moved; rfl
  | right => cases focus with
    | leaf => simp [navigate] at moved
    | fork => cases Option.some.inj moved; rfl
  | up => cases rest with
    | nil => simp [navigate] at moved
    | cons first rest => cases first with
      | left => cases Option.some.inj moved; rfl
      | right => cases Option.some.inj moved; rfl
  | rotateRight => cases focus with
    | leaf => simp [navigate] at moved
    | fork record left right => cases left with
      | leaf => simp [navigate] at moved
      | fork => cases Option.some.inj moved; rfl
  | rotateLeft => cases focus with
    | leaf => simp [navigate] at moved
    | fork record left right => cases right with
      | leaf => simp [navigate] at moved
      | fork => cases Option.some.inj moved; rfl

theorem Step.extend {program : Program σ ρ} {state next : σ} {before after : Cursor α ρ} {entry}
    (step : Step program state before next after entry) (outside : List (Frame α ρ)) :
    Step program state (before.extend outside) next (after.extend outside) entry := by
  cases step with
  | read instruction => exact .read instruction
  | nav instruction moved => exact .nav instruction (navigate_extend moved outside)
  | write instruction => exact .write instruction

theorem Run.extend {program : Program σ ρ} {state last : σ} {before after : Cursor α ρ} {reads cost}
    (run : Run program state before last after reads cost) (outside : List (Frame α ρ)) :
    Run program state (before.extend outside) last (after.extend outside) reads cost := by
  induction run with
  | halt stopped => exact .halt stopped
  | next first rest ih => exact .next (first.extend outside) ih

end ChaCha.Paper20261030.SourceLocalProgram
