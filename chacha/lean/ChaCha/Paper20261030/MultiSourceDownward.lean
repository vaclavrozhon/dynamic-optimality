import ChaCha.Paper20261030.MultiSourceComposition

/-! A local program executing a specified list of downward finger moves.
The evaluator below is proof-side semantics, not a tree-observation
instruction. Component entry uses schedules of at most five directions,
determined by two wing-presence bits.
-/

namespace ChaCha.Paper20261030.MultiSourceDownward

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram

variable {α ρ F : Type*} [DecidableEq F]

abbrev Schedule (F : Type*) := List (F × Bool)

def program : Program (Schedule F) F ρ
  | [] => .halt
  | (finger,right)::rest => .nav finger (if right then .right else .left) rest

def execute (config : Configuration F α ρ) : Schedule F → Option (Configuration F α ρ)
  | [] => some config
  | (finger,right)::rest => (config.fingers finger).bind fun position =>
      (locate config.tree position).bind fun current =>
      (SourceLocalProgram.navigate (if right then .right else .left) current).bind fun next =>
      execute (moveResult config finger (if right then .right else .left) current next) rest

theorem execute_run (schedule : Schedule F) (before after : Configuration F α ρ)
    (evaluated : execute before schedule = some after) : Run program schedule before [] after [] schedule.length := by
  induction schedule generalizing before with
  | nil =>
    cases Option.some.inj evaluated
    exact .halt rfl
  | cons first rest ih =>
    rcases first with ⟨finger,right⟩
    cases position : before.fingers finger with
    | none => simp only [execute,position,Option.bind_none,reduceCtorEq] at evaluated
    | some pos => cases located : locate before.tree pos with
      | none => simp only [execute,position,located,Option.bind_some,Option.bind_none,reduceCtorEq] at evaluated
      | some current => cases moved : SourceLocalProgram.navigate (if right then .right else .left) current with
        | none => simp only [execute,position,located,moved,Option.bind_some,Option.bind_none,reduceCtorEq] at evaluated
        | some next =>
          have tailRun := ih _ (by simpa only [execute,position,located,moved,Option.bind_some] using evaluated)
          exact .next (.nav (program := program) (state := (finger,right)::rest) (next := rest) rfl position located moved) tailRun

end ChaCha.Paper20261030.MultiSourceDownward
