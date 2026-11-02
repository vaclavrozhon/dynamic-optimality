import ChaCha.Paper20261030.MultiSourceAugment
import ChaCha.Paper20261030.MultiSourceService

/-! Calling a local program with parameters acquired by an actual read.
Only the reached record determines the dispatched parameters. The caller
does not supply a proof-side tree, cursor, or decoded header at runtime.
-/

namespace ChaCha.Paper20261030.MultiSourceReadDispatch

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram

variable {α ρ F σ π : Type*} [DecidableEq F]

inductive State (π σ : Type*) where
  | start
  | running (parameters : π) (phase : σ)
  | blocked

def next (decode : ρ → Option π) (initial : π → σ) : View ρ → State π σ
  | none => .blocked
  | some (record,_) => match decode record with
    | none => .blocked
    | some parameters => .running parameters (initial parameters)

def program (finger : F) (decode : ρ → Option π) (initial : π → σ) (source : π → Program σ F ρ) :
    Program (State π σ) F ρ
  | .start => .read finger (next decode initial)
  | .running parameters phase => (source parameters phase).mapState (State.running parameters)
  | .blocked => .halt

theorem dispatch (finger : F) (decode : ρ → Option π) (initial : π → σ) (source : π → Program σ F ρ)
    (config : Configuration F α ρ) (position : List Bool) (current : Cursor α ρ)
    (present : config.fingers finger = some position) (reached : locate config.tree position = some current)
    (parameters : π) (decoded : decode current.focus.rootRecord = some parameters)
    {last : σ} {target : Configuration F α ρ} {reads cost}
    (run : Run (source parameters) (initial parameters) config last target reads cost) :
    Run (program finger decode initial source) .start config (.running parameters last) target
      ((finger,current.focus.rootRecord)::reads) (cost+1) := by
  have first : Step (program finger decode initial source) .start config
      (.running parameters (initial parameters)) config (some (finger,current.focus.rootRecord)) := by
    simpa only [next,decoded] using
      Step.readSome (program := program finger decode initial source) (state := .start)
        (next := next decode initial) rfl present reached
  have rest := run.map_prefix (target := program finger decode initial source) (State.running parameters) (fun _ _ => rfl)
  have halted : program finger decode initial source (.running parameters last) = .halt := by
    have stopped : source parameters last = .halt := run.halted
    simp only [program,stopped,Instruction.mapState]
  exact .next first (rest.run halted)

end ChaCha.Paper20261030.MultiSourceReadDispatch
