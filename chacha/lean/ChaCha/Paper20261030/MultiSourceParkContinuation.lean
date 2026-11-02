import ChaCha.Paper20261030.CachedAnchorHandoff

set_option autoImplicit false

/-! One charged pointer copy parks a reached component root before the
working fingers are reused by a nested controller. All other fingers and
the entire stored tree are unchanged by this entry instruction. -/

namespace ChaCha.Paper20261030.MultiSourceParkContinuation

open ColoredStorage SourcePointer MultiSourceProgram

variable {α ρ F σ : Type*} [DecidableEq F]

def program (destination origin : F) (source : Program σ F ρ) (initial : σ) : Program (Option σ) F ρ
  | none => .copy destination origin (some initial)
  | some state => (source state).mapState some

theorem execute (destination origin : F) (source : Program σ F ρ) (initial last : σ)
    (before after : Configuration F α ρ) {reads cost}
    (body : Run source initial (copyResult before destination origin) last after reads cost) :
    Run (program destination origin source initial) none before (some last) after reads (cost+1) := by
  have lifted := body.map_prefix (target := program destination origin source initial) some (fun _ _ => rfl)
  exact .next (Step.copy (program := program destination origin source initial) (state := none) rfl) (lifted.run (by simp only [program,body.halted,Instruction.mapState]))

theorem parked (destination origin : F) (current : Cursor α ρ) (config : Configuration F α ρ)
    (positioned : MultiSourceSingleCursor.Represents origin current config) :
    MultiSourceSingleCursor.Represents destination current (copyResult config destination origin) :=
  ⟨positioned.1,by simpa only [copyResult,Function.update_self] using positioned.2⟩

theorem other (destination origin finger : F) (different : finger ≠ destination)
    (current : Cursor α ρ) (config : Configuration F α ρ)
    (positioned : MultiSourceSingleCursor.Represents finger current config) :
    MultiSourceSingleCursor.Represents finger current (copyResult config destination origin) :=
  ⟨positioned.1,by simpa only [copyResult,Function.update_of_ne different] using positioned.2⟩

end ChaCha.Paper20261030.MultiSourceParkContinuation
