import ChaCha.Paper20261030.GapSourceWriteProgram

/-! Compilation of a local auxiliary controller into the existing source
language with marked gap payloads. No auxiliary tree is stored in the
controller. The only temporary data are a current root record, two child
marker bits, or one pending record update. -/

namespace ChaCha.Paper20261030.GapSource.Controller

open ColoredStorage SourcePointer SourceLocalProgram Auxiliary DynamicOptimality

variable {κ ρ σ : Type*}

inductive State (σ κ ρ : Type*) where
  | ready (state : σ)
  | reading (state : σ) (phase : ReadState κ ρ)
  | writing (next : σ) (phase : WriteState κ ρ)
  | error

def finishRead (source : LocalProgram.Program σ κ ρ) (state : σ) : ReadState κ ρ → State σ κ ρ
  | .done view => match source state with | .read next => .ready (next view) | _ => .error
  | phase => .reading state phase

def finishWrite (next : σ) : WriteState κ ρ → State σ κ ρ
  | .done => .ready next
  | phase => .writing next phase

def code (source : LocalProgram.Program σ κ ρ) : Program (State σ κ ρ) (MarkedRecord κ ρ)
  | .ready state => match source state with
    | .halt => .halt
    | .read _ => (readProgram .start).mapState (finishRead source state)
    | .nav action next => .nav action (.ready next)
    | .write fresh next => (writeProgram (.start (.value fresh))).mapState (finishWrite next)
    | .writeSize fresh next => (writeProgram (.start (.size fresh))).mapState (finishWrite next)
  | .reading state phase => (readProgram phase).mapState (finishRead source state)
  | .writing next phase => (writeProgram phase).mapState (finishWrite next)
  | .error => .halt

theorem read_code (source : LocalProgram.Program σ κ ρ) (state : σ) (phase : ReadState κ ρ)
    (active : readProgram phase ≠ .halt) :
    code source (finishRead source state phase) = (readProgram phase).mapState (finishRead source state) := by
  cases phase with
  | done => exact False.elim (active rfl)
  | start | left | readLeft | upLeft | right | readRight | upRight => rfl

theorem write_code (source : LocalProgram.Program σ κ ρ) (next : σ) (phase : WriteState κ ρ)
    (active : writeProgram phase ≠ .halt) :
    code source (finishWrite next phase) = (writeProgram phase).mapState (finishWrite next) := by
  cases phase with
  | done => exact False.elim (active rfl)
  | start | write => rfl

end ChaCha.Paper20261030.GapSource.Controller
