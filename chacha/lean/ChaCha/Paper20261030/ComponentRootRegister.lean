import ChaCha.Paper20261030.LocalComponentSecondaryAccess

/-! Reading the logical root identifier from the compiler's own scalar
state at a source-root boundary. No physical-tree observation or guessed
identifier is used by the header-cache continuation.
-/

namespace ChaCha.Paper20261030.LocalComponentForestCompiler

variable {σ α ρ ι η C : Type*}

def rootRegister : State σ α ρ ι η C → Option η
  | .ready (.ready (.ready _ id)) => some id
  | _ => none

theorem rootRegister_ready (state : σ) (id : η) :
    rootRegister (ready (α := α) (ρ := ρ) (ι := ι) (C := C) state id) = some id := rfl

end ChaCha.Paper20261030.LocalComponentForestCompiler
