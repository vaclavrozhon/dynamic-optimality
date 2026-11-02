import ChaCha.Paper20261030.ImmutableStructuralCompiler

/-! Additional record storage in the structural compiler. Each state
retains one source continuation and at most three extra application
records. Structural identifiers, fixed-color masks, and the finite
program counter are separate scalar data. This does not replace the
application's reachable-state bounds or the bounds on identifier bits.
-/

namespace ChaCha.Paper20261030.Structural

variable {σ ρ ι C : Type*}

def ParentController.workingRecords : ParentController.State ρ ι C → Nat
  | .writeParent _ _ => 1
  | _ => 0

theorem ParentController.working_records (state : ParentController.State ρ ι C) :
    ParentController.workingRecords state ≤ 1 := by
  cases state <;> simp only [ParentController.workingRecords] <;> omega

def WriteController.workingRecords : WriteController.State ρ ι C → Nat
  | .writeRoot _ _ | .writeLeft _ | .writeRight _ => 1
  | _ => 0

theorem WriteController.working_records (state : WriteController.State ρ ι C) :
    WriteController.workingRecords state ≤ 1 := by
  cases state <;> simp only [WriteController.workingRecords] <;> omega

def ContextController.workingRecords (kernel : σ → Nat) : ContextController.State σ ρ ι C → Nat
  | .start | .done => 0
  | .running _ state => kernel state
  | .parent _ _ state => ParentController.workingRecords state

theorem ContextController.working_records (kernel : σ → Nat) (bound : Nat)
    (positive : 1 ≤ bound) (bounded : ∀ state, kernel state ≤ bound)
    (state : ContextController.State σ ρ ι C) : ContextController.workingRecords kernel state ≤ bound := by
  cases state with
  | start | done => exact Nat.zero_le _
  | running old state => exact bounded state
  | parent old fresh state => exact (ParentController.working_records state).trans positive

def Compiler.continuation : Compiler.State σ ρ ι C → σ
  | .ready state => state
  | .rotating _ next _ | .writing _ next _ => next

def Compiler.workingRecords (source : σ → Nat) : Compiler.State σ ρ ι C → Nat
  | .ready state => source state
  | .rotating _ next phase => source next + ContextController.workingRecords RotationController.workingRecords phase
  | .writing _ next phase => source next + 1 + ContextController.workingRecords WriteController.workingRecords phase

theorem Compiler.extra_records (source : σ → Nat) (state : Compiler.State σ ρ ι C) :
    Compiler.workingRecords source state ≤ source (Compiler.continuation state)+2 := by
  cases state with
  | ready state => simp only [workingRecords,continuation]; omega
  | rotating right next phase =>
    have bound := ContextController.working_records RotationController.workingRecords 2 (by omega)
      RotationController.working_records phase
    simp only [workingRecords,continuation]
    omega
  | writing fresh next phase =>
    have bound := ContextController.working_records WriteController.workingRecords 1 le_rfl
      WriteController.working_records phase
    simp only [workingRecords,continuation]
    omega

end ChaCha.Paper20261030.Structural

namespace ChaCha.Paper20261030.ImmutableSource

variable {σ ρ ι : Type*}

def continuation : State σ ρ ι → σ
  | .ready state => state
  | .writing _ _ next => next

def workingRecords (source : σ → Nat) : State σ ρ ι → Nat
  | .ready state => source state
  | .writing _ _ next => source next+1

theorem extra_records (source : σ → Nat) (state : State σ ρ ι) :
    workingRecords source state ≤ source (continuation state)+1 := by
  cases state <;> simp only [workingRecords,continuation] <;> omega

end ChaCha.Paper20261030.ImmutableSource

namespace ChaCha.Paper20261030.ImmutableStructural

variable {σ ρ ι C : Type*}

def continuation (state : State σ ρ ι C) : σ :=
  ImmutableSource.continuation (Structural.Compiler.continuation state)

def workingRecords (source : σ → Nat) (state : State σ ρ ι C) : Nat :=
  Structural.Compiler.workingRecords (ImmutableSource.workingRecords source) state

theorem extra_records (source : σ → Nat) (state : State σ ρ ι C) :
    workingRecords source state ≤ source (continuation state)+3 := by
  have structural := Structural.Compiler.extra_records (ImmutableSource.workingRecords source) state
  have immutable := ImmutableSource.extra_records source (Structural.Compiler.continuation state)
  unfold workingRecords continuation
  omega

end ChaCha.Paper20261030.ImmutableStructural
