import ChaCha.Paper20261030.GapBSTNavigationProgram
import ChaCha.Paper20261030.SourceLocalProgram
import DynamicOptimality.LocalProgramComposition

/-! A uniform compiler from source-local controllers to ordinary-BST-local
controllers. The additional state consists of a logical slot flag and the
fixed-size working records of one gap-encoding primitive. No subtree or
source cursor is stored in the controller state. -/

namespace ChaCha.Paper20261030.GapBST.Controller

open ColoredStorage Storage DynamicOptimality

variable {α ρ σ : Type*}

inductive State (σ ρ : Type*) where
  | ready (source : σ) (slot : Flag)
  | navigation (next : σ) (action : Navigation) (phase : NavigationState)
  | rotation (next : σ) (right : Bool) (phase : RotationState ρ)
  | writing (next : σ) (slot : Flag) (fresh : ρ) (phase : WriteState ρ)
  | error

def finishNavigation (next : σ) (action : Navigation) : NavigationState → State σ ρ
  | .done slot => .ready next slot
  | phase => .navigation next action phase

def finishRotation (next : σ) (right : Bool) : RotationState ρ → State σ ρ
  | .done => .ready next .internal
  | phase => .rotation next right phase

def finishWrite (next : σ) (slot : Flag) (fresh : ρ) : WriteState ρ → State σ ρ
  | .done => .ready next slot
  | phase => .writing next slot fresh phase

def leafFlag : Flag → Bool
  | .internal => false
  | _ => true

def startNavigation (next : σ) (slot : Flag) (action : Navigation) :
    LocalProgram.Instruction (State σ ρ) α (Slots ρ) :=
  (navigationProgram action (.start slot)).mapState (finishNavigation next action)

def startRotation (next : σ) (right : Bool) : LocalProgram.Instruction (State σ ρ) α (Slots ρ) :=
  (rotationProgram right .start).mapState (finishRotation next right)

def startMove (next : σ) (slot : Flag) : LocalProgram.Move → LocalProgram.Instruction (State σ ρ) α (Slots ρ)
  | .left => startNavigation next slot .left
  | .right => startNavigation next slot .right
  | .up => startNavigation next slot .up
  | .rotateRight => startRotation next true
  | .rotateLeft => startRotation next false

def code (source : SourceLocalProgram.Program σ ρ) : LocalProgram.Program (State σ ρ) α (Slots ρ)
  | .ready state slot => match source state with
    | .halt => .halt
    | .read next => .read (fun view => match slot.get view.entry.2.2 with
      | none => .error
      | some value => .ready (next value (leafFlag slot)) slot)
    | .nav move next => startMove next slot move
    | .write fresh next => (writeProgram fresh (.start slot)).mapState (finishWrite next slot fresh)
  | .navigation next action phase => (navigationProgram action phase).mapState (finishNavigation next action)
  | .rotation next right phase => (rotationProgram right phase).mapState (finishRotation next right)
  | .writing next slot fresh phase => (writeProgram fresh phase).mapState (finishWrite next slot fresh)
  | .error => .halt

theorem navigation_code (source : SourceLocalProgram.Program σ ρ) (next : σ) (action : Navigation)
    (phase : NavigationState) (active : navigationProgram (α := α) (ρ := ρ) action phase ≠ .halt) :
    code (α := α) source (finishNavigation next action phase) =
      (navigationProgram action phase).mapState (finishNavigation next action) := by
  cases phase with
  | start => rfl
  | move => rfl
  | done => simp [navigationProgram] at active

theorem rotation_code (source : SourceLocalProgram.Program σ ρ) (next : σ) (right : Bool)
    (phase : RotationState ρ) (active : rotationProgram (α := α) right phase ≠ .halt) :
    code (α := α) source (finishRotation next right phase) =
      (rotationProgram right phase).mapState (finishRotation next right) := by
  cases phase <;> first | rfl | simp [rotationProgram] at active

theorem write_code (source : SourceLocalProgram.Program σ ρ) (next : σ) (slot : Flag) (fresh : ρ)
    (phase : WriteState ρ) (active : writeProgram (α := α) fresh phase ≠ .halt) :
    code (α := α) source (finishWrite next slot fresh phase) =
      (writeProgram fresh phase).mapState (finishWrite next slot fresh) := by
  cases phase with
  | start => rfl
  | write => rfl
  | done => simp [writeProgram] at active

theorem flag_isLeaf (logical : SourcePointer.Cursor α ρ) :
    leafFlag (flag logical) = SourceLocalProgram.isLeaf logical.focus := by
  rcases logical with ⟨focus,rest⟩
  cases focus with
  | fork => rfl
  | leaf => cases rest with
    | nil => rfl
    | cons first rest => cases first <;> rfl

end ChaCha.Paper20261030.GapBST.Controller
