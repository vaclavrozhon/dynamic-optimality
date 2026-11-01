import TangoSquared.Paper20261030.MultiSourceComposition

set_option autoImplicit false

/-! Shared-tree executions whose writes preserve a chosen record label
at the reached vertex. Rotations are still ordinary charged operations;
this property concerns the actual local writes, not an inventory bound. -/

namespace TangoSquared.Paper20261030.MultiSourceWriteLabels

open ColoredStorage SourcePointer MultiSourceProgram

variable {α ρ ι κ F σ : Type*} [DecidableEq F]

def Stable (label : ρ → ι) (instruction : Instruction σ F ρ) (config : Configuration F α ρ) : Prop :=
  match instruction with
  | .write finger fresh _ => ∀ position current,
      config.fingers finger = some position → SourcePositions.locate config.tree position = some current →
      label fresh = label current.focus.rootRecord
  | _ => True

inductive Run (label : ρ → ι) (program : Program σ F ρ) :
    σ → Configuration F α ρ → σ → Configuration F α ρ → List (F × ρ) → Nat → Prop
  | halt {state config} (stopped : program state = .halt) : Run label program state config state config [] 0
  | next {state middle last before current after entry reads cost}
      (first : Step program state before middle current entry)
      (stable : Stable label (program state) before)
      (rest : Run label program middle current last after reads cost) :
      Run label program state before last after (entry.toList++reads) (cost+1)

theorem Run.run {label : ρ → ι} {source : Program σ F ρ} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (checked : Run label source state before last after reads cost) :
    MultiSourceProgram.Run source state before last after reads cost := by
  induction checked with
  | halt stopped => exact .halt stopped
  | next first stable rest ih => exact .next first ih

theorem Stable.relabel {label : ρ → ι} (forget : ι → κ) {instruction : Instruction σ F ρ}
    {config : Configuration F α ρ} (stable : Stable label instruction config) :
    Stable (forget ∘ label) instruction config := by
  cases instruction with
  | write finger fresh next =>
    intro position current present reached
    exact congrArg forget (stable position current present reached)
  | halt | read | nav | copy => trivial

theorem Run.relabel {label : ρ → ι} (forget : ι → κ) {source : Program σ F ρ} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (checked : Run label source state before last after reads cost) :
    Run (forget ∘ label) source state before last after reads cost := by
  induction checked with
  | halt stopped => exact .halt stopped
  | next first stable rest ih => exact .next first (stable.relabel forget) ih

end TangoSquared.Paper20261030.MultiSourceWriteLabels
