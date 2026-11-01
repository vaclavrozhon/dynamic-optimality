import TangoSquared.Paper20261030.MultiSourceWriteLabels

set_option autoImplicit false

/-! Finite prefixes of shared-tree runs with checked write labels. -/

namespace TangoSquared.Paper20261030.MultiSourceWriteLabels

open MultiSourceProgram

variable {α ρ ι F σ : Type*} [DecidableEq F]

inductive Steps (label : ρ → ι) (program : Program σ F ρ) :
    σ → Configuration F α ρ → σ → Configuration F α ρ → List (F × ρ) → Nat → Prop
  | nil (state config) : Steps label program state config state config [] 0
  | next {state middle last before current after entry reads cost}
      (first : Step program state before middle current entry)
      (stable : Stable label (program state) before)
      (rest : Steps label program middle current last after reads cost) :
      Steps label program state before last after (entry.toList++reads) (cost+1)

theorem Steps.then_run {label : ρ → ι} {source : Program σ F ρ} {state middle last : σ}
    {before current after : Configuration F α ρ} {firstReads lastReads firstCost lastCost}
    (front : Steps label source state before middle current firstReads firstCost)
    (back : Run label source middle current last after lastReads lastCost) :
    Run label source state before last after (firstReads++lastReads) (firstCost+lastCost) := by
  induction front with
  | nil => simpa only [List.nil_append,Nat.zero_add] using back
  | next first stable rest ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using Run.next first stable (ih back)

end TangoSquared.Paper20261030.MultiSourceWriteLabels

namespace TangoSquared.Paper20261030.MultiSourceProgram

variable {α ρ ι F σ : Type*} [DecidableEq F]

theorem Step.label_prefix {label : ρ → ι} {source : Program σ F ρ} {state next : σ}
    {before after : Configuration F α ρ} {entry}
    (step : Step source state before next after entry)
    (stable : MultiSourceWriteLabels.Stable label (source state) before) :
    MultiSourceWriteLabels.Steps label source state before next after entry.toList 1 := by
  simpa only [List.append_nil] using MultiSourceWriteLabels.Steps.next step stable (.nil next after)

end TangoSquared.Paper20261030.MultiSourceProgram
