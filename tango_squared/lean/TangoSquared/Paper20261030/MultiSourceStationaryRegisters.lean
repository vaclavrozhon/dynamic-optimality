import TangoSquared.Paper20261030.MultiSourceFingerLabels

set_option autoImplicit false

/-! A controller using edge moves, reads, and writes leaves every
register it neither moves nor assigns at its original address. -/

namespace TangoSquared.Paper20261030.MultiSourceProgram

open ColoredStorage SourcePointer SourcePositions

variable {α ρ F σ : Type*} [DecidableEq F]

def Instruction.EdgeOnly : Instruction σ F ρ → Prop
  | .nav _ .rotateLeft _ | .nav _ .rotateRight _ => False
  | _ => True

theorem Step.stationary_finger (finger : F) {source : Program σ F ρ}
    {state next : σ} {before after : Configuration F α ρ} {entry}
    (step : Step source state before next after entry) (edges : (source state).EdgeOnly)
    (kept : KeepsFinger finger (source state)) : after.fingers finger = before.fingers finger := by
  cases step with
  | readNone | readSome | write => rfl
  | @nav moved position current target action next instruction present reached advance =>
    simp only [instruction,KeepsFinger] at kept
    simp only [instruction] at edges
    cases action <;> try contradiction
    all_goals simp only [moveResult,Function.update_of_ne kept,transport,Option.map_id,id_eq]
  | copy instruction =>
    simp only [instruction,KeepsFinger] at kept
    exact Function.update_of_ne kept _ _

theorem Run.stationary_finger (finger : F) {source : Program σ F ρ}
    (safe : ∀ state, (source state).EdgeOnly ∧ KeepsFinger finger (source state))
    {state last : σ} {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost) : after.fingers finger = before.fingers finger := by
  induction run with
  | halt => rfl
  | next first rest ih => exact ih.trans (first.stationary_finger finger (safe _).1 (safe _).2)

end TangoSquared.Paper20261030.MultiSourceProgram
