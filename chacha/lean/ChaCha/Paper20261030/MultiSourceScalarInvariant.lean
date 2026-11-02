import ChaCha.Paper20261030.MultiSourceMask

set_option autoImplicit false

/-! Scalar state invariants and unchanged presence bits. -/

namespace ChaCha.Paper20261030.MultiSourceProgram

variable {α ρ κ F σ : Type*} [DecidableEq F]

def Instruction.Preserves (value : σ → κ) (state : σ) : Instruction σ F ρ → Prop
  | .halt => True
  | .read _ next => ∀ observed, value (next observed) = value state
  | .nav _ _ next | .write _ _ next | .copy _ _ next => value next = value state

theorem Step.scalar (value : σ → κ) {source : Program σ F ρ} {state next : σ}
    {before after : Configuration F α ρ} {entry}
    (step : Step source state before next after entry) (preserved : (source state).Preserves value state) :
    value next = value state := by
  cases step with
  | readNone instruction absent => exact (instruction ▸ preserved) none
  | readSome instruction present reached => exact (instruction ▸ preserved) _
  | nav instruction present reached moved => simpa only [instruction,Instruction.Preserves] using preserved
  | write instruction present reached => simpa only [instruction,Instruction.Preserves] using preserved
  | copy instruction => simpa only [instruction,Instruction.Preserves] using preserved

theorem Run.scalar (value : σ → κ) {source : Program σ F ρ}
    (preserved : ∀ state, (source state).Preserves value state)
    {state last : σ} {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost) : value last = value state := by
  induction run with
  | halt => rfl
  | next first rest ih => exact ih.trans (first.scalar value (preserved _))

def KeepsCopy (finger : F) : Instruction σ F ρ → Prop
  | .copy destination _ _ => finger ≠ destination
  | _ => True

end ChaCha.Paper20261030.MultiSourceProgram

namespace ChaCha.Paper20261030.MultiSourceMask

open MultiSourceProgram

variable {α ρ F σ : Type*} [DecidableEq F]

theorem preserves_bit (source : Program σ F ρ) (finger : F)
    (kept : ∀ state, KeepsCopy finger (source state)) (state : State σ F) :
    (program source state).Preserves (fun state => state.1 finger) state := by
  obtain ⟨bits,state⟩ := state
  have safe := kept state
  cases code : source state with
  | halt | read | nav | write => simp [program,code,Instruction.Preserves]
  | copy destination origin next =>
    simp only [code,KeepsCopy] at safe
    simp only [program,code,Instruction.Preserves]
    exact Function.update_of_ne safe _ _

theorem Run.bit (source : Program σ F ρ) (finger : F)
    (kept : ∀ state, KeepsCopy finger (source state))
    {bits finalBits : F → Bool} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : MultiSourceProgram.Run (program source) (bits,state) before (finalBits,last) after reads cost) :
    finalBits finger = bits finger :=
  run.scalar (fun state => state.1 finger) (preserves_bit source finger kept)

end ChaCha.Paper20261030.MultiSourceMask
