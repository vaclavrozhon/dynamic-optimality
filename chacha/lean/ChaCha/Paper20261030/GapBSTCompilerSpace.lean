import ChaCha.Paper20261030.GapBSTCompilerCorrectness

/-! The compiler's explicit additional working storage. It keeps the
source controller's existing register state once and adds at most six
source-record values. A physical read exposes at most three more values
in its current-node view. The single cursor is part of the execution
semantics, rather than a saved subtree in the register state. -/

namespace ChaCha.Paper20261030.GapBST.Controller

open Storage

variable {σ ρ : Type*}

def State.extraRecords : State σ ρ → List ρ
  | .ready _ _ | .navigation _ _ _ | .error => []
  | .rotation _ _ phase => phase.registers.flatMap Slots.values
  | .writing _ _ fresh (.write slots) => fresh::slots.values
  | .writing _ _ fresh _ => [fresh]

theorem rotation_records (phase : RotationState ρ) : (phase.registers.flatMap Slots.values).length ≤ 6 := by
  cases phase with
  | start | rotate | done => simp [RotationState.registers]
  | descend upper | readLower upper =>
    have bound := slots_size upper
    simp only [RotationState.registers,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    omega
  | writeLower upper lower | ascend upper lower | writeUpper upper lower =>
    have upperBound := slots_size upper
    have lowerBound := slots_size lower
    simp only [RotationState.registers,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append]
    omega

theorem extra_records (state : State σ ρ) : state.extraRecords.length ≤ 6 := by
  cases state with
  | ready | navigation | error => simp [State.extraRecords]
  | rotation next right phase => exact rotation_records phase
  | writing next slot fresh phase =>
    cases phase with
    | start | done => simp [State.extraRecords]
    | write slots =>
      have bound := slots_size slots
      simp only [State.extraRecords,List.length_cons]
      omega

end ChaCha.Paper20261030.GapBST.Controller
