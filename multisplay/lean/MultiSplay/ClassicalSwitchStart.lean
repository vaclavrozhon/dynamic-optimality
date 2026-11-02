import MultiSplay.ClassicalSwitchReference

/-! # The actual component start of an emitted switch

The start depth is one after the deepest nonpreferred edge on the reference
route, or zero when the whole route is preferred. It depends on the current
state at that emission, including every preceding deeper switch.
-/

namespace MultiSplay.ClassicalSwitch

open ChaCha.Primary (Key branch)
open EndpointEncoding

theorem rootPreferred_nil (state : State) : RootPreferred state [] := by
  intro owner side direction
  cases owner <;> simp [branch] at direction

theorem rootPreferred_cons (state : State) (edge : Bool) (rest : Key) :
    RootPreferred state (edge::rest) ↔ state [] = edge ∧ RootPreferred (below state edge) rest := by
  constructor
  · intro path
    exact ⟨path.head,path.below⟩
  · rintro ⟨head,tail⟩ owner side direction
    cases owner with
    | nil =>
        have equal : edge = side := by simpa [branch] using direction
        exact head.trans equal
    | cons other owner =>
        by_cases same : other = edge
        · subst other
          exact tail owner side (by simpa [branch, List.cons_prefix_cons] using direction)
        · simp [branch, List.cons_prefix_cons, same] at direction

def startDepth (state : State) : Key → Nat
  | [] => 0
  | edge :: rest =>
      if startDepth (below state edge) rest = 0 ∧ state [] = edge then 0
      else startDepth (below state edge) rest + 1

theorem startDepth_le (state : State) (address : Key) : startDepth state address ≤ address.length := by
  induction address generalizing state with
  | nil => rfl
  | cons edge rest ih =>
      have bounded := ih (below state edge)
      simp only [startDepth, List.length_cons]
      split <;> omega

theorem startDepth_zero (state : State) (address : Key) :
    startDepth state address = 0 ↔ RootPreferred state address := by
  induction address generalizing state with
  | nil => simp [startDepth, rootPreferred_nil]
  | cons edge rest ih =>
      rw [rootPreferred_cons]
      simp [startDepth, ih, and_comm]

/-- Every genuine owner depth at or below the component start sees the actual
edge toward the emitted node. The partial lookup also states that the edge
exists; the emission itself is not treated as a proper ancestor. -/
theorem startDepth_agrees (state : State) (address : Key) (depth : Nat)
    (above : startDepth state address ≤ depth) (proper : depth < address.length) :
    address[depth]? = some (state (address.take depth)) := by
  induction address generalizing state depth with
  | nil => simp at proper
  | cons edge rest ih =>
      cases depth with
      | zero =>
          have all : RootPreferred state (edge::rest) := (startDepth_zero _ _).mp (by omega)
          simp [all.head]
      | succ depth =>
          have lower : startDepth (below state edge) rest ≤ depth := by
            simp only [startDepth] at above
            split at above <;> omega
          simpa [List.take_succ_cons, below] using
            ih (below state edge) depth lower (by simpa using proper)

theorem startDepth_suffix (state : State) (address : Key) :
    RootPreferred (restrict state (address.take (startDepth state address)))
      (address.drop (startDepth state address)) := by
  induction address generalizing state with
  | nil => exact rootPreferred_nil _
  | cons edge rest ih =>
      simp only [startDepth]
      split
      · rename_i all
        simpa only [List.take_zero, List.drop_zero, restrict] using
          (rootPreferred_cons state edge rest).mpr ⟨all.2,(startDepth_zero _ _).mp all.1⟩
      · simpa only [List.take_succ_cons, List.drop_succ_cons, restrict] using ih (below state edge)

def annotatedSchedule (state : State) (address : Key) : List (State × Key × Nat) :=
  (schedule state (actualEmissions state address)).map fun entry =>
    (entry.1,entry.2,startDepth entry.1 entry.2)

theorem annotatedSchedule_owners (state : State) (address : Key) :
    (annotatedSchedule state address).map (fun entry => entry.2.1) = actualEmissions state address := by
  simp [annotatedSchedule, List.map_map, Function.comp_def]

end MultiSplay.ClassicalSwitch
