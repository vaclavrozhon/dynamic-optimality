import TangoSquared.Paper20261030.SourceObserverReadiness

/-! Actual acquisition of the exposed source boundary records. The
active tour reads low, high, and terminal in seven charged operations;
the sentinel tour reads high and terminal in four. Each returns to its
initial root and keeps only the two or three observed records.
-/

namespace TangoSquared.Paper20261030.BoundaryReadController

open ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ : Type*}

inductive State (ρ : Type*) where
  | start
  | descend (low : ρ)
  | readHigh (low : Option ρ)
  | descendTerminal (low : Option ρ) (high : ρ)
  | readTerminal (low : Option ρ) (high : ρ)
  | returnHigh (low : Option ρ) (high terminal : ρ)
  | returnLow (low high terminal : ρ)
  | done (low : Option ρ) (high terminal : ρ)

def program : Program (State ρ) ρ
  | .start => .read (fun record _ => .descend record)
  | .descend low => .nav .right (.readHigh (some low))
  | .readHigh low => .read (fun record _ => .descendTerminal low record)
  | .descendTerminal low high => .nav .left (.readTerminal low high)
  | .readTerminal low high => .read (fun record _ => .returnHigh low high record)
  | .returnHigh none high terminal => .nav .up (.done none high terminal)
  | .returnHigh (some low) high terminal => .nav .up (.returnLow low high terminal)
  | .returnLow low high terminal => .nav .up (.done (some low) high terminal)
  | .done _ _ _ => .halt

theorem readonly : ImmutableSource.ReadOnly (program (ρ := ρ)) := by
  intro state
  cases state <;> simp only [program,MultiSourceSingleCursor.EdgeMove]
  case returnHigh low high terminal => cases low <;> trivial

theorem active (low high terminal : ρ) (prefixTree tail : Source α ρ) (key : α) (outside) :
    Run program .start ⟨.fork low prefixTree (.fork high (.leaf key terminal) tail),outside⟩
      (.done (some low) high terminal) ⟨.fork low prefixTree (.fork high (.leaf key terminal) tail),outside⟩
      [low,high,terminal] 7 := by
  refine .next (Step.read (next := fun record _ => State.descend record) rfl) ?_
  refine .next (Step.nav (program := program) (action := .right) (next := State.readHigh (some low)) rfl rfl) ?_
  refine .next (Step.read (next := fun record _ => State.descendTerminal (some low) record) rfl) ?_
  refine .next (Step.nav (program := program) (action := .left) (next := State.readTerminal (some low) high) rfl rfl) ?_
  refine .next (Step.read (next := fun record _ => State.returnHigh (some low) high record) rfl) ?_
  refine .next (Step.nav (program := program) (action := .up) (next := State.returnLow low high terminal) rfl rfl) ?_
  exact .next (Step.nav (program := program) (action := .up) (next := State.done (some low) high terminal) rfl rfl) (.halt rfl)

theorem sentinel (high terminal : ρ) (tail : Source α ρ) (key : α) (outside) :
    Run program (.readHigh none) ⟨.fork high (.leaf key terminal) tail,outside⟩
      (.done none high terminal) ⟨.fork high (.leaf key terminal) tail,outside⟩ [high,terminal] 4 := by
  refine .next (Step.read (next := fun record _ => State.descendTerminal none record) rfl) ?_
  refine .next (Step.nav (program := program) (action := .left) (next := State.readTerminal none high) rfl rfl) ?_
  refine .next (Step.read (next := fun record _ => State.returnHigh none high record) rfl) ?_
  exact .next (Step.nav (program := program) (action := .up) (next := State.done none high terminal) rfl rfl) (.halt rfl)

def workingRecords : State ρ → Nat
  | .start => 0
  | .descend _ => 1
  | .readHigh low => low.toList.length
  | .descendTerminal low _ | .readTerminal low _ => low.toList.length+1
  | .returnHigh low _ _ | .done low _ _ => low.toList.length+2
  | .returnLow _ _ _ => 3

theorem working_records (state : State ρ) : workingRecords state ≤ 3 := by
  cases state <;> simp only [workingRecords,Option.length_toList]
  all_goals first | omega | (split <;> omega)

end TangoSquared.Paper20261030.BoundaryReadController
