import ChaCha.Paper20261030.SourceProgramComposition
import ChaCha.Paper20261030.ComponentMarkers
import DynamicOptimality.LocalProgram

/-! Local observation of an auxiliary node whose empty children have been
replaced by marked port trees. The program reads both child-entry bits and
returns to the current node. It never enters either child's interior. The
bits are the existing component markers, not additional ghost labels. -/

namespace ChaCha.Paper20261030.GapSource.Controller

open ColoredStorage SourcePointer SourceLocalProgram Auxiliary

variable {α κ ρ : Type*}

abbrev Record (κ ρ : Type*) := NodeRecord κ (fun _ => ρ)
abbrev MarkedRecord (κ ρ : Type*) := NodeRecord κ (fun _ => ρ×Bool)

def mark (entry : Record κ ρ) : MarkedRecord κ ρ :=
  (entry.1,⟨entry.2.1,(entry.2.2,false)⟩)

def unmark (entry : MarkedRecord κ ρ) : Record κ ρ :=
  (entry.1,⟨entry.2.1,entry.2.2.1⟩)

def boundary (entry : MarkedRecord κ ρ) : Bool := entry.2.2.2

inductive ReadState (κ ρ : Type*) where
  | start
  | left (root : Record κ ρ)
  | readLeft (root : Record κ ρ)
  | upLeft (root : Record κ ρ) (leftEmpty : Bool)
  | right (root : Record κ ρ) (leftEmpty : Bool)
  | readRight (root : Record κ ρ) (leftEmpty : Bool)
  | upRight (root : Record κ ρ) (leftEmpty rightEmpty : Bool)
  | done (view : DynamicOptimality.LocalProgram.View κ ρ)

def readProgram : Program (ReadState κ ρ) (MarkedRecord κ ρ)
  | .start => .read (fun entry _ => .left (unmark entry))
  | .left root => .nav .left (.readLeft root)
  | .readLeft root => .read (fun entry _ => .upLeft root (boundary entry))
  | .upLeft root leftEmpty => .nav .up (.right root leftEmpty)
  | .right root leftEmpty => .nav .right (.readRight root leftEmpty)
  | .readRight root leftEmpty => .read (fun entry _ => .upRight root leftEmpty (boundary entry))
  | .upRight root leftEmpty rightEmpty => .nav .up (.done ⟨root,leftEmpty,rightEmpty⟩)
  | .done _ => .halt

theorem read_fork (entry : MarkedRecord κ ρ) (left right : Source α (MarkedRecord κ ρ)) (outside) :
    Run readProgram .start ⟨.fork entry left right,outside⟩
      (.done ⟨unmark entry,boundary left.rootRecord,boundary right.rootRecord⟩)
      ⟨.fork entry left right,outside⟩ [entry,left.rootRecord,right.rootRecord] 7 := by
  apply Run.next (entry := some entry) (cost := 6)
  · apply Step.read (next := fun entry _ => .left (unmark entry)); rfl
  · apply Run.next (entry := none) (cost := 5)
    · apply Step.nav (action := .left) <;> rfl
    · apply Run.next (entry := some left.rootRecord) (cost := 4)
      · apply Step.read (next := fun value _ => .upLeft (unmark entry) (boundary value)); rfl
      · apply Run.next (entry := none) (cost := 3)
        · apply Step.nav (action := .up) <;> rfl
        · apply Run.next (entry := none) (cost := 2)
          · apply Step.nav (action := .right) <;> rfl
          · apply Run.next (entry := some right.rootRecord) (cost := 1)
            · apply Step.read (next := fun value _ => .upRight (unmark entry) (boundary left.rootRecord) (boundary value)); rfl
            · apply Run.next (entry := none) (cost := 0)
              · apply Step.nav (action := .up) <;> rfl
              · exact .halt rfl

end ChaCha.Paper20261030.GapSource.Controller
