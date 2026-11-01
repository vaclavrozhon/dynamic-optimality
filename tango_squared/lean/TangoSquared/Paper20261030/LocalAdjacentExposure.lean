import TangoSquared.Paper20261030.LocalOpenSplit
import TangoSquared.Paper20261030.AdjacentExposure

/-! Two actual local splits expose adjacent separators. Both retained
fragments stay open for subsequent joins. Every port interior stays
untouched, and the middle tree is the exact old gap.
-/

namespace TangoSquared.Paper20261030.BoundaryObservations.AdjacentExposureController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage SourcePointer Auxiliary AuxiliaryComponent SourceLocalProgram
open GapSource.Controller

variable {α ρ : Type*}

inductive State (ρ : Type*) where
  | first (phase : OpenSplitController.State Nat ρ)
  | goRight
  | second (phase : OpenSplitController.SplitState Nat ρ)
  | goUp
  | done

def afterFirst : OpenSplitController.State Nat ρ → State ρ
  | .done => .goRight
  | phase => .first phase

def afterSecond : OpenSplitController.SplitState Nat ρ → State ρ
  | .ready (.returning 0) => .goUp
  | phase => .second phase

def program (low : Nat) : Program (State ρ) (MarkedRecord Nat ρ)
  | .first phase => (OpenSplitController.program low phase).mapState afterFirst
  | .goRight => .nav .right (.second (.ready (.search 0)))
  | .second phase => (code (SplitController.program (low+1)) phase).mapState afterSecond
  | .goUp => .nav .up .done
  | .done => .halt

theorem first_code (low : Nat) (phase : OpenSplitController.State Nat ρ)
    (active : OpenSplitController.program low phase ≠ .halt) :
    program low (afterFirst phase) = (OpenSplitController.program low phase).mapState afterFirst := by
  cases phase with
  | start | writeOpen | splitting => rfl
  | done => exact False.elim (active rfl)

theorem second_code (low : Nat) (phase : OpenSplitController.SplitState Nat ρ)
    (active : code (SplitController.program (low+1)) phase ≠ .halt) :
    program low (afterSecond phase) = (code (SplitController.program (low+1)) phase).mapState afterSecond := by
  cases phase with
  | ready phase => cases phase with
    | returning depth => cases depth with
      | zero => exact False.elim (active rfl)
      | succ => rfl
    | search | descend | parent | turn | enter | joining | up | write => rfl
  | reading | writing | error => rfl

theorem expose (component : AuxiliaryComponent α Nat (fun _ => ρ×Bool)) (ordered : component.core.Ordered)
    (clean : Clean component.core) (marked : MarkedPorts component) (low : Nat)
    (firstFound : searchResult low component.core = true)
    (secondFound : searchResult (low+1) (cutRight component low firstFound).core = true) (outside) :
    ∃ reads cost, Run (program low) (.first .start) ⟨closed component,outside⟩ .done
      ⟨.fork (component.core.size,⟨low,(splitAt low component.core component.balanced firstFound).value⟩)
        (cutLeft component low firstFound).tree
        (.fork ((cutRight component low firstFound).core.size,
          ⟨low+1,(splitAt (low+1) (cutRight component low firstFound).core
            (cutRight component low firstFound).balanced secondFound).value⟩)
          (component.ports (gapIndex (low+1) component.core))
          (cutRight (cutRight component low firstFound) (low+1) secondFound).tree),outside⟩ reads cost ∧
      cost ≤ 80220*Nat.clog 2 (component.core.size+1)+4 := by
  let lowRecord : MarkedRecord Nat ρ := (component.core.size,⟨low,(splitAt low component.core component.balanced firstFound).value⟩)
  let left := cutLeft component low firstFound
  let right := cutRight component low firstFound
  obtain ⟨firstReads,firstCost,firstRun,firstBound⟩ := OpenSplitController.split component clean marked low firstFound outside
  obtain ⟨secondReads,secondCost,secondRun,secondBound⟩ := CleanController.split right
    (clean_split component clean low firstFound).2.2 (marked_cutRight component marked low firstFound)
    (low+1) secondFound (.right left.tree lowRecord::outside)
  have mid := adjacent_middle_port component ordered low firstFound secondFound
  rw [mid] at secondRun
  let highRecord : MarkedRecord Nat ρ := (right.core.size,⟨low+1,(splitAt (low+1) right.core right.balanced secondFound).value⟩)
  let highTree := Source.fork highRecord (component.ports (gapIndex (low+1) component.core))
    (cutRight right (low+1) secondFound).tree
  have down : Step (program low) .goRight ⟨.fork lowRecord left.tree right.tree,outside⟩
      (.second (.ready (.search 0))) ⟨right.tree,.right left.tree lowRecord::outside⟩ none := .nav rfl rfl
  have up : Step (program low) .goUp ⟨highTree,.right left.tree lowRecord::outside⟩
      .done ⟨.fork lowRecord left.tree highTree,outside⟩ none := .nav rfl rfl
  have finalRun := (firstRun.map_prefix afterFirst (first_code low)).then_run
    (.next down ((secondRun.map_prefix afterSecond (second_code low)).then_run (.next up (.halt rfl))))
  have smaller := Nat.clog_monotone 2 (Nat.add_le_add_right (cutRight_size_le component low firstFound) 1)
  exact ⟨_,_,finalRun,by dsimp only [right] at secondBound; omega⟩

end TangoSquared.Paper20261030.BoundaryObservations.AdjacentExposureController
