import ChaCha.Paper20261030.LocalComponentJoin
import ChaCha.Paper20261030.LocalRootMarker

/-! Executable reconstruction of exposed head-switch fragments.
The inner join restores the boundary and tail. If a prefix is present,
the outer join attaches it. The final root is closed. Both joins read
their existing separators; no remembered split history or target tree
is available to the program. All input fragment cores are open.
-/

namespace ChaCha.Paper20261030.BoundaryObservations.HeadRestoreController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage SourcePointer Auxiliary AuxiliaryComponent SourceLocalProgram GapSource.Controller

variable {α κ ρ : Type*} [Ord κ]

abbrev JoinState (κ ρ : Type*) := MarkedCutController.JoinState κ ρ

inductive State (κ ρ : Type*) where
  | start
  | inner (phase : JoinState κ ρ)
  | goUp
  | outer (phase : JoinState κ ρ)
  | closing (phase : RootMarkerController.State κ ρ)
  | done

def initial (prefixPresent : Bool) : State κ ρ :=
  if prefixPresent then .start else .inner (.ready (.observing 0 (.read 3 [])))

def afterInner (prefixPresent : Bool) : JoinState κ ρ → State κ ρ
  | .ready (.returning 0) => if prefixPresent then .goUp else .closing .start
  | phase => .inner phase

def afterOuter : JoinState κ ρ → State κ ρ
  | .ready (.returning 0) => .closing .start
  | phase => .outer phase

def afterClose : RootMarkerController.State κ ρ → State κ ρ
  | .done => .done
  | phase => .closing phase

def program (prefixPresent : Bool) : Program (State κ ρ) (MarkedRecord κ ρ)
  | .start => .nav .right (.inner (.ready (.observing 0 (.read 3 []))))
  | .inner phase => (code JoinController.program phase).mapState (afterInner prefixPresent)
  | .goUp => .nav .up (.outer (.ready (.observing 0 (.read 3 []))))
  | .outer phase => (code JoinController.program phase).mapState afterOuter
  | .closing phase => (RootMarkerController.program true false phase).mapState afterClose
  | .done => .halt

theorem inner_code (prefixPresent : Bool) (phase : JoinState κ ρ)
    (active : code JoinController.program phase ≠ .halt) :
    program prefixPresent (afterInner prefixPresent phase) =
      (code JoinController.program phase).mapState (afterInner prefixPresent) := by
  cases phase with
  | ready phase => cases phase with
    | returning depth => cases depth with
      | zero => exact False.elim (active rfl)
      | succ => rfl
    | observing | turn | descend | refresh | balancing => rfl
  | reading | writing | error => rfl

theorem outer_code (prefixPresent : Bool) (phase : JoinState κ ρ)
    (active : code JoinController.program phase ≠ .halt) :
    program prefixPresent (afterOuter phase) = (code JoinController.program phase).mapState afterOuter := by
  cases phase with
  | ready phase => cases phase with
    | returning depth => cases depth with
      | zero => exact False.elim (active rfl)
      | succ => rfl
    | observing | turn | descend | refresh | balancing => rfl
  | reading | writing | error => rfl

theorem close_code (prefixPresent : Bool) (phase : RootMarkerController.State κ ρ)
    (active : RootMarkerController.program true false phase ≠ .halt) :
    program prefixPresent (afterClose phase) = (RootMarkerController.program true false phase).mapState afterClose := by
  cases phase with
  | start | write => rfl
  | done => exact False.elim (active rfl)

theorem tail (right : AuxiliaryComponent α κ (fun _ => ρ×Bool))
    (clean : Clean right.core) (marked : MarkedPorts right)
    (key : κ) (value : ρ×Bool) (unmarked : value.2 = false)
    (port : Source α (MarkedRecord κ ρ)) (portMarked : entry port.rootRecord = true) (old : Nat) (outside) :
    ∃ reads cost, Run (program false) (initial false) ⟨.fork (old,⟨key,value⟩) port right.tree,outside⟩ .done
      ⟨closed (prepend key value port right),outside⟩ reads cost ∧
      cost ≤ 2100*Nat.clog 2 (right.core.size+1)+310 := by
  obtain ⟨reads,cost,run,bounded⟩ := CleanController.prepend right clean marked key value unmarked port portMarked old outside
  have joined := run.map_prefix (afterInner false) (inner_code false)
  have close := (RootMarkerController.close_component (prepend key value port right) outside).map_prefix
    (target := program false) afterClose (close_code false)
  exact ⟨_,_,joined.then_run (close.run rfl),by omega⟩

theorem active (headPart tail : AuxiliaryComponent α κ (fun _ => ρ×Bool))
    (prefixClean : Clean headPart.core) (tailClean : Clean tail.core)
    (prefixMarked : MarkedPorts headPart) (tailMarked : MarkedPorts tail)
    (low high : κ) (lowValue highValue : ρ×Bool)
    (lowUnmarked : lowValue.2 = false) (highUnmarked : highValue.2 = false)
    (port : Source α (MarkedRecord κ ρ)) (portMarked : entry port.rootRecord = true)
    (oldLow oldHigh : Nat) (outside) :
    ∃ reads cost, Run (program true) (initial true)
      ⟨.fork (oldLow,⟨low,lowValue⟩) headPart.tree (.fork (oldHigh,⟨high,highValue⟩) port tail.tree),outside⟩ .done
      ⟨closed (AuxiliaryComponent.join low lowValue headPart (prepend high highValue port tail)),outside⟩ reads cost ∧
      cost ≤ 2100*(Nat.clog 2 (tail.core.size+1)+Nat.clog 2 (headPart.core.size+1)+Nat.clog 2 (tail.core.size+2))+620 := by
  let restored := prepend high highValue port tail
  let lowRecord : MarkedRecord κ ρ := (oldLow,⟨low,lowValue⟩)
  let highRecord : MarkedRecord κ ρ := (oldHigh,⟨high,highValue⟩)
  obtain ⟨firstReads,firstCost,firstRun,firstBound⟩ := CleanController.prepend tail tailClean tailMarked high highValue highUnmarked port portMarked
    oldHigh (.right headPart.tree lowRecord::outside)
  obtain ⟨lastReads,lastCost,lastRun,lastBound⟩ := CleanController.join_components headPart restored prefixClean
    (clean_prepend high highValue highUnmarked port tail tailClean) prefixMarked
    (marked_prepend high highValue port portMarked tail tailMarked) low lowValue lowUnmarked oldLow outside
  have down : Step (program true) .start ⟨.fork lowRecord headPart.tree (.fork highRecord port tail.tree),outside⟩
      (.inner (.ready (.observing 0 (.read 3 [])))) ⟨.fork highRecord port tail.tree,.right headPart.tree lowRecord::outside⟩ none := .nav rfl rfl
  have up : Step (program true) .goUp ⟨restored.tree,.right headPart.tree lowRecord::outside⟩
      (.outer (.ready (.observing 0 (.read 3 [])))) ⟨.fork lowRecord headPart.tree restored.tree,outside⟩ none := .nav rfl rfl
  have close := (RootMarkerController.close_component (AuxiliaryComponent.join low lowValue headPart restored) outside).map_prefix
    (target := program true) afterClose (close_code true)
  have second := (lastRun.map_prefix afterOuter (outer_code true)).then_run (close.run rfl)
  have full := Run.next down ((firstRun.map_prefix (afterInner true) (inner_code true)).then_run (.next up second))
  refine ⟨_,_,full,?_⟩
  dsimp only [restored] at lastBound
  rw [prepend_size,show tail.core.size+1+1 = tail.core.size+2 by omega] at lastBound
  omega

end ChaCha.Paper20261030.BoundaryObservations.HeadRestoreController
