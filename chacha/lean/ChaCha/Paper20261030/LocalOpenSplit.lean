import ChaCha.Paper20261030.LocalMarkedCutProgram

/-! Opening a marked component and exposing one stored separator.
Every marker change uses an actual read and write. The output consists
of the existing exact split fragments with their cores left open.
-/

namespace ChaCha.Paper20261030.BoundaryObservations.OpenSplitController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary AuxiliaryComponent SourceLocalProgram
open GapSource.Controller

variable {α κ ρ : Type*} [Ord κ]

abbrev SplitState (κ ρ : Type*) := MarkedCutController.SplitState κ ρ

inductive State (κ ρ : Type*) where
  | start
  | writeOpen (record : MarkedRecord κ ρ)
  | splitting (phase : SplitState κ ρ)
  | done

def afterSplit : SplitState κ ρ → State κ ρ
  | .ready (.returning 0) => .done
  | phase => .splitting phase

def program (key : κ) : Program (State κ ρ) (MarkedRecord κ ρ)
  | .start => .read (fun record _ => .writeOpen (tag false record))
  | .writeOpen record => .write record (.splitting (.ready (.search 0)))
  | .splitting phase => (code (SplitController.program key) phase).mapState afterSplit
  | .done => .halt

theorem splitting_code (key : κ) (phase : SplitState κ ρ)
    (active : code (SplitController.program key) phase ≠ .halt) :
    program key (afterSplit phase) = (code (SplitController.program key) phase).mapState afterSplit := by
  cases phase with
  | ready phase => cases phase with
    | returning depth => cases depth with
      | zero => exact False.elim (active rfl)
      | succ => rfl
    | search | descend | parent | turn | enter | joining | up | write => rfl
  | reading | writing | error => rfl

theorem split [LawfulEqOrd κ] (component : AuxiliaryComponent α κ (fun _ => ρ×Bool))
    (clean : Clean component.core) (marked : MarkedPorts component)
    (key : κ) (found : searchResult key component.core = true) (outside) :
    ∃ reads cost, Run (program key) .start ⟨closed component,outside⟩ .done
      ⟨.fork (component.core.size,⟨key,(splitAt key component.core component.balanced found).value⟩)
        (cutLeft component key found).tree (cutRight component key found).tree,outside⟩ reads cost ∧
      cost ≤ 40110*Nat.clog 2 (component.core.size+1)+2 := by
  have nonempty : component.core ≠ .leaf := by intro empty; simp only [empty,searchResult,Bool.false_eq_true] at found
  have first : Step (program key) .start ⟨closed component,outside⟩
      (.writeOpen (tag false (closed component).rootRecord)) ⟨closed component,outside⟩
      (some (closed component).rootRecord) :=
    .read (next := fun record _ => State.writeOpen (tag false record)) rfl
  have second : Step (program key) (.writeOpen (tag false (closed component).rootRecord)) ⟨closed component,outside⟩
      (.splitting (.ready (.search 0))) ⟨component.tree,outside⟩ none := by
    rw [← MarkedCutController.open_root component clean nonempty]
    exact .write rfl
  obtain ⟨reads,cost,run,bounded⟩ := CleanController.split component clean marked key found outside
  have rest := run.map_prefix afterSplit (splitting_code key)
  exact ⟨_,cost+2,.next first (.next second (rest.run rfl)),by omega⟩

end ChaCha.Paper20261030.BoundaryObservations.OpenSplitController
