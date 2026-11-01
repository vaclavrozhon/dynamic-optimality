import TangoSquared.Paper20261030.CleanAuxiliaryControllers

/-! A local marked-component cut. The program opens the reached component,
exposes the requested separator, closes its right continuation, inserts the
separator into the left component, and closes the resulting prefix. All
records used for marker changes are read at the current cursor. -/

namespace TangoSquared.Paper20261030.BoundaryObservations.MarkedCutController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary AuxiliaryComponent SourceLocalProgram
open GapSource.Controller

variable {α κ ρ : Type*} [Ord κ]

abbrev SplitState (κ ρ : Type*) := GapSource.Controller.State (SplitController.State κ ρ) κ ρ
abbrev JoinState (κ ρ : Type*) := GapSource.Controller.State (JoinController.State κ ρ) κ ρ

inductive State (κ ρ : Type*) where
  | start
  | openWrite (record : MarkedRecord κ ρ)
  | splitting (state : SplitState κ ρ)
  | goRight
  | suffixRead
  | suffixWrite (record : MarkedRecord κ ρ)
  | goUp
  | joining (state : JoinState κ ρ)
  | closeRead
  | closeWrite (record : MarkedRecord κ ρ)
  | done

def splitting : SplitState κ ρ → State κ ρ
  | .ready (.returning 0) => .goRight
  | state => .splitting state

def joining : JoinState κ ρ → State κ ρ
  | .ready (.returning 0) => .closeRead
  | state => .joining state

def program (key : κ) : Program (State κ ρ) (MarkedRecord κ ρ)
  | .start => .read (fun record _ => .openWrite (tag false record))
  | .openWrite record => .write record (.splitting (.ready (.search 0)))
  | .splitting state => (code (SplitController.program key) state).mapState splitting
  | .goRight => .nav .right .suffixRead
  | .suffixRead => .read (fun record _ => .suffixWrite (tag true record))
  | .suffixWrite record => .write record .goUp
  | .goUp => .nav .up (.joining (.ready (.observing 0 (.read 3 []))))
  | .joining state => (code JoinController.program state).mapState joining
  | .closeRead => .read (fun record _ => .closeWrite (tag true record))
  | .closeWrite record => .write record .done
  | .done => .halt

theorem splitting_code (key : κ) (state : SplitState κ ρ)
    (active : code (SplitController.program key) state ≠ .halt) :
    program key (splitting state) = (code (SplitController.program key) state).mapState splitting := by
  cases state with
  | ready state => cases state with
    | returning depth => cases depth with
      | zero => exact False.elim (active rfl)
      | succ => rfl
    | search | descend | parent | turn | enter | joining | up | write => rfl
  | reading | writing | error => rfl

theorem joining_code (key : κ) (state : JoinState κ ρ)
    (active : code JoinController.program state ≠ .halt) :
    program key (joining state) = (code JoinController.program state).mapState joining := by
  cases state with
  | ready state => cases state with
    | returning depth => cases depth with
      | zero => exact False.elim (active rfl)
      | succ => rfl
    | observing | turn | descend | refresh | balancing => rfl
  | reading | writing | error => rfl

theorem open_root (component : AuxiliaryComponent α κ (fun _ => ρ×Bool))
    (clean : Clean component.core) (nonempty : component.core ≠ .leaf) :
    (closed component).setRoot (tag false (closed component).rootRecord) = component.tree := by
  have bit := open_entry component clean nonempty
  have unchanged : tag false component.tree.rootRecord = component.tree.rootRecord := by rw [← bit,tag_same]
  unfold closed
  cases shape : component.tree <;>
    simpa only [shape,Source.setRoot,Source.rootRecord,tag_tag] using
      congrArg (fun record => component.tree.setRoot record) unchanged

theorem open_prefix (key : κ) (component : AuxiliaryComponent α κ (fun _ => ρ×Bool))
    (clean : Clean component.core) (nonempty : component.core ≠ .leaf) (outside) :
    Steps (program key) .start ⟨closed component,outside⟩ (.splitting (.ready (.search 0)))
      ⟨component.tree,outside⟩ [(closed component).rootRecord] 2 := by
  have read : Step (program key) .start ⟨closed component,outside⟩
      (.openWrite (tag false (closed component).rootRecord)) ⟨closed component,outside⟩
      (some (closed component).rootRecord) := by
    apply Step.read (next := fun record _ => State.openWrite (tag false record)); rfl
  have write : Step (program key) (.openWrite (tag false (closed component).rootRecord))
      ⟨closed component,outside⟩ (.splitting (.ready (.search 0))) ⟨component.tree,outside⟩ none := by
    rw [← open_root component clean nonempty]
    exact .write rfl
  exact .next read (.next write (.nil _ _))

theorem suffix_prefix (key : κ) (record : MarkedRecord κ ρ)
    (left : Source α (MarkedRecord κ ρ)) (right : AuxiliaryComponent α κ (fun _ => ρ×Bool)) (outside) :
    Steps (program key) .goRight ⟨.fork record left right.tree,outside⟩
      (.joining (.ready (.observing 0 (.read 3 []))))
      ⟨.fork record left (closed right),outside⟩ [right.tree.rootRecord] 4 := by
  have down : Step (program key) .goRight ⟨.fork record left right.tree,outside⟩ .suffixRead
      ⟨right.tree,.right left record::outside⟩ none := .nav rfl rfl
  have read : Step (program key) .suffixRead ⟨right.tree,.right left record::outside⟩
      (.suffixWrite (tag true right.tree.rootRecord)) ⟨right.tree,.right left record::outside⟩
      (some right.tree.rootRecord) := by
    apply Step.read (next := fun record _ => State.suffixWrite (tag true record)); rfl
  have write : Step (program key) (.suffixWrite (tag true right.tree.rootRecord))
      ⟨right.tree,.right left record::outside⟩ .goUp ⟨closed right,.right left record::outside⟩ none := .write rfl
  have up : Step (program key) .goUp ⟨closed right,.right left record::outside⟩
      (.joining (.ready (.observing 0 (.read 3 [])))) ⟨.fork record left (closed right),outside⟩ none := .nav rfl rfl
  exact .next down (.next read (.next write (.next up (.nil _ _))))

theorem close_prefix (key : κ) (component : AuxiliaryComponent α κ (fun _ => ρ×Bool)) (outside) :
    Steps (program key) .closeRead ⟨component.tree,outside⟩ .done ⟨closed component,outside⟩
      [component.tree.rootRecord] 2 := by
  have read : Step (program key) .closeRead ⟨component.tree,outside⟩
      (.closeWrite (tag true component.tree.rootRecord)) ⟨component.tree,outside⟩ (some component.tree.rootRecord) := by
    apply Step.read (next := fun record _ => State.closeWrite (tag true record)); rfl
  have write : Step (program key) (.closeWrite (tag true component.tree.rootRecord))
      ⟨component.tree,outside⟩ .done ⟨closed component,outside⟩ none := .write rfl
  exact .next read (.next write (.nil _ _))

end TangoSquared.Paper20261030.BoundaryObservations.MarkedCutController
