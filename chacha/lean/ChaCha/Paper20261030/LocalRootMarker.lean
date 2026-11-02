import ChaCha.Paper20261030.LocalMarkedCutProgram

/-! Reading and changing a reached component-entry marker. Opening skips
physical leaves, which are the represented terminal components. Closing
also works on terminal components. Each operation uses at most two paid
commands and keeps at most one record. -/

namespace ChaCha.Paper20261030.BoundaryObservations.RootMarkerController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary AuxiliaryComponent SourceLocalProgram
open GapSource.Controller

variable {α κ ρ : Type*}

inductive State (κ ρ : Type*) where
  | start
  | write (record : MarkedRecord κ ρ)
  | done

def next (bit skipLeaf : Bool) (record : MarkedRecord κ ρ) (leaf : Bool) : State κ ρ :=
  if skipLeaf && leaf then .done else .write (tag bit record)

def program (bit skipLeaf : Bool) : Program (State κ ρ) (MarkedRecord κ ρ)
  | .start => .read (next bit skipLeaf)
  | .write record => .write record .done
  | .done => .halt

theorem change_root (bit : Bool) (source : Source α (MarkedRecord κ ρ)) (outside) :
    Run (program bit false) .start ⟨source,outside⟩ .done
      ⟨source.setRoot (tag bit source.rootRecord),outside⟩ [source.rootRecord] 2 := by
  have read : Step (program bit false) .start ⟨source,outside⟩
      (.write (tag bit source.rootRecord)) ⟨source,outside⟩ (some source.rootRecord) := by
    apply Step.read (next := next bit false); rfl
  have write : Step (program bit false) (.write (tag bit source.rootRecord))
      ⟨source,outside⟩ .done ⟨source.setRoot (tag bit source.rootRecord),outside⟩ none := .write rfl
  exact .next read (.next write (.halt rfl))

theorem close_component (component : AuxiliaryComponent α κ (fun _ => ρ×Bool)) (outside) :
    Run (program true false) .start ⟨component.tree,outside⟩ .done
      ⟨closed component,outside⟩ [component.tree.rootRecord] 2 := change_root true component.tree outside

theorem open_component [Ord κ] (component : AuxiliaryComponent α κ (fun _ => ρ×Bool))
    (clean : Clean component.core) (marked : MarkedPorts component)
    (terminal : component.core = .leaf → isLeaf component.tree = true) (outside) :
    ∃ reads cost, Run (program false true) .start ⟨closed component,outside⟩ .done
      ⟨component.tree,outside⟩ reads cost ∧ cost ≤ 2 := by
  by_cases empty : component.core = .leaf
  · have equal := closed_terminal component empty marked
    rw [equal]
    have read : Step (program false true) .start ⟨component.tree,outside⟩ .done
        ⟨component.tree,outside⟩ (some component.tree.rootRecord) := by
      have step : Step (program false true) .start ⟨component.tree,outside⟩
          (next false true component.tree.rootRecord (isLeaf component.tree))
          ⟨component.tree,outside⟩ (some component.tree.rootRecord) := .read rfl
      simpa only [next,terminal empty,Bool.and_self,ite_true] using step
    exact ⟨[component.tree.rootRecord],1,.next read (.halt rfl),by omega⟩
  · have physicalFork : isLeaf (closed component) = false := by
      unfold closed
      cases shape : component.core with
      | leaf => exact False.elim (empty shape)
      | inner => simp only [AuxiliaryComponent.tree,shape,recordTree,GapSource.encode,Source.setRoot,isLeaf]
    have read : Step (program false true) .start ⟨closed component,outside⟩
        (.write (tag false (closed component).rootRecord)) ⟨closed component,outside⟩
        (some (closed component).rootRecord) := by
      have step : Step (program false true) .start ⟨closed component,outside⟩
          (next false true (closed component).rootRecord (isLeaf (closed component)))
          ⟨closed component,outside⟩ (some (closed component).rootRecord) := .read rfl
      simpa only [next,physicalFork,Bool.and_false,Bool.false_eq_true,ite_false] using step
    have write : Step (program false true) (.write (tag false (closed component).rootRecord))
        ⟨closed component,outside⟩ .done ⟨component.tree,outside⟩ none := by
      rw [← MarkedCutController.open_root component clean empty]
      exact .write rfl
    exact ⟨[(closed component).rootRecord],2,.next read (.next write (.halt rfl)),le_rfl⟩

end ChaCha.Paper20261030.BoundaryObservations.RootMarkerController
