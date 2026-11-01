import TangoSquared.Paper20261030.LocalComponentCompiler
import TangoSquared.Paper20261030.ComponentRootPositions

/-!
# Reading the actual stored virtual cursor of a component

The virtual-color register points at the physical header piece. One
ordinary record read acquires its entire bounded stored cursor. The
payload decoder removes the attachment suffix, and the existing forest
connector executes the read in the shared original-key tree. No logical
virtual cursor or its contents are supplied to the running program.
-/

namespace TangoSquared.Paper20261030.StoredVirtualHeaderRead

open ColoredStorage SourcePointer ForestLocalProgram Structural PhysicalForestMetadata

variable {α β ρ C : Type*} [DecidableEq C]

inductive State (α ρ : Type*) where
  | start
  | done (stored : VirtualHeaderController.Virtual α ρ)
  | error

def decode : View (VirtualHeaderController.Datum α ρ) → State α ρ
  | some ([.header stored],_) => .done stored
  | _ => .error

def program (virtualColor : C) : Program (State α ρ) C (VirtualHeaderController.Datum α ρ)
  | .start => .read virtualColor decode
  | .done _ | .error => .halt

theorem read (virtualColor : C) (key : α) (forest : ProjectionForest.State C α ρ) :
    Run (program virtualColor) .start (VirtualHeaderController.encode virtualColor key forest)
      (.done (forest virtualColor)) (VirtualHeaderController.encode virtualColor key forest)
      [(virtualColor,[.header (forest virtualColor)])] 1 := by
  have present : VirtualHeaderController.encode virtualColor key forest virtualColor =
      some ⟨.leaf key [.header (forest virtualColor)],[]⟩ := by
    simp only [VirtualHeaderController.encode,ite_true]
  have step : Step (program virtualColor) .start (VirtualHeaderController.encode virtualColor key forest)
      (.done (forest virtualColor)) (VirtualHeaderController.encode virtualColor key forest)
      (some (virtualColor,[.header (forest virtualColor)])) :=
    Step.readSome (program := program virtualColor) (next := decode) rfl present
  exact .next step (.halt rfl)

def sharedProgram (virtualColor : C) :
    MultiSourceProgram.Program
      (PayloadForestController.State (State α ρ) C (VirtualHeaderController.Datum α ρ)) C
      (List (Option (VirtualHeaderController.Datum α ρ))) :=
  ForestConnector.program (PayloadForestController.program (program virtualColor))

theorem execute (virtualColor : C) (key : α) (forest : ProjectionForest.State C α ρ)
    (payload : C → α → Source β (List (Option (VirtualHeaderController.Datum α ρ))))
    (layout : Source C Unit) (distinct : (ForestConnector.colors layout).Nodup)
    (covers : ForestConnector.Covers layout
      (PayloadForestController.transform payload (VirtualHeaderController.encode virtualColor key forest)))
    (config : MultiSourceProgram.Configuration C β (List (Option (VirtualHeaderController.Datum α ρ))))
    (assembled : ForestConnector.assemble
      (PayloadForestController.transform payload (VirtualHeaderController.encode virtualColor key forest)) layout = some config) :
    ∃ reads cost,
      MultiSourceProgram.Run (sharedProgram virtualColor) (.ready .start) config
        (.ready (.done (forest virtualColor))) config reads cost ∧ cost ≤ 2 := by
  obtain ⟨reads,cost,actual,bound⟩ := PayloadForestController.compile_run _ payload (read virtualColor key forest)
  obtain ⟨target,finalAssembled,compiled⟩ := ForestConnector.compile_run _ actual layout distinct covers config assembled
  have same : target = config := Option.some.inj (finalAssembled.symm.trans assembled)
  subst target
  exact ⟨reads,cost,compiled,bound⟩

end TangoSquared.Paper20261030.StoredVirtualHeaderRead
