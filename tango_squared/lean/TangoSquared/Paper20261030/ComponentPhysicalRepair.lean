import TangoSquared.Paper20261030.LocalPhysicalContextSpace
import TangoSquared.Paper20261030.LocalComponentCompiler

/-!
# Physical boundary repair through the actual component datum wrappers

The per-vertex record consists of a physical identifier, a list of
logical records, and physical pointer fields. The source kernel repairs
these fields, then the existing packet, mirror, virtual-header, payload,
and connector compilers execute it in the shared original-key tree.
The target piece is exactly the canonical physical encoding of its
retained identifiers and logical lists.

The runtime input is a finite shape, a selected color, and a parent id.
Correct new logical lists and identifiers must already have been installed
at the exposed vertices. Establishing that state after block reassembly
remains a separate obligation.
-/

namespace TangoSquared.Paper20261030.ComponentPhysicalRepair

open ColoredStorage SourcePointer Structural PhysicalForestMetadata

variable {κ α β ρ ι C : Type*} [DecidableEq C]

abbrev Datum (α ρ ι : Type*) := VirtualHeaderController.Datum α (Record ρ ι)
abbrev Raw (C α ρ ι : Type*) := ProjectionForest.State C α (Record ρ ι)
abbrev State (κ α ρ ι C : Type*) := PayloadForestController.State
  (VirtualHeaderController.State
    (SourceForestLift.State (PhysicalContextRepair.State κ (Payload ρ ι) ι)) α (Record ρ ι)) C (Datum α ρ ι)

def ready (phase : PhysicalContextRepair.State κ (Payload ρ ι) ι) : State κ α ρ ι C :=
  .ready (.ready (.running phase))

def program (color virtualColor : C) (orientation : C → Bool) :
    MultiSourceProgram.Program (State κ α ρ ι C) C (List (Option (Datum α ρ ι))) :=
  ForestConnector.program (PayloadForestController.program (VirtualHeaderController.program virtualColor
    (ForestMirrorController.program orientation (SourceForestLift.program color (PhysicalContextRepair.program Prod.fst)))))

def view (virtualColor : C) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (List (Option (Datum α ρ ι)))) (raw : Raw C α ρ ι) :
    ProjectionForest.State C β (Option (Datum α ρ ι)) :=
  PayloadForestController.transform payload
    (VirtualHeaderController.encode virtualColor headerKey (ForestMirrorController.transform orientation raw))

def repaired (raw : Raw C α ρ ι) (color : C) (blocks : κ → Source α (Payload ρ ι))
    (context : Source κ (Record ρ ι)) : Raw C α ρ ι :=
  Function.update raw color (some (encodeCursor ⟨PhysicalContextRepair.plain blocks context,[]⟩))

theorem execute (color virtualColor : C) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (List (Option (Datum α ρ ι))))
    (blocks : κ → Source α (Payload ρ ι)) (parents : κ → Option ι) (context : Source κ (Record ρ ι))
    (raw : Raw C α ρ ι)
    (present : raw color = some (SourceForestLift.packet ⟨PhysicalContextRepair.input Prod.fst blocks parents context,[]⟩))
    (layout : Source C Unit) (distinct : (ForestConnector.colors layout).Nodup)
    (covers : ForestConnector.Covers layout (view virtualColor orientation headerKey payload raw))
    (config : MultiSourceProgram.Configuration C β (List (Option (Datum α ρ ι))))
    (assembled : ForestConnector.assemble (view virtualColor orientation headerKey payload raw) layout = some config) :
    ∃ target reads cost,
      MultiSourceProgram.Run (program color virtualColor orientation)
        (ready (.ready [.visit (context.mapRecords (fun _ => ())) none])) config (ready (.ready [])) target reads cost ∧
      ForestConnector.assemble (view virtualColor orientation headerKey payload (repaired raw color blocks context)) layout = some target ∧
      ForestConnector.Covers layout (view virtualColor orientation headerKey payload (repaired raw color blocks context)) ∧
      MultiSourceProgram.WellFormed target ∧ cost ≤ 4*PhysicalContextRepair.cost context := by
  obtain ⟨sourceReads,sourceRun⟩ := PhysicalContextRepair.run Prod.fst blocks parents context none []
  have pieceRun := SourceForestLift.run color sourceRun raw present
  have mirrored := ForestMirrorController.compile_run orientation _ pieceRun
  obtain ⟨headerReads,headerCost,headerRun,headerBound⟩ := VirtualHeaderController.compile_run virtualColor _ headerKey mirrored
  obtain ⟨reads,cost,actual,bounded⟩ := PayloadForestController.compile_run _ payload headerRun
  obtain ⟨target,finalAssembled,joined⟩ := ForestConnector.compile_run _ actual layout distinct covers config assembled
  refine ⟨target,reads,cost,joined,finalAssembled,covers.run actual,
    ForestConnector.assemble_wellFormed _ _ _ finalAssembled,?_⟩
  calc
    cost ≤ 2*(2*PhysicalContextRepair.cost context) := bounded.trans (Nat.mul_le_mul_left 2 headerBound)
    _ = 4*PhysicalContextRepair.cost context := by omega

theorem repaired_present (raw : Raw C α ρ ι) (color : C) (blocks : κ → Source α (Payload ρ ι))
    (context : Source κ (Record ρ ι)) :
    repaired raw color blocks context color = some (encodeCursor ⟨PhysicalContextRepair.plain blocks context,[]⟩) :=
  Function.update_self _ _ _

theorem repaired_other (raw : Raw C α ρ ι) (color other : C) (different : other ≠ color)
    (blocks : κ → Source α (Payload ρ ι)) (context : Source κ (Record ρ ι)) :
    repaired raw color blocks context other = raw other := Function.update_of_ne different _ _

theorem identifier_inventory (blocks : κ → Source α (Payload ρ ι)) (parents : κ → Option ι)
    (context : Source κ (Record ρ ι)) :
    (PhysicalContextRepair.input Prod.fst blocks parents context).inventory (fun record => record.1.1) =
      (PhysicalContextRepair.plain blocks context).inventory Prod.fst := by
  have erased := PhysicalContextRepair.input_erases Prod.fst blocks parents context
  have inventory := congrArg (fun tree => tree.inventory Prod.fst) erased
  simpa only [mapRecords_inventory,Function.comp_def] using inventory

end TangoSquared.Paper20261030.ComponentPhysicalRepair
