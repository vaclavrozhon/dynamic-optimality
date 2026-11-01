import TangoSquared.Paper20261030.EnclosedHeaderPath
import TangoSquared.Paper20261030.PathRecordRead
import TangoSquared.Paper20261030.CanonicalPacketLayerViews
import TangoSquared.Paper20261030.PrimaryComponentHeaderRefresh

set_option autoImplicit false

/-! Acquiring a component's actual stored virtual cursor directly from
its reached root in the shared tree. The already acquired wing bits
determine a path of at most two edges. One copy and one read complete
the operation; enclosing prefixes are skipped only in the root case. -/

namespace TangoSquared.Paper20261030.ReachedVirtualHeaderRead

open ColoredStorage SourcePointer Structural PhysicalForestMetadata PhysicalPacketStaging MultiSourceProgram
open ForestConnector.ThreeColors

variable {α β ρ ι η τ F : Type*} [DecidableEq F]

abbrev Stored (α ρ ι : Type*) := VirtualHeaderController.Virtual α (PhysicalForestMetadata.Record ρ ι)

def decode (readPacket : τ → Packet α ρ ι) (count : Nat) (path : List Bool) (record : τ) : Option (Stored α ρ ι) :=
  match (readPacket record).drop (if path.isEmpty then count else 0) with
  | some (.header stored)::none::_ => some stored
  | _ => none

def program (origin work : F) (readPacket : τ → Packet α ρ ι) (count : Nat) (header : PrimaryHeaderController.Header η) :=
  PathRecordRead.program origin work (decode readPacket count (PrimaryHeaderRefresh.path header)) (PrimaryHeaderRefresh.path header)

theorem execute (origin work : F) (readPacket : τ → Packet α ρ ι)
    (header : PrimaryHeaderController.Header η) (orientation : Option Bool → Bool) (headerKey : α)
    (payload : Option Bool → α → Source β (Packet α ρ ι)) (forest : TaggedForest (Option Bool) α ρ ι)
    (config : Configuration (Option Bool) β (Packet α ρ ι))
    (assembled : ForestConnector.assemble (ComponentPhysicalRepair.view none orientation headerKey payload (encode forest))
      (layout (ComponentPhysicalRepair.view none orientation headerKey payload (encode forest))) = some config)
    (leftWing : header.leftWing = (ComponentPhysicalRepair.view none orientation headerKey payload (encode forest) (some true)).isSome)
    (rightWing : header.rightWing = (ComponentPhysicalRepair.view none orientation headerKey payload (encode forest) (some false)).isSome)
    (saved : Packet α ρ ι) (current : Cursor β τ)
    (view : current.focus.mapRecords readPacket = config.tree.setRoot (saved++config.tree.rootRecord))
    (global : Configuration F β τ) (positioned : MultiSourceSingleCursor.Represents origin current global) :
    ∃ target reads cost,
      Run (program origin work readPacket saved.length header) none global
        (some (some (.done (some (ForestMirrorController.transform orientation (encode forest) none))))) target reads cost ∧
      target.tree = global.tree ∧
      (∀ finger, finger ≠ work → target.fingers finger = global.fingers finger) ∧ cost ≤ 4 := by
  let physical := ComponentPhysicalRepair.view none orientation headerKey payload (encode forest)
  let stored := ForestMirrorController.transform orientation (encode forest) none
  let headerTree := (payload none headerKey).setRoot (some (.header stored)::none::(payload none headerKey).rootRecord)
  have headerPresent : physical none = some ⟨headerTree,[]⟩ :=
    CanonicalPacketLayerViews.component_virtual none orientation headerKey payload forest
  have canonical : config = configuration physical ⟨headerTree,[]⟩ :=
    Option.some.inj (assembled.symm.trans (assemble_configuration physical ⟨headerTree,[]⟩ headerPresent))
  have pathEq : PrimaryHeaderRefresh.path header = headerPath physical := by
    simp only [PrimaryHeaderRefresh.path,headerPath,leftWing,rightWing,physical]
  have enclosedView : current.focus.mapRecords readPacket = (configuration physical ⟨headerTree,[]⟩).tree.setRoot
      (saved++(configuration physical ⟨headerTree,[]⟩).tree.rootRecord) := canonical ▸ view
  obtain ⟨reached,descended,packet⟩ := reached_header readPacket physical headerTree saved current enclosedView
  have decoded : decode readPacket saved.length (PrimaryHeaderRefresh.path header) reached.focus.rootRecord = some stored := by
    rw [decode,pathEq,packet]
    dsimp only [headerTree]
    cases payload none headerKey <;> rfl
  rw [← pathEq] at descended
  obtain ⟨target,actual,tree,located,others⟩ := PathRecordRead.execute origin work
    (decode readPacket saved.length (PrimaryHeaderRefresh.path header)) (PrimaryHeaderRefresh.path header) global current reached positioned descended
  rw [decoded] at actual
  exact ⟨target,_,_,actual,tree,others,by have short := PrimaryHeaderRefresh.path_length header; omega⟩

end TangoSquared.Paper20261030.ReachedVirtualHeaderRead
