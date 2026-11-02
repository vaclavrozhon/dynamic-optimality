import ChaCha.Paper20261030.EnclosedHeaderLeaf
import ChaCha.Paper20261030.ReachedVirtualHeaderRead
import ChaCha.Paper20261030.MultiSourceMappedService

set_option autoImplicit false

/-! Actual original-key service from a reached canonical component root.
The already read wing bits give a path of at most two edges. One copy,
the path traversal, and two reads cost at most five operations. All stored
records and other fingers are retained; no key search or ghost cursor is
used as a runtime argument. -/

namespace ChaCha.Paper20261030.ReachedBottomService

open ColoredStorage SourcePointer SourcePositions Structural PhysicalForestMetadata PhysicalPacketStaging MultiSourceProgram
open ForestConnector.ThreeColors

variable {α β ρ ι η τ F : Type*} [DecidableEq F]

def program (origin work : F) (header : PrimaryHeaderController.Header η) :=
  ReadCompletionController.program
    (PathRecordRead.program (ρ := τ) origin work (fun _ => ()) (PrimaryHeaderRefresh.path header)) work

theorem execute (origin work : F) (readPacket : τ → Packet α ρ ι)
    (header : PrimaryHeaderController.Header η) (orientation : Option Bool → Bool) (headerKey : α)
    (payload : Option Bool → α → Source β (Packet α ρ ι)) (forest : TaggedForest (Option Bool) α ρ ι)
    (config : Configuration (Option Bool) β (Packet α ρ ι))
    (assembled : ForestConnector.assemble (ComponentPhysicalRepair.view none orientation headerKey payload (encode forest))
      (layout (ComponentPhysicalRepair.view none orientation headerKey payload (encode forest))) = some config)
    (leftWing : header.leftWing = (ComponentPhysicalRepair.view none orientation headerKey payload (encode forest) (some true)).isSome)
    (rightWing : header.rightWing = (ComponentPhysicalRepair.view none orientation headerKey payload (encode forest) (some false)).isSome)
    (key : β) (bottomPacket : Packet α ρ ι) (bottomLeaf : payload none headerKey = .leaf key bottomPacket)
    (saved : Packet α ρ ι) (current : Cursor β τ)
    (view : current.focus.mapRecords readPacket = config.tree.setRoot (saved++config.tree.rootRecord))
    (global : Configuration F β τ) (positioned : MultiSourceSingleCursor.Represents origin current global) :
    ∃ target reads cost,
      Serves (program (τ := τ) origin work header) key (some none) global none target reads cost ∧
      target.tree = global.tree ∧
      (∀ finger, finger ≠ work → target.fingers finger = global.fingers finger) ∧ cost ≤ 5 := by
  let physical := ComponentPhysicalRepair.view none orientation headerKey payload (encode forest)
  let stored := ForestMirrorController.transform orientation (encode forest) none
  let packet : Packet α ρ ι := some (.header stored)::none::bottomPacket
  have headerPresent : physical none = some ⟨.leaf key packet,[]⟩ := by
    have actual := CanonicalPacketLayerViews.component_virtual none orientation headerKey payload forest
    simpa only [bottomLeaf,Source.rootRecord,Source.setRoot,packet] using actual
  have canonical : config = configuration physical ⟨.leaf key packet,[]⟩ :=
    Option.some.inj (assembled.symm.trans (assemble_configuration physical ⟨.leaf key packet,[]⟩ headerPresent))
  have pathEq : PrimaryHeaderRefresh.path header = headerPath physical := by
    simp only [PrimaryHeaderRefresh.path,headerPath,leftWing,rightWing,physical]
  have enclosedView : current.focus.mapRecords readPacket = (configuration physical ⟨.leaf key packet,[]⟩).tree.setRoot
      (saved++(configuration physical ⟨.leaf key packet,[]⟩).tree.rootRecord) := canonical ▸ view
  obtain ⟨reached,descended,leaf⟩ := reached_header_leaf readPacket physical key packet saved current enclosedView
  rw [← pathEq] at descended
  obtain ⟨target,actual,tree,located,others⟩ := PathRecordRead.execute origin work
    (fun _ : τ => ()) (PrimaryHeaderRefresh.path header) global current reached positioned descended
  have found : locate target.tree (address reached) = some reached := by
    rw [located.1]
    exact locate_cursor reached
  have atLeaf : locate target.tree (address reached) = some ⟨.leaf key reached.focus.rootRecord,reached.ancestors⟩ := by
    rw [found]
    exact congrArg some (congrArg (fun focus => Cursor.mk focus reached.ancestors) leaf)
  have service := ReadCompletionController.serve _ work actual key reached.focus.rootRecord (address reached)
    reached.ancestors located.2 atLeaf
  exact ⟨target,_,_,service,tree,others,by have short := PrimaryHeaderRefresh.path_length header; omega⟩

end ChaCha.Paper20261030.ReachedBottomService
