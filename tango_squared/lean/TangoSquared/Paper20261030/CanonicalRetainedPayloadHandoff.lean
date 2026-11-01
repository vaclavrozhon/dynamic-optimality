import TangoSquared.Paper20261030.EnclosingPayloadOccurrence
import TangoSquared.Paper20261030.RetainedSubtreeHandoff
import TangoSquared.Paper20261030.EnclosedRootedComponentExecution

set_option autoImplicit false

/-! Canonical component output supplies the retained-payload occurrence
required by the parked-finger theorem. Thus the caller need not assume a
physical output cursor, its physical id, or a free path to the next root.
An enclosing packet may differ at the root; removing that packet recovers
exactly the original payload, with all immutable identifiers intact. -/

namespace TangoSquared.Paper20261030.CanonicalRetainedPayloadHandoff

open ColoredStorage SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors MultiSourceProgram
open EnclosedRootedComponentExecution (Packet Cell)

variable {α β ρ ι η F : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq F]

local instance retainedHandoffColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

/-- Equality after removing the component's enclosing root packet. -/
def PayloadAt (payload : Source β (Packet α ρ ι η)) (current : Cursor β (Cell α ρ ι η)) : Prop :=
  (current.focus.mapRecords Prod.snd).setRoot payload.rootRecord = payload

theorem handoff (color : α → Option Bool) (decorated : Source α (η × ρ))
    (forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (headerKey : α) (payload : Option Bool → α → Source β (Packet α ρ ι η))
    (config : Configuration (Option Bool) β (Packet α ρ ι η))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (tree : Source β (Cell α ρ ι η)) (erases : tree.mapRecords Prod.snd = config.tree)
    (outside : List (Frame β (Cell α ρ ι η))) (saved : Packet α ρ ι η) (oldId : ι)
    (before after : Configuration F β (Cell α ρ ι η)) (exit : F)
    (returned : MultiSourceSingleCursor.Represents exit (EnclosingPacketOperation.output saved oldId ⟨tree,outside⟩) after)
    (leafWord : before.tree.shape.leaves = after.tree.shape.leaves)
    (order : after.tree.inorderLabels Prod.fst = before.tree.inorderLabels Prod.fst)
    (distinct : before.tree.shape.leaves.Nodup) (unique : (after.tree.inventory Prod.fst).Nodup)
    (finger : F) (parked : fingerLabel Prod.fst after finger = fingerLabel Prod.fst before finger)
    (current : Cursor β (Cell α ρ ι η)) (positioned : MultiSourceSingleCursor.Represents finger current before)
    (key : α) (member : key ∈ decorated.shape.leaves) (real : color key ≠ none)
    (initialPayload : PayloadAt (payload (color key) key) current) :
    ∃ actual : Cursor β (Cell α ρ ι η),
      MultiSourceSingleCursor.Represents finger actual after ∧ PayloadAt (payload (color key) key) actual ∧
      actual.focus.rootRecord.1 ≠ tree.rootRecord.1 ∧ actual.ancestors ≠ [] ∧
      (∃ packet : Packet α ρ ι η, packet.length = 2 ∧ actual.focus.mapRecords Prod.snd =
        (payload (color key) key).setRoot (packet ++ (payload (color key) key).rootRecord)) ∧
      (SubtreeMetadata.replacePayload current (payload (color key) key).rootRecord).focus =
        (SubtreeMetadata.replacePayload actual (payload (color key) key).rootRecord).focus := by
  obtain ⟨records,singleton,finalOutside,finalProper,viewTree⟩ := enclosed_payload_occurs color decorated forest represented headerKey payload config assembled
    tree erases outside saved oldId after exit returned key member real
  let focus := (payload (color key) key).setRoot (records.map some ++ none::(payload (color key) key).rootRecord)
  let view : Cursor β (Packet α ρ ι η) := ⟨focus,finalOutside⟩
  have normalized : view.focus.setRoot (payload (color key) key).rootRecord = payload (color key) key := by
    change ((payload (color key) key).setRoot _).setRoot _ = _
    cases payload (color key) key <;> rfl
  obtain ⟨actual,located,actualErases,same⟩ := retained_subtree_handoff_of_leaves leafWord order distinct unique finger parked
    current positioned view viewTree.symm (payload (color key) key).rootRecord (payload (color key) key).rootRecord
    (initialPayload.trans normalized.symm)
  have focusErases := congrArg Cursor.focus actualErases
  change actual.focus.mapRecords Prod.snd = view.focus at focusErases
  have payloadRep : PayloadAt (payload (color key) key) actual := by
    change (actual.focus.mapRecords Prod.snd).setRoot _ = _
    rw [focusErases]
    exact normalized
  have proper : actual.ancestors ≠ [] := by
    intro empty
    have contexts := congrArg Cursor.ancestors actualErases
    apply finalProper
    simpa only [Cursor.mapRecords,empty,List.map_nil,view] using contexts.symm
  refine ⟨actual,located,payloadRep,?_,proper,?_,same⟩
  case refine_2 =>
    refine ⟨records.map some ++ [none],by simp only [List.length_append,List.length_map,List.length_singleton,singleton],?_⟩
    simpa only [List.append_assoc,List.singleton_append] using focusErases
  intro equalId
  let root := EnclosingPacketOperation.output saved oldId ⟨tree,outside⟩
  have rootIdentity : actual.focus.rootRecord.1 = root.focus.rootRecord.1 := by
    simpa only [root,EnclosingPacketOperation.output,PacketPrefixTransfer.output_root_id] using equalId
  have cursorsSame := SourcePositions.cursors_eq_of_label Prod.fst actual root
    (located.1.symm.trans returned.1) (located.1 ▸ unique) rootIdentity
  obtain ⟨routing,_,inside,proper,piece⟩ := real_payload_occurs color decorated forest represented headerKey payload config assembled key member real
  have smaller := SubtreeMetadata.proper_leaves_lt
    ((payload (color key) key).setRoot (routing.map some ++ none::(payload (color key) key).rootRecord)) inside proper
  rw [← piece] at smaller
  simp only [source_setRoot_shape] at smaller
  have actualLeaves : actual.focus.shape.leaves = (payload (color key) key).shape.leaves := by
    have shapes := congrArg (fun source : Source β (Packet α ρ ι η) => source.shape.leaves) payloadRep
    simpa only [source_setRoot_shape,Source.mapRecords_shape] using shapes
  have rootLeaves : root.focus.shape.leaves = config.tree.shape.leaves := by
    simp only [root,EnclosingPacketOperation.output,PacketPrefixTransfer.output,PacketPrefixTransfer.attach,source_setRoot_shape]
    rw [← Source.mapRecords_shape Prod.snd tree,erases]
  have sizeSame := congrArg (fun cursor : Cursor β (Cell α ρ ι η) => cursor.focus.shape.leaves.length) cursorsSame
  rw [actualLeaves,rootLeaves] at sizeSame
  omega

end TangoSquared.Paper20261030.CanonicalRetainedPayloadHandoff
