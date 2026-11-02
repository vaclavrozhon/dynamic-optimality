import ChaCha.Paper20261030.CanonicalPayloadOccurrence
import ChaCha.Paper20261030.EnclosingPacketInvariants

set_option autoImplicit false

/-! Restoring the enclosing packet and repairing its parent keep every
proper payload subtree of the component. This makes the canonical port
occurrence available in the final shared physical configuration. -/

namespace ChaCha.Paper20261030.SourcePointer

open ColoredStorage

variable {α ρ : Type*}

theorem proper_subtree_setRoot (focus : Source α ρ) (outside : List (Frame α ρ))
    (proper : outside ≠ []) (fresh : ρ) :
    ∃ changed, changed ≠ [] ∧ (plug focus outside).setRoot fresh = plug focus changed := by
  induction outside generalizing focus with
  | nil => exact False.elim (proper rfl)
  | cons first rest ih =>
    cases rest with
    | nil => cases first with
      | left record sibling => exact ⟨[.left fresh sibling],by simp,rfl⟩
      | right sibling record => exact ⟨[.right sibling fresh],by simp,rfl⟩
    | cons second rest =>
      obtain ⟨changed,_,same⟩ := ih (plug focus [first]) (by simp)
      refine ⟨first::changed,by simp,?_⟩
      cases first <;> exact same

end ChaCha.Paper20261030.SourcePointer

namespace ChaCha.Paper20261030.EnclosingPacketOperation

open ColoredStorage SourcePointer PhysicalPacketStaging PacketLayers

variable {α β ρ ι : Type*} [DecidableEq ι]

theorem proper_payload (saved : Packet α ρ ι) (oldId : ι)
    (tree : Source β (Context.Cell α ρ ι)) (outside : List (Frame β (Context.Cell α ρ ι)))
    (payload : Source β (Packet α ρ ι)) (inside : List (Frame β (Packet α ρ ι)))
    (proper : inside ≠ []) (view : tree.mapRecords Prod.snd = plug payload inside) :
    ∃ finalOutside, finalOutside ≠ [] ∧ (output saved oldId ⟨tree,outside⟩).tree.mapRecords Prod.snd = plug payload finalOutside := by
  let finished := output saved oldId ⟨tree,outside⟩
  let packet := PacketPrefixTransfer.reidentify tree.rootRecord.1 saved ++ tree.rootRecord.2
  obtain ⟨changed,nonempty,same⟩ := proper_subtree_setRoot payload inside proper packet
  have focus : finished.focus.mapRecords Prod.snd = plug payload changed := by
    change (tree.setRoot (tree.rootRecord.1,packet)).mapRecords Prod.snd = _
    rw [Source.mapRecords_setRoot,view,same]
  refine ⟨changed ++ finished.ancestors.map (Frame.mapRecords Prod.snd),(fun empty => nonempty (List.append_eq_nil_iff.mp empty).1),?_⟩
  change (plug finished.focus finished.ancestors).mapRecords Prod.snd = _
  rw [← plug_mapRecords,focus,plug_append]

end ChaCha.Paper20261030.EnclosingPacketOperation

namespace ChaCha.Paper20261030.LocalComponentCompiler

open ColoredStorage SourcePointer Structural PhysicalForestMetadata LocalComponentForestCompiler
open ForestConnector.ThreeColors PhysicalPacketStaging PacketLayers MultiSourceProgram

variable {α β ρ ι η F : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq F]

local instance enclosingPayloadOccurrenceColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem enclosed_payload_occurs (color : α → Option Bool) (decorated : Source α (η × ρ))
    (forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (headerKey : α) (payload : Option Bool → α → Source β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    (config : Configuration (Option Bool) β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (tree : Source β (ι × List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    (erases : tree.mapRecords Prod.snd = config.tree)
    (outside : List (Frame β (ι × List (Option (PhysicalDatum α ρ ι η (Option Bool))))))
    (saved : List (Option (PhysicalDatum α ρ ι η (Option Bool)))) (oldId : ι)
    (target : Configuration F β (ι × List (Option (PhysicalDatum α ρ ι η (Option Bool))))) (exit : F)
    (returned : MultiSourceSingleCursor.Represents exit (EnclosingPacketOperation.output saved oldId ⟨tree,outside⟩) target)
    (key : α) (member : key ∈ decorated.shape.leaves) (real : color key ≠ none) :
    ∃ records : List (PhysicalDatum α ρ ι η (Option Bool)), records.length = 1 ∧ ∃ finalOutside, finalOutside ≠ [] ∧
      target.tree.mapRecords Prod.snd =
        plug ((payload (color key) key).setRoot (records.map some ++ none::(payload (color key) key).rootRecord)) finalOutside := by
  obtain ⟨records,singleton,inside,proper,view⟩ := real_payload_occurs color decorated forest represented headerKey payload config assembled key member real
  obtain ⟨finalOutside,nonempty,finalView⟩ := EnclosingPacketOperation.proper_payload saved oldId tree outside _ inside proper (erases.trans view)
  exact ⟨records,singleton,finalOutside,nonempty,by rw [returned.1]; exact finalView⟩

end ChaCha.Paper20261030.LocalComponentCompiler
