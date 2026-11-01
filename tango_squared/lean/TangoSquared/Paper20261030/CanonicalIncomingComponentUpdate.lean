import TangoSquared.Paper20261030.ReachedRoutingPayloadUpdate
import TangoSquared.Paper20261030.CanonicalForestWingUpdate
import TangoSquared.Paper20261030.CanonicalSubtreeValidity

set_option autoImplicit false

/-! The active component remains canonical after preparation changes the
root of its incoming payload. The updated routing witness and payload
function are proof data. The resulting view is the exact output of the
existing prefix-transfer and parent-repair operation. Physical validity
of that executed output supplies uniqueness of the new routing ids. -/

namespace TangoSquared.Paper20261030.CanonicalIncomingComponentUpdate

open ColoredStorage SourcePointer Structural PhysicalForestMetadata MultiSourceProgram
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors
open EnclosedRootedComponentExecution (Packet Cell)

variable {α β ρ ι η F : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq F]

local instance incomingComponentUpdateColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem update (markerId : ι) (color : α → Option Bool) (decorated : Source α (η × ρ))
    (forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (forestUnique : Unique forest)
    (headerKey : α) (payload : Option Bool → α → Source β (Packet α ρ ι η))
    (config : Configuration (Option Bool) β (Packet α ρ ι η))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    (tree : Source β (Cell α ρ ι η)) (erases : tree.mapRecords Prod.snd = config.tree)
    (outside : List (Frame β (Cell α ρ ι η))) (saved : Packet α ρ ι η) (old : ι)
    (neutral : PacketParentNeutral.Neutral saved)
    (global : Configuration F β (Cell α ρ ι η)) (exit finger : F)
    (returned : MultiSourceSingleCursor.Represents exit (EnclosingPacketOperation.output saved old ⟨tree,outside⟩) global)
    (valid : CanonicalComponentUniqueness.Valid markerId global.tree) (distinct : global.tree.shape.leaves.Nodup)
    (current : Cursor β (Cell α ρ ι η)) (positioned : MultiSourceSingleCursor.Represents finger current global)
    (key : α) (member : key ∈ decorated.shape.leaves) (real : color key ≠ none)
    (payloadAt : CanonicalRetainedPayloadHandoff.PayloadAt (payload (color key) key) current)
    (target : Source β (Cell α ρ ι η))
    (outputValid : CanonicalComponentUniqueness.Valid markerId
      (EnclosingPacketOperation.output (current.focus.rootRecord.2.take 2) current.focus.rootRecord.1
        ⟨target,current.ancestors⟩).tree) :
    let newPayload := Function.update payload (color key)
      (Function.update (payload (color key)) key (target.mapRecords Prod.snd))
    ∃ finalForest finalConfig,
      erase finalForest = erase forest ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey newPayload finalForest)
        (layout (representation none wingOrientation headerKey newPayload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey newPayload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      (EnclosingPacketOperation.output (current.focus.rootRecord.2.take 2) current.focus.rootRecord.1
        ⟨target,current.ancestors⟩).tree.mapRecords Prod.snd =
        plug (finalConfig.tree.setRoot
          (PacketPrefixTransfer.reidentify tree.rootRecord.1 saved ++ finalConfig.tree.rootRecord))
          ((EnclosingPacketOperation.output saved old ⟨tree,outside⟩).ancestors.map (Frame.mapRecords Prod.snd)) := by
  dsimp only
  obtain ⟨tagged,records,inside,originalConnectors,connectors,present,taggedEq,
    originalProper,originalEmpty,componentView,replacements,proper,connectorNeutral,rebuild,currentView⟩ :=
    CanonicalReachedPayloadPosition.position markerId color decorated forest represented headerKey payload config assembled
      tree erases outside saved old neutral global exit finger returned valid distinct current positioned key member real payloadAt
  let route := CanonicalRoutingCursor.cursor (payload (color key)) (wingOrientation (color key))
    ⟨.leaf key (current.focus.rootRecord.1,records),inside⟩
  let enclosing := (EnclosingPacketOperation.output saved old ⟨tree,outside⟩).ancestors.map (Frame.mapRecords Prod.snd)
  let newWingPayload := Function.update (payload (color key)) key (target.mapRecords Prod.snd)
  let newTagged := plug (.leaf key (target.rootRecord.1,records)) inside
  let newWing := CanonicalPacketLayerViews.routing newWingPayload (wingOrientation (color key)) none newTagged
  let newForest := CanonicalForestWingUpdate.replace forest (color key) newTagged
  let newPayload := Function.update payload (color key) newWingPayload
  let output := EnclosingPacketOperation.output (current.focus.rootRecord.2.take 2) current.focus.rootRecord.1
    ⟨target,current.ancestors⟩
  have prefixEq : current.focus.rootRecord.2.take 2 =
      CanonicalEnclosingPackets.layer current.focus.rootRecord.1 (.leaf records (parentId Prod.fst inside)) := by
    have focusView := congrArg Cursor.focus currentView
    change current.focus.mapRecords Prod.snd = route.focus at focusView
    rw [CanonicalRoutingCursor.leaf] at focusView
    have rootView := congrArg Source.rootRecord focusView
    simp only [Source.mapRecords_root] at rootView
    rw [rootView]
    cases payload (color key) key <;> rfl
  have context := congrArg Cursor.ancestors currentView
  change current.ancestors.map (Frame.mapRecords Prod.snd) = route.ancestors ++ (connectors++enclosing) at context
  have taggedUnique : (tagged.inventory Prod.fst).Nodup := forestUnique (color key) ⟨tagged,[]⟩ present
  have componentDistinct : config.tree.shape.leaves.Nodup := by
    have whole : (EnclosingPacketOperation.output saved old ⟨tree,outside⟩).tree.shape.leaves.Nodup := returned.1 ▸ distinct
    have focused := CanonicalRoutingCursor.focus_leaves_nodup _ _ whole
    rw [← erases,Source.mapRecords_shape]
    simpa only [EnclosingPacketOperation.output,PacketPrefixTransfer.output,PacketPrefixTransfer.attach,
      source_setRoot_shape] using focused
  have routingDistinct : route.tree.shape.leaves.Nodup :=
    CanonicalRoutingCursor.focus_leaves_nodup _ originalConnectors (componentView ▸ componentDistinct)
  have taggedDistinct : tagged.shape.leaves.Nodup := by
    rw [CanonicalRoutingCursor.tree] at routingDistinct
    rw [taggedEq]
    exact CanonicalPacketLayerViews.routing_keys_distinct _ _ _ _ routingDistinct
  have changed : output.tree.mapRecords Prod.snd = plug newWing (connectors++enclosing) := by
    dsimp only [output]
    rw [prefixEq]
    exact CanonicalRoutingPayloadUpdate.reached (payload (color key)) (wingOrientation (color key)) key records inside current
      (taggedEq ▸ taggedUnique) (taggedEq ▸ taggedDistinct) connectors enclosing proper connectorNeutral context target
  have newRealized := CanonicalComponentUniqueness.realized_focus markerId output.tree outputValid
    ⟨newWing,connectors++enclosing⟩ changed
  obtain ⟨physicalWing,wingErases,wingAligned,wingClear,wingUnique⟩ := newRealized _ rfl
  have newUnique := CanonicalRoutingUniqueness.unique markerId newWingPayload (wingOrientation (color key)) none
    newTagged physicalWing wingErases wingAligned wingClear wingUnique
  have forestErases : erase newForest = erase forest := CanonicalForestWingUpdate.erase_same forest (color key) tagged newTagged
    present ((CanonicalForestWingUpdate.leaf_erases key current.focus.rootRecord.1 target.rootRecord.1 records inside).trans
      (congrArg (Source.mapRecords Prod.snd) taggedEq.symm))
  have view : representation none wingOrientation headerKey newPayload newForest =
      Function.update (representation none wingOrientation headerKey payload forest) (color key) (some ⟨newWing,[]⟩) :=
    CanonicalForestWingUpdate.view none (color key) real wingOrientation headerKey payload newWingPayload forest newTagged
  obtain ⟨finalConfig,finalAssembly,finalTree⟩ := replacements ⟨newWing,[]⟩
  have emptyRecords : FrameRecords (fun record : Packet α ρ ι η => record = []) originalConnectors := by
    intro frame member
    have empty := originalEmpty frame member
    cases frame <;> exact empty
  have rootEmpty : tree.rootRecord.2 = [] := by
    have root := FrameRecords.root _ route.tree originalConnectors originalProper emptyRecords
    rw [← componentView,← erases,Source.mapRecords_root] at root
    exact root
  have finalRootEmpty : finalConfig.tree.rootRecord = [] := by
    rw [finalTree]
    exact FrameRecords.root _ newWing originalConnectors originalProper emptyRecords
  refine ⟨newForest,finalConfig,forestErases,forestErases.symm ▸ represented,
    CanonicalForestWingUpdate.unique forest (color key) newTagged forestUnique newUnique,?_,?_,?_⟩
  · rw [view]
    exact finalAssembly
  · intro q
    rw [view]
    by_cases equal : q = color key
    · subst q
      have oldPresent := CanonicalPacketLayerViews.component_real none (color key) real wingOrientation headerKey payload forest tagged present
      rw [Function.update_self]
      change true = (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest) (color key)).isSome
      rw [oldPresent]
      rfl
    · rw [Function.update_of_ne equal]
  · change output.tree.mapRecords Prod.snd = _
    rw [changed,plug_append,finalRootEmpty,finalTree]
    rw [rootEmpty] at rebuild
    rw [rebuild]
    rfl

end TangoSquared.Paper20261030.CanonicalIncomingComponentUpdate
