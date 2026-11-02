import ChaCha.Paper20261030.CanonicalIncomingComponentUpdate
import ChaCha.Paper20261030.CachedReachedAncestor

set_option autoImplicit false

/-! Reconstructing the actual cached active component after an incoming
operation. The logical forest and payload witnesses are updated by the
canonical routing theorem, while the retained active finger returns its
physical root and unchanged cache. This is the representation bridge
used after the executed incoming preparation. -/

namespace ChaCha.Paper20261030.CanonicalIncomingComponentUpdate

open ColoredStorage SourcePointer Structural PhysicalForestMetadata MultiSourceProgram
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors
open EnclosedRootedComponentExecution (Packet Cell)

variable {α β ρ ι η μ F : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq F]

local instance cachedIncomingUpdateColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem cached (markerId : ι) (color : α → Option Bool) (decorated : Source α (η × ρ))
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
    (initial final : Configuration F β (Cell α ρ ι η × μ)) (entry exit anchor : F)
    (parent : Cursor β (Cell α ρ ι η × μ))
    (parentRep : MultiSourceSingleCursor.Represents anchor parent initial)
    (parentErases : parent.mapRecords Prod.fst = EnclosingPacketOperation.output saved old ⟨tree,outside⟩)
    (valid : CanonicalComponentUniqueness.Valid markerId (initial.mapRecords Prod.fst).tree)
    (distinct : (initial.mapRecords Prod.fst).tree.shape.leaves.Nodup)
    (current : Cursor β (Cell α ρ ι η))
    (positioned : MultiSourceSingleCursor.Represents entry current (initial.mapRecords Prod.fst))
    (key : α) (member : key ∈ decorated.shape.leaves) (real : color key ≠ none)
    (payloadAt : CanonicalRetainedPayloadHandoff.PayloadAt (payload (color key) key) current)
    (target : Source β (Cell α ρ ι η))
    (returned : MultiSourceSingleCursor.Represents exit
      (EnclosingPacketOperation.output (current.focus.rootRecord.2.take 2) current.focus.rootRecord.1
        ⟨target,current.ancestors⟩) (final.mapRecords Prod.fst))
    (kept : CachedRootOperation.RetainedMetadata Prod.fst target.rootRecord.1 initial.tree final.tree)
    (parked : fingerLabel Prod.fst (final.mapRecords Prod.fst) anchor =
      fingerLabel Prod.fst (initial.mapRecords Prod.fst) anchor)
    (finalValid : CanonicalComponentUniqueness.Valid markerId (final.mapRecords Prod.fst).tree) :
    let newPayload := Function.update payload (color key)
      (Function.update (payload (color key)) key (target.mapRecords Prod.snd))
    ∃ finalForest finalConfig reached,
      erase finalForest = erase forest ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey newPayload finalForest)
        (layout (representation none wingOrientation headerKey newPayload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey newPayload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      MultiSourceSingleCursor.Represents anchor reached final ∧
      (reached.focus.mapRecords Prod.fst).mapRecords Prod.snd =
        finalConfig.tree.setRoot (PacketPrefixTransfer.reidentify tree.rootRecord.1 saved ++ finalConfig.tree.rootRecord) ∧
      reached.focus.rootRecord.1.1 = parent.focus.rootRecord.1.1 ∧
      reached.focus.rootRecord.2 = parent.focus.rootRecord.2 ∧
      (reached.mapRecords Prod.fst).ancestors = (parent.mapRecords Prod.fst).ancestors := by
  dsimp only
  have parentRaw := parentRep.mapRecords Prod.fst
  rw [parentErases] at parentRaw
  obtain ⟨finalForest,finalConfig,forestErases,finalRep,finalUnique,finalAssembly,presence,finalView⟩ :=
    update markerId color decorated forest represented forestUnique headerKey payload config assembled tree erases outside
      saved old neutral (initial.mapRecords Prod.fst) anchor entry parentRaw valid distinct current positioned key member real payloadAt
      target (returned.1 ▸ finalValid)
  obtain ⟨tagged,records,inside,originalConnectors,connectors,_,_,_,_,_,_,proper,_,_,currentView⟩ :=
    CanonicalReachedPayloadPosition.position markerId color decorated forest represented headerKey payload config assembled
      tree erases outside saved old neutral (initial.mapRecords Prod.fst) anchor entry parentRaw valid distinct current positioned key member real payloadAt
  let insideView :=
    (CanonicalRoutingCursor.cursor (payload (color key)) (wingOrientation (color key))
      ⟨.leaf key (current.focus.rootRecord.1,records),inside⟩).ancestors ++ connectors
  have insideProper : insideView ≠ [] := by
    intro empty
    exact proper (List.append_eq_nil_iff.mp empty).2
  have context : current.ancestors.map (Frame.mapRecords Prod.snd) =
      insideView ++ (parent.mapRecords Prod.fst).ancestors.map (Frame.mapRecords Prod.snd) := by
    rw [parentErases]
    simpa only [Cursor.mapRecords,List.append_assoc,insideView] using congrArg Cursor.ancestors currentView
  have outputView : (final.mapRecords Prod.fst).tree.mapRecords Prod.snd =
      plug (finalConfig.tree.setRoot (PacketPrefixTransfer.reidentify tree.rootRecord.1 saved ++ finalConfig.tree.rootRecord))
        ((parent.mapRecords Prod.fst).ancestors.map (Frame.mapRecords Prod.snd)) := by
    rw [returned.1,parentErases]
    exact finalView
  obtain ⟨reached,located,view,identity,cache,ancestors⟩ := CachedRootOperation.reached_ancestor
    (current.focus.rootRecord.2.take 2) current.focus.rootRecord.1 target initial final kept entry exit anchor current positioned
    parent parentRep insideView insideProper context returned finalValid.2.2 parked _ outputView
  exact ⟨finalForest,finalConfig,reached,forestErases,finalRep,finalUnique,finalAssembly,presence,located,view,identity,cache,ancestors⟩

end ChaCha.Paper20261030.CanonicalIncomingComponentUpdate
