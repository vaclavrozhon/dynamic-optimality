import ChaCha.Paper20261030.ReenteredComponentBody
import ChaCha.Paper20261030.EnclosedCanonicalComponent
import ChaCha.Paper20261030.EnclosingPacketAnchors

set_option autoImplicit false

/-! The enclosing component controller now includes charged entry.
Starting from one reached root, it strips the enclosing prefix, places
its fingers, runs the component, returns from the virtual header, and
repairs the enclosing prefix and parent references. Cost: at most 2*c+21
for a label-preserving payload execution of cost c. -/

namespace ChaCha.Paper20261030.ReenteredComponentExecution

open ColoredStorage SourcePointer MultiSourceProgram PhysicalPacketStaging PacketLayers
open ForestConnector.ThreeColors

variable {α β ρ ι G σ : Type*} [DecidableEq G] [DecidableEq ι]

def program (origin : Sum (Option Bool) G) (left right : Bool) (count levels : Nat) (hasParent : Bool)
    (source : Program σ (Option Bool) (Packet α ρ ι)) (initial : σ) :=
  MultiSourceEnclosingOperation.program origin (fun _ => .inl none) count levels hasParent
    (body origin left right source initial) (.first (.first NestedComponentEntry.destinations))

theorem execute (markerId : ι) (origin : Sum (Option Bool) G)
    (firstForest finalForest : ProjectionForest.State (Option Bool) β (Option (Datum α ρ ι)))
    (firstHeader finalHeader : Source β (Packet α ρ ι))
    (atRoots : ∀ q current, firstForest q = some current → current.ancestors = [])
    (source : Program σ (Option Bool) (Packet α ρ ι)) {initial last : σ}
    {after : Configuration (Option Bool) β (Packet α ρ ι)} {reads cost}
    (run : MultiSourceWriteLabels.Run (List.map PacketWriteLabels.label) source initial
      (configuration firstForest ⟨firstHeader,[]⟩) last after reads cost)
    (tree : Source β (Context.Cell α ρ ι))
    (erases : tree.mapRecords Prod.snd = (configuration firstForest ⟨firstHeader,[]⟩).tree)
    (outside : List (Frame β (Context.Cell α ρ ι)))
    (global : Configuration (Sum (Option Bool) G) β (Context.Cell α ρ ι))
    (atRoot : MultiSourceSingleCursor.Represents origin ⟨tree,outside⟩ global)
    (valid : WellFormed global) (physical : CanonicalComponentUniqueness.Valid markerId global.tree)
    (reserved : markerId ∉ global.tree.inventory Prod.fst) (saved : Packet α ρ ι)
    (assembled : after = configuration finalForest ⟨finalHeader,[]⟩)
    (presence : ∀ q, (finalForest q).isSome = (firstForest q).isSome) :
    ∃ (finalComponent : Configuration (Option Bool) β (Context.Cell α ρ ι)), ∃ entryBits finalBits target observed total,
      Run (program origin (firstForest (some true)).isSome (firstForest (some false)).isSome
          saved.length (headerPath firstForest).length (!outside.isEmpty) source initial)
        (.first .start) (MultiSourcePacketPrefix.attached saved tree outside global)
        (.second (some ⟨tree.rootRecord.1,finalComponent.tree.rootRecord.1,.second entryBits (finalBits,.ready last)⟩)
          (some .done)) target observed total ∧
      finalComponent.mapRecords Prod.snd = after ∧
      MultiSourceSingleCursor.Represents (.inl none)
        (EnclosingPacketOperation.output saved tree.rootRecord.1 ⟨finalComponent.tree,outside⟩) target ∧
      target.tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId target.tree ∧
      markerId ∉ target.tree.inventory Prod.fst ∧ WellFormed target ∧
      target.tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst ∧
      (∀ extra : G, fingerLabel Prod.fst target (.inr extra) = fingerLabel Prod.fst global (.inr extra)) ∧
      total ≤ 2*cost+21 := by
  obtain ⟨finalComponent,entryBits,finalBits,middle,bodyReads,bodyCost,bodyRun,finalErases,finalRep,
    middleTree,ids,middlePhysical,middleReserved,middleValid,bodyOrder,bodyAnchors,bound⟩ :=
    body_execute markerId origin firstForest firstHeader atRoots source run tree erases outside global atRoot valid physical reserved
  obtain ⟨focus,inside,maskedReturned,rootEq,length,short⟩ := NestedComponentReturn.header finalForest finalHeader
    finalComponent (finalErases.trans assembled) outside (middle.mask finalBits) finalRep
  have returned : MultiSourceSingleCursor.Represents (.inl none) ⟨focus,inside++outside⟩ middle :=
    ⟨maskedReturned.1,(mask_present finalBits middle (.inl none) _ maskedReturned.2).2⟩
  have inputValid := MultiSourcePacketPrefix.attached_wellFormed saved tree outside global atRoot.1 valid
  obtain ⟨target,observed,total,actual,targetRep,finalIds,others,finalValid,bounded⟩ :=
    MultiSourceEnclosingOperation.execute_others origin (fun _ => .inl none) saved
      (body origin (firstForest (some true)).isSome (firstForest (some false)).isSome source initial)
      (.first (.first NestedComponentEntry.destinations)) (.second entryBits (finalBits,.ready last))
      global middle bodyRun tree focus outside inside outside atRoot returned middlePhysical.2.2 inputValid
  rw [rootEq] at actual targetRep
  have samePath : headerPath finalForest = headerPath firstForest :=
    congrArg₂ (fun (right left : Bool) =>
      (if right then [false] else []) ++ (if left then [true] else []))
      (presence (some false)) (presence (some true))
  rw [length,congrArg List.length samePath] at actual
  have barePhysical : CanonicalComponentUniqueness.Valid markerId (plug finalComponent.tree outside) :=
    middleTree ▸ middlePhysical
  have bareReserved : markerId ∉ (plug finalComponent.tree outside).inventory Prod.fst := middleTree ▸ middleReserved
  obtain ⟨outputPhysical,outputReserved⟩ := EnclosingPacketOperation.valid markerId saved tree.rootRecord.1
    ⟨finalComponent.tree,outside⟩ bareReserved barePhysical
  have sameTree : target.tree.mapRecords Prod.fst = middle.tree.mapRecords Prod.fst := by
    rw [targetRep.1,EnclosingPacketOperation.identifier_tree,middleTree]
    rfl
  refine ⟨finalComponent,entryBits,finalBits,target,observed,total,actual,finalErases,targetRep,
    finalIds.trans ids,?_,?_,finalValid,?_,?_,by omega⟩
  · rw [targetRep.1]
    exact outputPhysical
  · rw [targetRep.1]
    exact outputReserved
  · have order := congrArg (Source.inorderLabels id) sameTree
    simp only [Source.inorderLabels_map,Function.comp_def,id_eq] at order
    exact order.trans bodyOrder
  · intro extra
    exact (fingerLabel_congr Prod.fst (.inr extra) sameTree (others (.inr extra) (by simp))).trans
      (bodyAnchors extra)

end ChaCha.Paper20261030.ReenteredComponentExecution
