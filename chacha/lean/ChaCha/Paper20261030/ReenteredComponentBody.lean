import ChaCha.Paper20261030.NestedComponentEntry
import ChaCha.Paper20261030.PacketWriteLabels
import ChaCha.Paper20261030.NestedImmutableAnchors

set_option autoImplicit false

/-! A component body starts from a single reached root. The controller
first places its working fingers, then executes the payload program with
immutable ids and a presence mask. No canonical initial finger placement
is assumed. Wing bits remain scalar inputs, to be read by the caller. -/

namespace ChaCha.Paper20261030.ReenteredComponentExecution

open ColoredStorage SourcePointer MultiSourceProgram PhysicalPacketStaging PacketLayers
open ForestConnector.ThreeColors

variable {α β ρ ι G σ : Type*} [DecidableEq G] [DecidableEq ι]

abbrev EntryState (G : Type*) := MultiSourceFinish.State (List (Sum (Option Bool) G))
  ((Sum (Option Bool) G → Bool) × MultiSourceDownward.Schedule (Option Bool)) Unit

def select (left right : Bool) : EntryState G → (Sum (Option Bool) G → Bool)
  | .first _ => NestedComponentEntry.bits left right
  | .second _ (bits,_) => bits

def body (origin : Sum (Option Bool) G) (left right : Bool)
    (source : Program σ (Option Bool) (Packet α ρ ι)) (initial : σ) :=
  MultiSourceFinish.program (NestedComponentEntry.program origin left right) (select left right)
    (fun bits => (bits,MultiSourceAugment.State.ready initial))
    (fun _ => MultiSourceMask.program (MultiSourceNestedImmutable.program (ι := ι) source))

theorem body_execute (markerId : ι) (origin : Sum (Option Bool) G)
    (firstForest : ProjectionForest.State (Option Bool) β (Option (Datum α ρ ι)))
    (firstHeader : Source β (Packet α ρ ι))
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
    (reserved : markerId ∉ global.tree.inventory Prod.fst) :
    ∃ (finalComponent : Configuration (Option Bool) β (Context.Cell α ρ ι)), ∃ entryBits finalBits target observed total,
      Run (body origin (firstForest (some true)).isSome (firstForest (some false)).isSome source initial)
        (.first (.first NestedComponentEntry.destinations)) global (.second entryBits (finalBits,.ready last)) target observed total ∧
      finalComponent.mapRecords Prod.snd = after ∧
      MultiSourceRegisterExtension.project (target.mask finalBits) = finalComponent.extend outside ∧
      target.tree = plug finalComponent.tree outside ∧
      target.tree.inventory Prod.fst = global.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId target.tree ∧
      markerId ∉ target.tree.inventory Prod.fst ∧ WellFormed target ∧
      target.tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst ∧
      (∀ extra : G, fingerLabel Prod.fst target (.inr extra) = fingerLabel Prod.fst global (.inr extra)) ∧
      total ≤ 2*cost+8 := by
  let left := (firstForest (some true)).isSome
  let right := (firstForest (some false)).isSome
  obtain ⟨component,entryBits,entered,entryReads,entryCost,entryRun,componentErases,componentTree,entryRep,entryTree,entryValid,entryBitsEq,entryOthers,entryBound⟩ :=
    NestedComponentEntry.execute Prod.snd origin firstForest firstHeader atRoots tree erases outside global atRoot valid
  have entryPhysical : CanonicalComponentUniqueness.Valid markerId (entered.mask entryBits).tree := by
    change CanonicalComponentUniqueness.Valid markerId entered.tree
    rw [entryTree]
    exact physical
  obtain ⟨finalComponent,logicalTarget,bodyReads,bodyCost,compiled,finalErases,finalRep,logicalTree,ids,invariant,_,bound⟩ :=
    MultiSourceNestedImmutable.execute_predicate (List.map PacketWriteLabels.label) (PacketWriteLabels.Relation markerId)
      source run component componentErases outside (entered.mask entryBits) entryRep
      (NestedComponentEntry.masked_wellFormed _ entered entryValid)
      ((PacketWriteLabels.holds_iff markerId _).mpr ⟨entryPhysical.1,entryPhysical.2.1⟩)
  obtain ⟨finalBits,target,bodyObserved,actual,maskEq,finalValid⟩ :=
    MultiSourceMask.compile_run compiled entryBits entered entryValid rfl
  have complete := MultiSourceFinish.finish (select left right)
    (fun bits => (bits,MultiSourceAugment.State.ready initial))
    (fun _ => MultiSourceMask.program (MultiSourceNestedImmutable.program (ι := ι) source)) entryRun actual
  have targetTree := congrArg (fun c : Configuration (Sum (Option Bool) G) β (Context.Cell α ρ ι) => c.tree) maskEq
  change target.tree = logicalTarget.tree at targetTree
  have globalIds : target.tree.inventory Prod.fst = global.tree.inventory Prod.fst := by
    rw [targetTree,ids]
    change entered.tree.inventory Prod.fst = global.tree.inventory Prod.fst
    rw [entryTree]
  obtain ⟨aligned,clear⟩ := (PacketWriteLabels.holds_iff markerId logicalTarget.tree).mp invariant
  have anchors := MultiSourceNestedImmutable.anchors source run.run component componentErases outside
    (entered.mask entryBits) entryRep compiled
  refine ⟨finalComponent,entryBits,finalBits,target,_,_,complete,finalErases,?_,targetTree.trans logicalTree,
    globalIds,?_,?_,finalValid,?_,?_,by omega⟩
  · rw [maskEq]
    exact finalRep
  · exact ⟨targetTree.symm ▸ aligned,targetTree.symm ▸ clear,globalIds.symm ▸ physical.2.2⟩
  · rw [globalIds]
    exact reserved
  · rw [targetTree,MultiSourceNestedImmutable.inorderLabels source run.run component componentErases outside
      (entered.mask entryBits) entryRep compiled]
    change entered.tree.inorderLabels Prod.fst = global.tree.inorderLabels Prod.fst
    rw [entryTree]
  · intro extra
    have initialBit : entryBits (.inr extra) = true := by
      rw [entryBitsEq]
      rfl
    have finalBit : finalBits (.inr extra) = true :=
      (MultiSourceMask.Run.bit _ (.inr extra)
        (MultiSourceRegisterExtension.keeps_copy_extra _ extra) actual).trans initialBit
    have initialLabel : fingerLabel Prod.fst (entered.mask entryBits) (.inr extra) =
        fingerLabel Prod.fst entered (.inr extra) := by
      simp only [fingerLabel,Configuration.mask,initialBit,if_true]
    have finalLabel : fingerLabel Prod.fst (target.mask finalBits) (.inr extra) =
        fingerLabel Prod.fst target (.inr extra) := by
      simp only [fingerLabel,Configuration.mask,finalBit,if_true]
    rw [← finalLabel,maskEq,anchors extra,initialLabel]
    exact fingerLabel_congr Prod.fst (.inr extra) (congrArg (Source.mapRecords Prod.fst) entryTree) (entryOthers extra)

end ChaCha.Paper20261030.ReenteredComponentExecution
