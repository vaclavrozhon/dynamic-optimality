import ChaCha.Paper20261030.LocalMixedHeadExchange
import ChaCha.Paper20261030.HeadRootBoundaryMetadata

/-!
# The mixed head controller at depth zero

There are four observed boundary records and no common prefix. We reuse
the eight-slot controller with its two prefix slots absent. The auxiliary
`lift` record has no children, so it produces no logical markers and no
physical packet; `active_layout` proves that the actual computed layout
is exactly the six-block root layout. It is not an allocated source node.

The same controller therefore handles this boundary without introducing
a nonempty-prefix hypothesis. Acquisition, canonical input representation,
neighbor repair, and component restoration remain separate obligations.
-/

namespace ChaCha.Paper20261030.RootMixedHeadExchange

open ColoredStorage SourcePointer SourceLocalProgram Structural HeadBoundary PhysicalPacketStaging PacketLayers
open PacketAlignment

variable {α β ρ ι η : Type*}

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

def lift (records : RootRecords ρ η) : Records ρ η (Option Bool) :=
  ⟨(records.oldTerminal.1,⟨none,∅,none⟩),records.oldHigh,records.incomingHigh,records.oldTerminal,records.incomingTerminal⟩

theorem prefix_absent (records : RootRecords ρ η) :
    ObservedHeadBlueprint.bits (lift records) 0 = false ∧
    ObservedHeadBlueprint.bits (lift records) 7 = false := ⟨rfl,rfl⟩

theorem no_prefix_records (records : RootRecords ρ η) (values : HeadBoundary.Record ρ η (Option Bool) → α)
    (color : Option Bool) : ObservedHeadBlueprint.connector values color (lift records).low = [] := rfl

private theorem add_nil (expression : Expression α ρ ι) : HeadPacketLayout.addLogical [] expression = expression := by
  cases expression <;> rfl

private theorem join_none_left (markerId : ι) (layout : HeadPacketLayout.Layout (Fin 8) α ρ ι) :
    HeadPacketLayout.realJoin markerId [] none layout = layout := by
  cases layout with
  | none => rfl
  | some tree => cases tree <;> simp only [HeadPacketLayout.realJoin,HeadPacketLayout.push,Option.map_some,
      Source.rootRecord,add_nil,Source.setRoot]

private theorem join_none_right (markerId : ι) (layout : HeadPacketLayout.Layout (Fin 8) α ρ ι) :
    HeadPacketLayout.realJoin markerId [] layout none = layout := by
  cases layout with
  | none => rfl
  | some tree => cases tree <;> simp only [HeadPacketLayout.realJoin,HeadPacketLayout.push,Option.map_some,
      Source.rootRecord,add_nil,Source.setRoot]

def activeLayout (markerId : ι) (bits : Fin 8 → Bool) (tl b tr : Fin 8)
    (boundary : HeadPacketLayout.Layout (Fin 8) α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (direction : Bool) (high terminal : HeadBoundary.Record ρ η (Option Bool))
    (header : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :=
  let child := HeadPacketLayout.attachment markerId terminal boundary
  let left := if direction then HeadPacketLayout.realJoin markerId (ObservedHeadBlueprint.owned (some true) high)
      child (HeadPacketLayout.block bits tl)
    else HeadPacketLayout.push (HeadPacketLayout.addLogical (ObservedHeadBlueprint.owned (some true) high))
      (HeadPacketLayout.block bits tl)
  let right := if direction then HeadPacketLayout.push (HeadPacketLayout.addLogical (ObservedHeadBlueprint.owned (some false) high))
      (HeadPacketLayout.block bits tr)
    else HeadPacketLayout.realJoin markerId (ObservedHeadBlueprint.owned (some false) high) (HeadPacketLayout.block bits tr) child
  HeadPacketLayout.primaryJoin (HeadPacketLayout.primaryJoin left (HeadPacketLayout.bottom b header)) right

theorem active_layout (markerId : ι) (bits : Fin 8 → Bool) (tl b tr : Fin 8)
    (noLeft : bits 0 = false) (noRight : bits 7 = false)
    (boundary : HeadPacketLayout.Layout (Fin 8) α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (direction : Bool) (records : RootRecords ρ η) (high terminal : HeadBoundary.Record ρ η (Option Bool))
    (header : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    HeadPacketLayout.active markerId bits 0 7 tl b tr boundary direction (lift records).low high terminal header =
      activeLayout markerId bits tl b tr boundary direction high terminal header := by
  simp only [HeadPacketLayout.active,activeLayout,ObservedHeadBlueprint.owned,
    ObservedHeadBlueprint.connector,lift,List.filterMap_nil]
  have leftAbsent : HeadPacketLayout.block (α := α) (ρ := HeadBoundary.Record ρ η (Option Bool)) (ι := ι) bits 0 = none := by
    simp only [HeadPacketLayout.block,noLeft,Bool.false_eq_true,if_false]
  have rightAbsent : HeadPacketLayout.block (α := α) (ρ := HeadBoundary.Record ρ η (Option Bool)) (ι := ι) bits 7 = none := by
    simp only [HeadPacketLayout.block,noRight,Bool.false_eq_true,if_false]
  rw [leftAbsent,rightAbsent,join_none_left,join_none_right]
  rfl

theorem run (markerId : ι) (direction : Bool) (old fresh : RootRecords ρ η)
    (oldHeader incomingHeader newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (newValid : Neutral markerId newHeader) (dormantValid : Neutral markerId dormantHeader)
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (ordinary : HeadPacketLayout.WingRoots markerId (ObservedHeadBlueprint.bits (lift old)) blocks)
    (before after : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (beforeFound : HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits (lift old)) direction (lift old) oldHeader incomingHeader = some before)
    (afterFound : HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits (lift old)) direction (lift fresh) newHeader dormantHeader = some after)
    (current : Cursor β (ι × Packet α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (represented : Reached.Stored blocks before current.focus)
    (aligned : SourceRecordPredicate.Holds (Predicate markerId) current.tree) :
    ∃ target reads cost,
      Run (MixedHeadExchange.program markerId
        (MixedHeadExchange.actions markerId direction (lift old) (lift fresh) oldHeader incomingHeader newHeader dormantHeader)
        (PacketLayers.Context.commands (after.mapRecords blueprint)))
        (.inl (.running (PacketLayers.Context.commands (before.mapRecords blueprint)))) current
        (.inr (.inr (.running []))) target reads cost ∧
      Reached.Repacked blocks after target.focus ∧
      target.ancestors.map (Frame.mapRecords Prod.snd) = current.ancestors.map (Frame.mapRecords Prod.snd) ∧
      target.tree.inventory Prod.fst = current.tree.inventory Prod.fst ∧
      SourceRecordPredicate.Holds (Predicate markerId) target.tree ∧ cost ≤ 692 :=
  MixedHeadExchange.run markerId direction (lift old) (lift fresh) oldHeader incomingHeader newHeader dormantHeader
    newValid dormantValid blocks ordinary before after beforeFound afterFound current represented aligned

end ChaCha.Paper20261030.RootMixedHeadExchange
