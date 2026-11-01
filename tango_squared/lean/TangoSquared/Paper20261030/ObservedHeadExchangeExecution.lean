import TangoSquared.Paper20261030.ObservedHeadParameters
import TangoSquared.Paper20261030.CanonicalHeadExecution

set_option autoImplicit false

/-! The finite head program is selected entirely from acquired data.
Its before/after contexts and physical repair blueprint are computed from
the five records, exit direction, and stored header packets. The source
trees used to justify this selection are not runtime arguments. -/

namespace TangoSquared.Paper20261030.ObservedHeadExchangeExecution

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers HeadBoundary
open RepairedPayloadLayouts
open ObservedHeadParameters (Data packet)

variable {α β ρ η F : Type*} [DecidableEq F]

abbrev Logical (ρ η : Type*) := HeadBoundary.Record ρ η (Option Bool)

structure Plan (α ρ η : Type*) where
  before : Source (Fin 8) (Expression α (Logical ρ η) Nat)
  after : Source (Fin 8) (Expression α (Logical ρ η) Nat)
  repair : Source (Fin 8) MixedPacketRepair.Layers

def plan (markerId : Nat) (data : Data α ρ η) : Option (Plan α ρ η) :=
  match HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits data.old) data.direction data.old
      (packet data.activeHeader) (packet data.incomingHeader),
    HeadPacketLayout.after markerId (ObservedHeadBlueprint.bits data.old) data.direction data.fresh
      (packet data.newHeader) (packet data.dormantHeader),
    HeadPacketRepair.after (ObservedHeadBlueprint.bits data.old) data.direction
      (packet data.newHeader).length (packet data.dormantHeader).length with
  | some before,some after,some repair => some ⟨before,after,repair⟩
  | _,_,_ => none

abbrev State (α ρ η : Type*) := Option (EnclosingPacketOperation.State
  (RepairedHeadExchange.State α (Logical ρ η) Nat) α (Logical ρ η) Nat)

def program (finger : F) (markerId count : Nat) (hasParent : Bool) (data : Data α ρ η) :
    MultiSourceProgram.Program (State α ρ η) F (Context.Cell α (Logical ρ η) Nat) :=
  match plan markerId data with
  | none => fun _ => .halt
  | some selected => MultiSourceSingleCursor.program
      (EnclosingPacketOperation.program count hasParent
        (RepairedHeadExchange.program markerId
          (MixedHeadExchange.actions markerId data.direction data.old data.fresh
            (packet data.activeHeader) (packet data.incomingHeader) (packet data.newHeader) (packet data.dormantHeader))
          (Context.commands (selected.after.mapRecords blueprint)) selected.repair)
        (.inl (.inl (.running (Context.commands (selected.before.mapRecords blueprint)))))) finger

theorem execute (finger : F) (markerId : Nat) (depth : α) (data : Data α ρ η)
    (enclosing : Packet α (Logical ρ η) Nat) (current : Cursor β (Context.Cell α (Logical ρ η) Nat))
    (blocks : Fin 8 → Source β (Packet α (Logical ρ η) Nat))
    (before : Source (Fin 8) (Expression α (Logical ρ η) Nat))
    (beforeFound : HeadPacketLayout.before markerId (ObservedHeadBlueprint.bits data.old) data.direction data.old
      (packet data.activeHeader) (packet data.incomingHeader) = some before)
    (stored : Reached.Stored blocks before current.focus)
    (ready : PacketConditions.wings (fun base => Ready base (.prefix [])) (ObservedHeadBlueprint.bits data.old) blocks)
    (clear : SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) current.tree)
    (reserved : markerId ∉ current.tree.inventory Prod.fst) (unique : (current.tree.inventory Prod.fst).Nodup)
    (aligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) current.tree)
    (activePayload incomingPayload : Option Bool → α → Source β (Packet α (Logical ρ η) Nat)) (headerKey : α)
    (head oldTail incomingTail : Bool → ProjectionLocal.Projected α (Logical ρ η))
    (witnesses : CanonicalRetainedBlocks.HeadWitnesses (ObservedHeadBlueprint.bits data.old) blocks
      activePayload incomingPayload headerKey head oldTail incomingTail)
    (separate : ∀ side, Separate (head side) (incomingTail side))
    (headAbsent : ∀ side, depth ∉ ports (head side)) (incomingAbsent : ∀ side, depth ∉ ports (incomingTail side))
    (config : MultiSourceProgram.Configuration F β (Context.Cell α (Logical ρ η) Nat))
    (located : MultiSourceSingleCursor.Represents finger
      ⟨PacketPrefixTransfer.attach enclosing current.focus,current.ancestors⟩ config)
    (wellFormed : MultiSourceProgram.WellFormed config) :
    ∃ selected bare finalConfig reads cost,
      plan markerId data = some selected ∧
      MultiSourceProgram.Run (program finger markerId enclosing.length (!current.ancestors.isEmpty) data)
        (some (.transferring .start)) config (some (.done (.inr (.ready [])))) finalConfig reads cost ∧
      MultiSourceSingleCursor.Represents finger (EnclosingPacketOperation.output enclosing current.focus.rootRecord.1 bare) finalConfig ∧
      CanonicalHeadSuccessor.Result activePayload incomingPayload head oldTail incomingTail data.direction depth data.fresh
        (packet data.newHeader) (packet data.dormantHeader) (activePayload none headerKey) (incomingPayload none headerKey)
        (some (bare.focus.mapRecords Prod.snd)) ∧
      finalConfig.tree.inventory Prod.fst = config.tree.inventory Prod.fst ∧
      CanonicalComponentUniqueness.Valid markerId finalConfig.tree ∧ markerId ∉ finalConfig.tree.inventory Prod.fst ∧
      MultiSourceProgram.WellFormed finalConfig ∧ cost ≤ 803 ∧ bare.ancestors.isEmpty = current.ancestors.isEmpty := by
  obtain ⟨after,repairPlan,bare,finalConfig,reads,cost,afterFound,repairFound,actual,returned,result,ids,valid,finalReserved,finalValid,bound,sameEmpty⟩ :=
    CanonicalHeadExecution.execute finger markerId data.direction depth data.old data.fresh
      (packet data.activeHeader) (packet data.incomingHeader) (packet data.newHeader) (packet data.dormantHeader)
      (PacketAlignment.header markerId data.newHeader) (PacketAlignment.header markerId data.dormantHeader)
      (MarkerFreePackets.header markerId data.newHeader) (MarkerFreePackets.header markerId data.dormantHeader)
      enclosing current blocks before beforeFound stored ready clear reserved unique aligned
      activePayload incomingPayload headerKey head oldTail incomingTail witnesses separate headAbsent incomingAbsent config located wellFormed
  have selected : plan markerId data = some ⟨before,after,repairPlan⟩ := by
    simp only [plan,beforeFound,afterFound,repairFound]
  refine ⟨⟨before,after,repairPlan⟩,bare,finalConfig,reads,cost,selected,?_,returned,result,ids,valid,finalReserved,finalValid,bound,sameEmpty⟩
  rw [program,selected]
  exact actual

end TangoSquared.Paper20261030.ObservedHeadExchangeExecution
