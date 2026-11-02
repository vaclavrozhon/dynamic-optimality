import ChaCha.Paper20261030.ObservedHeadParameters

set_option autoImplicit false

/-! Every computed replacement header carries a canonically annotated
rooted virtual tree with distinct local physical identifiers. This follows
from the runtime encoder, including its rejection of oversized inputs. -/

namespace ChaCha.Paper20261030.VirtualPhysicalPackets

open ColoredStorage SourcePointer PhysicalForestMetadata

variable {α ρ : Type*}

def Ready (header : VirtualHeaderController.Virtual α (Record ρ Nat)) : Prop :=
  ∃ tagged : Option (Source α (Payload ρ Nat)),
    header = tagged.map (fun source => encodeCursor ⟨source,[]⟩) ∧
    ∀ source, tagged = some source → (source.inventory Prod.fst).Nodup

theorem ready_none : Ready (none : VirtualHeaderController.Virtual α (Record ρ Nat)) :=
  ⟨none,rfl,by intro source impossible; cases impossible⟩

theorem ready_encode (source : Source α (List ρ)) : Ready (encode source) := by
  refine ⟨tagSmall source,rfl,?_⟩
  intro tagged found
  cases source with
  | leaf key records =>
    cases found
    exact Multiset.nodup_singleton _
  | fork records left right =>
    cases left <;> cases right <;> cases found
    change ({0} + {1} + {2} : Multiset Nat).Nodup
    decide

theorem ready_erases (header : VirtualHeaderController.Virtual α (Record ρ Nat)) (ready : Ready header)
    (plain : Option (Source α (List ρ)))
    (decoded : decode header = plain.map (fun source => ⟨source,[]⟩)) :
    ∃ tagged : Option (Source α (Payload ρ Nat)),
      header = tagged.map (fun source => encodeCursor ⟨source,[]⟩) ∧
      tagged.map (Source.mapRecords Prod.snd) = plain ∧
      ∀ source, tagged = some source → (source.inventory Prod.fst).Nodup := by
  obtain ⟨tagged,encoded,unique⟩ := ready
  refine ⟨tagged,encoded,?_,unique⟩
  rw [encoded] at decoded
  have views := congrArg (Option.map Cursor.focus) decoded
  cases tagged with
  | none =>
    cases plain <;> cases decoded
    rfl
  | some source =>
    rw [Option.map_some,decode_root] at decoded
    cases plain with
    | none => cases decoded
    | some tree => exact congrArg some (congrArg Cursor.focus (Option.some.inj decoded))

end ChaCha.Paper20261030.VirtualPhysicalPackets

namespace ChaCha.Paper20261030.VirtualHeadPacketController

open Structural.HeadBoundary

variable {α ρ η : Type*}

theorem packRoot_ready (header : VirtualHeadPackets.Header α ρ η) : VirtualPhysicalPackets.Ready (packRoot header) := by
  cases header with
  | none => exact VirtualPhysicalPackets.ready_none
  | some current =>
    rcases current with ⟨tree,ancestors⟩
    cases ancestors with
    | nil => exact VirtualPhysicalPackets.ready_encode tree
    | cons => exact VirtualPhysicalPackets.ready_none

theorem exchange_ready (old fresh : Records ρ η (Option Bool)) (active incoming newHeader dormantHeader : Physical α ρ η)
    (computed : exchange old fresh active incoming = some (newHeader,dormantHeader)) :
    VirtualPhysicalPackets.Ready newHeader ∧ VirtualPhysicalPackets.Ready dormantHeader := by
  unfold exchange at computed
  obtain ⟨pair,_,same⟩ := Option.map_eq_some_iff.mp computed
  cases same
  exact ⟨packRoot_ready pair.1,packRoot_ready pair.2⟩

end ChaCha.Paper20261030.VirtualHeadPacketController

namespace ChaCha.Paper20261030.ObservedHeadParameters

open Structural.HeadBoundary

variable {α ρ η : Type*}

theorem output_ready (identifier : ρ → η)
    (active incoming : BoundaryReadController.State (Structural.HeadBoundary.Record ρ η (Option Bool)))
    (activeHeader incomingHeader : Physical α ρ η) (data : Data α ρ η)
    (computed : compute identifier active incoming activeHeader incomingHeader = some data) :
    VirtualPhysicalPackets.Ready data.newHeader ∧ VirtualPhysicalPackets.Ready data.dormantHeader := by
  unfold compute at computed
  split at computed
  · cases computed
  · split at computed
    · obtain ⟨pair,exchanged,same⟩ := Option.map_eq_some_iff.mp computed
      cases same
      exact VirtualHeadPacketController.exchange_ready _ _ _ _ pair.1 pair.2 exchanged
    · cases computed

end ChaCha.Paper20261030.ObservedHeadParameters
