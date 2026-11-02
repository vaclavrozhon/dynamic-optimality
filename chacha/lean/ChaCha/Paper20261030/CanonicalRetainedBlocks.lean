import ChaCha.Paper20261030.CanonicalHeadWingViews
import ChaCha.Paper20261030.CanonicalRepairedRouting

set_option autoImplicit false

/-!
# Retained tagged block witnesses shared by input and output proofs

The input decomposition keeps each opaque block's canonical tagged
projection and old parent. Its presence bit is the observed bit. These
are proof witnesses only. Ordinary-root exclusion then supplies the
canonical repaired-routing invariant for exactly those same blocks.
-/

namespace ChaCha.Paper20261030.CanonicalRetainedBlocks

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers
open CanonicalPacketLayerViews CanonicalRoutingDecomposition

variable {κ α β ρ ι : Type*}

def Witness (bits : κ → Bool) (blocks : κ → Source β (Packet α ρ ι)) (key : κ)
    (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (plain : ProjectionLocal.Projected α ρ) : Prop :=
  ∃ (tagged : Option (Tagged α ρ ι)) (parent : Option ι),
    tagged.map (Source.mapRecords Prod.snd) = plain ∧ bits key = tagged.isSome ∧
    ∀ tree, tagged = some tree → blocks key = routing payload reverse parent tree

private theorem augmentation_erases (dummyId : ι) (source : Source β (Packet α ρ ι)) :
    (source.mapRecords (fun packet => (dummyId,packet))).mapRecords Prod.snd = source := by
  induction source <;> simp_all only [Source.mapRecords]

theorem of_piece (dummyId : ι) (bits : κ → Bool) (blocks : κ → Source β (Packet α ρ ι)) (key : κ)
    (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (plain : ProjectionLocal.Projected α ρ)
    (piece : MixedHeadInputView.Physical β α ρ ι) (fallback : Source β (Context.Cell α ρ ι))
    (canonical : CanonicalHeadWingViews.Canonical dummyId payload reverse plain piece)
    (present : bits key = piece.isSome) (block : blocks key = (piece.getD fallback).mapRecords Prod.snd) :
    Witness bits blocks key payload reverse plain := by
  obtain ⟨tagged,parent,erases,rfl⟩ := canonical
  refine ⟨tagged,parent,erases,?_,?_⟩
  · simpa only [render,Option.isSome_map] using present
  · intro tree equal
    subst tagged
    rw [block]
    simp only [render,Option.map_some,Option.getD_some]
    exact augmentation_erases dummyId _

private def firstId : Packet α ρ ι → Option ι
  | some (.real ((id,_),_)) :: _ => some id
  | _ => none

private theorem root_set {σ : Type*} (source : Source β σ) (record : σ) :
    (source.setRoot record).rootRecord = record := by cases source <;> rfl

private theorem firstId_routing (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (parent : Option ι) (tagged : Tagged α ρ ι) :
    firstId (routing payload reverse parent tagged).rootRecord = some tagged.rootRecord.1 := by
  cases tagged with
  | leaf key record => rw [leaf,root_set]; rfl
  | fork record left right => rw [fork]; rfl

theorem ordinary_id (markerId : ι) (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (parent : Option ι) (tagged : Tagged α ρ ι)
    (ordinary : OrdinaryBase markerId (routing payload reverse parent tagged).rootRecord (.prefix [])) :
    tagged.rootRecord.1 ≠ markerId := by
  obtain ⟨id,records,fields,rest,equal,different⟩ := ordinary
  have ids := congrArg firstId equal
  rw [firstId_routing] at ids
  have same : tagged.rootRecord.1 = id := Option.some.inj ids
  rw [same]
  exact different

theorem repaired (markerId : ι) (bits : κ → Bool) (blocks : κ → Source β (Packet α ρ ι)) (key : κ)
    (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (plain : ProjectionLocal.Projected α ρ)
    (witness : Witness bits blocks key payload reverse plain)
    (ordinary : bits key = true → OrdinaryBase markerId (blocks key).rootRecord (.prefix [])) :
    CanonicalRepairedRouting.Layout markerId blocks payload reverse plain
      (HeadPacketRepair.block bits key) (HeadPacketLayout.block bits key) := by
  obtain ⟨tagged,parent,erases,present,blockView⟩ := witness
  rw [← erases]
  apply CanonicalRepairedRouting.block markerId blocks payload reverse bits key tagged parent present blockView
  intro tree equal
  have valid := ordinary (by rw [present,equal]; rfl)
  rw [blockView tree equal] at valid
  exact ordinary_id markerId payload reverse parent tree valid

structure HeadWitnesses (bits : Fin 8 → Bool) (blocks : Fin 8 → Source β (Packet α ρ ι))
    (activePayload incomingPayload : Option Bool → α → Source β (Packet α ρ ι)) (headerKey : α)
    (head oldTail incomingTail : Bool → ProjectionLocal.Projected α ρ) : Prop where
  headLeft : Witness bits blocks 0 (activePayload (some true)) false (head true)
  headRight : Witness bits blocks 7 (activePayload (some false)) true (head false)
  oldLeft : Witness bits blocks 1 (activePayload (some true)) false (oldTail true)
  oldRight : Witness bits blocks 3 (activePayload (some false)) true (oldTail false)
  incomingLeft : Witness bits blocks 4 (incomingPayload (some true)) false (incomingTail true)
  incomingRight : Witness bits blocks 6 (incomingPayload (some false)) true (incomingTail false)
  oldBottom : blocks 2 = activePayload none headerKey
  newBottom : blocks 5 = incomingPayload none headerKey

end ChaCha.Paper20261030.CanonicalRetainedBlocks
