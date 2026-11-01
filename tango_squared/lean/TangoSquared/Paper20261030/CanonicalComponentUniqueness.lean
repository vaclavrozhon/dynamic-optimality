import TangoSquared.Paper20261030.CanonicalRoutingUniqueness
import TangoSquared.Paper20261030.CanonicalComponentReconstruction

set_option autoImplicit false

/-!
# Unique identifiers in reconstructed component forests

A canonical packet view inherits actual vertices from the surrounding
physical tree. Primary joins preserve this realization on each present
piece. Consequently both real routing witnesses have unique ids; the
virtual witness uses its separately checked local header ids.
-/

namespace TangoSquared.Paper20261030.CanonicalComponentUniqueness

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers
open CanonicalPacketLayerViews PhysicalForestMetadata

variable {α β ρ ι : Type*}

def Valid (markerId : ι) (source : Source β (Context.Cell α ρ ι)) : Prop :=
  SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) source ∧
  SourceRecordPredicate.Holds (MarkerFreePackets.Vertex markerId) source ∧
  (source.inventory Prod.fst).Nodup

def Realized (markerId : ι) (view : Option (Source β (Packet α ρ ι))) : Prop :=
  ∀ tree, view = some tree → ∃ source : Source β (Context.Cell α ρ ι),
    source.mapRecords Prod.snd = tree ∧ Valid markerId source

theorem of_source (markerId : ι) (source : Source β (Context.Cell α ρ ι))
    (valid : Valid markerId source) : Realized markerId (some (source.mapRecords Prod.snd)) := by
  intro tree equal
  exact ⟨source,Option.some.inj equal,valid⟩

theorem fork_valid (markerId : ι) (record : Context.Cell α ρ ι)
    (left right : Source β (Context.Cell α ρ ι)) (valid : Valid markerId (.fork record left right)) :
    Valid markerId left ∧ Valid markerId right := by
  obtain ⟨aligned,clear,ids⟩ := valid
  obtain ⟨_,al,ar⟩ := (SourceRecordPredicate.fork _ _ _ _).mp aligned
  obtain ⟨_,cl,cr⟩ := (SourceRecordPredicate.fork _ _ _ _).mp clear
  simp only [Source.inventory_fork,Multiset.nodup_add] at ids
  exact ⟨⟨al,cl,ids.1.2.1⟩,⟨ar,cr,ids.2.1⟩⟩

theorem join (markerId : ι) (left right : Option (Source β (Packet α ρ ι)))
    (valid : Realized markerId (ProjectionLocal.join left right)) :
    Realized markerId left ∧ Realized markerId right := by
  cases left with
  | none => exact ⟨(by intro tree equal; cases equal),valid⟩
  | some left =>
    cases right with
    | none => exact ⟨valid,by intro tree equal; cases equal⟩
    | some right =>
      obtain ⟨source,erases,actual⟩ := valid (.fork [] left right) rfl
      cases source with
      | leaf => cases erases
      | fork record actualLeft actualRight =>
        simp only [Source.mapRecords,Source.fork.injEq] at erases
        obtain ⟨leftValid,rightValid⟩ := fork_valid markerId record actualLeft actualRight actual
        constructor
        · intro tree equal
          exact ⟨actualLeft,erases.2.1.trans (Option.some.inj equal),leftValid⟩
        · intro tree equal
          exact ⟨actualRight,erases.2.2.trans (Option.some.inj equal),rightValid⟩

theorem routing_unique (markerId : ι) (payload : α → Source β (Packet α ρ ι))
    (reverse : Bool) (parent : Option ι) (tagged : Option (Tagged α ρ ι))
    (valid : Realized markerId (tagged.map (routing payload reverse parent))) :
    ∀ tree, tagged = some tree → (tree.inventory Prod.fst).Nodup := by
  intro tree equal
  rw [equal] at valid
  obtain ⟨source,erases,aligned,clear,ids⟩ := valid _ rfl
  exact CanonicalRoutingUniqueness.unique markerId payload reverse parent tree source erases aligned clear ids

theorem forest (markerId : ι) (leftPayload rightPayload : α → Source β (Packet α ρ ι))
    (left virtual right : Option (Tagged α ρ ι)) (header : Packet α ρ ι)
    (bottom : Source β (Packet α ρ ι))
    (valid : Realized markerId (CanonicalRepairedDormant.view leftPayload rightPayload left right header bottom))
    (virtualUnique : ∀ tree, virtual = some tree → (tree.inventory Prod.fst).Nodup) :
    Unique (CanonicalComponentReconstruction.forest left virtual right) := by
  obtain ⟨first,rightValid⟩ := join markerId _ _ valid
  obtain ⟨leftValid,_⟩ := join markerId _ _ first
  have leftUnique := routing_unique markerId leftPayload false none left leftValid
  have rightUnique := routing_unique markerId rightPayload true none right rightValid
  intro q current present
  cases q with
  | none =>
    cases virtual with
    | none => cases present
    | some tree =>
      have equal : (⟨tree,[]⟩ : Cursor α (ι × List ρ)) = current := Option.some.inj present
      rw [← equal]
      exact virtualUnique tree rfl
  | some side =>
    cases side with
    | false =>
      cases right with
      | none => cases present
      | some tree =>
        have equal : (⟨tree,[]⟩ : Cursor α (ι × List ρ)) = current := Option.some.inj present
        rw [← equal]
        exact rightUnique tree rfl
    | true =>
      cases left with
      | none => cases present
      | some tree =>
        have equal : (⟨tree,[]⟩ : Cursor α (ι × List ρ)) = current := Option.some.inj present
        rw [← equal]
        exact leftUnique tree rfl

end TangoSquared.Paper20261030.CanonicalComponentUniqueness
