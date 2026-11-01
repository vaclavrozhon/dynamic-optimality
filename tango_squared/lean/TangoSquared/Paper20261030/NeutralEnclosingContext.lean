import TangoSquared.Paper20261030.EnclosingPacketExtension
import TangoSquared.Paper20261030.CanonicalPayloadPosition

set_option autoImplicit false

/-! Enclosing leaf/header packets contain no child reference to repair.
Empty component connectors have the same property. Writing a neutral
root packet onto a proper connector context retains this property, so a
nested operation in a singleton routing wing cannot alter its connector. -/

namespace TangoSquared.Paper20261030.SourcePointer

open ColoredStorage

variable {α ρ : Type*}

def Frame.record : Frame α ρ → ρ
  | .left record _ | .right _ record => record

def FrameRecords (predicate : ρ → Prop) (outside : List (Frame α ρ)) : Prop :=
  ∀ current ∈ outside, predicate current.record

theorem proper_context_setRoot_preserves (predicate : ρ → Prop) (outside : List (Frame α ρ))
    (proper : outside ≠ []) (valid : FrameRecords predicate outside) (fresh : ρ) (good : predicate fresh) :
    ∃ changed, changed ≠ [] ∧ FrameRecords predicate changed ∧
      ∀ focus : Source α ρ, (plug focus outside).setRoot fresh = plug focus changed := by
  induction outside with
  | nil => exact False.elim (proper rfl)
  | cons first rest ih =>
    cases rest with
    | nil => cases first with
      | left record sibling => exact ⟨[.left fresh sibling],by simp,by simpa only [FrameRecords,List.mem_singleton,forall_eq,Frame.record] using good,fun _ => rfl⟩
      | right sibling record => exact ⟨[.right sibling fresh],by simp,by simpa only [FrameRecords,List.mem_singleton,forall_eq,Frame.record] using good,fun _ => rfl⟩
    | cons second rest =>
      have tail : FrameRecords predicate (second::rest) := fun current member => valid current (List.mem_cons_of_mem _ member)
      obtain ⟨changed,_,preserved,rebuild⟩ := ih (by simp) tail
      refine ⟨first::changed,by simp,?_,?_⟩
      · intro current member
        rcases List.mem_cons.mp member with equal | member
        · subst current
          exact valid first (List.mem_cons_self)
        · exact preserved current member
      · intro focus
        cases first with
        | left record sibling => exact rebuild (.fork record focus sibling)
        | right sibling record => exact rebuild (.fork record sibling focus)

theorem proper_subtree_setRoot_preserves (predicate : ρ → Prop) (focus : Source α ρ) (outside : List (Frame α ρ))
    (proper : outside ≠ []) (valid : FrameRecords predicate outside) (fresh : ρ) (good : predicate fresh) :
    ∃ changed, changed ≠ [] ∧ FrameRecords predicate changed ∧ (plug focus outside).setRoot fresh = plug focus changed := by
  obtain ⟨changed,proper,valid,rebuild⟩ := proper_context_setRoot_preserves predicate outside proper valid fresh good
  exact ⟨changed,proper,valid,rebuild focus⟩

theorem FrameRecords.root (predicate : ρ → Prop) (focus : Source α ρ) (outside : List (Frame α ρ))
    (proper : outside ≠ []) (valid : FrameRecords predicate outside) : predicate (plug focus outside).rootRecord := by
  induction outside generalizing focus with
  | nil => exact False.elim (proper rfl)
  | cons first rest ih =>
    have atHead := valid first (List.mem_cons_self)
    cases rest with
    | nil => cases first <;> exact atHead
    | cons second rest =>
      have tail : FrameRecords predicate (second::rest) := fun current member => valid current (List.mem_cons_of_mem _ member)
      cases first with
      | left record sibling => exact ih (.fork record focus sibling) (by simp) tail
      | right sibling record => exact ih (.fork record sibling focus) (by simp) tail

end TangoSquared.Paper20261030.SourcePointer

namespace TangoSquared.Paper20261030.PacketParentNeutral

open ColoredStorage SourcePointer PhysicalPacketStaging PacketLayers

variable {α β ρ ι : Type*} [DecidableEq ι]

def Neutral (packet : Packet α ρ ι) : Prop :=
  ∀ old fresh : ι, packet.map (PacketParentRepair.entry old fresh) = packet

theorem nil : Neutral ([] : Packet α ρ ι) := fun _ _ => rfl

theorem append {before after : Packet α ρ ι} (first : Neutral before) (last : Neutral after) : Neutral (before++after) := by
  intro old fresh
  rw [List.map_append,first old fresh,last old fresh]

theorem layers (vertex : ι) (context : List (CanonicalEnclosingPackets.Layer α ρ ι)) :
    Neutral (CanonicalEnclosingPackets.packet vertex context) :=
  fun old fresh => CanonicalEnclosingPackets.parent_preserves old fresh vertex context

theorem reidentify (packet : Packet α ρ ι) (vertex : ι) (neutral : Neutral packet) :
    Neutral (PacketPrefixTransfer.reidentify vertex packet) := by
  intro old fresh
  have commute (item : Option (Datum α ρ ι)) :
      PacketParentRepair.entry old fresh (PacketPrefixTransfer.reidentifyEntry vertex item) =
        PacketPrefixTransfer.reidentifyEntry vertex (PacketParentRepair.entry old fresh item) := by
    cases item with
    | none => rfl
    | some value => cases value with
      | header => rfl
      | real record => rfl
  change (packet.map (PacketPrefixTransfer.reidentifyEntry vertex)).map (PacketParentRepair.entry old fresh) = _
  rw [List.map_map]
  simp only [Function.comp_def,commute]
  change packet.map (PacketPrefixTransfer.reidentifyEntry vertex ∘ PacketParentRepair.entry old fresh) = _
  rw [← List.map_map,neutral old fresh]
  rfl

theorem empty_context (outside : List (Frame β (Packet α ρ ι))) (empty : ForestConnector.ThreeColors.EmptyConnector outside) :
    FrameRecords Neutral outside := by
  intro current member
  have blank := empty current member
  cases current with
  | left record sibling => change record = [] at blank; simp only [Frame.record,blank]; exact nil
  | right sibling record => change record = [] at blank; simp only [Frame.record,blank]; exact nil

theorem fixed_actual (old fresh : ι) (outside : List (Frame β (Context.Cell α ρ ι)))
    (neutral : FrameRecords Neutral (outside.map (Frame.mapRecords Prod.snd))) :
    EnclosingPacketOperation.FixedParent old fresh outside := by
  cases outside with
  | nil => trivial
  | cons first rest =>
    have atHead := neutral (first.mapRecords Prod.snd) (List.mem_cons_self)
    cases first with
    | left record sibling =>
      change Neutral record.2 at atHead
      change Frame.left (record.1,record.2.map (PacketParentRepair.entry old fresh)) sibling = _
      rw [atHead old fresh]
    | right sibling record =>
      change Neutral record.2 at atHead
      change Frame.right sibling (record.1,record.2.map (PacketParentRepair.entry old fresh)) = _
      rw [atHead old fresh]

theorem fixed_actual_prefix (old fresh : ι) (outside : List (Frame β (Context.Cell α ρ ι)))
    (inside rest : List (Frame β (Packet α ρ ι))) (proper : inside ≠ [])
    (view : outside.map (Frame.mapRecords Prod.snd) = inside++rest) (neutral : FrameRecords Neutral inside) :
    EnclosingPacketOperation.FixedParent old fresh outside := by
  cases inside with
  | nil => exact False.elim (proper rfl)
  | cons leading tail =>
    cases outside with
    | nil => cases view
    | cons first rest =>
      have same : first.mapRecords Prod.snd = leading := (List.cons.inj view).1
      have atHead := neutral leading (List.mem_cons_self)
      rw [← same] at atHead
      have fixed := fixed_actual old fresh [first] (by
        intro item member
        have equal : item = first.mapRecords Prod.snd := by simpa only [List.map_cons,List.map_nil,List.mem_singleton] using member
        simpa only [equal] using atHead)
      exact fixed

end TangoSquared.Paper20261030.PacketParentNeutral
