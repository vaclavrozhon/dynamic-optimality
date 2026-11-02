import ChaCha.Paper20261030.CanonicalRoutingPayloadUpdate
import ChaCha.Paper20261030.SourceSubtreeMetadata

set_option autoImplicit false

/-! Distinct routing leaves isolate a changed port from all sibling
payloads. Thus the canonical payload-update theorem needs no pointwise
agreement assumption beyond changing that one port. -/

namespace ChaCha.Paper20261030.CanonicalRoutingCursor

open ColoredStorage SourcePointer Structural PhysicalPacketStaging

variable {α β ρ ι : Type*}

theorem focus_leaves_nodup {δ : Type*} (focus : Source α δ) (outside : List (Frame α δ))
    (distinct : (plug focus outside).shape.leaves.Nodup) : focus.shape.leaves.Nodup := by
  rw [SubtreeMetadata.leaves_decomposition] at distinct
  exact distinct.of_append_left.of_append_right

theorem key_absent_outside {δ : Type*} (focus : Source α δ) (outside : List (Frame α δ))
    (distinct : (plug focus outside).shape.leaves.Nodup) (key : α) (member : key ∈ focus.shape.leaves) :
    ∀ current ∈ outside, key ∉ (sibling current).shape.leaves := by
  induction outside generalizing focus with
  | nil => intro current impossible; cases impossible
  | cons first rest ih =>
    cases first with
    | left value other =>
      have localUnique := focus_leaves_nodup (.fork value focus other) rest distinct
      have disjoint := (List.nodup_append'.mp localUnique).2.2
      intro current present
      rcases List.mem_cons.mp present with same | restMember
      · subst current
        exact fun otherMember => (List.disjoint_left.mp disjoint) member otherMember
      · exact ih (.fork value focus other) distinct (List.mem_append_left _ member) current restMember
    | right other value =>
      have localUnique := focus_leaves_nodup (.fork value other focus) rest distinct
      have disjoint := (List.nodup_append'.mp localUnique).2.2
      intro current present
      rcases List.mem_cons.mp present with same | restMember
      · subst current
        exact fun otherMember => (List.disjoint_left.mp disjoint) otherMember member
      · exact ih (.fork value other focus) distinct (List.mem_append_right _ member) current restMember

theorem update_agrees_of_distinct [DecidableEq α] (payload : α → Source β (Packet α ρ ι)) (key : α)
    (value : ι × List ρ) (fresh : Source β (Packet α ρ ι)) (outside : List (Frame α (ι × List ρ)))
    (distinct : (plug (.leaf key value) outside).shape.leaves.Nodup) :
    AgreeOutside payload (Function.update payload key fresh) outside :=
  update_agrees payload key fresh outside (key_absent_outside (.leaf key value) outside distinct key (by simp [Source.shape,RouterProjection.Router.leaves]))

end ChaCha.Paper20261030.CanonicalRoutingCursor

namespace ChaCha.Paper20261030.CanonicalRoutingPayloadUpdate

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers CanonicalPacketLayerViews CanonicalEnclosingPackets

variable {α β ρ ι : Type*} [DecidableEq α] [DecidableEq ι]

theorem update_unique (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (key : α) (old : ι) (records : List ρ) (outside : List (Frame α (ι × List ρ)))
    (unique : ((plug (.leaf key (old,records)) outside).inventory Prod.fst).Nodup)
    (distinct : (plug (.leaf key (old,records)) outside).shape.leaves.Nodup)
    (target : Source β (Context.Cell α ρ ι)) (physicalOutside : List (Frame β (Context.Cell α ρ ι)))
    (context : physicalOutside.map (Frame.mapRecords Prod.snd) =
      (CanonicalRoutingCursor.cursor payload reverse ⟨.leaf key (old,records),outside⟩).ancestors) :
    (EnclosingPacketOperation.output (layer old (.leaf records (parentId Prod.fst outside))) old
      ⟨target,physicalOutside⟩).tree.mapRecords Prod.snd =
      routing (Function.update payload key (target.mapRecords Prod.snd)) reverse none
        (plug (.leaf key (target.rootRecord.1,records)) outside) :=
  update payload reverse key old records outside unique target physicalOutside context
    (CanonicalRoutingCursor.update_agrees_of_distinct payload key (old,records) _ outside distinct)

end ChaCha.Paper20261030.CanonicalRoutingPayloadUpdate
