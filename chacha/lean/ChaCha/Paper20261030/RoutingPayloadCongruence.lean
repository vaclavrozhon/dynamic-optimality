import ChaCha.Paper20261030.CanonicalRoutingCursor

set_option autoImplicit false

/-! Changing one opaque payload leaves all other routing subtrees intact.
The statements inspect only representation witnesses; no running
controller evaluates a payload function or traverses a ghost context. -/

namespace ChaCha.Paper20261030.SourcePayloads

open ColoredStorage SourcePointer

variable {α β ρ : Type*}

theorem graft_congr (first second : α → Source β (List (Option ρ))) (source : Source α (List ρ))
    (agree : ∀ key ∈ source.shape.leaves, first key = second key) : graft first source = graft second source := by
  induction source with
  | leaf key record => simp only [graft,agree key (by simp [Source.shape,RouterProjection.Router.leaves])]
  | fork record left right ihl ihr =>
    have hl := ihl (fun key member => agree key (List.mem_append_left _ member))
    have hr := ihr (fun key member => agree key (List.mem_append_right _ member))
    simp only [graft,hl,hr]

end ChaCha.Paper20261030.SourcePayloads

namespace ChaCha.Paper20261030.CanonicalRoutingCursor

open ColoredStorage SourcePointer Structural PhysicalPacketStaging

variable {α β ρ ι : Type*}

def sibling {δ : Type*} : Frame α δ → Source α δ
  | .left _ tree | .right tree _ => tree

theorem frame_congr (first second : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (current : Frame α (PhysicalForestMetadata.Record ρ ι))
    (agree : ∀ key ∈ (sibling current).shape.leaves, first key = second key) :
    frame first reverse current = frame second reverse current := by
  have direct := SourcePayloads.graft_congr first second
    ((sibling current).mapRecords (fun record => [VirtualHeaderController.Datum.real record]))
    (by simpa only [Source.mapRecords_shape] using agree)
  have mirrored := SourcePayloads.graft_congr first second
    ((sibling current).mirror.mapRecords (fun record => [VirtualHeaderController.Datum.real record]))
    (by simpa only [Source.mapRecords_shape,Source.mirror_leaves,List.mem_reverse] using agree)
  cases current <;> cases reverse <;>
    simp only [frame,Bool.false_eq_true,if_false,if_true,Frame.mirror,Frame.mapRecords,SourcePayloads.frame,sibling] at direct mirrored ⊢ <;>
    first | rw [direct] | rw [mirrored]

def AgreeOutside (first second : α → Source β (Packet α ρ ι)) (outside : List (Frame α (ι × List ρ))) : Prop :=
  ∀ current ∈ outside, ∀ key ∈ (sibling current).shape.leaves, first key = second key

theorem frames_payload_congr (first second : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (focus : Source α (ι × List ρ)) (outside : List (Frame α (ι × List ρ)))
    (agree : AgreeOutside first second outside) :
    (Structural.frames Prod.fst (fun _ => (() : Unit)) focus outside).map (frame first reverse) =
      (Structural.frames Prod.fst (fun _ => (() : Unit)) focus outside).map (frame second reverse) := by
  induction outside generalizing focus with
  | nil => rfl
  | cons current rest ih =>
    have tail : AgreeOutside first second rest := fun item member => agree item (List.mem_cons_of_mem _ member)
    have atHead := agree current (List.mem_cons_self)
    cases current with
    | left value other =>
      simp only [Structural.frames,List.map_cons,List.cons.injEq]
      constructor
      · apply frame_congr
        simpa only [sibling,annotate_shape] using atHead
      · exact ih (.fork value focus other) tail
    | right other value =>
      simp only [Structural.frames,List.map_cons,List.cons.injEq]
      constructor
      · apply frame_congr
        simpa only [sibling,annotate_shape] using atHead
      · exact ih (.fork value other focus) tail

theorem ancestors_payload_congr (first second : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (current : Cursor α (ι × List ρ)) (agree : AgreeOutside first second current.ancestors) :
    (cursor first reverse current).ancestors = (cursor second reverse current).ancestors := by
  rw [ancestors,ancestors]
  exact frames_payload_congr first second reverse current.focus current.ancestors agree

/-- The changing payload is absent from every sibling precisely where
this ghost condition is used. A later unique-port argument supplies it. -/
theorem update_agrees [DecidableEq α] (payload : α → Source β (Packet α ρ ι)) (key : α)
    (fresh : Source β (Packet α ρ ι)) (outside : List (Frame α (ι × List ρ)))
    (absent : ∀ current ∈ outside, key ∉ (sibling current).shape.leaves) :
    AgreeOutside payload (Function.update payload key fresh) outside := by
  intro current member other present
  have different : other ≠ key := by intro same; subst other; exact absent current member present
  simp only [Function.update_of_ne different]

end ChaCha.Paper20261030.CanonicalRoutingCursor
