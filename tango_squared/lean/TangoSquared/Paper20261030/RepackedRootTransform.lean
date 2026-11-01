import TangoSquared.Paper20261030.CanonicalMixedPacketRepair

set_option autoImplicit false

/-! Root transformations commute with repacking when their packet-level
equation holds. In particular this allows a collapsed routing join to
be removed for an inductive representation proof, without losing any
of the retained immutable identifiers or opaque blocks. -/

namespace TangoSquared.Paper20261030.PacketLayers.Reached

open ColoredStorage SourcePointer Structural PhysicalPacketStaging

variable {κ α β ρ ι : Type*}

private theorem root_set {σ : Type*} (source : Source β σ) (record : σ) :
    (source.setRoot record).rootRecord = record := by cases source <;> rfl

private theorem set_set {σ : Type*} (source : Source β σ) (first last : σ) :
    (source.setRoot first).setRoot last = source.setRoot last := by cases source <;> rfl

theorem root_transform (blocks : κ → Source β (Packet α ρ ι))
    (context : Source κ (Expression α ρ ι)) (expression : Expression α ρ ι)
    (change : ι → Packet α ρ ι → Packet α ρ ι)
    (equation : ∀ id base, rebuilt id base expression = change id (rebuilt id base context.rootRecord))
    (target : Source β (Cell α ρ ι)) (repacked : Repacked blocks (context.setRoot expression) target) :
    ∃ source, Repacked blocks context source ∧
      target = source.setRoot (source.rootRecord.1,change source.rootRecord.1 source.rootRecord.2) := by
  cases context with
  | leaf key old =>
    cases repacked with
    | leaf _ _ block erases =>
      refine ⟨_,Repacked.leaf key old block erases,?_⟩
      simp only [root_set,set_set]
      exact congrArg (fun packet => block.setRoot (block.rootRecord.1,packet)) (equation _ _)
  | fork old left right =>
    cases repacked with
    | fork _ _ _ l r id hl hr =>
      refine ⟨_,Repacked.fork old left right l r id hl hr,?_⟩
      simp only [Source.rootRecord,Source.setRoot]
      exact congrArg (fun packet => Source.fork (id,packet) l r) (equation _ _)

theorem rebuilt_logical (id : ι) (base : Packet α ρ ι) (records : List ρ)
    (expression : Expression α ρ ι) (routing : HeadPacketLayout.Routing expression) :
    rebuilt id base (HeadPacketLayout.addLogical records expression) =
      PhysicalPacketStaging.Context.prependLogical records (rebuilt id base expression) := by
  cases expression with
  | base | raw => exact False.elim routing
  | whole => rfl
  | «prefix» tail =>
    cases base with
    | nil => rfl
    | cons entry rest => cases entry with
      | none => rfl
      | some datum => cases datum with
        | header => rfl
        | real record =>
          simp only [HeadPacketLayout.addLogical,rebuilt,PhysicalPacketStaging.Context.prependLogical,List.append_assoc]

theorem logical_decomposition (blocks : κ → Source β (Packet α ρ ι))
    (context : Source κ (Expression α ρ ι)) (routing : HeadPacketLayout.Routing context.rootRecord)
    (records : List ρ) (target : Source β (Cell α ρ ι))
    (repacked : Repacked blocks (context.setRoot (HeadPacketLayout.addLogical records context.rootRecord)) target) :
    ∃ source, Repacked blocks context source ∧
      target = source.setRoot (source.rootRecord.1,PhysicalPacketStaging.Context.prependLogical records source.rootRecord.2) :=
  root_transform blocks context _ (fun _ => PhysicalPacketStaging.Context.prependLogical records)
    (fun id base => rebuilt_logical id base records context.rootRecord routing) target repacked

theorem attachment_decomposition (blocks : κ → Source β (Packet α ρ ι))
    (context : Source κ (Expression α ρ ι)) (oldId : ι) (records : List ρ) (fields : Fields ι Unit)
    (target : Source β (Cell α ρ ι))
    (repacked : Repacked blocks (context.setRoot (.whole oldId records fields (.raw [none] context.rootRecord))) target) :
    ∃ source, Repacked blocks context source ∧
      target = source.setRoot (source.rootRecord.1,
        some (.real ((source.rootRecord.1,records),placeholder)) :: none :: source.rootRecord.2) :=
  root_transform blocks context _ (fun id packet => some (.real ((id,records),placeholder)) :: none :: packet)
    (fun _ _ => rfl) target repacked

end TangoSquared.Paper20261030.PacketLayers.Reached

namespace TangoSquared.Paper20261030.MixedPacketRepair

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers

variable {κ α β ρ ι : Type*}

def Routing : Layers → Prop
  | .prefix | .leaf _ | .fork _ => True
  | _ => False

theorem routing_of_matches {plan : Layers} {expression : Expression α ρ ι}
    (same : Matches plan expression) (routing : HeadPacketLayout.Routing expression) : Routing plan := by
  cases same <;> exact routing

theorem edit_prepend (plan : Layers) (routing : Routing plan) (parent : Option ι)
    (children : Option (ι × ι)) (records : List ρ) (packet : Packet α ρ ι) :
    edit plan parent children (PhysicalPacketStaging.Context.prependLogical records packet) =
      PhysicalPacketStaging.Context.prependLogical records (edit plan parent children packet) := by
  cases plan with
  | base | raw => exact False.elim routing
  | leaf rest | fork reverse | «prefix» =>
    cases packet with
    | nil => rfl
    | cons entry tail => cases entry with
      | none => rfl
      | some datum => cases datum <;> rfl

theorem output_prepend (context : Source κ Layers) (routing : Routing context.rootRecord)
    (parent : Option ι) (records : List ρ) (source : Source β (Cell α ρ ι)) :
    output context parent
      (source.setRoot (source.rootRecord.1,PhysicalPacketStaging.Context.prependLogical records source.rootRecord.2)) =
      (output context parent source).setRoot ((output context parent source).rootRecord.1,
        PhysicalPacketStaging.Context.prependLogical records (output context parent source).rootRecord.2) := by
  cases context with
  | leaf key plan =>
    cases source <;> simp only [output,Source.setRoot,Source.rootRecord,cell,edit_prepend plan routing]
  | fork plan left right => cases source with
    | leaf => rfl
    | fork record l r => simp only [output,Source.setRoot,Source.rootRecord,cell,edit_prepend plan routing]

theorem prepend_alignment (markerId : ι) (records : List ρ) (source : Source β (Cell α ρ ι)) :
    SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId)
      (source.setRoot (source.rootRecord.1,PhysicalPacketStaging.Context.prependLogical records source.rootRecord.2)) ↔
      SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) source := by
  cases source <;>
    simp only [Source.setRoot,Source.rootRecord,SourceRecordPredicate.leaf,SourceRecordPredicate.fork,
      PacketAlignment.Predicate,PacketLayers.prepend_aligned]

theorem raw_alignment_tail (markerId : ι) (records : Packet α ρ ι) (source : Source β (Cell α ρ ι))
    (aligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId)
      (source.setRoot (source.rootRecord.1,records++source.rootRecord.2))) :
    SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) source := by
  cases source with
  | leaf key record =>
    have valid := (SourceRecordPredicate.leaf _ _ _).mp aligned
    exact (SourceRecordPredicate.leaf _ _ _).mpr ((aligned_append_iff _ _ _ _).mp valid).2
  | fork record left right =>
    obtain ⟨valid,hl,hr⟩ := (SourceRecordPredicate.fork _ _ _ _).mp aligned
    exact (SourceRecordPredicate.fork _ _ _ _).mpr ⟨((aligned_append_iff _ _ _ _).mp valid).2,hl,hr⟩

end TangoSquared.Paper20261030.MixedPacketRepair
