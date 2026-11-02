import ChaCha.Paper20261030.LocalPacketPrefixTransfer

set_option autoImplicit false

/-!
# Repairing the immediate parent's packet references after a root change

The controller rewrites references to the old root in real packet fields,
leaving virtual headers unchanged. It returns to the new root by reading
the actual left child's immutable id. Thus the return direction is not
inferred from a logical child field in a possibly mirrored routing tree.
The tour costs five operations for a left child and seven for a right
child. Global physical-id uniqueness justifies the latter comparison.
-/

namespace ChaCha.Paper20261030.PacketParentRepair

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalPacketStaging PacketLayers

variable {α β ρ ι : Type*} [DecidableEq ι]

def child (old fresh : ι) (entry : Child ι Unit) : Child ι Unit :=
  if entry.id = old then { entry with id := fresh } else entry

def entry (old fresh : ι) : Option (Datum α ρ ι) → Option (Datum α ρ ι)
  | some (.real (payload,fields)) =>
      some (.real (payload,{fields with children := fields.children.map (fun pair => (child old fresh pair.1,child old fresh pair.2))}))
  | datum => datum

def edit (old fresh : ι) (record : Context.Cell α ρ ι) : Context.Cell α ρ ι :=
  (record.1,record.2.map (entry old fresh))

def frame (old fresh : ι) : Frame β (Context.Cell α ρ ι) → Frame β (Context.Cell α ρ ι)
  | .left record sibling => .left (edit old fresh record) sibling
  | .right sibling record => .right sibling (edit old fresh record)

inductive State (α ρ ι : Type*) where
  | start
  | readParent
  | writeParent (record : Context.Cell α ρ ι)
  | toLeft
  | inspectLeft
  | fromLeft
  | toRight
  | done

def program (old fresh : ι) : Program (State α ρ ι) (Context.Cell α ρ ι)
  | .start => .nav .up .readParent
  | .readParent => .read (fun record _ => .writeParent (edit old fresh record))
  | .writeParent record => .write record .toLeft
  | .toLeft => .nav .left .inspectLeft
  | .inspectLeft => .read (fun record _ => if record.1 = fresh then .done else .fromLeft)
  | .fromLeft => .nav .up .toRight
  | .toRight => .nav .right .done
  | .done => .halt

theorem left (old : ι) (source sibling : Source β (Context.Cell α ρ ι))
    (record : Context.Cell α ρ ι) (outside : List (Frame β (Context.Cell α ρ ι))) :
    Run (program old source.rootRecord.1) .start ⟨source,.left record sibling::outside⟩ .done
      ⟨source,.left (edit old source.rootRecord.1 record) sibling::outside⟩ [record,source.rootRecord] 5 := by
  let code := program (α := α) (ρ := ρ) old source.rootRecord.1
  refine .next (Step.nav (program := code) (action := .up) rfl rfl) ?_
  refine .next (Step.read (program := code) (next := fun record _ => State.writeParent (edit old source.rootRecord.1 record)) rfl) ?_
  refine .next (Step.write (program := code) rfl) ?_
  refine .next (Step.nav (program := code) (action := .left) rfl rfl) ?_
  have read := Step.read (program := code) (state := .inspectLeft)
    (cursor := ⟨source,.left (edit old source.rootRecord.1 record) sibling::outside⟩)
    (next := fun record _ => if record.1 = source.rootRecord.1 then State.done else State.fromLeft) rfl
  simp only [ite_true] at read
  exact .next read (.halt rfl)

theorem right (old : ι) (source sibling : Source β (Context.Cell α ρ ι))
    (record : Context.Cell α ρ ι) (outside : List (Frame β (Context.Cell α ρ ι)))
    (distinct : sibling.rootRecord.1 ≠ source.rootRecord.1) :
    Run (program old source.rootRecord.1) .start ⟨source,.right sibling record::outside⟩ .done
      ⟨source,.right sibling (edit old source.rootRecord.1 record)::outside⟩ [record,sibling.rootRecord] 7 := by
  let code := program (α := α) (ρ := ρ) old source.rootRecord.1
  refine .next (Step.nav (program := code) (action := .up) rfl rfl) ?_
  refine .next (Step.read (program := code) (next := fun record _ => State.writeParent (edit old source.rootRecord.1 record)) rfl) ?_
  refine .next (Step.write (program := code) rfl) ?_
  refine .next (Step.nav (program := code) (action := .left) rfl rfl) ?_
  have read := Step.read (program := code) (state := .inspectLeft)
    (cursor := ⟨sibling,.left (edit old source.rootRecord.1 record) source::outside⟩)
    (next := fun record _ => if record.1 = source.rootRecord.1 then State.done else State.fromLeft) rfl
  simp only [distinct,if_false] at read
  exact .next read (.next (Step.nav (program := code) (action := .up) rfl rfl)
    (.next (Step.nav (program := code) (action := .right) rfl rfl) (.halt rfl)))

theorem run (old : ι) (source : Source β (Context.Cell α ρ ι))
    (first : Frame β (Context.Cell α ρ ι)) (outside : List (Frame β (Context.Cell α ρ ι)))
    (unique : ((plug source (first::outside)).inventory Prod.fst).Nodup) :
    ∃ reads cost, Run (program old source.rootRecord.1) .start ⟨source,first::outside⟩ .done
      ⟨source,frame old source.rootRecord.1 first::outside⟩ reads cost ∧ cost ≤ 7 := by
  cases first with
  | left record sibling => exact ⟨_,5,left old source sibling record outside,by decide⟩
  | right sibling record =>
    have nodeUnique := Multiset.nodup_of_le (inventory_le_plug Prod.fst (.fork record sibling source) outside) unique
    exact ⟨_,7,right old source sibling record outside (child_ids_distinct Prod.fst record sibling source nodeUnique),le_rfl⟩

theorem entry_alignment (markerId vertexId old fresh : ι) (datum : Option (Datum α ρ ι)) :
    PacketAlignment.Entry markerId vertexId (entry old fresh datum) ↔ PacketAlignment.Entry markerId vertexId datum := by
  cases datum with
  | none => rfl
  | some datum => cases datum <;> rfl

theorem entry_clear (markerId old fresh : ι) (datum : Option (Datum α ρ ι)) :
    MarkerFreePackets.Entry markerId (entry old fresh datum) ↔ MarkerFreePackets.Entry markerId datum := by
  cases datum with
  | none => rfl
  | some datum => cases datum <;> rfl

theorem alignment (markerId old fresh : ι) (record : Context.Cell α ρ ι)
    (valid : PacketAlignment.Predicate markerId record) : PacketAlignment.Predicate markerId (edit old fresh record) := by
  intro datum member
  obtain ⟨previous,previousMember,rfl⟩ := (List.mem_map (f := entry old fresh) (l := record.2)).mp member
  exact (entry_alignment markerId record.1 old fresh previous).mpr (valid previous previousMember)

theorem clear (markerId old fresh : ι) (record : Context.Cell α ρ ι)
    (valid : MarkerFreePackets.Vertex markerId record) : MarkerFreePackets.Vertex markerId (edit old fresh record) := by
  intro datum member
  obtain ⟨previous,previousMember,rfl⟩ := (List.mem_map (f := entry old fresh) (l := record.2)).mp member
  exact (entry_clear markerId old fresh previous).mpr (valid previous previousMember)

theorem inventory (old fresh : ι) (source : Source β (Context.Cell α ρ ι))
    (first : Frame β (Context.Cell α ρ ι)) (outside : List (Frame β (Context.Cell α ρ ι))) :
    (plug source (frame old fresh first::outside)).inventory Prod.fst =
      (plug source (first::outside)).inventory Prod.fst := by
  cases first with
  | left record sibling =>
    exact plug_inventory_congr Prod.fst (by simp only [Source.inventory_fork,edit]) outside
  | right sibling record =>
    exact plug_inventory_congr Prod.fst (by simp only [Source.inventory_fork,edit]) outside

theorem preserves (predicate : Context.Cell α ρ ι → Prop) (old fresh : ι)
    (stable : ∀ record, predicate record → predicate (edit old fresh record))
    (source : Source β (Context.Cell α ρ ι))
    (first : Frame β (Context.Cell α ρ ι)) (outside : List (Frame β (Context.Cell α ρ ι)))
    (valid : SourceRecordPredicate.Holds predicate (plug source (first::outside))) :
    SourceRecordPredicate.Holds predicate (plug source (frame old fresh first::outside)) := by
  cases first with
  | left record sibling =>
    apply SourceRecordPredicate.context predicate (.fork record source sibling) (.fork (edit old fresh record) source sibling) outside _ valid
    intro inside
    obtain ⟨root,left,right⟩ := (SourceRecordPredicate.fork _ _ _ _).mp inside
    exact (SourceRecordPredicate.fork _ _ _ _).mpr ⟨stable record root,left,right⟩
  | right sibling record =>
    apply SourceRecordPredicate.context predicate (.fork record sibling source) (.fork (edit old fresh record) sibling source) outside _ valid
    intro inside
    obtain ⟨root,left,right⟩ := (SourceRecordPredicate.fork _ _ _ _).mp inside
    exact (SourceRecordPredicate.fork _ _ _ _).mpr ⟨stable record root,left,right⟩

theorem edit_length (old fresh : ι) (record : Context.Cell α ρ ι) :
    (edit old fresh record).2.length = record.2.length := List.length_map _

theorem neighbors_left (parent : Option ι) (reverse : Bool) (old fresh sibling : ι)
    (different : sibling ≠ old) (id : ι) (records : List ρ) :
    entry (α := α) old fresh (some (.real ((id,records),MixedPacketRepair.neighbors parent reverse (some (old,sibling))))) =
      some (.real ((id,records),MixedPacketRepair.neighbors parent reverse (some (fresh,sibling)))) := by
  cases reverse <;> simp only [entry,MixedPacketRepair.neighbors,Option.map_some,Bool.false_eq_true,if_false,if_true,
    child,different]

theorem neighbors_right (parent : Option ι) (reverse : Bool) (old fresh sibling : ι)
    (different : sibling ≠ old) (id : ι) (records : List ρ) :
    entry (α := α) old fresh (some (.real ((id,records),MixedPacketRepair.neighbors parent reverse (some (sibling,old))))) =
      some (.real ((id,records),MixedPacketRepair.neighbors parent reverse (some (sibling,fresh)))) := by
  cases reverse <;> simp only [entry,MixedPacketRepair.neighbors,Option.map_some,Bool.false_eq_true,if_false,if_true,
    child,different]

end ChaCha.Paper20261030.PacketParentRepair
