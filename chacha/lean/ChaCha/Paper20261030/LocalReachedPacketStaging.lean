import ChaCha.Paper20261030.HeadPacketRepacking

/-!
# Staging the actual mixed representation

Whole layers are recognized by their logical contents; their old physical
ids and neighbor fields are unrestricted. Thus a layout computed from
observed logical records does not prescribe physical fields it has not
read. The controller only inspects the record at the reached vertex.

`Stored` relates an actual physical subtree to the finite layout and its
retained blocks. The staging theorem preserves immutable identifiers and
alignment and produces exactly the decorated representation required by
the head-reassembly controller.
-/

namespace ChaCha.Paper20261030.PacketLayers

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalPacketStaging PacketAlignment RecordEditScript

variable {κ α β ρ ι : Type*}

def Matches (base : Packet α ρ ι) : Expression α ρ ι → Packet α ρ ι → Prop
  | .base,packet => packet = base
  | .raw records rest,packet => ∃ tail, packet = records++tail ∧ Matches base rest tail
  | .whole _ records _ rest,packet => ∃ id fields tail,
      packet = some (.real ((id,records),fields)) :: tail ∧ Matches base rest tail
  | .prefix records,packet => packet = PhysicalPacketStaging.Context.prependLogical records base

theorem stage_matches (markerId : ι) (base : Packet α ρ ι) (expression : Expression α ρ ι)
    (packet : Packet α ρ ι) (matching : Matches base expression packet) (ready : Ready base expression) :
    stage markerId (blueprint expression) packet = staged markerId base expression := by
  induction expression generalizing packet with
  | base => exact matching
  | raw records rest ih =>
    obtain ⟨tail,rfl,matched⟩ := matching
    simp only [blueprint,stage,List.take_left,List.drop_left,ih tail matched ready,staged]
  | whole id records fields rest ih =>
    obtain ⟨actualId,actualFields,tail,rfl,matched⟩ := matching
    simp only [blueprint,stage,ih tail matched ready,staged]
  | «prefix» records =>
    rw [matching]
    exact stage_exact markerId base (.prefix records) ready

theorem matched_aligned (markerId vertexId : ι) (base : Packet α ρ ι) (expression : Expression α ρ ι)
    (packet : Packet α ρ ι) (matching : Matches base expression packet) (aligned : Aligned markerId vertexId packet) :
    Aligned markerId vertexId (staged markerId base expression) := by
  induction expression generalizing packet with
  | base => exact matching ▸ aligned
  | raw records rest ih =>
    obtain ⟨tail,rfl,matched⟩ := matching
    obtain ⟨front,back⟩ := (aligned_append_iff _ _ _ _).mp aligned
    exact PacketAlignment.append _ _ _ _ front (ih tail matched back)
  | whole id records fields rest ih =>
    obtain ⟨actualId,actualFields,tail,rfl,matched⟩ := matching
    have back := ((aligned_cons_iff _ _ _ _).mp aligned).2
    exact PacketAlignment.append _ _ _ _ (markers markerId records vertexId) (ih tail matched back)
  | «prefix» records =>
    rw [matching] at aligned
    exact stage_aligned markerId vertexId base (.prefix records) aligned

namespace Reached

def Stored (blocks : κ → Source β (Packet α ρ ι)) :
    Source κ (Expression α ρ ι) → Source β (Cell α ρ ι) → Prop
  | .leaf key expression,source =>
      (source.mapRecords Prod.snd).setRoot (blocks key).rootRecord = blocks key ∧
      Matches (blocks key).rootRecord expression source.rootRecord.2
  | .fork expression left right,.fork record leftTree rightTree =>
      Matches [] expression record.2 ∧ Stored blocks left leftTree ∧ Stored blocks right rightTree
  | .fork _ _ _,.leaf _ _ => False

private theorem root_set {σ : Type*} (tree : Source β σ) (record : σ) :
    (tree.setRoot record).rootRecord = record := by cases tree <;> rfl

private theorem set_set {σ : Type*} (tree : Source β σ) (first last : σ) :
    (tree.setRoot first).setRoot last = tree.setRoot last := by cases tree <;> rfl

private theorem set_root {σ : Type*} (tree : Source β σ) : tree.setRoot tree.rootRecord = tree := by cases tree <;> rfl

theorem stage (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (context : Source κ (Expression α ρ ι)) (ordinary : Ordinary markerId blocks context)
    (source : Source β (Cell α ρ ι)) (represented : Stored blocks context source)
    (aligned : SourceRecordPredicate.Holds (Predicate markerId) source) :
    ∃ target,
      Transforms (Context.staging markerId) (Context.commands (context.mapRecords blueprint))
        source target (PhysicalPacketStaging.Context.budget context) ∧
      target.mapRecords Prod.snd = stagedTree markerId blocks context ∧
      target.mapRecords Prod.fst = source.mapRecords Prod.fst ∧
      SourceRecordPredicate.Holds (Predicate markerId) target := by
  induction context generalizing source with
  | leaf key expression =>
    let fresh := (source.rootRecord.1,staged markerId (blocks key).rootRecord expression)
    have computed := stage_matches markerId _ expression source.rootRecord.2 represented.2
      (ordinary_ready markerId _ expression ordinary)
    have freshValid := matched_aligned markerId source.rootRecord.1 _ expression source.rootRecord.2 represented.2
      (SourceRecordPredicate.root _ _ aligned)
    have actual := Transforms.edit (Context.staging (α := α) (ρ := ρ) markerId) (blueprint expression) source
    refine ⟨source.setRoot fresh,?_,?_,?_,SourceRecordPredicate.setRoot _ _ _ aligned freshValid⟩
    · simpa only [Context.commands,Source.mapRecords,Context.staging,Context.atId,computed,
        PhysicalPacketStaging.Context.budget,fresh] using actual
    · simp only [Source.mapRecords_setRoot,fresh,stagedTree,Source.mapRecords,PacketContext.all]
      rw [← represented.1,set_set]
      simp only [root_set,staged_exposed]
    · simp only [Source.mapRecords_setRoot,fresh,← Source.mapRecords_root Prod.fst source,set_root]
  | fork expression left right ihl ihr =>
    cases source with
    | leaf => exact False.elim represented
    | fork record leftTree rightTree =>
      obtain ⟨atRoot,leftAligned,rightAligned⟩ := (SourceRecordPredicate.fork _ _ _ _).mp aligned
      obtain ⟨leftTarget,leftRun,leftErases,leftIds,leftValid⟩ := ihl ordinary.2.1 leftTree represented.2.1 leftAligned
      obtain ⟨rightTarget,rightRun,rightErases,rightIds,rightValid⟩ := ihr ordinary.2.2 rightTree represented.2.2 rightAligned
      let fresh := (record.1,staged markerId [] expression)
      have computed := stage_matches markerId [] expression record.2 represented.1
        (ordinary_ready markerId [] expression ordinary.1)
      have first : Transforms (Context.staging markerId) [.edit (blueprint expression)]
          (.fork record leftTree rightTree) (.fork fresh leftTree rightTree) 2 := by
        have actual := Transforms.edit (Context.staging (α := α) (ρ := ρ) markerId) (blueprint expression)
          (.fork record leftTree rightTree)
        simpa only [Source.rootRecord,Source.setRoot,Context.staging,Context.atId,computed,fresh] using actual
      have actual := first.append ((leftRun.left fresh rightTree).append (rightRun.right fresh leftTarget))
      have cost : 2+((PhysicalPacketStaging.Context.budget left+2)+(PhysicalPacketStaging.Context.budget right+2)) =
          PhysicalPacketStaging.Context.budget (.fork expression left right) := by
        simp only [PhysicalPacketStaging.Context.budget]
        omega
      rw [cost] at actual
      refine ⟨.fork fresh leftTarget rightTarget,?_,?_,?_,?_⟩
      · simpa only [Context.commands,Source.mapRecords,List.singleton_append] using actual
      · simp only [Source.mapRecords,stagedTree,PacketContext.all,leftErases,rightErases,fresh,staged_exposed,List.append_nil]
      · simp only [Source.mapRecords,fresh,leftIds,rightIds]
      · exact (SourceRecordPredicate.fork (Predicate markerId) fresh leftTarget rightTarget).mpr
          ⟨matched_aligned markerId record.1 [] expression record.2 represented.1 atRoot,leftValid,rightValid⟩

end Reached
end ChaCha.Paper20261030.PacketLayers
