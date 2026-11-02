import ChaCha.Paper20261030.LocalPackedContextStaging

/-!
# Repacking an exposed context from identifiers at the reached vertices

The immutable second field belongs to the physical vertex. The controller
reads this field when merging temporary logical markers into a physical
packet. Thus a former join connector obtains its own physical identifier;
the controller does not copy an identifier from a different vertex.

Opaque blocks retain every record below their roots. Their root packet
must already agree with the immutable field, an invariant to establish
when allocating identifiers. Connector pointer fields are placeholders
until the subsequent physical boundary repair. No placeholder is used
for navigation by this finite edge traversal.
-/

namespace ChaCha.Paper20261030.PhysicalPacketStaging.Repacking

open ColoredStorage SourcePointer SourceLocalProgram Structural RecordEditScript

variable {κ α β ρ ι : Type*}

abbrev Augmented (α ρ ι : Type*) := Packet α ρ ι × ι

def Agrees (block : Source β (Augmented α ρ ι)) : Prop :=
  ∃ records fields rest, block.rootRecord.1 =
    some (.real ((block.rootRecord.2,records),fields)) :: rest

def prepend (records : List ρ) (record : Augmented α ρ ι) : Augmented α ρ ι :=
  (Context.prependLogical records record.1,record.2)

def staged (markerId : ι) (blocks : κ → Source β (Augmented α ρ ι)) :
    Source κ (List ρ × ι) → Source β (Augmented α ρ ι)
  | .leaf key record => (blocks key).setRoot
      (record.1.map (marker markerId) ++ (blocks key).rootRecord.1,(blocks key).rootRecord.2)
  | .fork record left right => .fork (record.1.map (marker markerId),record.2)
      (staged markerId blocks left) (staged markerId blocks right)

def packed (blocks : κ → Source β (Augmented α ρ ι)) :
    Source κ (List ρ × ι) → Source β (Augmented α ρ ι)
  | .leaf key record => (blocks key).setRoot (prepend record.1 (blocks key).rootRecord)
  | .fork record left right => .fork ([some (.real ((record.2,record.1),placeholder))],record.2)
      (packed blocks left) (packed blocks right)

def edit (descriptor : Bool × Nat) : Augmented α ρ ι → Augmented α ρ ι :=
  retainId (if descriptor.1 then packConnector descriptor.2 else packBlock descriptor.2)

private theorem root_set (source : Source β (Augmented α ρ ι)) (record : Augmented α ρ ι) :
    (source.setRoot record).rootRecord = record := by cases source <;> rfl

private theorem set_set (source : Source β (Augmented α ρ ι)) (first last : Augmented α ρ ι) :
    (source.setRoot first).setRoot last = source.setRoot last := by cases source <;> rfl

theorem pack_agrees (markerId : ι) (records : List ρ) (block : Source β (Augmented α ρ ι))
    (agrees : Agrees block) :
    packBlock records.length block.rootRecord.2
      (records.map (marker markerId) ++ block.rootRecord.1) =
      Context.prependLogical records block.rootRecord.1 := by
  obtain ⟨tail,fields,rest,equal⟩ := agrees
  rw [equal,pack_block_exact,Context.prependLogical]

theorem repack (markerId : ι) (blocks : κ → Source β (Augmented α ρ ι))
    (agrees : ∀ key, Agrees (blocks key)) (context : Source κ (List ρ × ι)) :
    Transforms edit (Context.commands (context.mapRecords (fun record => record.1.length)))
      (staged markerId blocks context) (packed blocks context) (Context.budget context) := by
  induction context with
  | leaf key record =>
    have actual := Transforms.edit (edit (α := α) (ρ := ρ) (ι := ι)) (false,record.1.length)
      (staged markerId blocks (.leaf key record))
    simpa only [staged,root_set,edit,Bool.false_eq_true,if_false,retainId,
      pack_agrees markerId record.1 (blocks key) (agrees key),set_set,
      packed,prepend,Context.commands,Source.mapRecords,Context.budget] using actual
  | fork record left right ihl ihr =>
    let fresh : Augmented α ρ ι := ([some (.real ((record.2,record.1),placeholder))],record.2)
    have first : Transforms edit [.edit (true,record.1.length)]
        (staged markerId blocks (.fork record left right))
        (.fork fresh (staged markerId blocks left) (staged markerId blocks right)) 2 := by
      have actual := Transforms.edit (edit (α := α) (ρ := ρ) (ι := ι)) (true,record.1.length)
        (staged markerId blocks (.fork record left right))
      have exactPacket := pack_connector_exact (α := α) markerId record.2 record.1 []
      simp only [List.append_nil] at exactPacket
      simpa only [staged,Source.rootRecord,edit,if_true,retainId,exactPacket,Source.setRoot,fresh] using actual
    have actual := first.append ((ihl.left fresh (staged markerId blocks right)).append
      (ihr.right fresh (packed blocks left)))
    have cost : 2+((Context.budget left+2)+(Context.budget right+2)) =
        Context.budget (.fork record left right) := by
      simp only [Context.budget]
      omega
    rw [cost] at actual
    simpa only [Context.commands,Source.mapRecords,List.singleton_append,packed,fresh] using actual

private theorem map_set {τ υ : Type*} (f : τ → υ) (source : Source β τ) (record : τ) :
    (source.setRoot record).mapRecords f = (source.mapRecords f).setRoot (f record) := by cases source <;> rfl

theorem staged_erases (markerId : ι) (blocks : κ → Source β (Augmented α ρ ι))
    (context : Source κ (List ρ × ι)) :
    (staged markerId blocks context).mapRecords Prod.fst =
      Context.stagedTree markerId (fun key => (blocks key).mapRecords Prod.fst)
        (context.mapRecords (fun record => (record.1,record.2,placeholder))) := by
  induction context with
  | leaf => simp only [staged,map_set,Context.stagedTree,Source.mapRecords,Source.mapRecords_root]
  | fork record left right ihl ihr =>
    simp only [staged,Source.mapRecords,Context.stagedTree,ihl,ihr]

theorem packed_erases (blocks : κ → Source β (Augmented α ρ ι)) (context : Source κ (List ρ × ι)) :
    (packed blocks context).mapRecords Prod.fst =
      Context.inputTree (fun key => (blocks key).mapRecords Prod.fst)
        (context.mapRecords (fun record => (record.1,record.2,placeholder))) := by
  induction context with
  | leaf => simp only [packed,map_set,Context.inputTree,prepend,Source.mapRecords,Source.mapRecords_root]
  | fork record left right ihl ihr =>
    simp only [packed,Source.mapRecords,Context.inputTree,ihl,ihr]

/-- The complete tree of retained physical identifiers is unchanged by
repacking, including every identifier inside every opaque block. -/
theorem identifiers (markerId : ι) (blocks : κ → Source β (Augmented α ρ ι))
    (context : Source κ (List ρ × ι)) :
    (packed blocks context).mapRecords Prod.snd = (staged markerId blocks context).mapRecords Prod.snd := by
  induction context with
  | leaf => simp only [packed,staged,map_set,prepend]
  | fork record left right ihl ihr => simp only [packed,staged,Source.mapRecords,ihl,ihr]

end ChaCha.Paper20261030.PhysicalPacketStaging.Repacking
