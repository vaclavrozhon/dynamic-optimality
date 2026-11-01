import TangoSquared.Paper20261030.LocalPhysicalPacketStaging
import TangoSquared.Paper20261030.LocalRecordEditScript
import TangoSquared.Paper20261030.LocalDecoratedReassembly

/-!
# Staging a whole exposed physical-packet context

At a connector, the local script splits its logical packet into markers.
At an opaque block root, it splits only the known logical prefix and
keeps the residual physical packet and the complete payload suffix.
The result is exactly the decorated-context representation used by the
checked block-reassembly script. No block interior is visited.

For eight present blocks, staging costs 58 operations and the script
contains 43 commands. The context and its packed-prefix representation
must still be derived for the actual head-switch boundary; absent wings
and virtual headers require their corresponding finite context cases.
-/

namespace TangoSquared.Paper20261030.PhysicalPacketStaging.Context

open ColoredStorage SourcePointer SourceLocalProgram Structural RecordEditScript

variable {κ α β ρ ι : Type*}

abbrev ContextRecord (ρ ι : Type*) := List ρ × (ι × Fields ι Unit)

def RootPacket (block : Source β (Packet α ρ ι)) : Prop :=
  ∃ id records fields rest, block.rootRecord = some (.real ((id,records),fields)) :: rest

def prependLogical (prefixRecords : List ρ) : Packet α ρ ι → Packet α ρ ι
  | some (.real ((id,records),fields)) :: rest => some (.real ((id,prefixRecords++records),fields)) :: rest
  | records => records

def inputTree (blocks : κ → Source β (Packet α ρ ι)) : Source κ (ContextRecord ρ ι) → Source β (Packet α ρ ι)
  | .leaf key record => (blocks key).setRoot (prependLogical record.1 (blocks key).rootRecord)
  | .fork record left right =>
    .fork [some (.real ((record.2.1,record.1),record.2.2))] (inputTree blocks left) (inputTree blocks right)

def stagedTree (markerId : ι) (blocks : κ → Source β (Packet α ρ ι)) : Source κ (ContextRecord ρ ι) → Source β (Packet α ρ ι)
  | .leaf key record => (blocks key).setRoot (record.1.map (marker markerId) ++ (blocks key).rootRecord)
  | .fork record left right => .fork (record.1.map (marker markerId)) (stagedTree markerId blocks left) (stagedTree markerId blocks right)

def edit (markerId : ι) (descriptor : Bool × Nat) : Packet α ρ ι → Packet α ρ ι :=
  if descriptor.1 then stageConnector markerId else stageBlock markerId descriptor.2

def commands : Source κ Nat → List (Command (Bool × Nat))
  | .leaf _ count => [.edit (false,count)]
  | .fork count left right => .edit (true,count) :: (RecordEditScript.left (commands left) ++ RecordEditScript.right (commands right))

def budget {τ : Type*} : Source κ τ → Nat
  | .leaf _ _ => 2
  | .fork _ left right => 6+budget left+budget right

private theorem root_set (source : Source β (Packet α ρ ι)) (records : Packet α ρ ι) :
    (source.setRoot records).rootRecord = records := by cases source <;> rfl

private theorem set_set (source : Source β (Packet α ρ ι)) (first last : Packet α ρ ι) :
    (source.setRoot first).setRoot last = source.setRoot last := by cases source <;> rfl

theorem stage_prepend (markerId : ι) (prefixRecords : List ρ) (block : Source β (Packet α ρ ι))
    (packet : RootPacket block) :
    stageBlock markerId prefixRecords.length (prependLogical prefixRecords block.rootRecord) =
      prefixRecords.map (marker markerId) ++ block.rootRecord := by
  obtain ⟨id,records,fields,rest,equal⟩ := packet
  rw [equal,prependLogical,stage_block_exact]

theorem stage (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (packets : ∀ key, RootPacket (blocks key)) (context : Source κ (ContextRecord ρ ι)) :
    Transforms (edit markerId) (commands (context.mapRecords (fun record => record.1.length)))
      (inputTree blocks context) (stagedTree markerId blocks context) (budget context) := by
  induction context with
  | leaf key record =>
    have actual := Transforms.edit (edit markerId) (false,record.1.length) (inputTree blocks (.leaf key record))
    simpa only [inputTree,root_set,edit,Bool.false_eq_true,if_false,
      stage_prepend markerId record.1 (blocks key) (packets key),set_set,
      stagedTree,commands,Source.mapRecords,budget] using actual
  | fork record left right ihl ihr =>
    have first : Transforms (edit markerId) [.edit (true,record.1.length)]
        (inputTree blocks (.fork record left right))
        (.fork (record.1.map (marker markerId)) (inputTree blocks left) (inputTree blocks right)) 2 := by
      have actual := Transforms.edit (edit markerId) (true,record.1.length) (inputTree blocks (.fork record left right))
      simpa only [inputTree,Source.rootRecord,edit,if_true,stageConnector,List.append_nil,Source.setRoot] using actual
    have actual := first.append ((ihl.left (record.1.map (marker markerId)) (inputTree blocks right)).append
      (ihr.right (record.1.map (marker markerId)) (stagedTree markerId blocks left)))
    have cost : 2+((budget left+2)+(budget right+2)) = budget (.fork record left right) := by
      simp only [budget]
      omega
    rw [cost] at actual
    simpa only [commands,Source.mapRecords,List.singleton_append,stagedTree] using actual

theorem staged_decorated (markerId : ι) (blocks : κ → Source β (Packet α ρ ι)) (context : Source κ (ContextRecord ρ ι)) :
    some (stagedTree markerId blocks context) =
      OrderedContext.decorated (fun key => some (blocks key)) (context.mapRecords (fun record => record.1.map (marker markerId))) := by
  induction context with
  | leaf => rfl
  | fork record left right ihl ihr =>
    simp only [stagedTree,Source.mapRecords,OrderedContext.decorated,← ihl,← ihr,
      ProjectionLocal.join,ProjectionLocal.decorate,Option.map_some,Source.rootRecord,Source.setRoot,List.append_nil]

theorem budget_leaves {τ : Type*} (context : Source κ τ) : budget context+6 = 8*context.shape.leaves.length := by
  induction context with
  | leaf => rfl
  | fork record left right ihl ihr =>
    simp only [budget,Source.shape,RouterProjection.Router.leaves,List.length_append]
    omega

theorem command_count (blueprint : Source κ Nat) : (commands blueprint).length+5 = 6*blueprint.shape.leaves.length := by
  induction blueprint with
  | leaf => rfl
  | fork record left right ihl ihr =>
    simp only [commands,RecordEditScript.left,RecordEditScript.right,List.length_cons,List.length_append,
      List.length_nil,Source.shape,RouterProjection.Router.leaves]
    omega

theorem eight_blocks (context : Source κ (ContextRecord ρ ι)) (eight : context.shape.leaves.length = 8) :
    budget context = 58 ∧ (commands (context.mapRecords (fun record => record.1.length))).length = 43 := by
  have cost := budget_leaves context
  have length := command_count (context.mapRecords (fun record => record.1.length))
  rw [Source.mapRecords_shape,eight] at length
  rw [eight] at cost
  omega

end TangoSquared.Paper20261030.PhysicalPacketStaging.Context
