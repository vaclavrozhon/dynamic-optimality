import TangoSquared.Paper20261030.LocalPacketLayerStaging
import TangoSquared.Paper20261030.PrunedPacketContext

/-!
# Mixed-layer edits throughout an exposed physical context

The finite traversal edits each exposed vertex once, including roots of
retained blocks. Its instructions contain only layer tags and lengths.
The identifier is the first field, as in the immutable reassembly
compiler. Both staging and repacking leave the complete identifier tree
unchanged and never enter a retained block.

`render` and `Valid` describe the representation in proofs. They are not
inputs to the running controller. An eight-block traversal costs at most
58 operations, independently of the sizes of the retained blocks.
-/

namespace TangoSquared.Paper20261030.PacketLayers.Context

open ColoredStorage SourcePointer SourceLocalProgram Structural PhysicalPacketStaging RecordEditScript

variable {κ α β ρ ι : Type*}

abbrev Cell (α ρ ι : Type*) := ι × Packet α ρ ι
abbrev Record (α ρ ι : Type*) := Expression α ρ ι × ι

def render (value : Expression α ρ ι → Packet α ρ ι → ι → Packet α ρ ι)
    (blocks : κ → Source β (Cell α ρ ι)) : Source κ (Record α ρ ι) → Source β (Cell α ρ ι)
  | .leaf key record => (blocks key).setRoot
      ((blocks key).rootRecord.1,value record.1 (blocks key).rootRecord.2 (blocks key).rootRecord.1)
  | .fork record left right => .fork (record.2,value record.1 [] record.2)
      (render value blocks left) (render value blocks right)

def Valid (condition : Expression α ρ ι → Packet α ρ ι → ι → Prop)
    (blocks : κ → Source β (Cell α ρ ι)) : Source κ (Record α ρ ι) → Prop
  | .leaf key record => condition record.1 (blocks key).rootRecord.2 (blocks key).rootRecord.1
  | .fork record left right => condition record.1 [] record.2 ∧ Valid condition blocks left ∧ Valid condition blocks right

def commands : Source κ Blueprint → List (Command Blueprint)
  | .leaf _ descriptor => [.edit descriptor]
  | .fork descriptor left right => .edit descriptor ::
      (RecordEditScript.left (commands left) ++ RecordEditScript.right (commands right))

def atId (edit : ι → Packet α ρ ι → Packet α ρ ι) (record : Cell α ρ ι) : Cell α ρ ι :=
  (record.1,edit record.1 record.2)

def staging (markerId : ι) (descriptor : Blueprint) : Cell α ρ ι → Cell α ρ ι :=
  atId (fun _ => stage markerId descriptor)

def repacking (descriptor : Blueprint) : Cell α ρ ι → Cell α ρ ι := atId (fun id => repack id descriptor)

private theorem root_set {τ : Type*} (source : Source β τ) (record : τ) :
    (source.setRoot record).rootRecord = record := by cases source <;> rfl

private theorem set_set {τ : Type*} (source : Source β τ) (first last : τ) :
    (source.setRoot first).setRoot last = source.setRoot last := by cases source <;> rfl

theorem transform (edit : Blueprint → Cell α ρ ι → Cell α ρ ι)
    (before after : Expression α ρ ι → Packet α ρ ι → ι → Packet α ρ ι)
    (condition : Expression α ρ ι → Packet α ρ ι → ι → Prop)
    (localEdit : ∀ expression base id, condition expression base id →
      edit (blueprint expression) (id,before expression base id) = (id,after expression base id))
    (blocks : κ → Source β (Cell α ρ ι)) (context : Source κ (Record α ρ ι))
    (valid : Valid condition blocks context) :
    Transforms edit (commands (context.mapRecords (fun record => blueprint record.1)))
      (render before blocks context) (render after blocks context) (PhysicalPacketStaging.Context.budget context) := by
  induction context with
  | leaf key record =>
    have actual := Transforms.edit edit (blueprint record.1) (render before blocks (.leaf key record))
    simpa only [render,root_set,localEdit _ _ _ valid,set_set,Source.mapRecords,commands,
      PhysicalPacketStaging.Context.budget] using actual
  | fork record left right ihl ihr =>
    have first : Transforms edit [.edit (blueprint record.1)]
        (render before blocks (.fork record left right))
        (.fork (record.2,after record.1 [] record.2) (render before blocks left) (render before blocks right)) 2 := by
      have actual := Transforms.edit edit (blueprint record.1) (render before blocks (.fork record left right))
      simpa only [render,Source.rootRecord,Source.setRoot,localEdit _ _ _ valid.1] using actual
    have actual := first.append (((ihl valid.2.1).left _ (render before blocks right)).append
      ((ihr valid.2.2).right _ (render after blocks left)))
    have cost : 2+((PhysicalPacketStaging.Context.budget left+2)+(PhysicalPacketStaging.Context.budget right+2)) =
        PhysicalPacketStaging.Context.budget (.fork record left right) := by
      simp only [PhysicalPacketStaging.Context.budget]
      omega
    rw [cost] at actual
    simpa only [commands,Source.mapRecords,List.singleton_append,render] using actual

theorem stage_context (markerId : ι) (blocks : κ → Source β (Cell α ρ ι))
    (context : Source κ (Record α ρ ι)) (valid : Valid (fun expression base _ => Ready base expression) blocks context) :
    Transforms (staging markerId) (commands (context.mapRecords (fun record => blueprint record.1)))
      (render (fun expression base _ => stored base expression) blocks context)
      (render (fun expression base _ => staged markerId base expression) blocks context)
      (PhysicalPacketStaging.Context.budget context) :=
  transform _ _ _ _ (fun expression base id ready => by
    simp only [staging,atId,stage_exact markerId base expression ready]) blocks context valid

theorem repack_context (markerId : ι) (blocks : κ → Source β (Cell α ρ ι))
    (context : Source κ (Record α ρ ι))
    (valid : Valid (fun expression base id => ReadyAt id base expression) blocks context) :
    Transforms repacking (commands (context.mapRecords (fun record => blueprint record.1)))
      (render (fun expression base _ => staged markerId base expression) blocks context)
      (render (fun expression base id => rebuilt id base expression) blocks context)
      (PhysicalPacketStaging.Context.budget context) :=
  transform _ _ _ _ (fun expression base id ready => by
    simp only [repacking,atId,repack_exact markerId id base expression ready]) blocks context valid

theorem ready_from_alignment (markerId : ι) (blocks : κ → Source β (Cell α ρ ι))
    (context : Source κ (Record α ρ ι))
    (ordinary : Valid (fun expression base _ => OrdinaryBase markerId base expression) blocks context)
    (aligned : SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId)
      (render (fun expression base _ => staged markerId base expression) blocks context)) :
    Valid (fun expression base id => ReadyAt id base expression) blocks context := by
  induction context with
  | leaf key record =>
    have atRoot := SourceRecordPredicate.root _ _ aligned
    simp only [render,root_set,PacketAlignment.Predicate] at atRoot
    exact PacketLayers.ready_from_alignment markerId _ _ _ ordinary atRoot
  | fork record left right ihl ihr =>
    obtain ⟨atRoot,hl,hr⟩ := (SourceRecordPredicate.fork _ _ _ _).mp aligned
    exact ⟨PacketLayers.ready_from_alignment markerId _ _ _ ordinary.1 atRoot,
      ihl ordinary.2.1 hl,ihr ordinary.2.2 hr⟩

private theorem map_set {τ υ : Type*} (f : τ → υ) (source : Source β τ) (record : τ) :
    (source.setRoot record).mapRecords f = (source.mapRecords f).setRoot (f record) := by cases source <;> rfl

theorem identifiers (before after : Expression α ρ ι → Packet α ρ ι → ι → Packet α ρ ι)
    (blocks : κ → Source β (Cell α ρ ι)) (context : Source κ (Record α ρ ι)) :
    (render before blocks context).mapRecords Prod.fst = (render after blocks context).mapRecords Prod.fst := by
  induction context <;> simp_all only [render,map_set,Source.mapRecords]

theorem staged_decorated (markerId : ι) (blocks : κ → Source β (Cell α ρ ι))
    (context : Source κ (Record α ρ ι)) :
    some ((render (fun expression base _ => staged markerId base expression) blocks context).mapRecords Prod.snd) =
      OrderedContext.decorated (fun key => some ((blocks key).mapRecords Prod.snd))
        (context.mapRecords (fun record => exposed markerId record.1)) := by
  induction context with
  | leaf => simp only [render,map_set,Source.mapRecords_root,Source.mapRecords,OrderedContext.decorated,
      ProjectionLocal.decorate,Option.map_some,staged_exposed]
  | fork record left right ihl ihr =>
    simp only [render,Source.mapRecords,OrderedContext.decorated,← ihl,← ihr,
      ProjectionLocal.join,ProjectionLocal.decorate,Option.map_some,Source.rootRecord,Source.setRoot,
      staged_exposed,List.append_nil]

theorem command_count (context : Source κ Blueprint) :
    (commands context).length+5 = 6*context.shape.leaves.length := by
  induction context with
  | leaf => rfl
  | fork record left right ihl ihr =>
    simp only [commands,RecordEditScript.left,RecordEditScript.right,List.length_cons,List.length_append,
      List.length_nil,Source.shape,RouterProjection.Router.leaves]
    omega

theorem eight_bounds (context : Source κ (Record α ρ ι)) (eight : context.shape.leaves.length ≤ 8) :
    PhysicalPacketStaging.Context.budget context ≤ 58 ∧
    (commands (context.mapRecords (fun record => blueprint record.1))).length ≤ 43 := by
  have cost := PhysicalPacketStaging.Context.budget_leaves context
  have length := command_count (context.mapRecords (fun record => blueprint record.1))
  rw [Source.mapRecords_shape] at length
  omega

end TangoSquared.Paper20261030.PacketLayers.Context
