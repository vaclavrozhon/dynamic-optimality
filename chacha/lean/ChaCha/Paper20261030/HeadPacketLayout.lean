import ChaCha.Paper20261030.LocalPacketLayerContext

/-!
# The mixed packet layout computed at a head boundary

Routing joins introduce a real physical packet, even when its logical
record list is empty. Primary joins introduce an empty outer list.
An attachment prepends a whole real packet and a delimiter; a virtual
bottom prepends its raw header packet. Suppressed routing joins merge
their logical prefix into the first remaining real packet.

These distinctions determine the staging and repacking blueprint from
the observed masks, the five boundary records, and the two small stored
headers. Physical ids and pointer fields below are proof placeholders:
staging reads existing fields and repacking uses the reached immutable id.
-/

namespace ChaCha.Paper20261030.HeadPacketLayout

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers
open ProjectionLocal HeadBoundary HeadBlocks

variable {κ α ρ ι η : Type*}

abbrev Layout (κ α ρ ι : Type*) := Option (Source κ (Expression α ρ ι))

def Routing : Expression α ρ ι → Prop
  | .whole _ _ _ _ | .prefix _ => True
  | _ => False

def addLogical (records : List ρ) : Expression α ρ ι → Expression α ρ ι
  | .whole id tail fields rest => .whole id (records++tail) fields rest
  | .prefix tail => .prefix (records++tail)
  | expression => expression

theorem addLogical_exposed (markerId : ι) (records : List ρ) (expression : Expression α ρ ι)
    (routing : Routing expression) :
    exposed markerId (addLogical records expression) = records.map (marker markerId) ++ exposed markerId expression := by
  cases expression <;> simp_all only [Routing,addLogical,exposed,List.map_append,List.append_assoc]

theorem addLogical_routing (records : List ρ) (expression : Expression α ρ ι) (routing : Routing expression) :
    Routing (addLogical records expression) := by cases expression <;> exact routing

def push (edit : Expression α ρ ι → Expression α ρ ι) : Layout κ α ρ ι → Layout κ α ρ ι :=
  Option.map (fun tree => tree.setRoot (edit tree.rootRecord))

def realJoin (markerId : ι) (records : List ρ) : Layout κ α ρ ι → Layout κ α ρ ι → Layout κ α ρ ι
  | none,none => none
  | some left,none => push (addLogical records) (some left)
  | none,some right => push (addLogical records) (some right)
  | some left,some right => some (.fork (.whole markerId records placeholder .base) left right)

def primaryJoin : Layout κ α ρ ι → Layout κ α ρ ι → Layout κ α ρ ι
  | none,right => right
  | left,none => left
  | some left,some right => some (.fork .base left right)

def block (bits : κ → Bool) (key : κ) : Layout κ α ρ ι :=
  if bits key then some (.leaf key (.prefix [])) else none

def bottom (key : κ) (packet : Packet α ρ ι) : Layout κ α ρ ι := some (.leaf key (.raw packet .base))

def attachment (markerId : ι) (record : ρ) (child : Layout κ α ρ ι) : Layout κ α ρ ι :=
  push (fun expression => .whole markerId [record] placeholder (.raw [none] expression)) child

def RoutingRoot : Layout κ α ρ ι → Prop
  | none => True
  | some tree => Routing tree.rootRecord

theorem block_routing (bits : κ → Bool) (key : κ) : RoutingRoot (block (α := α) (ρ := ρ) (ι := ι) bits key) := by
  unfold block
  split <;> trivial

private theorem root_set {σ : Type*} (tree : Source κ σ) (record : σ) :
    (tree.setRoot record).rootRecord = record := by cases tree <;> rfl

theorem push_routing (records : List ρ) (layout : Layout κ α ρ ι) (valid : RoutingRoot layout) :
    RoutingRoot (push (addLogical records) layout) := by
  cases layout with
  | none => trivial
  | some tree =>
    simp only [push,Option.map_some,RoutingRoot,root_set]
    exact addLogical_routing records _ valid

theorem join_routing (markerId : ι) (records : List ρ) (left right : Layout κ α ρ ι)
    (hl : RoutingRoot left) (hr : RoutingRoot right) : RoutingRoot (realJoin markerId records left right) := by
  cases left <;> cases right
  · trivial
  · exact push_routing records _ hr
  · exact push_routing records _ hl
  · trivial

theorem attachment_routing (markerId : ι) (record : ρ) (child : Layout κ α ρ ι) :
    RoutingRoot (attachment markerId record child) := by
  cases child with
  | none => trivial
  | some tree => simp only [attachment,push,Option.map_some,RoutingRoot,root_set,Routing]

def view (markerId : ι) : Layout κ α ρ ι → Projected κ (Option (Datum α ρ ι)) :=
  Option.map (Source.mapRecords (exposed markerId))

private theorem map_set {σ τ : Type*} (f : σ → τ) (tree : Source κ σ) (record : σ) :
    (tree.setRoot record).mapRecords f = (tree.mapRecords f).setRoot (f record) := by cases tree <;> rfl

theorem push_view (markerId : ι) (edit : Expression α ρ ι → Expression α ρ ι) (prefixRecords : Packet α ρ ι)
    (layout : Layout κ α ρ ι)
    (equal : ∀ tree, layout = some tree → exposed markerId (edit tree.rootRecord) = prefixRecords ++ exposed markerId tree.rootRecord) :
    view markerId (push edit layout) = decorate prefixRecords (view markerId layout) := by
  cases layout with
  | none => rfl
  | some tree =>
    simp only [push,view,Option.map_some,map_set,equal tree rfl,decorate,Source.mapRecords_root]

theorem logical_view (markerId : ι) (records : List ρ) (layout : Layout κ α ρ ι) (valid : RoutingRoot layout) :
    view markerId (push (addLogical records) layout) = decorate (records.map (marker markerId)) (view markerId layout) :=
  push_view markerId _ _ layout (by
    intro tree equal
    subst layout
    exact addLogical_exposed markerId records _ valid)

theorem realJoin_view (markerId : ι) (records : List ρ) (left right : Layout κ α ρ ι)
    (hl : RoutingRoot left) (hr : RoutingRoot right) :
    view markerId (realJoin markerId records left right) =
      decorate (records.map (marker markerId)) (join (view markerId left) (view markerId right)) := by
  cases left with
  | none => cases right with
    | none => rfl
    | some right => exact logical_view markerId records _ hr
  | some left => cases right with
    | none => exact logical_view markerId records _ hl
    | some right => simp only [realJoin,view,Option.map_some,Source.mapRecords,exposed,List.append_nil,
        join,decorate,Source.rootRecord,Source.setRoot]

theorem primaryJoin_view (markerId : ι) (left right : Layout κ α ρ ι) :
    view markerId (primaryJoin left right) = join (view markerId left) (view markerId right) := by
  cases left <;> cases right <;> rfl

theorem attachment_view (markerId : ι) (record : ρ) (child : Layout κ α ρ ι) :
    view markerId (attachment markerId record child) =
      decorate [marker markerId record,none] (view markerId child) :=
  push_view markerId _ _ child (by intro tree _; rfl)

theorem block_view (markerId : ι) (bits : κ → Bool) (key : κ) :
    view markerId (block (α := α) (ρ := ρ) bits key) = if bits key then some (.leaf key []) else none := by
  unfold block
  split <;> rfl

theorem bottom_view (markerId : ι) (key : κ) (packet : Packet α ρ ι) :
    view markerId (bottom key packet) = decorate packet (some (.leaf key [])) := by
  simp only [view,bottom,Option.map_some,Source.mapRecords,exposed,List.append_nil,decorate,Source.rootRecord,Source.setRoot]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem owned_markers (markerId : ι) (q : Option Bool) (record : HeadBoundary.Record ρ η (Option Bool)) :
    (ObservedHeadBlueprint.owned q record).map (marker (α := α) markerId) =
      ObservedHeadBlueprint.connector (PacketAlignment.markerValue markerId) q record := by
  unfold ObservedHeadBlueprint.owned ObservedHeadBlueprint.connector
  cases record.2.children with
  | none => rfl
  | some children =>
    rcases children with ⟨left,right⟩
    dsimp only
    split <;> rfl

def dormant (markerId : ι) (bits : Fin 8 → Bool) (l b r : Fin 8)
    (high : HeadBoundary.Record ρ η (Option Bool))
    (header : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    Layout (Fin 8) α (HeadBoundary.Record ρ η (Option Bool)) ι :=
  primaryJoin (primaryJoin
    (push (addLogical (ObservedHeadBlueprint.owned (some true) high)) (block bits l))
    (bottom b header))
    (push (addLogical (ObservedHeadBlueprint.owned (some false) high)) (block bits r))

def active (markerId : ι) (bits : Fin 8 → Bool) (l r tl b tr : Fin 8)
    (boundary : Layout (Fin 8) α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (direction : Bool) (low high terminal : HeadBoundary.Record ρ η (Option Bool))
    (header : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    Layout (Fin 8) α (HeadBoundary.Record ρ η (Option Bool)) ι :=
  let child := attachment markerId terminal boundary
  let left := if direction then realJoin markerId (ObservedHeadBlueprint.owned (some true) high) child (block bits tl)
    else push (addLogical (ObservedHeadBlueprint.owned (some true) high)) (block bits tl)
  let right := if direction then push (addLogical (ObservedHeadBlueprint.owned (some false) high)) (block bits tr)
    else realJoin markerId (ObservedHeadBlueprint.owned (some false) high) (block bits tr) child
  primaryJoin (primaryJoin
    (realJoin markerId (ObservedHeadBlueprint.owned (some true) low) (block bits l) left)
    (bottom b header))
    (realJoin markerId (ObservedHeadBlueprint.owned (some false) low) right (block bits r))

def bare (bits : Fin 8 → Bool) (key : Fin 8) : Projected (Fin 8) (Option (Datum α ρ ι)) :=
  if bits key then some (.leaf key []) else none

theorem dormant_view (markerId : ι) (bits : Fin 8 → Bool) (l b r : Fin 8)
    (high : HeadBoundary.Record ρ η (Option Bool))
    (header : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    view markerId (dormant markerId bits l b r high header) =
      dormantView (bare bits l) (some (.leaf b [])) (bare bits r)
        (ObservedHeadBlueprint.dormant (PacketAlignment.markerValue markerId) high header) := by
  simp only [dormant,primaryJoin_view,logical_view _ _ _ (block_routing _ _),bottom_view,block_view,
    owned_markers,dormantView,ObservedHeadBlueprint.dormant,bare]
  rfl

theorem active_view (markerId : ι) (bits : Fin 8 → Bool) (l r tl b tr : Fin 8)
    (boundary : Layout (Fin 8) α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (direction : Bool) (low high terminal : HeadBoundary.Record ρ η (Option Bool))
    (header : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    view markerId (active markerId bits l r tl b tr boundary direction low high terminal header) =
      activeView (bare bits l) (bare bits r) (bare bits tl) (some (.leaf b [])) (bare bits tr)
        (view markerId boundary) direction
        (ObservedHeadBlueprint.active (PacketAlignment.markerValue markerId) low high terminal header) := by
  have blocksRouting (key : Fin 8) := block_routing (α := α) (ρ := HeadBoundary.Record ρ η (Option Bool)) (ι := ι) bits key
  have childRouting := attachment_routing markerId terminal boundary
  cases direction <;>
    simp only [active,Bool.false_eq_true,if_false,if_true,primaryJoin_view,
      realJoin_view _ _ _ _ (blocksRouting _) (join_routing _ _ _ _ childRouting (blocksRouting _)),
      realJoin_view _ _ _ _ (blocksRouting _) (push_routing _ _ (blocksRouting _)),
      realJoin_view _ _ _ _ (join_routing _ _ _ _ (blocksRouting _) childRouting) (blocksRouting _),
      realJoin_view _ _ _ _ (push_routing _ _ (blocksRouting _)) (blocksRouting _),
      realJoin_view _ _ _ _ childRouting (blocksRouting _),
      realJoin_view _ _ _ _ (blocksRouting _) childRouting,
      logical_view _ _ _ (blocksRouting _),bottom_view,block_view,attachment_view,owned_markers,
      activeView,ObservedHeadBlueprint.active,bare,marker,PacketAlignment.markerValue]
  all_goals rfl

def before (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool)
    (records : Records ρ η (Option Bool))
    (oldHeader incomingHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    Layout (Fin 8) α (HeadBoundary.Record ρ η (Option Bool)) ι :=
  active markerId bits 0 7 1 2 3 (dormant markerId bits 4 5 6 records.incomingHigh incomingHeader)
    direction records.low records.oldHigh records.oldTerminal oldHeader

def after (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool)
    (records : Records ρ η (Option Bool))
    (newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι) :
    Layout (Fin 8) α (HeadBoundary.Record ρ η (Option Bool)) ι :=
  active markerId bits 0 7 4 5 6 (dormant markerId bits 1 2 3 records.oldHigh dormantHeader)
    (!direction) records.low records.incomingHigh records.incomingTerminal newHeader

theorem before_view (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool)
    (records : Records ρ η (Option Bool))
    (oldHeader incomingHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (oldPresent : bits 2 = true) (newPresent : bits 5 = true) :
    view markerId (before markerId bits direction records oldHeader incomingHeader) =
      OrderedContext.decorated (bare bits)
        (ObservedHeadBlueprint.beforeContext (PacketAlignment.markerValue markerId) direction records oldHeader incomingHeader) := by
  simp only [before,active_view,dormant_view,ObservedHeadBlueprint.beforeContext,
    ExposedLocal.before_realize,exposedBefore,bare,oldPresent,newPresent,if_true]

theorem after_view (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool)
    (records : Records ρ η (Option Bool))
    (newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (oldPresent : bits 2 = true) (newPresent : bits 5 = true) :
    view markerId (after markerId bits direction records newHeader dormantHeader) =
      OrderedContext.decorated (bare bits)
        (ObservedHeadBlueprint.afterContext (PacketAlignment.markerValue markerId) direction records newHeader dormantHeader) := by
  simp only [after,active_view,dormant_view,ObservedHeadBlueprint.afterContext,
    ExposedLocal.after_realize,exposedAfter,bare,oldPresent,newPresent,if_true]

theorem decorated_bare (bits : Fin 8 → Bool) (context : Source (Fin 8) (Packet α ρ ι)) :
    OrderedContext.decorated (bare bits) context = PacketContext.prune List.append bits context := by
  induction context with
  | leaf key record =>
    cases present : bits key <;> simp only [OrderedContext.decorated,bare,PacketContext.prune,present,
      Bool.false_eq_true,if_false,if_true,decorate,Option.map_some,Option.map_none,Source.rootRecord,Source.setRoot,List.append_nil]
  | fork record left right ihl ihr =>
    simp only [OrderedContext.decorated,PacketContext.prune,ihl,ihr]
    cases PacketContext.prune List.append bits left <;> cases PacketContext.prune List.append bits right <;>
      simp only [PacketContext.combine,PacketContext.push,join,decorate,Option.map_none,Option.map_some,
        Source.rootRecord,Source.setRoot,List.append_nil]
    all_goals rfl

theorem after_pruned (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool)
    (records : Records ρ η (Option Bool))
    (newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (oldPresent : bits 2 = true) (newPresent : bits 5 = true)
    (layout : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (found : after markerId bits direction records newHeader dormantHeader = some layout) :
    PacketContext.prune List.append bits
      (ObservedHeadBlueprint.afterContext (PacketAlignment.markerValue markerId) direction records newHeader dormantHeader) =
      some (layout.mapRecords (exposed markerId)) := by
  have equal := after_view markerId bits direction records newHeader dormantHeader oldPresent newPresent
  rw [decorated_bare,found] at equal
  exact equal.symm

theorem after_size (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool)
    (records : Records ρ η (Option Bool))
    (newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (oldPresent : bits 2 = true) (newPresent : bits 5 = true)
    (layout : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (found : after markerId bits direction records newHeader dormantHeader = some layout) :
    layout.shape.leaves.length ≤ 8 := by
  have small := PacketContext.size_le List.append bits _ _
    (after_pruned markerId bits direction records newHeader dormantHeader oldPresent newPresent layout found)
  rw [Source.mapRecords_shape] at small
  have equal := congrArg List.length
    (ObservedHeadBlueprint.block_order (PacketAlignment.markerValue (α := α) markerId) direction records records
      newHeader dormantHeader newHeader dormantHeader)
  rw [ObservedHeadBlueprint.block_count] at equal
  omega

theorem after_realizes {β : Type*} (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool)
    (records : Records ρ η (Option Bool))
    (newHeader dormantHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (oldPresent : bits 2 = true) (newPresent : bits 5 = true)
    (layout : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (found : after markerId bits direction records newHeader dormantHeader = some layout)
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)) :
    some (PacketContext.all blocks (layout.mapRecords (exposed markerId))) =
      OrderedContext.decorated (fun key => if bits key then some (blocks key) else none)
        (ObservedHeadBlueprint.afterContext (PacketAlignment.markerValue markerId) direction records newHeader dormantHeader) := by
  have actual := PacketContext.realizes bits blocks
    (ObservedHeadBlueprint.afterContext (PacketAlignment.markerValue markerId) direction records newHeader dormantHeader)
  rw [after_pruned markerId bits direction records newHeader dormantHeader oldPresent newPresent layout found] at actual
  exact actual

theorem before_pruned (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool)
    (records : Records ρ η (Option Bool))
    (oldHeader incomingHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (oldPresent : bits 2 = true) (newPresent : bits 5 = true)
    (layout : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (found : before markerId bits direction records oldHeader incomingHeader = some layout) :
    PacketContext.prune List.append bits
      (ObservedHeadBlueprint.beforeContext (PacketAlignment.markerValue markerId) direction records oldHeader incomingHeader) =
      some (layout.mapRecords (exposed markerId)) := by
  have equal := before_view markerId bits direction records oldHeader incomingHeader oldPresent newPresent
  rw [decorated_bare,found] at equal
  exact equal.symm

theorem before_size (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool)
    (records : Records ρ η (Option Bool))
    (oldHeader incomingHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (oldPresent : bits 2 = true) (newPresent : bits 5 = true)
    (layout : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (found : before markerId bits direction records oldHeader incomingHeader = some layout) :
    layout.shape.leaves.length ≤ 8 := by
  have small := PacketContext.size_le List.append bits _ _
    (before_pruned markerId bits direction records oldHeader incomingHeader oldPresent newPresent layout found)
  simpa only [Source.mapRecords_shape,ObservedHeadBlueprint.block_count] using small

theorem before_realizes {β : Type*} (markerId : ι) (bits : Fin 8 → Bool) (direction : Bool)
    (records : Records ρ η (Option Bool))
    (oldHeader incomingHeader : Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)
    (oldPresent : bits 2 = true) (newPresent : bits 5 = true)
    (layout : Source (Fin 8) (Expression α (HeadBoundary.Record ρ η (Option Bool)) ι))
    (found : before markerId bits direction records oldHeader incomingHeader = some layout)
    (blocks : Fin 8 → Source β (Packet α (HeadBoundary.Record ρ η (Option Bool)) ι)) :
    some (PacketContext.all blocks (layout.mapRecords (exposed markerId))) =
      OrderedContext.decorated (fun key => if bits key then some (blocks key) else none)
        (ObservedHeadBlueprint.beforeContext (PacketAlignment.markerValue markerId) direction records oldHeader incomingHeader) := by
  have actual := PacketContext.realizes bits blocks
    (ObservedHeadBlueprint.beforeContext (PacketAlignment.markerValue markerId) direction records oldHeader incomingHeader)
  rw [before_pruned markerId bits direction records oldHeader incomingHeader oldPresent newPresent layout found] at actual
  exact actual

end ChaCha.Paper20261030.HeadPacketLayout
