import TangoSquared.Paper20261030.MixedPacketRepairCorrectness
import TangoSquared.Paper20261030.CanonicalPacketLayerViews

set_option autoImplicit false

/-!
# Canonical meanings of the mixed repair constructors

An opaque routing block needs only its external parent changed. The
internal routing annotation, including the orientation of its children,
is retained. At an attachment the outer routing leaf and its delimiter
are preserved while the attached component is repaired with no parent.
These equations relate the mixed repair to the existing canonical
component encoding, rather than merely checking individual pointer fields.
-/

namespace TangoSquared.Paper20261030.CanonicalMixedPacketRepair

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers
open CanonicalPacketLayerViews MixedPacketRepair

variable {κ α β ρ ι : Type*}

private theorem root_set {σ : Type*} (source : Source β σ) (record : σ) :
    (source.setRoot record).rootRecord = record := by cases source <;> rfl

private theorem set_set {σ : Type*} (source : Source β σ) (first last : σ) :
    (source.setRoot first).setRoot last = source.setRoot last := by cases source <;> rfl

/-- Updating the first real packet's parent is exactly re-annotating the
external parent of a canonical routing tree, with all payloads intact. -/
theorem routing_parent (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (old fresh : Option ι) (tagged : Tagged α ρ ι) :
    (routing payload reverse old tagged).setRoot
      (edit .prefix fresh none (routing payload reverse old tagged).rootRecord) =
      routing payload reverse fresh tagged := by
  cases tagged with
  | leaf key record =>
    rw [leaf,leaf,root_set,set_set]
    rfl
  | fork record left right =>
    rw [fork,fork]
    rfl

theorem prefix_edit (records : List ρ) (parent : Option ι) (packet : Packet α ρ ι) :
    edit .prefix parent none (PhysicalPacketStaging.Context.prependLogical records packet) =
      PhysicalPacketStaging.Context.prependLogical records (edit .prefix parent none packet) := by
  cases packet with
  | nil => rfl
  | cons entry rest => cases entry with
    | none => rfl
    | some datum => cases datum <;> rfl

/-- Agreement with the immutable vertex id follows from the maintained
alignment and the absence of temporary markers at an endpoint. -/
theorem routing_root_id (markerId : ι) (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (parent : Option ι) (tagged : Tagged α ρ ι) (source : Source β (Cell α ρ ι))
    (erases : source.mapRecords Prod.snd = routing payload reverse parent tagged)
    (aligned : PacketAlignment.Aligned markerId source.rootRecord.1 source.rootRecord.2)
    (clear : MarkerFreePackets.Packet markerId source.rootRecord.2) : source.rootRecord.1 = tagged.rootRecord.1 := by
  have root := congrArg Source.rootRecord erases
  simp only [Source.mapRecords_root] at root
  cases tagged with
  | leaf key record =>
    rw [leaf,root_set] at root
    rw [root] at aligned clear
    have ordinary := clear _ List.mem_cons_self
    exact ((aligned _ List.mem_cons_self).resolve_left ordinary).symm
  | fork record left right =>
    rw [fork] at root
    rw [root] at aligned clear
    have ordinary := clear _ List.mem_cons_self
    exact ((aligned _ List.mem_cons_self).resolve_left ordinary).symm

theorem routing_root_id_of_ordinary (markerId : ι) (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (parent : Option ι) (tagged : Tagged α ρ ι) (source : Source β (Cell α ρ ι))
    (erases : source.mapRecords Prod.snd = routing payload reverse parent tagged)
    (aligned : PacketAlignment.Aligned markerId source.rootRecord.1 source.rootRecord.2)
    (ordinary : tagged.rootRecord.1 ≠ markerId) : source.rootRecord.1 = tagged.rootRecord.1 := by
  have root := congrArg Source.rootRecord erases
  simp only [Source.mapRecords_root] at root
  cases tagged with
  | leaf key record =>
    rw [leaf,root_set] at root
    rw [root] at aligned
    exact ((aligned _ List.mem_cons_self).resolve_left ordinary).symm
  | fork record left right =>
    rw [fork] at root
    rw [root] at aligned
    exact ((aligned _ List.mem_cons_self).resolve_left ordinary).symm
/-- Repacking a collapsed logical prefix and repairing the block's
parent yields the canonical encoding of the same tagged block with that
logical prefix. No internal physical fields are rebuilt or discarded. -/
theorem opaque_block (key : κ) (records : List ρ) (parent oldParent : Option ι)
    (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (tagged : Tagged α ρ ι)
    (block : Source β (Cell α ρ ι))
    (erases : block.mapRecords Prod.snd = routing payload reverse oldParent tagged) :
    (output (.leaf key .prefix) parent
      (block.setRoot (block.rootRecord.1,rebuilt block.rootRecord.1 (routing payload reverse oldParent tagged).rootRecord
        (.prefix records)))).mapRecords Prod.snd =
      routing payload reverse parent (prepend records tagged) := by
  simp only [output,Source.mapRecords_setRoot,cell,root_set,set_set,rebuilt,erases]
  rw [prefix_edit,logical_prefix,← routing_parent payload reverse oldParent parent tagged]
  simp only [root_set,set_set]

/-- The actual child ids read by a routing-fork repair are exactly the
canonical neighbor descriptors of its newly assembled tagged tree.
The two tagged arguments are in physical order; a right wing reverses
that order in its logical routing tree. -/
theorem routing_fork (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (parent : Option ι) (id : ι) (records : List ρ) (oldFields : Fields ι Unit)
    (leftPlan rightPlan : Source κ Layers) (left right : Source β (Cell α ρ ι))
    (leftTagged rightTagged : Tagged α ρ ι)
    (leftId : left.rootRecord.1 = leftTagged.rootRecord.1) (rightId : right.rootRecord.1 = rightTagged.rootRecord.1)
    (leftView : (output leftPlan (some id) left).mapRecords Prod.snd = routing payload reverse (some id) leftTagged)
    (rightView : (output rightPlan (some id) right).mapRecords Prod.snd = routing payload reverse (some id) rightTagged) :
    (output (.fork (.fork reverse) leftPlan rightPlan) parent
      (.fork (id,[some (.real ((id,records),oldFields))]) left right)).mapRecords Prod.snd =
      routing payload reverse parent
        (.fork (id,records) (if reverse then rightTagged else leftTagged) (if reverse then leftTagged else rightTagged)) := by
  simp only [output,cell,edit,childParent,Layers.hasFork,if_true,Source.mapRecords,leftView,rightView,leftId,rightId]
  rw [fork_fields,CanonicalPacketLayerViews.fork]
  cases reverse <;> rfl

/-- Empty primary connectors separate components: neither child inherits
the primary connector's id as a routing parent. -/
theorem primary_fork (parent : Option ι) (id : ι)
    (leftPlan rightPlan : Source κ Layers) (left right : Source β (Cell α ρ ι)) :
    output (.fork .base leftPlan rightPlan) parent (.fork (id,[]) left right) =
      .fork (id,[]) (output leftPlan none left) (output rightPlan none right) := rfl

/-- Raw header prefixes are retained verbatim. They do not change which
component owns the parent fields below them. -/
theorem raw (context : Source κ Layers) (parent : Option ι) (packet : Packet α ρ ι)
    (source : Source β (Cell α ρ ι)) :
    output (context.setRoot (.raw packet.length context.rootRecord)) parent
      (source.setRoot (source.rootRecord.1,packet++source.rootRecord.2)) =
      (output context parent source).setRoot
        ((output context parent source).rootRecord.1,packet++(output context parent source).rootRecord.2) := by
  cases context with
  | leaf key plan =>
    cases source <;>
      simp only [output,Source.setRoot,Source.rootRecord,cell,edit,List.take_left,List.drop_left]
  | fork plan left right =>
    cases source with
    | leaf key record => rfl
    | fork record l r =>
      simp only [output,Source.setRoot,Source.rootRecord,cell,edit,List.take_left,List.drop_left,
        childParent,Layers.hasFork]

/-- A whole routing-leaf packet ends its own routing tree, even when its
payload is a fork. The attached component is repaired independently with
parent `none`; its child-parent propagation is unchanged. -/
theorem attachment (context : Source κ Layers) (parent : Option ι) (records : List ρ)
    (oldFields : Fields ι Unit) (source : Source β (Cell α ρ ι)) (fits : Fits context source) :
    output (context.setRoot (.leaf (.raw 1 context.rootRecord))) parent
      (source.setRoot (source.rootRecord.1,
        some (.real ((source.rootRecord.1,records),oldFields)) :: none :: source.rootRecord.2)) =
      (output context none source).setRoot
        ((output context none source).rootRecord.1,
          some (.real (((output context none source).rootRecord.1,records),neighbors parent false none)) ::
            none :: (output context none source).rootRecord.2) := by
  cases context with
  | leaf key plan => cases source <;> rfl
  | fork plan left right => cases source with
    | leaf key record => exact False.elim fits
    | fork record l r => rfl

end TangoSquared.Paper20261030.CanonicalMixedPacketRepair
