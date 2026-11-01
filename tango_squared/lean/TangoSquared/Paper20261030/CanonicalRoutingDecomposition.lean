import TangoSquared.Paper20261030.CanonicalPacketLayerViews
import TangoSquared.Paper20261030.RootPackedForest

/-!
# Decomposing canonical real projections at exposed joins

The maintained tagged projection determines its own packet identifiers
and child fields. A suppressed logical join only prefixes the surviving
packet. A genuine routing fork keeps both children, and a mirrored wing
exchanges their physical order while retaining their logical fields.

`render` adds a dummy outer identifier solely for this representation
proof. The packet relation is invariant under replacing those outer ids;
the execution theorem still uses the actual immutable vertex ids and
requires their separate alignment invariant.
-/

namespace TangoSquared.Paper20261030.PacketLayers.Reached

open ColoredStorage PhysicalPacketStaging

variable {κ α β ρ ι : Type*}

theorem stored_of_erasure (blocks : κ → Source β (Packet α ρ ι))
    (context : Source κ (Expression α ρ ι)) (source target : Source β (Context.Cell α ρ ι))
    (stored : Stored blocks context source) (same : source.mapRecords Prod.snd = target.mapRecords Prod.snd) :
    Stored blocks context target := by
  induction context generalizing source target with
  | leaf key expression =>
    have root := congrArg Source.rootRecord same
    simp only [Source.mapRecords_root] at root
    exact ⟨same ▸ stored.1,root ▸ stored.2⟩
  | fork expression left right ihl ihr =>
    cases source with
    | leaf => exact False.elim stored
    | fork record l r => cases target with
      | leaf => cases same
      | fork fresh a b =>
        simp only [Source.mapRecords,Source.fork.injEq] at same
        exact ⟨same.1 ▸ stored.1,ihl l a stored.2.1 same.2.1,ihr r b stored.2.2 same.2.2⟩

end TangoSquared.Paper20261030.PacketLayers.Reached

namespace TangoSquared.Paper20261030.CanonicalRoutingDecomposition

open ColoredStorage SourcePointer Structural PhysicalPacketStaging CanonicalPacketLayerViews
open PacketLayers.Representation

variable {α β ρ ι : Type*}

def render (dummyId : ι) (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (parent : Option ι) (tagged : Option (Tagged α ρ ι)) :=
  tagged.map (fun source => (routing payload reverse parent source).mapRecords (fun packet => (dummyId,packet)))

theorem augment_prefix (dummyId : ι) (records : List ρ) (source : Source β (Packet α ρ ι)) :
    (source.setRoot (PhysicalPacketStaging.Context.prependLogical records source.rootRecord)).mapRecords (fun packet => (dummyId,packet)) =
      addRoot records (source.mapRecords (fun packet => (dummyId,packet))) := by
  simp only [Source.mapRecords_setRoot,addRoot,Source.mapRecords_root]

theorem join_decompose (dummyId : ι) (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (parent : Option ι)
    (records : List ρ) (left right : ProjectionLocal.Projected α ρ)
    (tagged : Option (Tagged α ρ ι))
    (erases : tagged.map (Source.mapRecords Prod.snd) = ProjectionLocal.decorate records (ProjectionLocal.join left right)) :
    ∃ taggedLeft taggedRight leftParent rightParent packetId packetFields,
      taggedLeft.map (Source.mapRecords Prod.snd) = left ∧
      taggedRight.map (Source.mapRecords Prod.snd) = right ∧
      render dummyId payload reverse parent tagged =
        physicalJoin dummyId packetId packetFields records
          (if reverse then render dummyId payload reverse rightParent taggedRight else render dummyId payload reverse leftParent taggedLeft)
          (if reverse then render dummyId payload reverse leftParent taggedLeft else render dummyId payload reverse rightParent taggedRight) := by
  cases left with
  | none => cases right with
    | none =>
      have missing : tagged = none := by simpa only [ProjectionLocal.join,ProjectionLocal.decorate,Option.map_none,Option.map_eq_none_iff] using erases
      subst tagged
      refine ⟨none,none,parent,parent,dummyId,placeholder,rfl,rfl,?_⟩
      cases reverse <;> rfl
    | some right =>
      cases tagged with
      | none => cases erases
      | some tagged =>
        have equation : tagged.mapRecords Prod.snd = right.setRoot (records++right.rootRecord) := Option.some.inj erases
        obtain ⟨block,blockErases,rfl⟩ := unprepend records right tagged equation
        refine ⟨none,some block,parent,parent,dummyId,placeholder,rfl,congrArg some blockErases,?_⟩
        cases reverse <;>
          simp only [render,Option.map_none,Option.map_some,Bool.false_eq_true,if_false,if_true,
            physicalJoin,logical_prefix,augment_prefix]
  | some left => cases right with
    | none =>
      cases tagged with
      | none => cases erases
      | some tagged =>
        have equation : tagged.mapRecords Prod.snd = left.setRoot (records++left.rootRecord) := Option.some.inj erases
        obtain ⟨block,blockErases,rfl⟩ := unprepend records left tagged equation
        refine ⟨some block,none,parent,parent,dummyId,placeholder,congrArg some blockErases,rfl,?_⟩
        cases reverse <;>
          simp only [render,Option.map_none,Option.map_some,Bool.false_eq_true,if_false,if_true,
            physicalJoin,logical_prefix,augment_prefix]
    | some right =>
      cases tagged with
      | none => cases erases
      | some tagged =>
        have equation : tagged.mapRecords Prod.snd = .fork records left right := by
          simpa only [Option.map_some,ProjectionLocal.join,ProjectionLocal.decorate,Source.setRoot,Source.rootRecord,
            List.append_nil,Option.some.injEq] using erases
        obtain ⟨id,taggedLeft,taggedRight,rfl,leftErases,rightErases⟩ := fork_decomposition records left right tagged equation
        refine ⟨some taggedLeft,some taggedRight,some id,some id,id,
          fields Prod.fst (fun _ => (() : Unit)) parent (.fork (id,records) taggedLeft taggedRight),
          congrArg some leftErases,congrArg some rightErases,?_⟩
        cases reverse <;>
          simp only [render,Option.map_some,Bool.false_eq_true,if_false,if_true,
            physicalJoin,CanonicalPacketLayerViews.fork,Source.mapRecords]

end TangoSquared.Paper20261030.CanonicalRoutingDecomposition
