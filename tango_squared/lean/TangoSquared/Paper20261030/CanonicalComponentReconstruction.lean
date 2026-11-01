import TangoSquared.Paper20261030.CanonicalRepairedDormant
import TangoSquared.Paper20261030.CanonicalComponentAssembly
import TangoSquared.Paper20261030.ComponentOriginalKeys

set_option autoImplicit false

/-!
# Rebuilding the maintained component forest from canonical output pieces

The two real routing witnesses and a stored virtual witness determine a
rooted three-color forest. Equality of their logical erasures to the
three packed projections proves the existing forest invariant. Its actual
connector assembly has exactly the repaired left/header/right view.
-/

namespace TangoSquared.Paper20261030.CanonicalComponentReconstruction

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PhysicalForestMetadata
open CanonicalPacketLayerViews LocalComponentCompiler

variable {α β ρ ι : Type*}

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

def forest (left virtual right : Option (Tagged α ρ ι)) : TaggedForest (Option Bool) α ρ ι
  | some true => left.map (fun source => ⟨source,[]⟩)
  | none => virtual.map (fun source => ⟨source,[]⟩)
  | some false => right.map (fun source => ⟨source,[]⟩)

theorem represents [DecidableEq α] (color : α → Option Bool) (source : Source α ρ)
    (left virtual right : Option (Tagged α ρ ι))
    (hl : left.map (Source.mapRecords Prod.snd) = packed color (some true) source)
    (hv : virtual.map (Source.mapRecords Prod.snd) = packed color none source)
    (hr : right.map (Source.mapRecords Prod.snd) = packed color (some false) source) :
    ProjectionForest.Represents color ⟨source,[]⟩ (erase (forest left virtual right)) := by
  have roots : erase (forest left virtual right) = ProjectionForest.roots color source := by
    funext q
    cases q with
    | none =>
      rw [ProjectionForest.roots,← hv]
      cases virtual <;> rfl
    | some side => cases side with
      | true => rw [ProjectionForest.roots,← hl]; cases left <;> rfl
      | false => rw [ProjectionForest.roots,← hr]; cases right <;> rfl
  rw [roots]
  exact ProjectionForest.represents_roots color source

def header (virtual : Option (Tagged α ρ ι)) : Packet α ρ ι :=
  [some (.header (virtual.map (fun source => encodeCursor ⟨source,[]⟩))),none]

theorem left_piece (left virtual right : Option (Tagged α ρ ι)) (headerKey : α)
    (payload : Option Bool → α → Source β (Packet α ρ ι)) :
    ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode (forest left virtual right)) (some true) =
      left.map (fun source => ⟨routing (payload (some true)) false none source,[]⟩) := by
  cases left with
  | none =>
    simp only [ComponentPhysicalRepair.view,PayloadForestController.transform,VirtualHeaderController.encode,
      reduceCtorEq,if_false,ForestMirrorController.transform,encode,forest,Option.map_none]
  | some source =>
    exact component_real none (some true) (by decide) wingOrientation headerKey payload (forest (some source) virtual right) source rfl

theorem right_piece (left virtual right : Option (Tagged α ρ ι)) (headerKey : α)
    (payload : Option Bool → α → Source β (Packet α ρ ι)) :
    ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode (forest left virtual right)) (some false) =
      right.map (fun source => ⟨routing (payload (some false)) true none source,[]⟩) := by
  cases right with
  | none =>
    simp only [ComponentPhysicalRepair.view,PayloadForestController.transform,VirtualHeaderController.encode,
      reduceCtorEq,if_false,ForestMirrorController.transform,encode,forest,Option.map_none]
  | some source =>
    exact component_real none (some false) (by decide) wingOrientation headerKey payload (forest left virtual (some source)) source rfl

theorem virtual_piece (left virtual right : Option (Tagged α ρ ι)) (headerKey : α)
    (payload : Option Bool → α → Source β (Packet α ρ ι)) :
    ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode (forest left virtual right)) none =
      some ⟨(payload none headerKey).setRoot (header virtual++(payload none headerKey).rootRecord),[]⟩ := by
  rw [component_virtual]
  cases virtual <;> rfl

theorem assemble_tree (pieces : ProjectionForest.State (Option Bool) β (Option (Datum α ρ ι)))
    (middle : Cursor β (Packet α ρ ι)) (present : pieces none = some middle)
    (config : MultiSourceProgram.Configuration (Option Bool) β (Packet α ρ ι))
    (assembled : ForestConnector.assemble pieces (ForestConnector.ThreeColors.layout pieces) = some config) :
    some config.tree = ProjectionLocal.join
      (ProjectionLocal.join ((pieces (some true)).map Cursor.tree) ((pieces none).map Cursor.tree))
      ((pieces (some false)).map Cursor.tree) := by
  cases left : pieces (some true) <;> cases right : pieces (some false) <;>
    simp only [ForestConnector.ThreeColors.layout,left,right,Option.isSome_none,Option.isSome_some,
      Bool.false_eq_true,if_false,if_true,ForestConnector.assemble,present,Option.map_some,
      Option.bind_some,Option.some.injEq] at assembled <;>
    rw [← assembled,present] <;> rfl

theorem assembled (left virtual right : Option (Tagged α ρ ι)) (headerKey : α)
    (payload : Option Bool → α → Source β (Packet α ρ ι)) :
    ∃ config : MultiSourceProgram.Configuration (Option Bool) β (Packet α ρ ι),
      ForestConnector.assemble
        (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode (forest left virtual right)))
        (ForestConnector.ThreeColors.layout
          (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode (forest left virtual right)))) = some config ∧
      some config.tree = CanonicalRepairedDormant.view (payload (some true)) (payload (some false))
        left right (header virtual) (payload none headerKey) := by
  have middle := virtual_piece left virtual right headerKey payload
  obtain ⟨config,assembly⟩ := ForestConnector.ThreeColors.assemble_exists _ _ middle
  refine ⟨config,assembly,?_⟩
  have tree := assemble_tree _ _ middle config assembly
  rw [left_piece,right_piece,middle] at tree
  simpa only [Option.map_map,Option.map_some,Function.comp_def,Cursor.tree,plug,CanonicalRepairedDormant.view] using tree

end TangoSquared.Paper20261030.CanonicalComponentReconstruction
