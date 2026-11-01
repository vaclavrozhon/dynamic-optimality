import TangoSquared.Paper20261030.CursorRepresentationShapes
import TangoSquared.Paper20261030.ThreeColorConfiguration

/-! Exact key words of the actual component representation. Mirroring
reverses only a routing wing; payload key words retain their own order.
The virtual projection contributes the real header payload exactly once.
-/

namespace TangoSquared.Paper20261030.ForestRepresentation

open ColoredStorage SourcePointer Structural PhysicalForestMetadata

variable {α β ρ ι η C : Type*} [DecidableEq α] [LinearOrder C]

def word (forest : ProjectionForest.State C α ρ) (q : C) : List α :=
  ((forest q).map (fun current => current.tree.shape.leaves)).getD []

theorem represented_word (color : α → C) (source : Cursor α ρ) (forest : ProjectionForest.State C α ρ)
    (represented : ProjectionForest.Represents color source forest) (q : C) :
    word forest q = source.tree.shape.leaves.filter (keepColor color q) := by
  have rep := represented q
  cases location : forest q with
  | none =>
    rw [location] at rep
    have empty := packed_none_shape color q source.tree ((packed_none_iff color q source.tree).mpr rep)
    have leaves := congrArg RouterProjection.Router.leaves empty
    simpa only [word,location,Option.map_none,Option.getD_none,RouterProjection.Router.leaves_prune,
      RouterProjection.Router.leaves] using leaves.symm
  | some current =>
    rw [location] at rep
    simp only [word,location,Option.map_some,Option.getD_some,packed_shape color q source.tree rep.1,
      RouterProjection.Router.leaves_prune]

theorem encode_word (forest : TaggedForest C α ρ ι) (q : C) : word (encode forest) q = word (erase forest) q := by
  cases location : forest q <;>
    simp [word,encode,erase,location,encodeCursor,SourceForestLift.packet,Cursor.mapRecords_tree,
      Source.mapRecords_shape,cursor_tree,annotate_shape]

theorem mirror_word (orientation : C → Bool) (forest : ProjectionForest.State C α ρ) (q : C) :
    word (ForestMirrorController.transform orientation forest) q =
      if orientation q then (word forest q).reverse else word forest q := by
  cases location : forest q <;> cases reversed : orientation q <;>
    simp [word,ForestMirrorController.transform,ForestMirrorController.turn,location,reversed,Cursor.mirror_tree,Source.mirror_leaves]

theorem header_real_word (virtualColor q : C) (different : q ≠ virtualColor) (key : α)
    (forest : ProjectionForest.State C α ρ) :
    word (VirtualHeaderController.encode virtualColor key forest) q = word forest q := by
  cases location : forest q <;>
    simp [word,VirtualHeaderController.encode,different,location,Cursor.mapRecords_tree,Source.mapRecords_shape]

theorem header_virtual_word (virtualColor : C) (key : α) (forest : ProjectionForest.State C α ρ) :
    word (VirtualHeaderController.encode virtualColor key forest) virtualColor = [key] := by
  simp [word,VirtualHeaderController.encode,Cursor.tree,plug,Source.shape,RouterProjection.Router.leaves]

theorem payload_word (payload : C → α → Source β (List (Option ρ))) (forest : ProjectionForest.State C α ρ) (q : C) :
    word (PayloadForestController.transform payload forest) q = (word forest q).flatMap (fun key => (payload q key).shape.leaves) := by
  cases location : forest q <;>
    simp [word,PayloadForestController.transform,location,Cursor.payload_tree,SourcePayloads.graft_leaves]

end TangoSquared.Paper20261030.ForestRepresentation

namespace TangoSquared.Paper20261030.LocalComponentCompiler

open ColoredStorage SourcePointer Structural PhysicalForestMetadata LocalComponentForestCompiler ForestRepresentation

variable {α β ρ ι η C : Type*} [DecidableEq α] [LinearOrder C]

theorem real_word (color : α → C) (decorated : Cursor α (η × ρ))
    (forest : TaggedForest C α (LocalColoredCompiler.LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color (cursor Prod.fst color decorated) (erase forest))
    (virtualColor q : C) (different : q ≠ virtualColor) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (List (Option (PhysicalDatum α ρ ι η C)))) :
    word (representation virtualColor orientation headerKey payload forest) q =
      (if orientation q then (decorated.tree.shape.leaves.filter (keepColor color q)).reverse
        else decorated.tree.shape.leaves.filter (keepColor color q)).flatMap (fun key => (payload q key).shape.leaves) := by
  rw [representation,payload_word,header_real_word virtualColor q different,mirror_word,encode_word,
    represented_word color _ _ represented,cursor_tree,annotate_shape]

theorem virtual_word (virtualColor : C) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (List (Option (PhysicalDatum α ρ ι η C))))
    (forest : TaggedForest C α (LocalColoredCompiler.LogicalRecord ρ η C) ι) :
    word (representation virtualColor orientation headerKey payload forest) virtualColor = (payload virtualColor headerKey).shape.leaves := by
  rw [representation,payload_word,header_virtual_word]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]

end TangoSquared.Paper20261030.LocalComponentCompiler
