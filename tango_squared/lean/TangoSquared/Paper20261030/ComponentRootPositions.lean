import TangoSquared.Paper20261030.CursorRepresentationShapes

/-! At a source-root boundary every real projection finger is also at
its own root. This follows from the projection invariant, rather than
being an additional placement hypothesis. All component translations
preserve these root positions, including the physical header replacement.
-/

namespace TangoSquared.Paper20261030.LocalComponentCompiler

open ColoredStorage SourcePointer Structural PhysicalForestMetadata LocalComponentForestCompiler

variable {α β ρ ι η C : Type*} [DecidableEq α] [LinearOrder C]

theorem tagged_root (color : α → C) (decorated : Source α (η × ρ))
    (forest : TaggedForest C α (LocalColoredCompiler.LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (q : C) (current : Cursor α (PhysicalForestMetadata.Payload (LocalColoredCompiler.LogicalRecord ρ η C) ι))
    (present : forest q = some current) : current.ancestors = [] := by
  have rep := represented q
  simp only [erase,present,Option.map_some,ProjectionForest.RepresentsAt] at rep
  have root := ColoredStorage.Represents.root_ancestors color q _ _ rep
  simpa only [Cursor.mapRecords,List.map_eq_nil_iff] using root

theorem representation_root (color : α → C) (decorated : Source α (η × ρ))
    (forest : TaggedForest C α (LocalColoredCompiler.LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (virtualColor : C) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (List (Option (PhysicalDatum α ρ ι η C))))
    (q : C) (current : Cursor β (List (Option (PhysicalDatum α ρ ι η C))))
    (present : representation virtualColor orientation headerKey payload forest q = some current) :
    current.ancestors = [] := by
  by_cases virtual : q = virtualColor
  · subst q
    simp only [representation,PayloadForestController.transform,VirtualHeaderController.encode,ite_true,Option.map_some,Option.some.injEq] at present
    rw [← present]
    rfl
  · cases location : forest q with
    | none =>
      simp [representation,PayloadForestController.transform,VirtualHeaderController.encode,virtual,
        ForestMirrorController.transform,encode,location] at present
    | some physical =>
      have atRoot := tagged_root color decorated forest represented q physical location
      cases reversed : orientation q <;>
        simp only [representation,PayloadForestController.transform,VirtualHeaderController.encode,virtual,if_false,
          ForestMirrorController.transform,encode,location,Option.map_some,ForestMirrorController.turn,reversed,
          Bool.false_eq_true,Bool.true_eq,if_true,Option.some.injEq] at present <;>
        rw [← present] <;>
        simp [SourcePayloads.cursor,Cursor.mapRecords,Cursor.mirror,encodeCursor,SourceForestLift.packet,cursor,frames,atRoot]

end TangoSquared.Paper20261030.LocalComponentCompiler
