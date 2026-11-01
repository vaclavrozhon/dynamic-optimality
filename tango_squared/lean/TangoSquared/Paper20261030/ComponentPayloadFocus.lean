import TangoSquared.Paper20261030.PackedLeafFocus

/-! Exposing a real logical depth leaf puts its owning physical finger
at the unchanged payload root. Only the routing prefix and attachment
delimiter precede the payload's own root metadata. The mirror translation
does not change which payload is reached.
-/

namespace TangoSquared.Paper20261030.LocalComponentCompiler

open ColoredStorage SourcePointer Structural PhysicalForestMetadata LocalComponentForestCompiler

variable {α β ρ ι η C : Type*} [DecidableEq α] [LinearOrder C]

theorem real_payload_focus (color : α → C) (decorated : Cursor α (η × ρ)) (key : α) (logical : η × ρ)
    (leaf : decorated.focus = .leaf key logical)
    (forest : TaggedForest C α (LocalColoredCompiler.LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color (cursor Prod.fst color decorated) (erase forest))
    (virtualColor : C) (realColor : color key ≠ virtualColor) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (List (Option (PhysicalDatum α ρ ι η C)))) :
    ∃ current, ∃ (routing : List (PhysicalDatum α ρ ι η C)),
      representation virtualColor orientation headerKey payload forest (color key) = some current ∧
      current.focus = (payload (color key) key).setRoot
        (routing.map some ++ none::(payload (color key) key).rootRecord) := by
  have sourceLeaf : (cursor Prod.fst color decorated).focus =
      .leaf key (logical,fields Prod.fst color (parentId Prod.fst decorated.ancestors) (.leaf key logical)) := by
    simp only [cursor,leaf,annotate]
  have owning : color key ∈ (cursor Prod.fst color decorated).tree.support color := by
    apply ProjectionForest.support_focus color (cursor Prod.fst color decorated).focus _
    rw [sourceLeaf]
    simp only [Source.support,Finset.mem_singleton]
  have rep := represented (color key)
  cases location : forest (color key) with
  | none =>
    simp only [erase,location,Option.map_none,ProjectionForest.RepresentsAt] at rep
    exact False.elim (rep owning)
  | some physical =>
    simp only [erase,location,Option.map_some,ProjectionForest.RepresentsAt] at rep
    obtain ⟨records,focus⟩ := ColoredStorage.Represents.focus_leaf color key _ _ _ sourceLeaf rep
    cases physicalLeaf : physical.focus with
    | fork value left right =>
      simp only [Cursor.mapRecords,physicalLeaf,Source.mapRecords,reduceCtorEq] at focus
    | leaf other value =>
      have same : other = key := by
        simpa only [Cursor.mapRecords,physicalLeaf,Source.mapRecords,Source.leaf.injEq] using (show other = key ∧ value.2 = records from by
          simpa only [Cursor.mapRecords,physicalLeaf,Source.mapRecords,Source.leaf.injEq] using focus) |>.1
      subst other
      cases reversed : orientation (color key) <;>
        simp [representation,PayloadForestController.transform,VirtualHeaderController.encode,realColor,
          ForestMirrorController.transform,ForestMirrorController.turn,reversed,encode,location,encodeCursor,
          SourceForestLift.packet,Cursor.mapRecords,Cursor.mirror,cursor,physicalLeaf,annotate,
          Source.mapRecords,Source.mirror,SourcePayloads.cursor,SourcePayloads.graft] <;>
        exact ⟨[.real (value,fields Prod.fst (fun _ : α => ()) (parentId Prod.fst physical.ancestors) (.leaf key value))],rfl⟩

end TangoSquared.Paper20261030.LocalComponentCompiler
