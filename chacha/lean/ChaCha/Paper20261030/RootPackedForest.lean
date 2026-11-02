import ChaCha.Paper20261030.CursorRepresentationShapes
import ChaCha.Paper20261030.VirtualPhysicalPackets

/-!
# Recovering packed root views from the maintained forest invariant

At a source root, erasing the physical identifiers gives exactly the
canonical packed projections, including absent colors. Thus the contents
of a stored virtual header are determined by the maintained invariant;
they are not an additional input to the running controller.
-/

namespace ChaCha.Paper20261030.RootPackedForest

open ColoredStorage SourcePointer PhysicalForestMetadata

variable {α ρ ι C : Type*} [DecidableEq α] [LinearOrder C]

theorem erases (color : α → C) (source : Source α ρ)
    (forest : TaggedForest C α ρ ι)
    (represented : ProjectionForest.Represents color ⟨source,[]⟩ (erase forest)) (q : C) :
    erase forest q = (packed color q source).map (fun tree => ⟨tree,[]⟩) := by
  have actual := represented q
  cases present : erase forest q with
  | none =>
    rw [present] at actual
    have absent := (packed_none_iff color q source).mpr actual
    simp only [absent,Option.map_none]
  | some current =>
    rw [present] at actual
    have root := represents_root color q source actual.1
    have same := ColoredStorage.Represents.unique color q ⟨source,[]⟩ actual root
    have packing : packed color q source = some current.tree := actual.1
    rw [packing]
    exact congrArg some same

theorem present (color : α → C) (source : Source α ρ)
    (forest : TaggedForest C α ρ ι)
    (represented : ProjectionForest.Represents color ⟨source,[]⟩ (erase forest))
    (q : C) (plain : Source α (List ρ)) (packing : packed color q source = some plain) :
    ∃ tagged : Source α (Payload ρ ι), forest q = some ⟨tagged,[]⟩ ∧ tagged.mapRecords Prod.snd = plain := by
  have exactView := erases color source forest represented q
  rw [packing] at exactView
  cases found : forest q with
  | none => simp only [erase,found,Option.map_none,Option.map_some,reduceCtorEq] at exactView
  | some current =>
    rcases current with ⟨tagged,ancestors⟩
    simp only [erase,found,Option.map_some,Option.some.injEq,Cursor.mapRecords,Cursor.mk.injEq] at exactView
    have root : ancestors = [] := List.map_eq_nil_iff.mp exactView.2
    subst ancestors
    exact ⟨tagged,rfl,exactView.1⟩

theorem absent (color : α → C) (source : Source α ρ)
    (forest : TaggedForest C α ρ ι)
    (represented : ProjectionForest.Represents color ⟨source,[]⟩ (erase forest))
    (q : C) (packing : packed color q source = none) : forest q = none := by
  have exactView := erases color source forest represented q
  rw [packing] at exactView
  simpa only [erase,Option.map_none,Option.map_eq_none_iff] using exactView

/-- The virtual orientation is the original source orientation. Mirroring
real right-wing projections has no effect on this stored header. -/
theorem decode_virtual (color : α → C) (source : Source α ρ)
    (forest : TaggedForest C α ρ Nat)
    (represented : ProjectionForest.Represents color ⟨source,[]⟩ (erase forest))
    (virtualColor : C) (orientation : C → Bool) (forward : orientation virtualColor = false) :
    VirtualPhysicalPackets.decode
      (ForestMirrorController.transform orientation (encode forest) virtualColor) =
      (packed color virtualColor source).map (fun tree => ⟨tree,[]⟩) := by
  cases packing : packed color virtualColor source with
  | none =>
    have missing := absent color source forest represented virtualColor packing
    simp only [ForestMirrorController.transform,encode,missing,Option.map_none,VirtualPhysicalPackets.decode]
  | some plain =>
    obtain ⟨tagged,found,erased⟩ := present color source forest represented virtualColor plain packing
    simp only [ForestMirrorController.transform,encode,found,Option.map_some,ForestMirrorController.turn,
      forward,Bool.false_eq_true,if_false,VirtualPhysicalPackets.decode_root,erased]

end ChaCha.Paper20261030.RootPackedForest
