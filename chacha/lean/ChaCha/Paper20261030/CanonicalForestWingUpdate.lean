import ChaCha.Paper20261030.CanonicalPayloadPosition
import ChaCha.Paper20261030.RoutingUniquePort

set_option autoImplicit false

/-! Updating one real routing wing after its nested component changes
root. Reidentifying the routing leaf preserves the erased logical forest.
The physical view changes only that wing and its opaque payload function;
its virtual header and the other wing retain their exact views. -/

namespace ChaCha.Paper20261030.CanonicalForestWingUpdate

open ColoredStorage SourcePointer Structural PhysicalForestMetadata PhysicalPacketStaging

variable {α β ρ ι C : Type*} [DecidableEq C]

def replace (forest : TaggedForest C α ρ ι) (q : C) (fresh : Source α (ι × List ρ)) : TaggedForest C α ρ ι :=
  Function.update forest q (some ⟨fresh,[]⟩)

theorem erase_same (forest : TaggedForest C α ρ ι) (q : C) (before after : Source α (ι × List ρ))
    (present : forest q = some ⟨before,[]⟩) (same : after.mapRecords Prod.snd = before.mapRecords Prod.snd) :
    erase (replace forest q after) = erase forest := by
  funext other
  by_cases equal : other = q
  · subst other
    simp only [erase,replace,Function.update_self,present,Option.map_some,Cursor.mapRecords,List.map_nil,same]
  · simp only [erase,replace,Function.update_of_ne equal]

theorem unique (forest : TaggedForest C α ρ ι) (q : C) (after : Source α (ι × List ρ))
    (oldUnique : Unique forest) (newUnique : (after.inventory Prod.fst).Nodup) : Unique (replace forest q after) := by
  intro other current present
  by_cases equal : other = q
  · subst other
    simp only [replace,Function.update_self,Option.some.injEq] at present
    rw [← present]
    exact newUnique
  · rw [replace,Function.update_of_ne equal] at present
    exact oldUnique other current present

theorem leaf_erases (key : α) (old fresh : ι) (records : List ρ) (outside : List (Frame α (ι × List ρ))) :
    (plug (.leaf key (fresh,records)) outside).mapRecords Prod.snd =
      (plug (.leaf key (old,records)) outside).mapRecords Prod.snd := by
  rw [← plug_mapRecords,← plug_mapRecords]
  rfl

theorem view (virtualColor q : C) (different : q ≠ virtualColor) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (Packet α ρ ι)) (newPayload : α → Source β (Packet α ρ ι))
    (forest : TaggedForest C α ρ ι) (after : Source α (ι × List ρ)) :
    ComponentPhysicalRepair.view virtualColor orientation headerKey (Function.update payload q newPayload)
      (encode (replace forest q after)) =
      Function.update (ComponentPhysicalRepair.view virtualColor orientation headerKey payload (encode forest)) q
        (some ⟨CanonicalPacketLayerViews.routing newPayload (orientation q) none after,[]⟩) := by
  funext other
  by_cases equal : other = q
  · subst other
    rw [Function.update_self]
    have here := CanonicalPacketLayerViews.component_real virtualColor q different orientation headerKey
      (Function.update payload q newPayload) (replace forest q after) after (Function.update_self _ _ _)
    simpa only [Function.update_self] using here
  · simp only [ComponentPhysicalRepair.view,PayloadForestController.transform,VirtualHeaderController.encode,
      ForestMirrorController.transform,encode,replace,Function.update_of_ne equal,Function.update_of_ne different.symm]

end ChaCha.Paper20261030.CanonicalForestWingUpdate
