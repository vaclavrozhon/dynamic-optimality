import ChaCha.Paper20261030.CanonicalForestWingUpdate
import ChaCha.Paper20261030.ThreeColorWingReplacement

set_option autoImplicit false

/-! Reassembling a canonical component when one real routing wing changes.
The enclosing connector context, virtual header, other wing, and wing
presence bits are retained. The changed wing's logical forest erasure is
handled separately by `CanonicalForestWingUpdate.erase_same`. -/

namespace ChaCha.Paper20261030.CanonicalForestWingUpdate

open ColoredStorage SourcePointer Structural PhysicalForestMetadata PhysicalPacketStaging ForestConnector.ThreeColors

variable {α β ρ ι : Type*}

theorem assembled (side : Bool) (orientation : Option Bool → Bool) (headerKey : α)
    (payload : Option Bool → α → Source β (Packet α ρ ι)) (newPayload : α → Source β (Packet α ρ ι))
    (forest : TaggedForest (Option Bool) α ρ ι) (before after : Source α (ι × List ρ))
    (present : forest (some side) = some ⟨before,[]⟩)
    (header : Cursor β (Packet α ρ ι))
    (virtualPresent : ComponentPhysicalRepair.view none orientation headerKey payload (encode forest) none = some header)
    (config : MultiSourceProgram.Configuration (Option Bool) β (Packet α ρ ι))
    (assembled : ForestConnector.assemble (ComponentPhysicalRepair.view none orientation headerKey payload (encode forest))
      (layout (ComponentPhysicalRepair.view none orientation headerKey payload (encode forest))) = some config) :
    let fresh := ComponentPhysicalRepair.view none orientation headerKey (Function.update payload (some side) newPayload)
      (encode (replace forest (some side) after))
    ∃ finalConfig outside,
      ForestConnector.assemble fresh (layout fresh) = some finalConfig ∧
      outside ≠ [] ∧ EmptyConnector outside ∧
      config.tree = plug (CanonicalPacketLayerViews.routing (payload (some side)) (orientation (some side)) none before) outside ∧
      finalConfig.tree = plug (CanonicalPacketLayerViews.routing newPayload (orientation (some side)) none after) outside ∧
      (∀ q, (fresh q).isSome =
        (ComponentPhysicalRepair.view none orientation headerKey payload (encode forest) q).isSome) := by
  dsimp only
  let original := ComponentPhysicalRepair.view none orientation headerKey payload (encode forest)
  let fresh := ComponentPhysicalRepair.view none orientation headerKey (Function.update payload (some side) newPayload)
    (encode (replace forest (some side) after))
  let newWing : Cursor β (Packet α ρ ι) := ⟨CanonicalPacketLayerViews.routing newPayload (orientation (some side)) none after,[]⟩
  have changed : fresh = Function.update original (some side) (some newWing) :=
    view none (some side) (by simp) orientation headerKey payload newPayload forest after
  have here := CanonicalPacketLayerViews.component_real none (some side) (by simp) orientation headerKey payload forest before present
  have canonical : config = configuration original header :=
    Option.some.inj (assembled.symm.trans (assemble_configuration original header virtualPresent))
  have headerSame : fresh none = some header := by
    rw [changed,Function.update_of_ne (by simp)]
    exact virtualPresent
  obtain ⟨outside,proper,empty,beforeTree,replacements⟩ := replace_piece original header side _ here
  refine ⟨configuration fresh header,outside,assemble_configuration fresh header headerSame,proper,empty,?_,?_,?_⟩
  · rw [canonical]
    exact beforeTree
  · rw [changed]
    exact replacements newWing
  · intro q
    change (fresh q).isSome = (original q).isSome
    rw [changed]
    by_cases equal : q = some side
    · subst q
      simp only [Function.update_self,original,here,Option.isSome_some]
    · rw [Function.update_of_ne equal]

end ChaCha.Paper20261030.CanonicalForestWingUpdate
