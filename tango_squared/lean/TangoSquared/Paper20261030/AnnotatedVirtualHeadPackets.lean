import TangoSquared.Paper20261030.PrimaryVirtualPackets

/-!
# Prepared virtual packets of canonically annotated sources

The boundary records here are the actual structural annotations, not
independent records with assumed masks. For primary depth intervals the
absent prefix and the unique completion leaf follow from their leaf words.
-/

namespace TangoSquared.Paper20261030.AnnotatedVirtualHeadPackets

open ColoredStorage SourcePointer Structural HeadBoundary

variable {α ρ ι : Type*}

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

abbrev record (identifier : ρ → ι) (color : α → Option Bool) (parent : Option ι) (source : Source α ρ) :=
  (source.rootRecord,fields identifier color parent source)

theorem active (identifier : ρ → ι) (color : α → Option Bool)
    (low high terminal : ρ) (depth bottom : α) (direction : Bool) (headPart tail : Source α ρ)
    (boundary : color depth = some direction)
    (absent : packed color none (annotate identifier color (some (identifier low)) headPart) = none)
    (tailPacket : List (Record ρ ι (Option Bool)))
    (tailPacked : packed color none (annotate identifier color (some (identifier high)) tail) = some (.leaf bottom tailPacket)) :
    packed color none (annotate identifier color none (.fork low headPart (.fork high (.leaf depth terminal) tail))) =
      some (.leaf bottom
        (VirtualHeadPackets.prefixes
          (record identifier color none (.fork low headPart (.fork high (.leaf depth terminal) tail)))
          (record identifier color (some (identifier low)) (.fork high (.leaf depth terminal) tail)) ++ tailPacket)) := by
  apply VirtualHeadPackets.active_packing color _ _ _ depth bottom direction
    (annotate identifier color (some (identifier low)) headPart)
    (annotate identifier color (some (identifier high)) tail)
    (descriptor identifier color headPart) (descriptor identifier color (.fork high (.leaf depth terminal) tail))
    (descriptor identifier color (.leaf depth terminal)) (descriptor identifier color tail)
    rfl rfl
  · exact (ObservedHeadBlueprint.annotate_support identifier color (some (identifier low)) headPart).symm
  · simp only [descriptor,Source.support,ObservedHeadBlueprint.annotate_support]
  · rfl
  · exact (ObservedHeadBlueprint.annotate_support identifier color (some (identifier high)) tail).symm
  · exact boundary
  · exact absent
  · exact tailPacked

theorem dormant [DecidableEq α] (identifier : ρ → ι) (color : α → Option Bool)
    (high terminal : ρ) (depth bottom : α) (tail : Source α ρ)
    (boundary : color depth = none) (tailPacket : List (Record ρ ι (Option Bool)))
    (tailPacked : packed color none (annotate identifier color (some (identifier high)) tail) = some (.leaf bottom tailPacket)) :
    packed color none (annotate identifier color none (.fork high (.leaf depth terminal) tail)) =
      some (.fork [record identifier color none (.fork high (.leaf depth terminal) tail)]
        (.leaf depth [record identifier color (some (identifier high)) (.leaf depth terminal)]) (.leaf bottom tailPacket)) :=
  VirtualHeadPackets.dormant_packing color _ _ depth bottom _ boundary tailPacket tailPacked

theorem root_active (identifier : ρ → ι) (color : α → Option Bool)
    (high terminal : ρ) (depth bottom : α) (direction : Bool) (tail : Source α ρ)
    (boundary : color depth = some direction) (tailPacket : List (Record ρ ι (Option Bool)))
    (tailPacked : packed color none (annotate identifier color (some (identifier high)) tail) = some (.leaf bottom tailPacket)) :
    packed color none (annotate identifier color none (.fork high (.leaf depth terminal) tail)) =
      some (.leaf bottom (ObservedHeadBlueprint.owned none
        (record identifier color none (.fork high (.leaf depth terminal) tail)) ++ tailPacket)) := by
  apply VirtualHeadPackets.root_active_packing color _ _ depth bottom direction _
    (descriptor identifier color (.leaf depth terminal)) (descriptor identifier color tail) rfl rfl
  · exact (ObservedHeadBlueprint.annotate_support identifier color (some (identifier high)) tail).symm
  · exact boundary
  · exact tailPacked

open PreferredProjection PrimaryWings PackedPrimary

variable {κ : Type*} [DecidableEq κ]

theorem active_interval (identifier : ρ → ι) (tree : PrefRouter κ)
    (low high terminal : ρ) (depth : Nat) (direction : Bool) (headPart tail : Source Nat ρ)
    (boundary : color 0 tree depth = some direction) (beforeBottom : depth < (exits tree).length)
    (prefixDepths : ∀ key ∈ headPart.shape.leaves, key < depth)
    (tailDepths : tail.shape.leaves = List.range' (depth+1) ((exits tree).length-depth)) :
    ∃ tailPacket,
      packed (color 0 tree) none
        (annotate identifier (color 0 tree) none (.fork low headPart (.fork high (.leaf depth terminal) tail))) =
        some (.leaf (exits tree).length
          (VirtualHeadPackets.prefixes
            (record identifier (color 0 tree) none (.fork low headPart (.fork high (.leaf depth terminal) tail)))
            (record identifier (color 0 tree) (some (identifier low)) (.fork high (.leaf depth terminal) tail)) ++ tailPacket)) := by
  have absent := PrimaryVirtualPackets.prefix_absent tree
    (annotate identifier (color 0 tree) (some (identifier low)) headPart)
    (by rw [annotate_shape]; exact fun key member => (prefixDepths key member).trans beforeBottom)
  obtain ⟨tailPacket,tailPacked⟩ := PrimaryVirtualPackets.interval_packet 0 tree (depth+1)
    (annotate identifier (color 0 tree) (some (identifier high)) tail) (Nat.zero_le _) (by omega)
    (by rw [annotate_shape,tailDepths]; congr 1 <;> omega)
  change packed (color 0 tree) none (annotate identifier (color 0 tree) (some (identifier high)) tail) =
    some (.leaf (0+(exits tree).length) tailPacket) at tailPacked
  rw [Nat.zero_add] at tailPacked
  exact ⟨tailPacket,active identifier (color 0 tree) low high terminal depth _ direction headPart tail boundary absent tailPacket tailPacked⟩

theorem dormant_interval (identifier : ρ → ι) (tree : PrefRouter κ)
    (high terminal : ρ) (depth : Nat) (tail : Source Nat ρ)
    (tailDepths : tail.shape.leaves = List.range' (depth+1) ((exits tree).length+1)) :
    ∃ tailPacket,
      packed (color (depth+1) tree) none
        (annotate identifier (color (depth+1) tree) none (.fork high (.leaf depth terminal) tail)) =
        some (.fork [record identifier (color (depth+1) tree) none (.fork high (.leaf depth terminal) tail)]
          (.leaf depth [record identifier (color (depth+1) tree) (some (identifier high)) (.leaf depth terminal)])
          (.leaf (depth+1+(exits tree).length) tailPacket)) := by
  have boundary : color (depth+1) tree depth = none := by simp [color,portAt]
  obtain ⟨tailPacket,tailPacked⟩ := PrimaryVirtualPackets.interval_packet (depth+1) tree (depth+1)
    (annotate identifier (color (depth+1) tree) (some (identifier high)) tail) le_rfl (by omega)
    (by rw [annotate_shape,tailDepths]; congr 1 <;> omega)
  exact ⟨tailPacket,dormant identifier (color (depth+1) tree) high terminal depth _ tail boundary tailPacket tailPacked⟩

theorem root_active_interval (identifier : ρ → ι) (tree : PrefRouter κ)
    (high terminal : ρ) (direction : Bool) (tail : Source Nat ρ)
    (boundary : color 0 tree 0 = some direction) (nonempty : 0 < (exits tree).length)
    (tailDepths : tail.shape.leaves = List.range' 1 (exits tree).length) :
    ∃ tailPacket,
      packed (color 0 tree) none (annotate identifier (color 0 tree) none (.fork high (.leaf 0 terminal) tail)) =
        some (.leaf (exits tree).length (ObservedHeadBlueprint.owned none
          (record identifier (color 0 tree) none (.fork high (.leaf 0 terminal) tail)) ++ tailPacket)) := by
  obtain ⟨tailPacket,tailPacked⟩ := PrimaryVirtualPackets.interval_packet 0 tree 1
    (annotate identifier (color 0 tree) (some (identifier high)) tail) (Nat.zero_le _) (by omega)
    (by rw [annotate_shape,tailDepths]; congr 1 <;> omega)
  change packed (color 0 tree) none (annotate identifier (color 0 tree) (some (identifier high)) tail) =
    some (.leaf (0+(exits tree).length) tailPacket) at tailPacked
  rw [Nat.zero_add] at tailPacked
  exact ⟨tailPacket,root_active identifier (color 0 tree) high terminal 0 _ direction tail boundary tailPacket tailPacked⟩

end TangoSquared.Paper20261030.AnnotatedVirtualHeadPackets
