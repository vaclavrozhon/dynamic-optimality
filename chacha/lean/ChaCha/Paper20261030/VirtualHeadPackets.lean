import ChaCha.Paper20261030.ObservedHeadBlueprint
import ChaCha.Paper20261030.HeadRootBoundaryMetadata

/-!
# Rebuilding the bounded virtual packets of a head switch

An active virtual projection is one bottom leaf. A dormant projection
contains its sentinel and bottom leaves. The controller below consumes
these stored cursors and the observed old/new boundary records. It strips
the known old prefixes, transfers the bottom packets, and reconstructs
the two virtual projections. No unbounded source tree is inspected.

This module concerns logical packets. Re-encoding their physical ids and
pointer fields and writing the resulting datums are separate steps.
-/

namespace ChaCha.Paper20261030.VirtualHeadPackets

open ColoredStorage SourcePointer Structural HeadBoundary ProjectionLocal ObservedHeadBlueprint

variable {α ρ ι : Type*}

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

abbrev Logical (ρ ι : Type*) := Record ρ ι (Option Bool)
abbrev Header (α ρ ι : Type*) := Option (Cursor α (List (Logical ρ ι)))

def prefixes (low high : Logical ρ ι) : List (Logical ρ ι) := owned none low ++ owned none high

def exchange (old fresh : Records ρ ι (Option Bool)) (active incoming : Header α ρ ι) :
    Option (Header α ρ ι × Header α ρ ι) :=
  match active,incoming with
  | some ⟨.leaf oldBottom oldPacket,[]⟩,
      some ⟨.fork _ (.leaf depth _) (.leaf newBottom incomingPacket),[]⟩ =>
    some (some ⟨.leaf newBottom (prefixes fresh.low fresh.incomingHigh ++ incomingPacket),[]⟩,
      some ⟨.fork [fresh.oldHigh] (.leaf depth [fresh.oldTerminal])
        (.leaf oldBottom (oldPacket.drop (prefixes old.low old.oldHigh).length)),[]⟩)
  | _,_ => none

theorem exchange_exact (old fresh : Records ρ ι (Option Bool)) (depth oldBottom newBottom : α)
    (oldPacket incomingPacket : List (Logical ρ ι)) :
    exchange old fresh
      (some ⟨.leaf oldBottom (prefixes old.low old.oldHigh ++ oldPacket),[]⟩)
      (some ⟨.fork [old.incomingHigh] (.leaf depth [old.incomingTerminal]) (.leaf newBottom incomingPacket),[]⟩) =
      some (some ⟨.leaf newBottom (prefixes fresh.low fresh.incomingHigh ++ incomingPacket),[]⟩,
        some ⟨.fork [fresh.oldHigh] (.leaf depth [fresh.oldTerminal]) (.leaf oldBottom oldPacket),[]⟩) := by
  simp only [exchange,List.drop_left]

def exchangeRoot (old fresh : RootRecords ρ ι) (active incoming : Header α ρ ι) :
    Option (Header α ρ ι × Header α ρ ι) :=
  match active,incoming with
  | some ⟨.leaf oldBottom oldPacket,[]⟩,
      some ⟨.fork _ (.leaf depth _) (.leaf newBottom incomingPacket),[]⟩ =>
    some (some ⟨.leaf newBottom (owned none fresh.incomingHigh ++ incomingPacket),[]⟩,
      some ⟨.fork [fresh.oldHigh] (.leaf depth [fresh.oldTerminal])
        (.leaf oldBottom (oldPacket.drop (owned none old.oldHigh).length)),[]⟩)
  | _,_ => none

theorem exchange_root_exact (old fresh : RootRecords ρ ι) (depth oldBottom newBottom : α)
    (oldPacket incomingPacket : List (Logical ρ ι)) :
    exchangeRoot old fresh
      (some ⟨.leaf oldBottom (owned none old.oldHigh ++ oldPacket),[]⟩)
      (some ⟨.fork [old.incomingHigh] (.leaf depth [old.incomingTerminal]) (.leaf newBottom incomingPacket),[]⟩) =
      some (some ⟨.leaf newBottom (owned none fresh.incomingHigh ++ incomingPacket),[]⟩,
        some ⟨.fork [fresh.oldHigh] (.leaf depth [fresh.oldTerminal]) (.leaf oldBottom oldPacket),[]⟩) := by
  simp only [exchangeRoot,List.drop_left]

theorem owner_virtual (color : α → Option Bool) (left right : Source α (Logical ρ ι))
    (leftVirtual : none ∈ left.support color) (rightVirtual : none ∈ right.support color) :
    owner color left right = none := by
  have member : none ∈ left.support color ∩ right.support color := Finset.mem_inter.mpr ⟨leftVirtual,rightVirtual⟩
  have nonempty : (left.support color ∩ right.support color).Nonempty := ⟨none,member⟩
  rw [owner,dif_pos nonempty]
  apply le_antisymm
  · exact Finset.min'_le _ _ member
  · exact (show (⊥ : WithBot Bool) ≤ _ from bot_le)

theorem active_packing (color : α → Option Bool) (low high terminal : Logical ρ ι)
    (depth bottom : α) (direction : Bool) (headPart tail : Source α (Logical ρ ι))
    (lowLeft lowRight highLeft highRight : Child ι (Option Bool))
    (lowChildren : low.2.children = some (lowLeft,lowRight))
    (highChildren : high.2.children = some (highLeft,highRight))
    (lowLeftMask : lowLeft.colors = headPart.support color)
    (lowRightMask : lowRight.colors = (Source.fork high (.leaf depth terminal) tail).support color)
    (highLeftMask : highLeft.colors = (Source.leaf depth terminal).support color)
    (highRightMask : highRight.colors = tail.support color)
    (boundary : color depth = some direction)
    (absent : packed color none headPart = none) (tailPacket : List (Logical ρ ι))
    (tailPacked : packed color none tail = some (.leaf bottom tailPacket)) :
    packed color none (.fork low headPart (.fork high (.leaf depth terminal) tail)) =
      some (.leaf bottom (prefixes low high ++ tailPacket)) := by
  rw [fork_packing color none low headPart _ lowLeft lowRight lowChildren lowLeftMask lowRightMask,
    fork_packing color none high (.leaf depth terminal) tail highLeft highRight highChildren highLeftMask highRightMask]
  have leafPacked : packed color none (.leaf depth terminal) = none := by
    simp only [packed,pack,boundary,reduceCtorEq,if_false,Stored.toSource]
  rw [absent,leafPacked,tailPacked]
  simp only [join,
    decorate,Option.map_some,Source.setRoot,Source.rootRecord,prefixes,List.append_assoc]

theorem dormant_packing [DecidableEq α] (color : α → Option Bool) (high terminal : Logical ρ ι)
    (depth bottom : α) (tail : Source α (Logical ρ ι))
    (boundary : color depth = none) (tailPacket : List (Logical ρ ι))
    (tailPacked : packed color none tail = some (.leaf bottom tailPacket)) :
    packed color none (.fork high (.leaf depth terminal) tail) =
      some (.fork [high] (.leaf depth [terminal]) (.leaf bottom tailPacket)) := by
  have tailVirtual : none ∈ tail.support color := by
    have present := PackedRotationController.packed_isSome color none tail
    rw [tailPacked] at present
    exact of_decide_eq_true present.symm
  have owns := owner_virtual color (.leaf depth terminal) tail (by simp only [Source.support,boundary,Finset.mem_singleton]) tailVirtual
  rw [packed_fork]
  have leafPacked : packed color none (.leaf depth terminal) = some (.leaf depth [terminal]) := by
    simp only [packed,pack,boundary,if_true,Stored.toSource]
  rw [leafPacked,tailPacked]
  simp only [owns,decide_true,
    join,attach,Option.map_some,Source.setRoot,Source.rootRecord,if_true]

theorem root_active_packing (color : α → Option Bool) (high terminal : Logical ρ ι)
    (depth bottom : α) (direction : Bool) (tail : Source α (Logical ρ ι))
    (leftChild rightChild : Child ι (Option Bool))
    (children : high.2.children = some (leftChild,rightChild))
    (leftMask : leftChild.colors = (Source.leaf depth terminal).support color)
    (rightMask : rightChild.colors = tail.support color)
    (boundary : color depth = some direction) (tailPacket : List (Logical ρ ι))
    (tailPacked : packed color none tail = some (.leaf bottom tailPacket)) :
    packed color none (.fork high (.leaf depth terminal) tail) =
      some (.leaf bottom (owned none high ++ tailPacket)) := by
  rw [fork_packing color none high (.leaf depth terminal) tail leftChild rightChild children leftMask rightMask]
  have leafPacked : packed color none (.leaf depth terminal) = none := by
    simp only [packed,pack,boundary,reduceCtorEq,if_false,Stored.toSource]
  rw [leafPacked,tailPacked]
  rfl

end ChaCha.Paper20261030.VirtualHeadPackets
