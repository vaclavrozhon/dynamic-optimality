import TaggedPreparation
import OrderedJunctionTransfer

/-! Whole-block transfers preserve the actual entry/base relation globally.
The movement can affect arbitrarily many members; no per-member payment
or numerical variation bound is used here. -/

namespace GreedyMerge.StateLabels

open OrderedBlocks Primitives BlockCoverage
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

theorem frozenTagged_filter_cover (predicate : Frozen → Bool) (blocks : List Frozen)
    (item : Entry × ℕ) :
    (item ∈ frozenTagged (blocks.filter predicate) ∨
      item ∈ frozenTagged (blocks.filter (fun block => !predicate block))) ↔
        item ∈ frozenTagged blocks := by
  simp only [frozenTagged, List.mem_flatMap, List.mem_filter]
  constructor
  · rintro (⟨block, ⟨member, _⟩, present⟩ | ⟨block, ⟨member, _⟩, present⟩) <;>
      exact ⟨block, member, present⟩
  · rintro ⟨block, member, present⟩
    cases selected : predicate block with
    | true => exact Or.inl ⟨block, ⟨member, selected⟩, present⟩
    | false => exact Or.inr ⟨block, ⟨member, by simp [selected]⟩, present⟩

theorem separateOuter_tagged_cover (side : Bool) (cut fresh : ℕ) (state : SideState)
    (item : Entry × ℕ) :
    (item ∈ frozenTagged (separateOuter side cut fresh state).1 ∨
      item ∈ frozenTagged (separateOuter side cut fresh state).2) ↔
        item ∈ frozenTagged state.shrinking := by
  unfold separateOuter
  rw [frozenTagged_filter_cover, frozenTagged_cutList]

theorem moveOuter_tagged_cover (side : Bool) (cut fresh sourceRank receiverRank : ℕ)
    (source receiver : SideState) (item : Entry × ℕ) :
    (item ∈ tagged sourceRank (moveOuter side cut fresh source receiver).1 ∨
      item ∈ tagged receiverRank (moveOuter side cut fresh source receiver).2) ↔
    (item ∈ tagged sourceRank source ∨ item ∈ tagged receiverRank receiver) := by
  have partition := separateOuter_tagged_cover side cut fresh source item
  simp only [moveOuter, transfer, tagged_eq, frozenTagged_append, List.mem_append]
  tauto

theorem moveJunction_hasBase {n : ℕ} (rank : ℕ → ℕ)
    (oldOwner newOwner : External n) (lo hi : ℕ) (fresh : Bool → ℕ)
    (states : States n) (different : oldOwner ≠ newOwner) (key base : ℕ) :
    HasBase rank (moveJunction oldOwner newOwner lo hi fresh states) key base ↔
      HasBase rank states key base := by
  constructor
  · rintro ⟨owner, side, entry, member, equal⟩
    by_cases old : owner = oldOwner
    · subst owner
      have localMem : (entry, base) ∈ tagged (rank oldOwner.val)
          (moveOuter side (junctionCut side lo hi) (fresh side)
            (states oldOwner side) (states newOwner side)).1 := by
        simpa [moveJunction] using member
      rcases (moveOuter_tagged_cover side (junctionCut side lo hi) (fresh side)
        (rank oldOwner.val) (rank newOwner.val) _ _ (entry, base)).mp (Or.inl localMem) with first | second
      · exact ⟨oldOwner, side, entry, first, equal⟩
      · exact ⟨newOwner, side, entry, second, equal⟩
    · by_cases new : owner = newOwner
      · subst owner
        have localMem : (entry, base) ∈ tagged (rank newOwner.val)
            (moveOuter side (junctionCut side lo hi) (fresh side)
              (states oldOwner side) (states newOwner side)).2 := by
          simpa [moveJunction, different.symm] using member
        rcases (moveOuter_tagged_cover side (junctionCut side lo hi) (fresh side)
          (rank oldOwner.val) (rank newOwner.val) _ _ (entry, base)).mp (Or.inr localMem) with first | second
        · exact ⟨oldOwner, side, entry, first, equal⟩
        · exact ⟨newOwner, side, entry, second, equal⟩
      · exact ⟨owner, side, entry, by simpa [moveJunction, old, new] using member, equal⟩
  · rintro ⟨owner, side, entry, member, equal⟩
    have install (side : Bool)
        (localMem : (entry, base) ∈ tagged (rank oldOwner.val)
            (moveOuter side (junctionCut side lo hi) (fresh side)
              (states oldOwner side) (states newOwner side)).1 ∨
          (entry, base) ∈ tagged (rank newOwner.val)
            (moveOuter side (junctionCut side lo hi) (fresh side)
              (states oldOwner side) (states newOwner side)).2) :
        HasBase rank (moveJunction oldOwner newOwner lo hi fresh states) key base := by
      rcases localMem with first | second
      · exact ⟨oldOwner, side, entry, by simpa [moveJunction] using first, equal⟩
      · exact ⟨newOwner, side, entry, by simpa [moveJunction, different.symm] using second, equal⟩
    by_cases old : owner = oldOwner
    · subst owner
      apply install side
      exact (moveOuter_tagged_cover side (junctionCut side lo hi) (fresh side)
        (rank oldOwner.val) (rank newOwner.val) _ _ (entry, base)).mpr (Or.inl member)
    · by_cases new : owner = newOwner
      · subst owner
        apply install side
        exact (moveOuter_tagged_cover side (junctionCut side lo hi) (fresh side)
          (rank oldOwner.val) (rank newOwner.val) _ _ (entry, base)).mpr (Or.inr member)
      · exact ⟨owner, side, entry, by simpa [moveJunction, old, new] using member, equal⟩

theorem label_congr {n : ℕ} (rank : ℕ → ℕ) (K : ℤ) (first second : States n) (key : ℕ)
    (same : ∀ base, HasBase rank first key base ↔ HasBase rank second key base) :
    label rank K first key = label rank K second key := by
  classical
  have equal : HasBase rank first key = HasBase rank second key :=
    funext (fun base => propext (same base))
  let lookup (predicate : ℕ → Prop) : ℤ :=
    if present : ∃ base, predicate base then
      (Splay.Analysis.contractedGap (rank key - present.choose) : ℤ) else K
  change lookup (HasBase rank first key) = lookup (HasBase rank second key)
  rw [equal]

theorem moveJunction_label {n : ℕ} (rank : ℕ → ℕ) (K : ℤ)
    (oldOwner newOwner : External n) (lo hi : ℕ) (fresh : Bool → ℕ)
    (states : States n) (different : oldOwner ≠ newOwner) (key : ℕ) :
    label rank K (moveJunction oldOwner newOwner lo hi fresh states) key = label rank K states key :=
  label_congr rank K _ _ key (moveJunction_hasBase rank oldOwner newOwner lo hi fresh states different key)

theorem prepareComparator_label {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (families ids : NameSupply n)
    (ports : List ℕ) (bulkOwners : Finset (External n)) (states : HeapSides n)
    (K : ℤ) (key : ℕ) (outside : key ∉ ports) :
    label before.externalDepth K (prepareComparator profile families ids ports bulkOwners states).1 key =
      label before.externalDepth K states key := by
  apply label_congr
  intro base
  simpa only [outside, not_false_eq_true, and_true] using
    prepareComparator_hasBase profile families ids ports bulkOwners states key base

end GreedyMerge.StateLabels

#print axioms GreedyMerge.StateLabels.moveJunction_label
#print axioms GreedyMerge.StateLabels.prepareComparator_label
