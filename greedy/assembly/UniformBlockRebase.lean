import BlockUpperBase
import OrderedBlockNumerics

/-!
Concrete atomic rebasing after the executed comparator preparation and
junction transfer. The first actual block member determines the signed
shift; there is no supplied numerical shift parameter or rebase output.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open Splay.Analysis

def UniformBlocks (shift : ℕ → ℤ) (state : SideState) : Prop :=
  ∀ block ∈ state.shrinking, ∀ first ∈ block.members, ∀ second ∈ block.members,
    shift first.key = shift second.key

theorem prepareComparator_uniform {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth)
    (families ids : NameSupply n) (ports : List ℕ) (bulkOwners : Finset (External n))
    (states : HeapSides n) (valid : ∀ owner side, Valid owner.val side (states owner side)) :
    ∀ owner side, UniformBlocks (rankShift before after)
      ((prepareComparator profile families ids ports bulkOwners states).1 owner side) := by
  intro owner side block member first firstMem second secondMem
  apply prepareProfile_uniform_shift profile ids (ports.length+2) _ _ owner side member firstMem secondMem
  apply sealOwners_valid
  apply detachPorts_valid
  exact prepareAllGrowers_valid before after _ _ states valid

theorem cutList_uniform (shift : ℕ → ℤ) (side : Bool) (cut fresh : ℕ)
    (state : SideState) (uniform : UniformBlocks shift state) :
    ∀ piece ∈ cutList side cut fresh state.shrinking,
      ∀ first ∈ piece.members, ∀ second ∈ piece.members, shift first.key=shift second.key := by
  intro piece member first firstMem second secondMem
  obtain ⟨old,oldMem,desc⟩ := cutList_descends side cut fresh state.shrinking piece member
  exact uniform old oldMem first (desc.2.2.subset firstMem) second (desc.2.2.subset secondMem)

theorem moveOuter_uniform (shift : ℕ → ℤ) (side : Bool) (cut fresh : ℕ)
    (source receiver : SideState) (hs : UniformBlocks shift source)
    (hr : UniformBlocks shift receiver) :
    UniformBlocks shift (moveOuter side cut fresh source receiver).1 ∧
      UniformBlocks shift (moveOuter side cut fresh source receiver).2 := by
  have hp := cutList_uniform shift side cut fresh source hs
  constructor
  · intro block member
    exact hp block (List.mem_filter.mp member).1
  · intro block member
    rcases List.mem_append.mp member with hold | hmoved
    · exact hr block hold
    · exact hp block (List.mem_filter.mp hmoved).1

theorem moveJunction_uniform {n : ℕ} (shift : ℕ → ℤ)
    (oldOwner newOwner : External n) (lo hi : ℕ) (fresh : Bool → ℕ) (states : HeapSides n)
    (uniform : ∀ owner side, UniformBlocks shift (states owner side)) :
    ∀ owner side, UniformBlocks shift (moveJunction oldOwner newOwner lo hi fresh states owner side) := by
  intro owner side
  have hm := moveOuter_uniform shift side (junctionCut side lo hi) (fresh side)
    (states oldOwner side) (states newOwner side) (uniform oldOwner side) (uniform newOwner side)
  unfold moveJunction
  split_ifs
  · exact hm.1
  · exact hm.2
  · exact uniform owner side

def blockShift (beforeRank afterRank : ℕ → ℕ) (block : Frozen) : ℤ :=
  match block.members with
  | [] => 0
  | entry :: _ => (afterRank entry.key : ℤ) - beforeRank entry.key

def rebaseFrozen (beforeRank afterRank : ℕ → ℕ) (owner : ℕ) (block : Frozen) : Frozen :=
  rebase (transportedBase block.base (afterRank owner) (blockShift beforeRank afterRank block)) block

def rebaseSide (beforeRank afterRank : ℕ → ℕ) (owner : ℕ) (state : SideState) : SideState :=
  ⟨state.shrinking.map (rebaseFrozen beforeRank afterRank owner),state.grower⟩

def rebaseAll {n : ℕ} (before after : BST 0 n) (states : HeapSides n) : HeapSides n :=
  fun owner side => rebaseSide before.externalDepth after.externalDepth owner.val (states owner side)

@[simp] theorem rebaseSide_entries (beforeRank afterRank : ℕ → ℕ) (owner : ℕ)
    (state : SideState) : entries (rebaseSide beforeRank afterRank owner state)=entries state := by
  simp [entries,frozenEntries,rebaseSide,List.flatMap_map,rebaseFrozen,rebase]

@[simp] theorem rebaseSide_grower (beforeRank afterRank : ℕ → ℕ) (owner : ℕ)
    (state : SideState) : (rebaseSide beforeRank afterRank owner state).grower=state.grower := rfl

@[simp] theorem rebaseAll_entries {n : ℕ} (before after : BST 0 n) (states : HeapSides n)
    (owner : External n) (side : Bool) :
    entries (rebaseAll before after states owner side)=entries (states owner side) :=
  rebaseSide_entries _ _ _ _

@[simp] theorem rebaseAll_grower {n : ℕ} (before after : BST 0 n) (states : HeapSides n)
    (owner : External n) (side : Bool) :
    (rebaseAll before after states owner side).grower=(states owner side).grower := rfl

theorem rebaseSide_valid (beforeRank afterRank : ℕ → ℕ) (owner : ℕ) (side : Bool)
    (state : SideState) (valid : Valid owner side state) :
    Valid owner side (rebaseSide beforeRank afterRank owner state) := by
  simpa only [Valid,rebaseSide_entries,rebaseSide_grower] using valid

theorem rebaseAll_valid {n : ℕ} (before after : BST 0 n) (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side)) :
    ∀ owner side, Valid owner.val side (rebaseAll before after states owner side) := by
  intro owner side
  exact rebaseSide_valid _ _ _ _ _ (valid owner side)

theorem rebaseAll_sound {n : ℕ} (before after tree : BST 0 n) (states : HeapSides n)
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree after) tree owner (states owner side)) :
    ∀ owner side, ParentSound (Snapshot.ofTree after) tree owner
      (rebaseAll before after states owner side) := by
  intro owner side entry member
  exact sound owner side entry (by simpa using member)

theorem blockShift_eq (beforeRank afterRank : ℕ → ℕ) (block : Frozen)
    (uniform : ∀ first ∈ block.members, ∀ second ∈ block.members,
      (afterRank first.key : ℤ)-beforeRank first.key = (afterRank second.key : ℤ)-beforeRank second.key)
    (entry : Entry) (member : entry ∈ block.members) :
    (afterRank entry.key : ℤ)-beforeRank entry.key = blockShift beforeRank afterRank block := by
  cases h : block.members with
  | nil => simp [h] at member
  | cons first rest =>
      simpa [blockShift,h] using (uniform first (by simp [h]) entry member).symm

/-- The constructed rebase has a valid new absolute base and decreases
all represented labels. The old base only needs its upper bound: the
owner may already have changed during the whole-block transfer. -/
theorem rebaseFrozen_numeric (beforeRank afterRank : ℕ → ℕ) (owner : ℕ) (block : Frozen)
    (oldUpper : ∀ entry ∈ block.members, block.base ≤ beforeRank entry.key)
    (newParent : ∀ entry ∈ block.members, afterRank owner ≤ afterRank entry.key)
    (uniform : ∀ first ∈ block.members, ∀ second ∈ block.members,
      (afterRank first.key : ℤ)-beforeRank first.key = (afterRank second.key : ℤ)-beforeRank second.key) :
    BaseValid afterRank owner (rebaseFrozen beforeRank afterRank owner block) ∧
      ∀ entry ∈ block.members,
        (contractedGap (afterRank entry.key - (rebaseFrozen beforeRank afterRank owner block).base) : ℤ) ≤
          contractedGap (beforeRank entry.key-block.base) := by
  have point := fun entry member => transportedBase_valid (beforeRank entry.key) (afterRank entry.key)
    block.base (afterRank owner) (blockShift beforeRank afterRank block)
    (oldUpper entry member) (newParent entry member)
    (by have h := blockShift_eq beforeRank afterRank block uniform entry member; omega)
  constructor
  · constructor
    · exact le_max_left _ _
    · intro entry member
      exact (point entry member).2.1
  · intro entry member
    exact_mod_cast contractedGap_mono (point entry member).2.2

/-- Whole-heap output bases are valid under the actual new comparator.
No numerical condition on the transfer's intermediate owner/base pair
is required. -/
theorem rebaseAll_numeric {n : ℕ} (before after tree : BST 0 n) (states : HeapSides n)
    (upper : ∀ owner side, UpperBase before.externalDepth (states owner side))
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree after) tree owner (states owner side))
    (uniform : ∀ owner side, UniformBlocks (rankShift before after) (states owner side)) :
    (∀ owner side, ∀ block ∈ (rebaseAll before after states owner side).shrinking,
      BaseValid after.externalDepth owner.val block) ∧
    (∀ owner side, ∀ block ∈ (states owner side).shrinking, ∀ entry ∈ block.members,
      (contractedGap (after.externalDepth entry.key -
        (rebaseFrozen before.externalDepth after.externalDepth owner.val block).base) : ℤ) ≤
      contractedGap (before.externalDepth entry.key-block.base)) := by
  have numeric := fun owner side block member => rebaseFrozen_numeric before.externalDepth after.externalDepth
    owner.val block (upper owner side block member)
    (fun entry entryMem => parentSound_rank_floor after tree owner _ (sound owner side) entry
      (List.mem_append_left _ (List.mem_flatMap.mpr ⟨block,member,entryMem⟩)))
    (uniform owner side block member)
  constructor
  · intro owner side block member
    obtain ⟨old,oldMem,rfl⟩ := List.mem_map.mp member
    exact (numeric owner side old oldMem).1
  · intro owner side block member
    exact (numeric owner side block member).2

end GreedyMerge.OrderedBlocks

#print axioms GreedyMerge.OrderedBlocks.prepareComparator_uniform
#print axioms GreedyMerge.OrderedBlocks.moveJunction_uniform
#print axioms GreedyMerge.OrderedBlocks.rebaseAll_numeric
#print axioms GreedyMerge.OrderedBlocks.rebaseAll_valid
#print axioms GreedyMerge.OrderedBlocks.rebaseAll_sound
