import OrderedJunctionTransfer
import NatBaseTransport
import AdministrationTimeline

/-!
The numerical invariant omitted by history-only Descends: every frozen
absolute base stays below every old member rank through preparation and
bulk movement. Conversion uses the actual old parent's rank. This permits
atomic uniform-shift rebase before paid port restoration.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open Splay.Analysis

def UpperBlocks (rank : ℕ → ℕ) (blocks : List Frozen) : Prop :=
  ∀ block ∈ blocks, ∀ entry ∈ block.members, block.base ≤ rank entry.key

def UpperBase (rank : ℕ → ℕ) (state : SideState) : Prop :=
  UpperBlocks rank state.shrinking

theorem parentSound_rank_floor {n : ℕ} (before tree : BST 0 n) (owner : External n)
    (state : SideState) (sound : ParentSound (Snapshot.ofTree before) tree owner state)
    (entry : Entry) (member : entry ∈ entries state) :
    before.externalDepth owner.val ≤ before.externalDepth entry.key := by
  obtain ⟨record,hkey,hparent⟩ := sound entry member
  have h := rank_canonicalParent_lt (Snapshot.ofTree before) tree hparent
  change before.externalDepth owner.val < before.externalDepth record.val at h
  rw [hkey] at h
  exact Nat.le_of_lt h

theorem convert_upperBase (rank : ℕ → ℕ) (owner family id base : ℕ) (state : SideState)
    (upper : UpperBase rank state)
    (growerFloor : ∀ entry ∈ growerEntries state.grower, base ≤ rank entry.key) :
    UpperBase rank (convert owner family id base state) := by
  cases hg : state.grower with
  | none => simpa [convert,hg] using upper
  | some grower =>
      by_cases hempty : grower.members=[]
      · simpa [convert,hg,hempty] using upper
      · intro block member entry entryMem
        have hm : block ∈ state.shrinking ∨ block=freeze grower.id base grower := by
          simpa [convert,hg,hempty] using member
        rcases hm with hm | rfl
        · exact upper block hm entry entryMem
        · exact growerFloor entry (by simpa [growerEntries,hg,freeze] using entryMem)

theorem convert_old_rank_upperBase {n : ℕ} (before tree : BST 0 n) (owner : External n)
    (family id : ℕ) (state : SideState)
    (upper : UpperBase before.externalDepth state)
    (sound : ParentSound (Snapshot.ofTree before) tree owner state) :
    UpperBase before.externalDepth
      (convert owner.val family id (before.externalDepth owner.val) state) := by
  apply convert_upperBase before.externalDepth owner.val family id _ state upper
  intro entry member
  exact parentSound_rank_floor before tree owner state sound entry (List.mem_append_right _ member)

theorem cutBlock_same_base (side : Bool) (cut leftId rightId : ℕ) (block : Frozen)
    (piece : Frozen) (member : piece ∈ cutBlock side cut leftId rightId block) :
    piece.base=block.base := by
  classical
  unfold cutBlock at member
  split_ifs at member
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> rfl
  · have heq : piece=block := by simpa using member
    rw [heq]

theorem cutList_upperBlocks (rank : ℕ → ℕ) (side : Bool) (cut fresh : ℕ)
    (blocks : List Frozen) (upper : UpperBlocks rank blocks) :
    UpperBlocks rank (cutList side cut fresh blocks) := by
  induction blocks generalizing fresh with
  | nil => simp [UpperBlocks,cutList]
  | cons block rest ih =>
      intro piece member entry entryMem
      rcases List.mem_append.mp member with hhead | htail
      · have desc := cutBlock_descends side cut fresh (fresh+1) block piece hhead
        rw [cutBlock_same_base side cut fresh (fresh+1) block piece hhead]
        exact upper block (by simp) entry (desc.2.2.subset entryMem)
      · exact ih (fresh+2) (fun old hold => upper old (by simp [hold])) piece htail entry entryMem

theorem cutState_upperBase (rank : ℕ → ℕ) (side : Bool) (cut fresh : ℕ)
    (state : SideState) (upper : UpperBase rank state) :
    UpperBase rank (cutState side cut fresh state) :=
  cutList_upperBlocks rank side cut fresh state.shrinking upper

theorem prepareCuts_upperBase {n : ℕ} (rank : ℕ → ℕ) (allocate : NameSupply n)
    (cuts : List (ℕ × ℕ)) (stage : ℕ) (states : HeapSides n)
    (upper : ∀ owner side, UpperBase rank (states owner side)) :
    ∀ owner side, UpperBase rank ((prepareCuts allocate cuts stage states).1 owner side) := by
  induction cuts generalizing stage states with
  | nil => exact upper
  | cons entry rest ih =>
      apply ih
      intro owner side
      exact cutState_upperBase rank side entry.1 (allocate stage owner side) _ (upper owner side)

theorem prepareGrower_upperBase {n : ℕ} (before after tree : BST 0 n) (owner : External n)
    (family id : ℕ) (state : SideState) (upper : UpperBase before.externalDepth state)
    (sound : ParentSound (Snapshot.ofTree before) tree owner state) :
    UpperBase before.externalDepth (prepareGrower before after owner family id state) := by
  unfold prepareGrower
  split_ifs
  · exact convert_old_rank_upperBase before tree owner family id state upper sound
  · exact upper

theorem eraseFrozenKey_upperBase (rank : ℕ → ℕ) (key : ℕ) (state : SideState)
    (upper : UpperBase rank state) : UpperBase rank (eraseFrozenKey key state) := by
  intro block member entry entryMem
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp member
  exact upper old hold entry (List.mem_filter.mp entryMem).1

theorem detachPort_old_upperBase {n : ℕ} (before tree : BST 0 n) (owner : External n)
    (family id key : ℕ) (state : SideState) (upper : UpperBase before.externalDepth state)
    (sound : ParentSound (Snapshot.ofTree before) tree owner state) :
    UpperBase before.externalDepth
      (detachPort owner.val family id (before.externalDepth owner.val) key state) := by
  apply eraseFrozenKey_upperBase
  unfold sealPortSource
  split_ifs
  · exact convert_old_rank_upperBase before tree owner family id state upper sound
  · exact upper

theorem detachPorts_upperBase {n : ℕ} (before tree : BST 0 n) (families ids : NameSupply n)
    (ports : List ℕ) (stage : ℕ) (states : HeapSides n)
    (upper : ∀ owner side, UpperBase before.externalDepth (states owner side))
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner (states owner side)) :
    ∀ owner side, UpperBase before.externalDepth
      ((detachPorts before families ids ports stage states).1 owner side) := by
  induction ports generalizing stage states with
  | nil => exact upper
  | cons key rest ih =>
      apply ih (stage+1) (detachAll before key (families stage) (ids stage) states)
      · intro owner side
        exact detachPort_old_upperBase before tree owner _ _ key _ (upper owner side) (sound owner side)
      · exact detachAll_sound before tree key _ _ states sound

theorem sealOwners_upperBase {n : ℕ} (before tree : BST 0 n) (owners : Finset (External n))
    (families ids : External n → Bool → ℕ) (states : HeapSides n)
    (upper : ∀ owner side, UpperBase before.externalDepth (states owner side))
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner (states owner side)) :
    ∀ owner side, UpperBase before.externalDepth
      (sealOwners before owners families ids states owner side) := by
  intro owner side
  unfold sealOwners
  split_ifs
  · exact convert_old_rank_upperBase before tree owner _ _ _ (upper owner side) (sound owner side)
  · exact upper owner side

/-- The numerical upper-base invariant survives the complete executed
comparator preparation, including all selected grower conversions. -/
theorem prepareComparator_upperBase {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (families ids : NameSupply n) (ports : List ℕ) (bulkOwners : Finset (External n))
    (states : HeapSides n)
    (upper : ∀ owner side, UpperBase before.externalDepth (states owner side))
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner (states owner side)) :
    ∀ owner side, UpperBase before.externalDepth
      ((prepareComparator profile families ids ports bulkOwners states).1 owner side) := by
  apply prepareCuts_upperBase
  apply sealOwners_upperBase before tree
  · apply detachPorts_upperBase before tree
    · intro owner side
      exact prepareGrower_upperBase before after tree owner _ _ _ (upper owner side) (sound owner side)
    · exact prepareAllGrowers_sound before after tree _ _ states sound
  · apply detachPorts_sound before tree
    exact prepareAllGrowers_sound before after tree _ _ states sound

theorem moveOuter_upperBase (rank : ℕ → ℕ) (side : Bool) (cut fresh : ℕ)
    (source receiver : SideState) (hs : UpperBase rank source) (hr : UpperBase rank receiver) :
    UpperBase rank (moveOuter side cut fresh source receiver).1 ∧
      UpperBase rank (moveOuter side cut fresh source receiver).2 := by
  have hp := cutList_upperBlocks rank side cut fresh source.shrinking hs
  constructor
  · intro block member
    exact hp block (List.mem_filter.mp member).1
  · intro block member
    rcases List.mem_append.mp member with hold | hmoved
    · exact hr block hold
    · exact hp block (List.mem_filter.mp hmoved).1

theorem moveJunction_upperBase {n : ℕ} (rank : ℕ → ℕ)
    (oldOwner newOwner : External n) (lo hi : ℕ) (fresh : Bool → ℕ) (states : HeapSides n)
    (upper : ∀ owner side, UpperBase rank (states owner side)) :
    ∀ owner side, UpperBase rank (moveJunction oldOwner newOwner lo hi fresh states owner side) := by
  intro owner side
  have hm := moveOuter_upperBase rank side (junctionCut side lo hi) (fresh side)
    (states oldOwner side) (states newOwner side) (upper oldOwner side) (upper newOwner side)
  unfold moveJunction
  split_ifs
  · exact hm.1
  · exact hm.2
  · exact upper owner side

end GreedyMerge.OrderedBlocks

#print axioms GreedyMerge.OrderedBlocks.prepareComparator_upperBase
#print axioms GreedyMerge.OrderedBlocks.moveJunction_upperBase
