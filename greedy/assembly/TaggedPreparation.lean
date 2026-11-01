import StateLabels
import OrderedComparatorPreparation

/-!
Preparation preserves actual entry/base pairs, except that paid ports
are detached. This is the literal bridge from spatial state changes to
the global label lookup, including grower conversions at the old rank.
-/

namespace GreedyMerge.StateLabels

open OrderedBlocks Primitives BlockCoverage
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

def frozenTagged (blocks : List Frozen) : List (Entry × ℕ) :=
  blocks.flatMap (fun block => block.members.map (fun entry => (entry, block.base)))

theorem tagged_eq (ownerRank : ℕ) (state : SideState) :
    tagged ownerRank state = frozenTagged state.shrinking ++
      (growerEntries state.grower).map (fun entry => (entry, ownerRank)) := rfl

@[simp] theorem frozenTagged_append (first second : List Frozen) :
    frozenTagged (first ++ second) = frozenTagged first ++ frozenTagged second := by
  simp [frozenTagged]

theorem tagged_convert (owner family id ownerRank : ℕ) (state : SideState) :
    tagged ownerRank (convert owner family id ownerRank state) = tagged ownerRank state := by
  cases grower : state.grower with
  | none => simp [convert, grower]
  | some old =>
      by_cases empty : old.members = []
      · simp [convert, grower, empty]
      · simp [convert, grower, empty, tagged, freeze, emptyGrower, growerEntries]

theorem frozenTagged_cutBlock (side : Bool) (cut leftId rightId : ℕ) (block : Frozen) :
    frozenTagged (cutBlock side cut leftId rightId block) =
      block.members.map (fun entry => (entry, block.base)) := by
  classical
  unfold cutBlock
  split_ifs <;> simp [frozenTagged, ← List.map_append]

theorem frozenTagged_cutList (side : Bool) (cut fresh : ℕ) (blocks : List Frozen) :
    frozenTagged (cutList side cut fresh blocks) = frozenTagged blocks := by
  induction blocks generalizing fresh with
  | nil => rfl
  | cons block rest ih =>
      simp only [cutList, frozenTagged_append, frozenTagged_cutBlock, ih]
      rfl

theorem tagged_cutState (ownerRank : ℕ) (side : Bool) (cut fresh : ℕ) (state : SideState) :
    tagged ownerRank (cutState side cut fresh state) = tagged ownerRank state := by
  change frozenTagged (cutList side cut fresh state.shrinking) ++ _ = frozenTagged state.shrinking ++ _
  rw [frozenTagged_cutList]
  rfl

theorem tagged_prepareGrower {n : ℕ} (before after : BST 0 n) (owner : External n)
    (family id : ℕ) (state : SideState) :
    tagged (before.externalDepth owner.val) (prepareGrower before after owner family id state) =
      tagged (before.externalDepth owner.val) state := by
  unfold prepareGrower
  split_ifs
  · exact tagged_convert ..
  · rfl

theorem frozenTagged_erase (key : ℕ) (blocks : List Frozen) :
    frozenTagged (blocks.map (eraseMember key)) =
      (frozenTagged blocks).filter (fun item => item.1.key != key) := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      simp only [List.map_cons, frozenTagged, List.flatMap_cons, List.filter_append]
      change _ ++ frozenTagged (rest.map (eraseMember key)) =
        _ ++ (frozenTagged rest).filter (fun item => item.1.key != key)
      rw [ih]
      congr 1
      simp [eraseMember, List.filter_map, Function.comp_def]

theorem tagged_sealPortSource (owner family id ownerRank key : ℕ) (state : SideState) :
    tagged ownerRank (sealPortSource owner family id ownerRank key state) = tagged ownerRank state := by
  unfold sealPortSource
  split_ifs
  · exact tagged_convert ..
  · rfl

theorem tagged_detachPort (owner family id ownerRank key : ℕ) (state : SideState) :
    tagged ownerRank (detachPort owner family id ownerRank key state) =
      (tagged ownerRank state).filter (fun item => item.1.key != key) := by
  let sealed := sealPortSource owner family id ownerRank key state
  have growing : ((growerEntries sealed.grower).map (fun entry => (entry, ownerRank))).filter
      (fun item => item.1.key != key) =
        (growerEntries sealed.grower).map (fun entry => (entry, ownerRank)) := by
    apply List.filter_eq_self.mpr
    intro item member
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    simpa only [bne_iff_ne] using sealPortSource_grower_absent owner family id ownerRank key state entry present
  change frozenTagged (sealed.shrinking.map (eraseMember key)) ++ _ = _
  rw [frozenTagged_erase]
  rw [← tagged_sealPortSource owner family id ownerRank key state]
  change _ = (frozenTagged sealed.shrinking ++ _).filter _
  rw [List.filter_append, growing]
  rfl

theorem tagged_detachPorts {n : ℕ} (before : BST 0 n) (families ids : NameSupply n)
    (ports : List ℕ) (stage : ℕ) (states : HeapSides n) (owner : External n) (side : Bool) :
    tagged (before.externalDepth owner.val)
      ((detachPorts before families ids ports stage states).1 owner side) =
    (tagged (before.externalDepth owner.val) (states owner side)).filter
      (fun item => decide (item.1.key ∉ ports)) := by
  induction ports generalizing stage states with
  | nil => simp [detachPorts]
  | cons key rest ih =>
      change tagged _ ((detachPorts before families ids rest (stage + 1)
        (detachAll before key (families stage) (ids stage) states)).1 owner side) = _
      rw [ih]
      unfold detachAll
      rw [tagged_detachPort, List.filter_filter]
      apply List.filter_congr
      intro item member
      apply Bool.eq_iff_iff.mpr
      simp [and_comm]

theorem tagged_sealOwners {n : ℕ} (before : BST 0 n) (owners : Finset (External n))
    (families ids : External n → Bool → ℕ) (states : HeapSides n)
    (owner : External n) (side : Bool) :
    tagged (before.externalDepth owner.val) (sealOwners before owners families ids states owner side) =
      tagged (before.externalDepth owner.val) (states owner side) := by
  unfold sealOwners
  split_ifs
  · exact tagged_convert ..
  · rfl

theorem tagged_prepareCuts {n : ℕ} (rank : ℕ → ℕ) (allocate : NameSupply n)
    (cuts : List (ℕ × ℕ)) (stage : ℕ) (states : HeapSides n) (owner : External n) (side : Bool) :
    tagged (rank owner.val) ((prepareCuts allocate cuts stage states).1 owner side) =
      tagged (rank owner.val) (states owner side) := by
  induction cuts generalizing stage states with
  | nil => rfl
  | cons entry rest ih =>
      change tagged _ ((prepareCuts allocate rest (stage + 1)
        (cutAllOwners entry.1 (allocate stage) states)).1 owner side) = _
      rw [ih]
      exact tagged_cutState ..

theorem tagged_prepareComparator {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (families ids : NameSupply n)
    (ports : List ℕ) (bulkOwners : Finset (External n)) (states : HeapSides n)
    (owner : External n) (side : Bool) :
    tagged (before.externalDepth owner.val)
      ((prepareComparator profile families ids ports bulkOwners states).1 owner side) =
      (tagged (before.externalDepth owner.val) (states owner side)).filter
        (fun item => decide (item.1.key ∉ ports)) := by
  unfold prepareComparator
  rw [tagged_prepareCuts, tagged_sealOwners, tagged_detachPorts]
  unfold prepareAllGrowers
  rw [tagged_prepareGrower]

theorem prepareComparator_hasBase {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (families ids : NameSupply n)
    (ports : List ℕ) (bulkOwners : Finset (External n)) (states : HeapSides n)
    (key base : ℕ) :
    HasBase before.externalDepth
      (prepareComparator profile families ids ports bulkOwners states).1 key base ↔
      HasBase before.externalDepth states key base ∧ key ∉ ports := by
  constructor
  · rintro ⟨owner, side, entry, member, equal⟩
    rw [tagged_prepareComparator] at member
    obtain ⟨present, outside⟩ := List.mem_filter.mp member
    exact ⟨⟨owner, side, entry, present, equal⟩, by simpa only [equal, decide_eq_true_eq] using outside⟩
  · rintro ⟨⟨owner, side, entry, member, equal⟩, outside⟩
    refine ⟨owner, side, entry, ?_, equal⟩
    rw [tagged_prepareComparator]
    exact List.mem_filter.mpr ⟨member, by simpa only [equal, decide_eq_true_eq] using outside⟩

end GreedyMerge.StateLabels

#print axioms GreedyMerge.StateLabels.tagged_prepareComparator
#print axioms GreedyMerge.StateLabels.prepareComparator_hasBase
