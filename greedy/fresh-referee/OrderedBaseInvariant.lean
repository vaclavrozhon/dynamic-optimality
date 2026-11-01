import OrderedRefinementMacro

/-!
Closure of the numerical absolute-base invariant through paid restoration.
Intermediate whole-block transfer is permitted to violate the lower owner
bound; concrete rebasing restores it before these fixed-rank primitives.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)
open GreedyMerge.BlockCoverage (Represented Sound)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

def BasesValid (rank : ℕ → ℕ) (owner : ℕ) (state : SideState) : Prop :=
  ∀ block ∈ state.shrinking, BaseValid rank owner block

theorem convert_bases (rank : ℕ → ℕ) (owner family id : ℕ) (state : SideState)
    (bases : BasesValid rank owner state)
    (floor : ∀ entry ∈ growerEntries state.grower, rank owner ≤ rank entry.key) :
    BasesValid rank owner (convert owner family id (rank owner) state) := by
  cases hg : state.grower with
  | none => simpa [convert,hg] using bases
  | some grower =>
      by_cases empty : grower.members=[]
      · simpa [convert,hg,empty] using bases
      · intro block member
        have choices : block ∈ state.shrinking ∨ block=freeze grower.id (rank owner) grower := by
          simpa [convert,hg,empty] using member
        rcases choices with old | rfl
        · exact bases block old
        · exact ⟨le_refl _,fun entry member => floor entry (by simpa [growerEntries,hg,freeze] using member)⟩

theorem cutList_bases (rank : ℕ → ℕ) (owner : ℕ) (side : Bool) (cut fresh : ℕ)
    (blocks : List Frozen) (bases : ∀ block ∈ blocks, BaseValid rank owner block) :
    ∀ block ∈ cutList side cut fresh blocks, BaseValid rank owner block := by
  induction blocks generalizing fresh with
  | nil => simp [cutList]
  | cons old rest ih =>
      intro block member
      rcases List.mem_append.mp member with head | tail
      · have inherited := cutBlock_descends side cut fresh (fresh+1) old block head
        have sameBase := cutBlock_same_base side cut fresh (fresh+1) old block head
        have oldBases := bases old (by simp)
        exact ⟨by simpa only [sameBase] using oldBases.1,
          fun entry entryMem => by rw [sameBase]; exact oldBases.2 entry (inherited.2.2.subset entryMem)⟩
      · exact ih (fresh+2) (fun block member => bases block (by simp [member])) block tail

theorem installPaid_bases (rank : ℕ → ℕ) (owner : ℕ) (side : Bool)
    (splitStart paidId paidFamily : ℕ) (entry : Entry) (state : SideState)
    (bases : BasesValid rank owner state) (entryFloor : rank owner ≤ rank entry.key) :
    BasesValid rank owner (installPaid owner side splitStart paidId paidFamily (rank owner) entry state) := by
  have pieces := cutList_bases rank owner side entry.key splitStart state.shrinking bases
  intro block member
  change block ∈ (separateOuter side entry.key splitStart state).1 ++
    [singleton paidId paidFamily owner (rank owner) entry] ++ (separateOuter side entry.key splitStart state).2 at member
  simp only [List.mem_append,List.mem_singleton] at member
  rcases member with (inside | paid) | outside
  · exact pieces block (List.mem_filter.mp inside).1
  · subst block
    exact ⟨le_refl _,by simpa [singleton] using entryFloor⟩
  · exact pieces block (List.mem_filter.mp outside).1

theorem paidInsertion_bases {n : ℕ} (comparator tree : BST 0 n) (owner : External n) (side : Bool)
    (replacementFamily replacementId splitStart paidId paidFamily : ℕ) (entry : Entry) (state : SideState)
    (bases : BasesValid comparator.externalDepth owner.val state)
    (sound : ParentSound (Snapshot.ofTree comparator) tree owner state)
    (entryFloor : comparator.externalDepth owner.val ≤ comparator.externalDepth entry.key) :
    BasesValid comparator.externalDepth owner.val
      (paidInsertion owner.val side replacementFamily replacementId splitStart paidId paidFamily
        (comparator.externalDepth owner.val) entry state) := by
  apply installPaid_bases comparator.externalDepth owner.val side splitStart paidId paidFamily entry _ _ entryFloor
  apply convert_bases comparator.externalDepth owner.val replacementFamily replacementId state bases
  intro entry member
  exact parentSound_rank_floor comparator tree owner state sound entry (List.mem_append_right _ member)

theorem restorePort_bases {n : ℕ} (comparator tree : BST 0 n)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n) (states : HeapSides n)
    (key : ∀ owner, (makeEntry owner).key=record.val)
    (bases : ∀ owner side, BasesValid comparator.externalDepth owner.val (states owner side))
    (sound : Sound (Snapshot.ofTree comparator) tree states) :
    ∀ owner side, BasesValid comparator.externalDepth owner.val
      ((restorePort (Snapshot.ofTree comparator) tree names makeEntry record states).1 owner side) := by
  intro owner side
  cases parent : canonicalParent (Snapshot.ofTree comparator) tree record with
  | none => simpa only [restorePort,parent] using bases owner side
  | some actualOwner =>
      simp only [restorePort,parent,replaceSide]
      split_ifs with place
      · obtain ⟨ownerEq,sideEq⟩ := place
        subst owner
        subst side
        apply paidInsertion_bases comparator tree actualOwner _ names.replacementFamily names.replacementId
          names.splitStart names.paidId names.paidFamily _ _ (bases actualOwner _) (sound actualOwner _)
        rw [key]
        exact Nat.le_of_lt (rank_canonicalParent_lt (Snapshot.ofTree comparator) tree parent)
      · exact bases owner side

theorem restorePorts_bases {n : ℕ} (comparator tree : BST 0 n)
    (names : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (key : ∀ stage record owner, (makeEntry stage record owner).key=record.val)
    (ports : List (External n)) (distinct : ports.Nodup) (stage : ℕ) (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound (Snapshot.ofTree comparator) tree states)
    (absent : ∀ record ∈ ports, ¬ Represented states record.val)
    (bases : ∀ owner side, BasesValid comparator.externalDepth owner.val (states owner side)) :
    ∀ owner side, BasesValid comparator.externalDepth owner.val
      ((restorePorts (Snapshot.ofTree comparator) tree names makeEntry ports stage states).1 owner side) := by
  induction ports generalizing stage states with
  | nil => exact bases
  | cons record rest ih =>
      let head := restorePort (Snapshot.ofTree comparator) tree (names stage) (makeEntry stage record) record states
      have headValid := restorePort_valid (Snapshot.ofTree comparator) tree (names stage) (makeEntry stage record)
        record states valid (key stage record) (absent record (by simp))
      have headSound := restorePort_sound (Snapshot.ofTree comparator) tree (names stage) (makeEntry stage record)
        record states valid sound (key stage record)
      have headBases := restorePort_bases comparator tree (names stage) (makeEntry stage record) record states
        (key stage record) bases sound
      have tailAbsent : ∀ other ∈ rest, ¬ Represented head.1 other.val := by
        intro other member represented
        rcases (restorePort_represented (Snapshot.ofTree comparator) tree (names stage) (makeEntry stage record)
          record states valid (key stage record) other.val).mp represented with old | ⟨sameKey,_⟩
        · exact absent other (by simp [member]) old
        · have same : other=record := Fin.ext sameKey
          exact (List.nodup_cons.mp distinct).1 (by simpa only [same] using member)
      exact ih (List.nodup_cons.mp distinct).2 (stage+1) head.1 headValid headSound tailAbsent headBases

theorem eraseFrozenKey_bases (rank : ℕ → ℕ) (owner key : ℕ) (state : SideState)
    (bases : BasesValid rank owner state) : BasesValid rank owner (eraseFrozenKey key state) := by
  intro block member
  obtain ⟨old,oldMem,rfl⟩ := List.mem_map.mp member
  exact ⟨(bases old oldMem).1,fun entry entryMem => (bases old oldMem).2 entry (List.mem_filter.mp entryMem).1⟩

theorem detachPort_bases {n : ℕ} (comparator tree : BST 0 n) (owner : External n)
    (family id key : ℕ) (state : SideState)
    (bases : BasesValid comparator.externalDepth owner.val state)
    (sound : ParentSound (Snapshot.ofTree comparator) tree owner state) :
    BasesValid comparator.externalDepth owner.val
      (detachPort owner.val family id (comparator.externalDepth owner.val) key state) := by
  apply eraseFrozenKey_bases
  unfold sealPortSource
  split_ifs
  · apply convert_bases _ _ _ _ _ bases
    intro entry member
    exact parentSound_rank_floor comparator tree owner state sound entry (List.mem_append_right _ member)
  · exact bases

theorem detachPorts_bases {n : ℕ} (comparator tree : BST 0 n) (families ids : NameSupply n)
    (ports : List ℕ) (stage : ℕ) (states : HeapSides n)
    (bases : ∀ owner side, BasesValid comparator.externalDepth owner.val (states owner side))
    (sound : Sound (Snapshot.ofTree comparator) tree states) :
    ∀ owner side, BasesValid comparator.externalDepth owner.val
      ((detachPorts comparator families ids ports stage states).1 owner side) := by
  induction ports generalizing stage states with
  | nil => exact bases
  | cons key rest ih =>
      apply ih (stage+1)
      · intro owner side
        exact detachPort_bases comparator tree owner _ _ key _ (bases owner side) (sound owner side)
      · exact detachAll_sound comparator tree key _ _ states sound

#print axioms paidInsertion_bases
#print axioms restorePorts_bases
#print axioms detachPorts_bases

end GreedyMerge.OrderedBlocks
