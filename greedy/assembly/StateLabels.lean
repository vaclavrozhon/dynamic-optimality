import HeapBlockCoverage
import Splay.Analysis.ContractedGap

/-!
Read the actual global contracted labels from the block state. Frozen
members use their stored absolute base; growing members use the actual
owner's rank. Strict spatial order and canonical parent soundness imply
that this lookup has a unique base. No separately supplied global label
function or bucket-consistency premise is needed for the definition.
-/

namespace GreedyMerge.StateLabels

open OrderedBlocks Primitives BlockCoverage
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis

def tagged (ownerRank : ℕ) (state : SideState) : List (Entry × ℕ) :=
  state.shrinking.flatMap (fun block => block.members.map (fun entry => (entry, block.base))) ++
    (growerEntries state.grower).map (fun entry => (entry, ownerRank))

theorem tagged_entries (ownerRank : ℕ) (state : SideState) :
    (tagged ownerRank state).map Prod.fst = entries state := by
  simp [tagged, entries, frozenEntries, List.map_flatMap, List.map_map, Function.comp_def]

theorem entries_key_nodup (owner : ℕ) (side : Bool) (state : SideState)
    (valid : Valid owner side state) : (entries state |>.map Entry.key).Nodup := by
  change ((entries state).map Entry.key).Pairwise (· ≠ ·)
  apply List.pairwise_map.mpr
  apply valid.1.imp
  intro first second ordered
  cases side <;> simp only [outward, Bool.false_eq_true, if_false, if_true] at ordered <;> omega

theorem tagged_key_nodup (ownerRank owner : ℕ) (side : Bool) (state : SideState)
    (valid : Valid owner side state) :
    ((tagged ownerRank state).map (fun item => item.1.key)).Nodup := by
  have result := entries_key_nodup owner side state valid
  rw [← tagged_entries ownerRank state, List.map_map] at result
  exact result

theorem tagged_member_entry (ownerRank : ℕ) (state : SideState) (entry : Entry) (base : ℕ)
    (member : (entry, base) ∈ tagged ownerRank state) : entry ∈ entries state := by
  rw [← tagged_entries ownerRank state]
  exact List.mem_map.mpr ⟨(entry, base), member, rfl⟩

theorem tagged_frozen (ownerRank : ℕ) (state : SideState) (block : Frozen)
    (blockMember : block ∈ state.shrinking) (entry : Entry) (member : entry ∈ block.members) :
    (entry, block.base) ∈ tagged ownerRank state := by
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨block, blockMember, List.mem_map.mpr ⟨entry, member, rfl⟩⟩

theorem tagged_growing (ownerRank : ℕ) (state : SideState) (entry : Entry)
    (member : entry ∈ growerEntries state.grower) :
    (entry, ownerRank) ∈ tagged ownerRank state :=
  List.mem_append_right _ (List.mem_map.mpr ⟨entry, member, rfl⟩)

def HasBase {n : ℕ} (rank : ℕ → ℕ) (states : States n) (key base : ℕ) : Prop :=
  ∃ owner side entry, (entry, base) ∈ tagged (rank owner.val) (states owner side) ∧ entry.key = key

theorem base_unique {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (rank : ℕ → ℕ) (states : States n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound snapshot tree states) (key first second : ℕ)
    (firstBase : HasBase rank states key first) (secondBase : HasBase rank states key second) :
    first = second := by
  obtain ⟨a, aSide, aEntry, aMember, aKey⟩ := firstBase
  obtain ⟨b, bSide, bEntry, bMember, bKey⟩ := secondBase
  have aPresent := tagged_member_entry _ _ _ _ aMember
  have bPresent := tagged_member_entry _ _ _ _ bMember
  obtain ⟨rfl, rfl⟩ := key_location_unique snapshot tree states valid sound
    aPresent bPresent (aKey.trans bKey.symm)
  have equal := List.inj_on_of_nodup_map
    (tagged_key_nodup (rank a.val) a.val aSide (states a aSide) (valid a aSide))
    aMember bMember (aKey.trans bKey.symm)
  exact congrArg Prod.snd equal

noncomputable def label {n : ℕ} (rank : ℕ → ℕ) (K : ℤ) (states : States n)
    (key : ℕ) : ℤ := by
  classical
  exact if present : ∃ base, HasBase rank states key base then
    (contractedGap (rank key - present.choose) : ℤ)
  else K

theorem label_of_base {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (rank : ℕ → ℕ) (K : ℤ) (states : States n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound snapshot tree states) (key base : ℕ)
    (hasBase : HasBase rank states key base) :
    label rank K states key = contractedGap (rank key - base) := by
  have present : ∃ base, HasBase rank states key base := ⟨base, hasBase⟩
  simp only [label, dif_pos present]
  rw [base_unique snapshot tree rank states valid sound key present.choose base
    present.choose_spec hasBase]

theorem label_of_frozen {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (rank : ℕ → ℕ) (K : ℤ) (states : States n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound snapshot tree states) (owner : External n) (side : Bool)
    (block : Frozen) (blockMember : block ∈ (states owner side).shrinking)
    (entry : Entry) (member : entry ∈ block.members) :
    label rank K states entry.key = contractedGap (rank entry.key - block.base) := by
  apply label_of_base snapshot tree rank K states valid sound
  exact ⟨owner, side, entry, tagged_frozen _ _ block blockMember entry member, rfl⟩

theorem label_of_growing {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (rank : ℕ → ℕ) (K : ℤ) (states : States n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound snapshot tree states) (owner : External n) (side : Bool)
    (entry : Entry) (member : entry ∈ growerEntries (states owner side).grower) :
    label rank K states entry.key = contractedGap (rank entry.key - rank owner.val) := by
  apply label_of_base snapshot tree rank K states valid sound
  exact ⟨owner, side, entry, tagged_growing _ _ entry member, rfl⟩

theorem root_label {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (rank : ℕ → ℕ) (K : ℤ) (states : States n) (sound : Sound snapshot tree states) :
    label rank K states (canonicalRoot snapshot tree).val = K := by
  unfold label
  apply dif_neg
  rintro ⟨base, owner, side, entry, member, key⟩
  obtain ⟨record, recordKey, parent⟩ := sound owner side entry
    (tagged_member_entry _ _ _ _ member)
  have equal : record = canonicalRoot snapshot tree := Fin.ext (recordKey.trans key)
  have none := (canonicalParent_eq_none_iff snapshot tree record).2 equal
  rw [parent] at none
  contradiction

/-- Bounds hold for the actual state-defined labels even during temporary
detachment: missing records receive the same bounded fallback label. -/
theorem label_bounded {n : ℕ} (rank : ℕ → ℕ) (H : ℕ) (states : States n)
    (record : External n) (cap : rank record.val ≤ H) :
    1 ≤ label rank (contractedGap H) states record.val ∧
      label rank (contractedGap H) states record.val ≤ contractedGap H := by
  unfold label
  split_ifs with present
  · have lower : 1 ≤ contractedGap (rank record.val - present.choose) := by
      unfold contractedGap
      omega
    have upper := contractedGap_mono ((Nat.sub_le (rank record.val) present.choose).trans cap)
    exact ⟨by exact_mod_cast lower, by exact_mod_cast upper⟩
  · constructor
    · have lower : 1 ≤ contractedGap H := by unfold contractedGap; omega
      exact_mod_cast lower
    · rfl

end GreedyMerge.StateLabels

#print axioms GreedyMerge.StateLabels.label_of_frozen
#print axioms GreedyMerge.StateLabels.label_of_growing
#print axioms GreedyMerge.StateLabels.label_bounded
