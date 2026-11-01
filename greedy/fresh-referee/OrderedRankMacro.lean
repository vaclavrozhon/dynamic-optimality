import OrderedIdSupport
import OrderedGrowerUniformity

/-!
The comparator branch with unchanged canonical parents. Actual rank-mismatch
growers are sealed, actual rank boundaries are cut, and every block is
rebased by its actual uniform signed rank shift. No port is detached.
The structural parent-equality hypothesis is discharged by the no-junction
case of the separate literal-fork dichotomy.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.BlockCoverage (Sound Complete)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

noncomputable def administerRankOnly {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (families ids : NameSupply n)
    (states : HeapSides n) : HeapSides n × ℕ :=
  let prepared := prepareComparator profile families ids [] ∅ states
  (rebaseAll before after prepared.1,prepared.2)

theorem administerRankOnly_spec {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (parentPreserved : ∀ record, canonicalParent (Snapshot.ofTree after) tree record =
      canonicalParent (Snapshot.ofTree before) tree record)
    (families ids : NameSupply n) (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound (Snapshot.ofTree before) tree states)
    (complete : Complete (Snapshot.ofTree before) tree states)
    (persistent : PersistentGrowers states) :
    let result := administerRankOnly profile families ids states
    (∀ owner side, Valid owner.val side (result.1 owner side)) ∧
    Sound (Snapshot.ofTree after) tree result.1 ∧
    Complete (Snapshot.ofTree after) tree result.1 ∧
    PersistentGrowers result.1 ∧ result.2 ≤ 4*(depth+2)^2 := by
  let prepared := prepareComparator profile families ids [] ∅ states
  have preparedValid := prepareComparator_valid profile families ids [] ∅ states valid
  have sameMembers : ∀ owner side entry,
      entry ∈ entries (prepared.1 owner side) ↔ entry ∈ entries (states owner side) := by
    intro owner side entry
    simpa using prepareComparator_membership profile families ids [] ∅ states owner side entry
  have preparedSound : Sound (Snapshot.ofTree after) tree prepared.1 := by
    intro owner side entry member
    obtain ⟨record,equal,parent⟩ := sound owner side entry ((sameMembers owner side entry).mp member)
    exact ⟨record,equal,by rw [parentPreserved,parent]⟩
  refine ⟨rebaseAll_valid before after prepared.1 preparedValid,
    rebaseAll_sound before after tree prepared.1 preparedSound,?_,?_,?_⟩
  · intro record owner parent _
    rw [parentPreserved] at parent
    obtain ⟨side,entry,member,equal⟩ := complete record owner parent (by simp)
    refine ⟨side,entry,?_,equal⟩
    change entry ∈ entries (rebaseAll before after prepared.1 owner side)
    rw [rebaseAll_entries]
    exact (sameMembers owner side entry).mpr member
  · intro owner side
    change (rebaseAll before after prepared.1 owner side).grower.isSome=true
    rw [rebaseAll_grower,prepareComparator_grower_isSome]
    exact persistent owner side
  · simpa [administerRankOnly] using prepareComparator_births_le profile tree families ids [] ∅ states valid sound

theorem administerRankOnly_bases {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (parentPreserved : ∀ record, canonicalParent (Snapshot.ofTree after) tree record =
      canonicalParent (Snapshot.ofTree before) tree record)
    (families ids : NameSupply n) (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound (Snapshot.ofTree before) tree states)
    (upper : ∀ owner side, UpperBase before.externalDepth (states owner side)) :
    ∀ owner side, ∀ block ∈ ((administerRankOnly profile families ids states).1 owner side).shrinking,
      BaseValid after.externalDepth owner.val block := by
  have oldSound := prepareComparator_sound profile tree families ids [] ∅ states sound
  have newSound : ∀ owner side, ParentSound (Snapshot.ofTree after) tree owner
      ((prepareComparator profile families ids [] ∅ states).1 owner side) := by
    intro owner side entry member
    obtain ⟨record,equal,parent⟩ := oldSound owner side entry member
    exact ⟨record,equal,by rw [parentPreserved,parent]⟩
  exact (rebaseAll_numeric before after tree _
    (prepareComparator_upperBase profile tree families ids [] ∅ states upper sound) newSound
    (prepareComparator_uniform profile families ids [] ∅ states valid)).1

theorem administerRankOnly_id_support {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (families ids : NameSupply n) (states : HeapSides n) :
    SupportsIds states (administerRankOnly profile families ids states).1
      (prepareComparatorIds profile families ids [] ∅ states) := by
  have support := supportsIds_trans (prepareComparator_id_support profile families ids [] ∅ states)
    (rebaseAll_id_support before after _)
  simpa only [List.append_nil,administerRankOnly] using support

#print axioms administerRankOnly_spec
#print axioms administerRankOnly_bases
#print axioms administerRankOnly_id_support

end GreedyMerge.OrderedBlocks
