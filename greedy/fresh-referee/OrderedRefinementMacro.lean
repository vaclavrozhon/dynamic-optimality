import OrderedIdSupport
import RefinementRotationHeap

/-!
Concrete administration for bounded parent changes at a fixed comparator.
The selected actual records are detached from their old source blocks and
restored at their actual final parents. One actual refinement rotation
supplies at most four records through the checked geometric support theorem.
The conservative implementation therefore creates at most twenty instances.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)
open GreedyMerge.BlockCoverage (Represented Sound CompleteExcept Complete)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

noncomputable def reparentSelected {n : ℕ} (comparator afterTree : BST 0 n)
    (families ids : NameSupply n) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (ports : List (External n)) (states : HeapSides n) : HeapSides n × ℕ :=
  let detached := detachPorts comparator families ids (ports.map Fin.val) 0 states
  let restored := restorePorts (Snapshot.ofTree comparator) afterTree paidNames makeEntry ports 0 detached.1
  (restored.1,detached.2+restored.2)

noncomputable def reparentSelectedIds {n : ℕ} (comparator afterTree : BST 0 n)
    (families ids : NameSupply n) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (ports : List (External n)) (states : HeapSides n) : List ℕ :=
  detachPortsIds comparator families ids (ports.map Fin.val) 0 states ++
    restorePortsIds (Snapshot.ofTree comparator) afterTree paidNames makeEntry ports 0
      (detachPorts comparator families ids (ports.map Fin.val) 0 states).1

@[simp] theorem reparentSelectedIds_length {n : ℕ} (comparator afterTree : BST 0 n)
    (families ids : NameSupply n) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (ports : List (External n)) (states : HeapSides n) :
    (reparentSelectedIds comparator afterTree families ids paidNames makeEntry ports states).length =
      (reparentSelected comparator afterTree families ids paidNames makeEntry ports states).2 := by
  simp [reparentSelectedIds,reparentSelected]

theorem reparentSelected_id_support {n : ℕ} (comparator afterTree : BST 0 n)
    (families ids : NameSupply n) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (ports : List (External n)) (states : HeapSides n) :
    SupportsIds states (reparentSelected comparator afterTree families ids paidNames makeEntry ports states).1
      (reparentSelectedIds comparator afterTree families ids paidNames makeEntry ports states) := by
  exact supportsIds_trans (detachPorts_id_support comparator families ids (ports.map Fin.val) 0 states)
    (restorePorts_id_support (Snapshot.ofTree comparator) afterTree paidNames makeEntry ports 0 _)

theorem reparentSelected_spec {n : ℕ} (comparator beforeTree afterTree : BST 0 n)
    (families ids : NameSupply n) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (key : ∀ stage record owner, (makeEntry stage record owner).key = record.val)
    (ports : List (External n)) (distinct : ports.Nodup)
    (parentPreserved : ∀ record, record ∉ ports →
      canonicalParent (Snapshot.ofTree comparator) afterTree record =
        canonicalParent (Snapshot.ofTree comparator) beforeTree record)
    (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound (Snapshot.ofTree comparator) beforeTree states)
    (complete : Complete (Snapshot.ofTree comparator) beforeTree states)
    (persistent : PersistentGrowers states) :
    let result := reparentSelected comparator afterTree families ids paidNames makeEntry ports states
    (∀ owner side, Valid owner.val side (result.1 owner side)) ∧
    Sound (Snapshot.ofTree comparator) afterTree result.1 ∧
    Complete (Snapshot.ofTree comparator) afterTree result.1 ∧
    PersistentGrowers result.1 ∧ result.2 ≤ 5*ports.length := by
  classical
  let detached := detachPorts comparator families ids (ports.map Fin.val) 0 states
  have detachedValid := detachPorts_valid comparator families ids (ports.map Fin.val) 0 states valid
  have avoids : ∀ owner side entry, entry ∈ entries (detached.1 owner side) → entry.key ∉ ports.map Fin.val := by
    intro owner side entry member
    exact (detachPorts_membership comparator families ids (ports.map Fin.val) 0 states owner side entry).mp member |>.2
  have detachedSound : Sound (Snapshot.ofTree comparator) afterTree detached.1 := by
    intro owner side entry member
    have oldMember := (detachPorts_membership comparator families ids (ports.map Fin.val) 0 states owner side entry).mp member |>.1
    obtain ⟨record,equal,parent⟩ := sound owner side entry oldMember
    refine ⟨record,equal,?_⟩
    rw [parentPreserved record, parent]
    intro selected
    exact avoids owner side entry member (List.mem_map.mpr ⟨record,selected,equal⟩)
  have detachedComplete : CompleteExcept (Snapshot.ofTree comparator) afterTree detached.1
      (ports.map Fin.val).toFinset := by
    intro record owner parent outside
    have notSelected : record ∉ ports := by
      intro selected
      exact outside (List.mem_toFinset.mpr (List.mem_map.mpr ⟨record,selected,rfl⟩))
    rw [parentPreserved record notSelected] at parent
    obtain ⟨side,entry,member,equal⟩ := complete record owner parent (by simp)
    refine ⟨side,entry,?_,equal⟩
    apply (detachPorts_membership comparator families ids (ports.map Fin.val) 0 states owner side entry).mpr
    exact ⟨member,by simpa only [equal,List.mem_toFinset] using outside⟩
  have absent : ∀ record ∈ ports, ¬ Represented detached.1 record.val := by
    intro record selected ⟨owner,side,entry,member,equal⟩
    exact avoids owner side entry member (List.mem_map.mpr ⟨record,selected,equal.symm⟩)
  have restored := restorePorts_valid_sound_births (Snapshot.ofTree comparator) afterTree paidNames makeEntry key
    ports distinct 0 detached.1 detachedValid detachedSound absent
  have restoredComplete := restorePorts_complete (Snapshot.ofTree comparator) afterTree paidNames makeEntry key
    ports distinct 0 detached.1 detachedValid detachedSound absent detachedComplete
  refine ⟨restored.1,restored.2.1,restoredComplete,?_,?_⟩
  · intro owner side
    change ((restorePorts (Snapshot.ofTree comparator) afterTree paidNames makeEntry ports 0 detached.1).1
      owner side).grower.isSome = true
    rw [restorePorts_grower_isSome,detachPorts_grower_isSome]
    exact persistent owner side
  · have detachmentBudget := detachPorts_births_le comparator beforeTree families ids (ports.map Fin.val) 0 states valid sound
    have restorationBudget := restored.2.2
    change detached.2 ≤ (ports.map Fin.val).length at detachmentBudget
    simp only [List.length_map] at detachmentBudget
    change detached.2 + (restorePorts (Snapshot.ofTree comparator) afterTree paidNames makeEntry ports 0 detached.1).2 ≤ _
    omega

/-- A chosen finite parent-support list is obtained from the actual
refinement rotation, not supplied as an administration-budget assumption. -/
noncomputable def refinementRotationPorts {n depth : ℕ} (snapshot : Snapshot n)
    {beforeTree afterTree : BST 0 n} (rotation : RotationAt depth beforeTree afterTree) : List (External n) :=
  (Classical.choose (RefinementRotation.rotation_parent_support snapshot rotation)).toList

theorem refinementRotationPorts_spec {n depth : ℕ} (snapshot : Snapshot n)
    {beforeTree afterTree : BST 0 n} (rotation : RotationAt depth beforeTree afterTree) :
    (refinementRotationPorts snapshot rotation).Nodup ∧
    (refinementRotationPorts snapshot rotation).length ≤ 4 ∧
    (∀ record, record ∉ refinementRotationPorts snapshot rotation →
      canonicalParent snapshot afterTree record = canonicalParent snapshot beforeTree record) := by
  classical
  have chosen := Classical.choose_spec (RefinementRotation.rotation_parent_support snapshot rotation)
  exact ⟨Finset.nodup_toList _,by simpa only [refinementRotationPorts,Finset.length_toList] using chosen.1,
    fun record outside => chosen.2 record (by simpa only [refinementRotationPorts,Finset.mem_toList] using outside)⟩

noncomputable def administerRefinementRotation {n depth : ℕ} (comparator : BST 0 n)
    {beforeTree afterTree : BST 0 n} (rotation : RotationAt depth beforeTree afterTree)
    (families ids : NameSupply n) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry) (states : HeapSides n) : HeapSides n × ℕ :=
  reparentSelected comparator afterTree families ids paidNames makeEntry
    (refinementRotationPorts (Snapshot.ofTree comparator) rotation) states

theorem administerRefinementRotation_spec {n depth : ℕ} (comparator : BST 0 n)
    {beforeTree afterTree : BST 0 n} (rotation : RotationAt depth beforeTree afterTree)
    (families ids : NameSupply n) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (key : ∀ stage record owner, (makeEntry stage record owner).key=record.val)
    (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound (Snapshot.ofTree comparator) beforeTree states)
    (complete : Complete (Snapshot.ofTree comparator) beforeTree states)
    (persistent : PersistentGrowers states) :
    let result := administerRefinementRotation comparator rotation families ids paidNames makeEntry states
    (∀ owner side, Valid owner.val side (result.1 owner side)) ∧
    Sound (Snapshot.ofTree comparator) afterTree result.1 ∧
    Complete (Snapshot.ofTree comparator) afterTree result.1 ∧
    PersistentGrowers result.1 ∧ result.2 ≤ 20 := by
  have ports := refinementRotationPorts_spec (Snapshot.ofTree comparator) rotation
  have result := reparentSelected_spec comparator beforeTree afterTree families ids paidNames makeEntry key
    _ ports.1 ports.2.2 states valid sound complete persistent
  exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,le_trans result.2.2.2.2 (by omega)⟩

#print axioms reparentSelected_spec
#print axioms reparentSelected_id_support
#print axioms administerRefinementRotation_spec

end GreedyMerge.OrderedBlocks
