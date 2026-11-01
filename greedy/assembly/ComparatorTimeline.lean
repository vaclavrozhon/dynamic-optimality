import ComparatorLabels
import AdministrationTimeline

/-! The concrete changed-junction macro supplies a valid finite label
timeline with at most three paid update cells. Both endpoints are read
from actual block states. No aggregate variation premise is introduced. -/

namespace GreedyMerge.StateLabels

open OrderedBlocks Primitives BlockCoverage
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyForest.Timeline

theorem administerJunction_timeline {Block : Type*} {n a b depth treeDepth : ℕ}
    {before after : BST 0 n}
    (step : KeyRotationAt a b depth before after) (profile : RotationCutProfile before after depth)
    (tree : BST 0 n) (node : AtNode n)
    (occurrence : SubtreeAt (.node node.left node.right) treeDepth tree)
    (separated : ComparatorOuter.Separated node (2*a+1) (2*b+1))
    (oldOwner newOwner : External n)
    (oldValue : oldOwner.val = 2*a+1) (newValue : newOwner.val = 2*b+1)
    (oldRoot : subtreeOwner (Snapshot.ofTree before) (.node node.left node.right) occurrence.bounds.2 = oldOwner)
    (newRoot : subtreeOwner (Snapshot.ofTree after) (.node node.left node.right) occurrence.bounds.2 = newOwner)
    (different : oldOwner ≠ newOwner) (families ids : NameSupply n) (bulkFresh : Bool → ℕ)
    (paidNames : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (entryKey : ∀ stage record owner, (makeEntry stage record owner).key = record.val)
    (states : HeapSides n)
    (valid : ∀ owner side, OrderedBlocks.Valid owner.val side (states owner side))
    (sound : Sound (Snapshot.ofTree before) tree states)
    (complete : Complete (Snapshot.ofTree before) tree states)
    (persistent : PersistentGrowers states)
    (upper : ∀ owner side, UpperBase before.externalDepth (states owner side))
    (H : ℕ) (height : ∀ record : External n, after.externalDepth record.val ≤ H) :
    let result := (administerJunction profile tree families ids node oldOwner newOwner bulkFresh
      paidNames makeEntry states).1
    let initial : External n → ℤ := fun record => label before.externalDepth (contractedGap H) states record.val
    let target : External n → ℤ := fun record => label after.externalDepth (contractedGap H) result record.val
    let ports := (junctionRecords (Snapshot.ofTree before) node).toFinset
    let updates := relabel (Block:=Block) target ports (List.ofFn (fun record : External n => record))
    GreedyForest.Timeline.Valid (contractedGap H) initial updates ∧
      run initial updates = target ∧ Nat.card (Paid updates) ≤ 3 := by
  classical
  let result := (administerJunction profile tree families ids node oldOwner newOwner bulkFresh
    paidNames makeEntry states).1
  let initial : External n → ℤ := fun record => label before.externalDepth (contractedGap H) states record.val
  let target : External n → ℤ := fun record => label after.externalDepth (contractedGap H) result record.val
  let ports := (junctionRecords (Snapshot.ofTree before) node).toFinset
  let records := List.ofFn (fun record : External n => record)
  have free : ∀ record, record ∉ ports → target record ≤ initial record := by
    intro record outside
    apply administerJunction_label_le step profile tree node occurrence separated oldOwner newOwner
      oldValue newValue oldRoot newRoot different families ids bulkFresh paidNames makeEntry entryKey
      states valid sound complete persistent upper
    intro member
    have mapped : record.val ∈ (junctionRecords (Snapshot.ofTree before) node).map Fin.val := member
    obtain ⟨port, portMember, equal⟩ := List.mem_map.mp mapped
    have same : port = record := Fin.ext equal
    exact outside (List.mem_toFinset.mpr (same ▸ portMember))
  have bounded : ∀ record ∈ records, 1 ≤ target record ∧ target record ≤ (contractedGap H : ℤ) := by
    intro record _
    exact label_bounded after.externalDepth H result record (height record)
  have distinct : records.Nodup := List.nodup_ofFn.mpr (fun _ _ equal => equal)
  refine ⟨valid_relabel initial target ports records bounded free, ?_, ?_⟩
  · funext record
    exact run_relabel_at_mem initial target ports records record (List.mem_ofFn.mpr ⟨record, rfl⟩)
  · have bound := paid_relabel_card_le_ports (Block:=Block) target ports records distinct
    have portsBound : ports.card ≤ 3 :=
      List.toFinset_card_le (junctionRecords (Snapshot.ofTree before) node)
    exact bound.trans portsBound

end GreedyMerge.StateLabels

#print axioms GreedyMerge.StateLabels.administerJunction_timeline
