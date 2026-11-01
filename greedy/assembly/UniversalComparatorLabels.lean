import ComparatorTimeline
import OrderedUniversalComparator

/-! Every actual comparator rotation has a concrete label timeline with
at most three paid cells. The quiet/changed case and its ports come from
the actual rotation geometry; no caller-supplied case analysis is needed. -/

namespace GreedyMerge.StateLabels

open OrderedBlocks Primitives BlockCoverage
open GreedyMerge.ComparatorOuter (RotationPlan rotationPlan)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyForest.Timeline

theorem administerRankOnly_label_le {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (parents : ∀ record, canonicalParent (Snapshot.ofTree after) tree record =
      canonicalParent (Snapshot.ofTree before) tree record)
    (families ids : NameSupply n) (states : HeapSides n) (ready : Ready before tree states)
    (K : ℤ) (key : ℕ) :
    label after.externalDepth K (administerRankOnly profile families ids states).1 key ≤
      label before.externalDepth K states key := by
  let prepared := (prepareComparator profile families ids [] ∅ states).1
  have upper : ∀ owner side, UpperBase before.externalDepth (states owner side) :=
    fun owner side block member => (ready.bases owner side block member).2
  have preparedValid := prepareComparator_valid profile families ids [] ∅ states ready.valid
  have oldSound := prepareComparator_sound profile tree families ids [] ∅ states ready.sound
  have newSound : Sound (Snapshot.ofTree after) tree prepared := by
    intro owner side entry member
    obtain ⟨record, equal, parent⟩ := oldSound owner side entry member
    exact ⟨record, equal, by rw [parents, parent]⟩
  have bound := rebaseAll_label_le before after tree K prepared preparedValid newSound
    (prepareComparator_upperBase profile tree families ids [] ∅ states upper ready.sound)
    (prepareComparator_uniform profile families ids [] ∅ states ready.valid)
    (prepareComparator_grower_uniform profile families ids [] ∅ states) key
  have unchanged := prepareComparator_label profile families ids [] ∅ states K key (by simp)
  exact bound.trans_eq unchanged

noncomputable def planPorts {n a b : ℕ} {before after tree : BST 0 n}
    (plan : RotationPlan before after tree a b) : List (External n) :=
  match plan with
  | .quiet _ => []
  | .junction certificate => junctionRecords (Snapshot.ofTree before) certificate.node

theorem planPorts_length {n a b : ℕ} {before after tree : BST 0 n}
    (plan : RotationPlan before after tree a b) : (planPorts plan).length ≤ 3 := by
  cases plan <;> simp [planPorts, junctionRecords]

theorem executeComparatorPlan_label_le {n a b depth : ℕ} {before after : BST 0 n}
    (step : KeyRotationAt a b depth before after) (profile : RotationCutProfile before after depth)
    (tree : BST 0 n) (plan : RotationPlan before after tree a b) (families ids : NameSupply n)
    (bulkFresh : Bool → ℕ) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (entryKey : ∀ stage record owner, (makeEntry stage record owner).key = record.val)
    (states : HeapSides n) (ready : Ready before tree states) (K : ℤ) (key : ℕ)
    (outside : key ∉ (planPorts plan).map Fin.val) :
    label after.externalDepth K
      (executeComparatorPlan profile tree plan families ids bulkFresh paidNames makeEntry states).1 key ≤
      label before.externalDepth K states key := by
  cases plan with
  | quiet parents => exact administerRankOnly_label_le profile tree parents families ids states ready K key
  | junction certificate =>
      exact administerJunction_label_le step profile tree certificate.node certificate.occurrence
        certificate.separated _ _ certificate.oldValue certificate.newValue rfl rfl certificate.different
        families ids bulkFresh paidNames makeEntry entryKey states ready.valid ready.sound ready.complete
        ready.persistent (fun owner side block member => (ready.bases owner side block member).2) K key outside

/-- The universal macro and its exact actual endpoint labels instantiate
the accounting timeline with zero or three selected ports. -/
theorem administerComparator_timeline {Block : Type*} {n a b depth : ℕ} {before after : BST 0 n}
    (step : KeyRotationAt a b depth before after) (profile : RotationCutProfile before after depth)
    (tree : BST 0 n) (families ids : NameSupply n) (bulkFresh : Bool → ℕ)
    (paidNames : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (entryKey : ∀ stage record owner, (makeEntry stage record owner).key = record.val)
    (states : HeapSides n) (ready : Ready before tree states)
    (H : ℕ) (height : ∀ record : External n, after.externalDepth record.val ≤ H) :
    let result := (administerComparator step profile tree families ids bulkFresh paidNames makeEntry states).1
    let initial : External n → ℤ := fun record => label before.externalDepth (contractedGap H) states record.val
    let target : External n → ℤ := fun record => label after.externalDepth (contractedGap H) result record.val
    let ports := (planPorts (rotationPlan step tree)).toFinset
    let updates := relabel (Block:=Block) target ports (List.ofFn (fun record : External n => record))
    GreedyForest.Timeline.Valid (contractedGap H) initial updates ∧
      run initial updates = target ∧ Nat.card (Paid updates) ≤ 3 := by
  classical
  let result := (administerComparator step profile tree families ids bulkFresh paidNames makeEntry states).1
  let initial : External n → ℤ := fun record => label before.externalDepth (contractedGap H) states record.val
  let target : External n → ℤ := fun record => label after.externalDepth (contractedGap H) result record.val
  let ports := (planPorts (rotationPlan step tree)).toFinset
  let records := List.ofFn (fun record : External n => record)
  have free : ∀ record, record ∉ ports → target record ≤ initial record := by
    intro record outside
    apply executeComparatorPlan_label_le step profile tree (rotationPlan step tree) families ids bulkFresh
      paidNames makeEntry entryKey states ready
    intro member
    obtain ⟨port, portMember, equal⟩ := List.mem_map.mp member
    exact outside (List.mem_toFinset.mpr ((Fin.ext equal : port = record) ▸ portMember))
  have bounded : ∀ record ∈ records, 1 ≤ target record ∧ target record ≤ (contractedGap H : ℤ) := by
    intro record _
    exact label_bounded after.externalDepth H result record (height record)
  have distinct : records.Nodup := List.nodup_ofFn.mpr (fun _ _ equal => equal)
  refine ⟨valid_relabel initial target ports records bounded free, ?_, ?_⟩
  · funext record
    exact run_relabel_at_mem initial target ports records record (List.mem_ofFn.mpr ⟨record, rfl⟩)
  · exact (paid_relabel_card_le_ports (Block:=Block) target ports records distinct).trans
      ((List.toFinset_card_le _).trans (planPorts_length _))

end GreedyMerge.StateLabels

#print axioms GreedyMerge.StateLabels.administerComparator_timeline
