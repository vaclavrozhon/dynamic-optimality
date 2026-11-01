import TaggedRestoration
import OrderedRefinementMacro
import AdministrationTimeline

/-! Exact global-label preservation outside the selected parent changes.
For an actual fixed-rank refinement rotation, the geometric support has
at most four records, yielding at most four paid timeline cells. -/

namespace GreedyMerge.StateLabels

open OrderedBlocks Primitives BlockCoverage
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyForest.Timeline

theorem detachPorts_label {n : ℕ} (comparator : BST 0 n) (K : ℤ)
    (families ids : NameSupply n) (ports : List ℕ) (stage : ℕ) (states : States n)
    (key : ℕ) (outside : key ∉ ports) :
    label comparator.externalDepth K (detachPorts comparator families ids ports stage states).1 key =
      label comparator.externalDepth K states key := by
  apply label_congr
  intro base
  constructor
  · rintro ⟨owner, side, entry, member, equal⟩
    rw [tagged_detachPorts] at member
    exact ⟨owner, side, entry, (List.mem_filter.mp member).1, equal⟩
  · rintro ⟨owner, side, entry, member, equal⟩
    refine ⟨owner, side, entry, ?_, equal⟩
    rw [tagged_detachPorts]
    exact List.mem_filter.mpr ⟨member, by simpa only [equal, decide_eq_true_eq] using outside⟩

theorem reparentSelected_label {n : ℕ} (comparator afterTree : BST 0 n) (K : ℤ)
    (families ids : NameSupply n) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (entryKey : ∀ stage record owner, (makeEntry stage record owner).key = record.val)
    (ports : List (External n)) (states : States n) (key : ℕ)
    (outside : key ∉ ports.map Fin.val) :
    label comparator.externalDepth K
      (reparentSelected comparator afterTree families ids paidNames makeEntry ports states).1 key =
      label comparator.externalDepth K states key := by
  unfold reparentSelected
  rw [restorePorts_label comparator afterTree K paidNames makeEntry entryKey ports 0 _ key outside]
  exact detachPorts_label comparator K families ids (ports.map Fin.val) 0 states key outside

theorem reparentSelected_timeline {Block : Type*} {n : ℕ} (comparator afterTree : BST 0 n)
    (families ids : NameSupply n) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (entryKey : ∀ stage record owner, (makeEntry stage record owner).key = record.val)
    (ports : List (External n)) (states : States n)
    (H : ℕ) (height : ∀ record : External n, comparator.externalDepth record.val ≤ H) :
    let result := (reparentSelected comparator afterTree families ids paidNames makeEntry ports states).1
    let initial : External n → ℤ := fun record => label comparator.externalDepth (contractedGap H) states record.val
    let target : External n → ℤ := fun record => label comparator.externalDepth (contractedGap H) result record.val
    let updates := relabel (Block:=Block) target ports.toFinset (List.ofFn (fun record : External n => record))
    GreedyForest.Timeline.Valid (contractedGap H) initial updates ∧
      run initial updates = target ∧ Nat.card (Paid updates) ≤ ports.length := by
  classical
  let result := (reparentSelected comparator afterTree families ids paidNames makeEntry ports states).1
  let initial : External n → ℤ := fun record => label comparator.externalDepth (contractedGap H) states record.val
  let target : External n → ℤ := fun record => label comparator.externalDepth (contractedGap H) result record.val
  let records := List.ofFn (fun record : External n => record)
  have free : ∀ record, record ∉ ports.toFinset → target record ≤ initial record := by
    intro record outside
    apply le_of_eq
    apply reparentSelected_label comparator afterTree _ families ids paidNames makeEntry entryKey ports states
    intro member
    obtain ⟨port, portMember, equal⟩ := List.mem_map.mp member
    exact outside (List.mem_toFinset.mpr ((Fin.ext equal : port = record) ▸ portMember))
  have bounded : ∀ record ∈ records, 1 ≤ target record ∧ target record ≤ (contractedGap H : ℤ) := by
    intro record _
    exact label_bounded comparator.externalDepth H result record (height record)
  have distinct : records.Nodup := List.nodup_ofFn.mpr (fun _ _ equal => equal)
  refine ⟨valid_relabel initial target ports.toFinset records bounded free, ?_, ?_⟩
  · funext record
    exact run_relabel_at_mem initial target ports.toFinset records record (List.mem_ofFn.mpr ⟨record, rfl⟩)
  · exact (paid_relabel_card_le_ports (Block:=Block) target ports.toFinset records distinct).trans
      (List.toFinset_card_le ports)

/-- The actual rotation supplies its support; no paid-count assumption is
accepted. This theorem is only the label timeline, while the companion
structural macro proves final parent soundness and heap coverage. -/
theorem refinementRotation_timeline {Block : Type*} {n depth : ℕ} (comparator : BST 0 n)
    {beforeTree afterTree : BST 0 n} (rotation : RotationAt depth beforeTree afterTree)
    (families ids : NameSupply n) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (entryKey : ∀ stage record owner, (makeEntry stage record owner).key = record.val)
    (states : States n) (H : ℕ)
    (height : ∀ record : External n, comparator.externalDepth record.val ≤ H) :
    let result := (administerRefinementRotation comparator rotation families ids paidNames makeEntry states).1
    let initial : External n → ℤ := fun record => label comparator.externalDepth (contractedGap H) states record.val
    let target : External n → ℤ := fun record => label comparator.externalDepth (contractedGap H) result record.val
    let ports := (refinementRotationPorts (Snapshot.ofTree comparator) rotation).toFinset
    let updates := relabel (Block:=Block) target ports (List.ofFn (fun record : External n => record))
    GreedyForest.Timeline.Valid (contractedGap H) initial updates ∧
      run initial updates = target ∧ Nat.card (Paid updates) ≤ 4 := by
  have result := reparentSelected_timeline (Block:=Block) comparator afterTree families ids paidNames
    makeEntry entryKey (refinementRotationPorts (Snapshot.ofTree comparator) rotation) states H height
  exact ⟨result.1, result.2.1,
    result.2.2.trans (refinementRotationPorts_spec (Snapshot.ofTree comparator) rotation).2.1⟩

end GreedyMerge.StateLabels

#print axioms GreedyMerge.StateLabels.reparentSelected_label
#print axioms GreedyMerge.StateLabels.refinementRotation_timeline
