import OrderedPersistentGrowers
import UniformBlockRebase

/-!
Concrete fixed-refinement comparator administration, assembled from the
constructed preparation and bulk transfer. Numerical rebasing and actual
paid port restoration are composed below once their local interfaces apply.
The cost is derived from operations, not assumed by an abstract trace field.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.BlockCoverage (Represented Sound CompleteExcept Complete)

noncomputable def junctionRecords {n : ℕ} (snapshot : Snapshot n) (node : AtNode n) : List (External n) :=
  [node.branchMin snapshot .left, node.branchMin snapshot .middle, node.branchMin snapshot .right]

@[simp] theorem junctionRecords_keys {n : ℕ} (snapshot : Snapshot n) (node : AtNode n) :
    (junctionRecords snapshot node).map Fin.val = junctionPorts snapshot node := rfl

theorem junctionRecords_distinct {n : ℕ} (snapshot : Snapshot n) (node : AtNode n) :
    (junctionRecords snapshot node).Nodup := ComparatorOuter.junction_ports_pairwise_distinct snapshot node

noncomputable def prepareMoveJunction {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (families ids : NameSupply n)
    (node : AtNode n) (oldOwner newOwner : External n) (bulkFresh : Bool → ℕ)
    (states : HeapSides n) : HeapSides n × ℕ :=
  let prepared := prepareComparator profile families ids (junctionPorts (Snapshot.ofTree before) node)
    {oldOwner, newOwner} states
  let moved := moveJunction oldOwner newOwner node.lower node.upper bulkFresh prepared.1
  (moved, prepared.2 + junctionTransferBirths oldOwner node.lower node.upper prepared.1)

/-- The actual preparation and bulk move already produce the correct new
canonical parent for every nonport, preserve all nonport coverage, and
leave precisely the ports to be reinstated. -/
theorem prepareMoveJunction_spec {n a b depth treeDepth : ℕ} {before after : BST 0 n}
    (step : KeyRotationAt a b depth before after) (profile : RotationCutProfile before after depth)
    (tree : BST 0 n) (node : AtNode n)
    (occurrence : SubtreeAt (.node node.left node.right) treeDepth tree)
    (separated : ComparatorOuter.Separated node (2*a+1) (2*b+1))
    (oldOwner newOwner : External n)
    (oldValue : oldOwner.val = 2*a+1) (newValue : newOwner.val = 2*b+1)
    (oldRoot : subtreeOwner (Snapshot.ofTree before) (.node node.left node.right) occurrence.bounds.2 = oldOwner)
    (newRoot : subtreeOwner (Snapshot.ofTree after) (.node node.left node.right) occurrence.bounds.2 = newOwner)
    (different : oldOwner ≠ newOwner) (families ids : NameSupply n) (bulkFresh : Bool → ℕ)
    (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound (Snapshot.ofTree before) tree states)
    (complete : Complete (Snapshot.ofTree before) tree states)
    (persistent : PersistentGrowers states) :
    let result := prepareMoveJunction profile families ids node oldOwner newOwner bulkFresh states
    (∀ owner side, Valid owner.val side (result.1 owner side)) ∧
    Sound (Snapshot.ofTree after) tree result.1 ∧
    CompleteExcept (Snapshot.ofTree after) tree result.1
      (junctionPorts (Snapshot.ofTree before) node).toFinset ∧
    (∀ key ∈ junctionPorts (Snapshot.ofTree before) node, ¬ Represented result.1 key) ∧
    PersistentGrowers result.1 ∧ result.2 ≤ 4*(depth+2)^2+11 := by
  classical
  let ports := junctionPorts (Snapshot.ofTree before) node
  let owners : Finset (External n) := {oldOwner, newOwner}
  let prepared := prepareComparator profile families ids ports owners states
  let moved := moveJunction oldOwner newOwner node.lower node.upper bulkFresh prepared.1
  have preparedValid := prepareComparator_valid profile families ids ports owners states valid
  have preparedSound := prepareComparator_sound profile tree families ids ports owners states sound
  have oldEmpty : ∀ side, growerEntries (prepared.1 oldOwner side).grower = [] := by
    intro side
    exact prepareComparator_bulk_empty profile families ids ports owners states oldOwner (by simp [owners]) side
  have newEmpty : ∀ side, growerEntries (prepared.1 newOwner side).grower = [] := by
    intro side
    exact prepareComparator_bulk_empty profile families ids ports owners states newOwner (by simp [owners]) side
  have avoids : ∀ owner side entry, entry ∈ entries (prepared.1 owner side) → entry.key ∉ ports := by
    intro owner side entry member
    exact (prepareComparator_membership profile families ids ports owners states owner side entry).mp member |>.2
  have movedValid := moveJunction_valid (Snapshot.ofTree before) (Snapshot.ofTree after) tree
    (.node node.left node.right) occurrence oldOwner newOwner oldRoot newRoot different bulkFresh prepared.1
    preparedValid preparedSound oldEmpty newEmpty
  have movedSound := moveJunction_sound step tree node occurrence separated oldOwner newOwner oldValue newValue
    oldRoot newRoot different bulkFresh prepared.1 preparedValid preparedSound avoids oldEmpty newEmpty
  have covered : CompleteExcept (Snapshot.ofTree before) tree prepared.1 ports.toFinset := by
    intro record owner parent outside
    obtain ⟨side, entry, member, equal⟩ := complete record owner parent (by simp)
    refine ⟨side, entry, ?_, equal⟩
    apply (prepareComparator_membership profile families ids ports owners states owner side entry).mpr
    exact ⟨member, by simpa only [equal, List.mem_toFinset] using outside⟩
  have rootCase : canonicalRoot (Snapshot.ofTree before) tree = canonicalRoot (Snapshot.ofTree after) tree ∨
      (canonicalRoot (Snapshot.ofTree before) tree).val ∈ ports.toFinset := by
    have changes := ComparatorHeap.snapshot_min_changes step (subtreeLower tree (Nat.le_refl n))
      (subtreeUpper tree (Nat.le_refl n)) (subtree_nonempty tree (Nat.le_refl n))
    change canonicalRoot (Snapshot.ofTree before) tree = canonicalRoot (Snapshot.ofTree after) tree ∨
      ((canonicalRoot (Snapshot.ofTree before) tree).val = 2*a+1 ∧
       (canonicalRoot (Snapshot.ofTree after) tree).val = 2*b+1) at changes
    rcases changes with same | changed
    · exact Or.inl same
    · right
      have oldPort := (junction_owner_keys_mem step node separated oldOwner newOwner oldRoot newRoot).1
      apply List.mem_toFinset.mpr
      simpa only [changed.1, oldValue] using oldPort
  have represented : ∀ key, Represented moved key ↔ Represented prepared.1 key :=
    moveJunction_represented oldOwner newOwner node.lower node.upper different bulkFresh prepared.1
      preparedValid oldEmpty newEmpty
  have movedComplete := BlockCoverage.completeExcept_reparent (Snapshot.ofTree before) (Snapshot.ofTree after)
    tree tree prepared.1 moved ports.toFinset covered movedSound rootCase
    (fun key _ present => (represented key).mpr present)
  have missing : ∀ key ∈ ports, ¬ Represented moved key := by
    intro key member present
    obtain ⟨owner, side, entry, entryMem, equal⟩ := (represented key).mp present
    exact avoids owner side entry entryMem (by simpa only [equal] using member)
  have movedPersistent : PersistentGrowers moved := by
    intro owner side
    rw [moveJunction_grower_eq]
    rw [prepareComparator_grower_isSome]
    exact persistent owner side
  have preparationBudget := prepareComparator_births_le profile tree families ids ports owners states valid sound
  have movingBudget := junctionTransferBirths_le_four oldOwner node.lower node.upper prepared.1
    (preparedValid oldOwner)
  have portsLength : ports.length = 3 := rfl
  have ownerCard : owners.card = 2 := by simp [owners, different]
  refine ⟨movedValid, movedSound, movedComplete, missing, movedPersistent, ?_⟩
  change prepared.2 + junctionTransferBirths oldOwner node.lower node.upper prepared.1 ≤ _
  change prepared.2 ≤ 4*(depth+2)^2 + ports.length + 2*owners.card at preparationBudget
  rw [portsLength, ownerCard] at preparationBudget
  omega

/-- The executed changed-junction macro, including concrete numerical
rebasing and paid reinsertion at the actual final canonical parent. -/
noncomputable def administerJunction {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (families ids : NameSupply n) (node : AtNode n)
    (oldOwner newOwner : External n) (bulkFresh : Bool → ℕ)
    (paidNames : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (states : HeapSides n) : HeapSides n × ℕ :=
  let moved := prepareMoveJunction profile families ids node oldOwner newOwner bulkFresh states
  let rebased := rebaseAll before after moved.1
  let restored := restorePorts (Snapshot.ofTree after) tree paidNames makeEntry
    (junctionRecords (Snapshot.ofTree before) node) 0 rebased
  (restored.1, moved.2 + restored.2)

/-- Structural completion of the concrete macro. Every actual nonroot is
represented at its actual final parent, and all persistent side growers
survive. The birth bound is computed from executed operations, including
two new instances per actual binary split. -/
theorem administerJunction_spec {n a b depth treeDepth : ℕ} {before after : BST 0 n}
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
    (key : ∀ stage record owner, (makeEntry stage record owner).key = record.val)
    (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound (Snapshot.ofTree before) tree states)
    (complete : Complete (Snapshot.ofTree before) tree states)
    (persistent : PersistentGrowers states) :
    let result := administerJunction profile tree families ids node oldOwner newOwner bulkFresh
      paidNames makeEntry states
    (∀ owner side, Valid owner.val side (result.1 owner side)) ∧
    Sound (Snapshot.ofTree after) tree result.1 ∧
    Complete (Snapshot.ofTree after) tree result.1 ∧
    PersistentGrowers result.1 ∧ result.2 ≤ 4*(depth+2)^2+23 := by
  classical
  let moved := prepareMoveJunction profile families ids node oldOwner newOwner bulkFresh states
  let rebased := rebaseAll before after moved.1
  let ports := junctionRecords (Snapshot.ofTree before) node
  obtain ⟨movedValid, movedSound, movedComplete, movedAbsent, movedPersistent, movedBudget⟩ :=
    prepareMoveJunction_spec step profile tree node occurrence separated oldOwner newOwner oldValue newValue
      oldRoot newRoot different families ids bulkFresh states valid sound complete persistent
  have rebasedValid := rebaseAll_valid before after moved.1 movedValid
  have rebasedSound := rebaseAll_sound before after tree moved.1 movedSound
  have rebasedAbsent : ∀ record ∈ ports, ¬ Represented rebased record.val := by
    intro record member present
    apply movedAbsent record.val (List.mem_map.mpr ⟨record, member, rfl⟩)
    obtain ⟨owner, side, entry, entryMem, equal⟩ := present
    exact ⟨owner, side, entry, by simpa only [rebased, rebaseAll_entries] using entryMem, equal⟩
  have rebasedComplete : CompleteExcept (Snapshot.ofTree after) tree rebased
      (ports.map Fin.val).toFinset := by
    intro record owner parent outside
    obtain ⟨side, entry, member, equal⟩ := movedComplete record owner parent outside
    exact ⟨side, entry, by simpa only [rebased, rebaseAll_entries] using member, equal⟩
  have restored := restorePorts_valid_sound_births (Snapshot.ofTree after) tree paidNames makeEntry key
    ports (junctionRecords_distinct _ _) 0 rebased rebasedValid rebasedSound rebasedAbsent
  have restoredComplete := restorePorts_complete (Snapshot.ofTree after) tree paidNames makeEntry key
    ports (junctionRecords_distinct _ _) 0 rebased rebasedValid rebasedSound rebasedAbsent rebasedComplete
  refine ⟨restored.1, restored.2.1, restoredComplete, ?_, ?_⟩
  · intro owner side
    change ((restorePorts (Snapshot.ofTree after) tree paidNames makeEntry ports 0 rebased).1
      owner side).grower.isSome = true
    rw [restorePorts_grower_isSome, rebaseAll_grower]
    exact movedPersistent owner side
  · change moved.2 + (restorePorts (Snapshot.ofTree after) tree paidNames makeEntry ports 0 rebased).2 ≤ _
    change moved.2 ≤ 4*(depth+2)^2+11 at movedBudget
    have restoredBudget := restored.2.2
    have portsLength : ports.length = 3 := rfl
    rw [portsLength] at restoredBudget
    omega

#print axioms prepareMoveJunction_spec
#print axioms administerJunction_spec

end GreedyMerge.OrderedBlocks
