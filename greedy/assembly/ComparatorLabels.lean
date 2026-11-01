import StateRebase
import TaggedRestoration
import OrderedComparatorMacro

/-!
The full executed changed-junction comparator macro weakly decreases every
actual state-defined label outside its three actual junction ports. All
numerical facts are derived from the concrete preparation, bulk movement,
uniform rebase and restoration program. This handles the changed-junction
case; universal comparator case selection and recanonicalization are separate.
-/

namespace GreedyMerge.StateLabels

open OrderedBlocks Primitives BlockCoverage
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

theorem administerJunction_label_le {n a b depth treeDepth : ℕ} {before after : BST 0 n}
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
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound (Snapshot.ofTree before) tree states)
    (complete : Complete (Snapshot.ofTree before) tree states)
    (persistent : PersistentGrowers states)
    (upper : ∀ owner side, UpperBase before.externalDepth (states owner side))
    (K : ℤ) (key : ℕ) (outside : key ∉ junctionPorts (Snapshot.ofTree before) node) :
    label after.externalDepth K
      (administerJunction profile tree families ids node oldOwner newOwner bulkFresh paidNames makeEntry states).1 key ≤
      label before.externalDepth K states key := by
  classical
  let ports := junctionPorts (Snapshot.ofTree before) node
  let owners : Finset (External n) := {oldOwner, newOwner}
  let prepared := (prepareComparator profile families ids ports owners states).1
  let moved := moveJunction oldOwner newOwner node.lower node.upper bulkFresh prepared
  have movedSpec := prepareMoveJunction_spec step profile tree node occurrence separated oldOwner newOwner
    oldValue newValue oldRoot newRoot different families ids bulkFresh states valid sound complete persistent
  have movedValid : ∀ owner side, Valid owner.val side (moved owner side) := movedSpec.1
  have movedSound : Sound (Snapshot.ofTree after) tree moved := movedSpec.2.1
  have preparedUpper := prepareComparator_upperBase profile tree families ids ports owners states upper sound
  have movedUpper := moveJunction_upperBase before.externalDepth oldOwner newOwner node.lower node.upper
    bulkFresh prepared preparedUpper
  have preparedUniform := prepareComparator_uniform profile families ids ports owners states valid
  have movedUniform := moveJunction_uniform (rankShift before after) oldOwner newOwner node.lower node.upper
    bulkFresh prepared preparedUniform
  have preparedGrowing := prepareComparator_grower_uniform profile families ids ports owners states
  have movedGrowing := moveJunction_grower_uniform (rankShift before after) oldOwner newOwner node.lower node.upper
    bulkFresh prepared preparedGrowing
  have rebaseDecrease := rebaseAll_label_le before after tree K moved movedValid movedSound
    movedUpper movedUniform movedGrowing key
  have restoreEqual := restorePorts_label after tree K paidNames makeEntry entryKey
    (junctionRecords (Snapshot.ofTree before) node) 0 (rebaseAll before after moved) key
      (by simpa only [junctionRecords_keys] using outside)
  calc
    label after.externalDepth K
        (administerJunction profile tree families ids node oldOwner newOwner bulkFresh paidNames makeEntry states).1 key =
        label after.externalDepth K (rebaseAll before after moved) key := restoreEqual
    _ ≤ label before.externalDepth K moved key := rebaseDecrease
    _ = label before.externalDepth K prepared key :=
      moveJunction_label before.externalDepth K oldOwner newOwner node.lower node.upper bulkFresh prepared different key
    _ = label before.externalDepth K states key :=
      prepareComparator_label profile families ids ports owners states K key outside

end GreedyMerge.StateLabels

#print axioms GreedyMerge.StateLabels.administerJunction_label_le
