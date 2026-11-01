import Greedy.ClosedStructural
import Greedy.ClosedPaid
import Greedy.FreshRecanonicalization

/-! Actual administration only creates families newer than a closed family. -/

namespace Greedy.ClosedFamilies

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation GreedyMerge.ComparatorOuter

theorem comparator_closed {n a b depth family : ℕ} {property : Frozen → Prop} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n) (plan : RotationPlan before after tree a b)
    (reader : ℕ → HeapSides n → External n → External n → Entry) (start : ℕ) (states : HeapSides n)
    (closed : HeapClosed family property states) (hereditary : Hereditary property) (past : family < start) :
    HeapClosed family property (allocateComparatorPlan profile tree plan reader start states).states := by
  cases plan with
  | quiet parents =>
      exact rebase_closed before after _ (allocated_preparation_closed profile start [] ∅ states closed hereditary past) hereditary
  | junction certificate =>
      have prepared := allocated_preparation_closed profile start
        (junctionPorts (Snapshot.ofTree before) certificate.node)
        {certificate.node.owner (Snapshot.ofTree before), certificate.node.owner (Snapshot.ofTree after)} states closed hereditary past
      have moved := junction_closed (certificate.node.owner (Snapshot.ofTree before))
        (certificate.node.owner (Snapshot.ofTree after)) certificate.node.lower certificate.node.upper
        (allocateComparatorPreparation profile (junctionPorts (Snapshot.ofTree before) certificate.node)
          {certificate.node.owner (Snapshot.ofTree before), certificate.node.owner (Snapshot.ofTree after)} start states).next
        _ prepared hereditary
      have rebased := rebase_closed before after _ moved hereditary
      apply restoration_closed (Snapshot.ofTree after) tree reader _ 0 _ _ rebased hereditary
      exact past.trans_le ((allocateComparatorPreparation_monotone profile _ _ start states).trans
        (allocateJunction_monotone _ _ certificate.node.lower certificate.node.upper _ _))

theorem refinement_closed {n family : ℕ} {property : Frozen → Prop} (comparator tree : BST 0 n)
    (ports : List (External n)) (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) (closed : HeapClosed family property states)
    (hereditary : Hereditary property) (past : family < start) :
    HeapClosed family property (FreshRecanonicalization.allocate comparator tree ports reader start states).states := by
  apply restoration_closed (Snapshot.ofTree comparator) tree reader ports 0 _ _ _ hereditary
    (past.trans_le (Nat.le_add_right _ _))
  exact detachPorts_closed comparator start (ports.map Fin.val) 0 states closed hereditary past

end Greedy.ClosedFamilies
