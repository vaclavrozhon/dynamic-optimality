import Greedy.FamilyInvariant
import Greedy.FreshRecanonicalization

/-! Whole administrative macros preserve global fragment-history order. -/

namespace Greedy.FamilyOrder

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.ComparatorOuter

theorem restoration_invariant {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry) (clock : ℕ)
    (time : ∀ stage current record owner, (reader stage current record owner).joined = clock+stage)
    (ports : List (External n)) (stage start : ℕ) (states : HeapSides n)
    (inv : Invariant (clock+stage) start states) :
    Invariant (clock+stage+ports.length) (freshRestorePorts snapshot tree reader ports stage start states).next
      (freshRestorePorts snapshot tree reader ports stage start states).states := by
  induction ports generalizing stage start states with
  | nil => simpa only [freshRestorePorts, List.length_nil, Nat.add_zero] using inv
  | cons record rest ih =>
      have head := restorePort_invariant snapshot tree record (reader stage states record) (time stage states record) states inv
      have tail := ih (stage+1) _ _ (by simpa only [Nat.add_assoc] using head)
      simpa only [freshRestorePorts, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using tail

theorem comparator_invariant {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n) (plan : RotationPlan before after tree a b)
    (reader : ℕ → HeapSides n → External n → External n → Entry) (clock : ℕ)
    (time : ∀ stage current record owner, (reader stage current record owner).joined = clock+stage)
    (start : ℕ) (states : HeapSides n) (inv : Invariant clock start states) :
    Invariant (clock+3) (allocateComparatorPlan profile tree plan reader start states).next
      (allocateComparatorPlan profile tree plan reader start states).states := by
  cases plan with
  | quiet parents =>
      exact (rebase_invariant before after _ (allocated_preparation_invariant profile start [] ∅ states inv)).advance (clock+3) (by omega)
  | junction certificate =>
      have prepared := allocated_preparation_invariant profile start
        (junctionPorts (Snapshot.ofTree before) certificate.node)
        {certificate.node.owner (Snapshot.ofTree before), certificate.node.owner (Snapshot.ofTree after)} states inv
      have moved := junction_invariant _ _ certificate.different certificate.node.lower certificate.node.upper _ _ prepared
      have rebased := rebase_invariant before after _ moved
      have restored := restoration_invariant (Snapshot.ofTree after) tree reader clock time
        (junctionRecords (Snapshot.ofTree before) certificate.node) 0 _ _ (by simpa using rebased)
      simpa only [allocateComparatorPlan, Nat.add_zero, junctionRecords, List.length_cons, List.length_nil] using restored

theorem refinement_invariant {n : ℕ} (comparator tree : BST 0 n) (ports : List (External n))
    (reader : ℕ → HeapSides n → External n → External n → Entry) (clock : ℕ)
    (time : ∀ stage current record owner, (reader stage current record owner).joined = clock+stage)
    (start : ℕ) (states : HeapSides n) (inv : Invariant clock start states) :
    Invariant (clock+ports.length) (FreshRecanonicalization.allocate comparator tree ports reader start states).next
      (FreshRecanonicalization.allocate comparator tree ports reader start states).states := by
  have detached := detachPorts_invariant comparator start (ports.map Fin.val) 0 states (by simpa using inv)
  have restored := restoration_invariant (Snapshot.ofTree comparator) tree reader clock time ports 0
    (start + Fintype.card (Place n)*ports.length) _ (by simpa only [Nat.add_zero, Nat.zero_add, List.length_map] using detached)
  simpa only [FreshRecanonicalization.allocate, Nat.add_zero] using restored

end Greedy.FamilyOrder
