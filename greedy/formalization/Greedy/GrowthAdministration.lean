import Greedy.GrowthRestoration
import Greedy.FreshComparator
import Greedy.FreshRecanonicalization

/-! Literal administrative macros preserve complete chronological grower books. -/

namespace Greedy.GrowthJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.GrowthBook GreedyMerge.GrowthWindows GreedyMerge.ComparatorOuter

theorem junction_grower {n : ℕ} (oldOwner newOwner : External n) (lo hi start : ℕ)
    (states : HeapSides n) (owner : External n) (side : Bool) :
    ((allocateJunction oldOwner newOwner lo hi start states).states owner side).grower = (states owner side).grower := by
  rw [allocateJunction_eq]
  unfold moveJunction
  split_ifs with old new
  · subst owner; rfl
  · subst owner; rfl
  · rfl

theorem junction_good {n : ℕ} (oldOwner newOwner : External n) (lo hi clock start : ℕ)
    (states : HeapSides n) (books : HeapBooks n) (good : HeapGood clock start states books) :
    let result := allocateJunction oldOwner newOwner lo hi start states
    HeapGood clock result.next result.states books := by
  have moved := heap_grower_congr good
    (fun owner side => (junction_grower oldOwner newOwner lo hi start states owner side).symm)
  exact heap_advance moved clock _ (le_refl _) (allocateJunction_monotone oldOwner newOwner lo hi start states)

theorem rebase_good {n clock next : ℕ} (before after : BST 0 n)
    (states : HeapSides n) (books : HeapBooks n) (good : HeapGood clock next states books) :
    HeapGood clock next (rebaseAll before after states) books :=
  heap_grower_congr good (fun _ _ => rfl)

noncomputable def comparatorBooks {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) (books : HeapBooks n) : HeapBooks n :=
  match plan with
  | .quiet _ => preparationBooks before after start [] ∅ states books
  | .junction certificate =>
      let oldOwner := certificate.node.owner (Snapshot.ofTree before)
      let newOwner := certificate.node.owner (Snapshot.ofTree after)
      let ports := junctionPorts (Snapshot.ofTree before) certificate.node
      let prepared := allocateComparatorPreparation profile ports {oldOwner,newOwner} start states
      let preparedBooks := preparationBooks before after start ports {oldOwner,newOwner} states books
      let moved := allocateJunction oldOwner newOwner certificate.node.lower certificate.node.upper prepared.next prepared.states
      restorationBooks (Snapshot.ofTree after) tree reader (junctionRecords (Snapshot.ofTree before) certificate.node)
        0 moved.next (rebaseAll before after moved.states) preparedBooks

theorem comparatorBooks_good {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (clock start : ℕ) (states : HeapSides n) (books : HeapBooks n) (good : HeapGood clock start states books) :
    let result := allocateComparatorPlan profile tree plan reader start states
    HeapGood clock result.next result.states (comparatorBooks profile tree plan reader start states books) := by
  cases plan with
  | quiet parents =>
      exact rebase_good before after _ _ (allocated_preparation_good profile clock start [] ∅ states books good)
  | junction certificate =>
      exact restorationBooks_good (Snapshot.ofTree after) tree reader _ clock 0 _ _ _
        (rebase_good before after _ _
          (junction_good _ _ _ _ clock _ _ _
            (allocated_preparation_good profile clock start _ _ states books good)))

noncomputable def refinementBooks {n : ℕ} (comparator tree : BST 0 n)
    (ports : List (External n)) (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) (books : HeapBooks n) : HeapBooks n :=
  let names := sequenceNames start
  let detached := (detachPorts comparator names names (ports.map Fin.val) 0 states).1
  let detachedBooks := detachBooks comparator start (ports.map Fin.val) 0 states books
  restorationBooks (Snapshot.ofTree comparator) tree reader ports 0
    (start + Fintype.card (Place n)*ports.length) detached detachedBooks

theorem refinementBooks_good {n : ℕ} (comparator tree : BST 0 n)
    (ports : List (External n)) (reader : ℕ → HeapSides n → External n → External n → Entry)
    (clock start : ℕ) (states : HeapSides n) (books : HeapBooks n) (good : HeapGood clock start states books) :
    let result := FreshRecanonicalization.allocate comparator tree ports reader start states
    HeapGood clock result.next result.states (refinementBooks comparator tree ports reader start states books) := by
  apply restorationBooks_good
  simpa only [List.length_map, Nat.zero_add, Nat.mul_zero, Nat.add_zero] using
    detachBooks_good comparator clock start (ports.map Fin.val) 0 states books (by simpa using good)

end Greedy.GrowthJournal
