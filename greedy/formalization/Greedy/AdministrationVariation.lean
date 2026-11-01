import Greedy.RestorationVariation
import Greedy.HistoryAdministration

/-! Exact agreement of the existing administrative history and journal. -/

namespace Greedy.AdministrationJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation GreedyMerge.ComparatorOuter
open EntryJournal RestorationJournal

theorem plan_agrees {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (K : ℤ) (clock start : ℕ) (states : HeapSides n)
    (state : WeightedMemory.State (External n)) (history : LabelHistory.History (External n))
    (current : LabelHistory.current history = state.label) :
    let actions := planJournal profile tree plan K (Execution.entryReader after K clock) start states
    let finalHistory := LabelSnapshots.planHistory profile tree plan K clock start states history
    let result := allocateComparatorPlan profile tree plan (Execution.entryReader after K clock) start states
    (run state actions).label = labels after K result.states ∧
      LabelHistory.current finalHistory = (run state actions).label ∧
      LabelHistory.variation finalHistory = LabelHistory.variation history + total absoluteChange state actions := by
  have result := administration_agrees after tree K clock (prepare profile tree plan start states).ports
    0 (prepare profile tree plan start states).next (prepare profile tree plan start states).states state history current
  dsimp only at result
  rw [prepare_restoration] at result
  exact result

theorem refinement_agrees {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (ports : List (External n)) (clock start : ℕ) (states : HeapSides n)
    (state : WeightedMemory.State (External n)) (history : LabelHistory.History (External n))
    (current : LabelHistory.current history = state.label) :
    let actions := refinement comparator tree K ports (Execution.entryReader comparator K clock) start states
    let finalHistory := LabelSnapshots.refinementHistory comparator tree K ports clock start states history
    let result := FreshRecanonicalization.allocate comparator tree ports (Execution.entryReader comparator K clock) start states
    (run state actions).label = labels comparator K result.states ∧
      LabelHistory.current finalHistory = (run state actions).label ∧
      LabelHistory.variation finalHistory = LabelHistory.variation history + total absoluteChange state actions :=
  administration_agrees comparator tree K clock ports 0 (start + Fintype.card (Place n)*ports.length)
    (detachPorts comparator (sequenceNames start) (sequenceNames start) (ports.map Fin.val) 0 states).1 state history current

end Greedy.AdministrationJournal
