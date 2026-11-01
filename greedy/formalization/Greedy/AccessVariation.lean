import Greedy.JournalAbsoluteVariation
import Greedy.HistoryAccess
import Greedy.AccessJournal

/-! Prefix label correctness identifies the access history's exact variation. -/

namespace Greedy.AccessJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks GreedyMerge.PathPlateau
open EntryJournal RestorationJournal

theorem history_program_agrees {n : ℕ} (comparator : BST 0 n) (K : ℤ)
    (source : External n) (sourceSide : External n × External n → Bool)
    (kind : External n × External n → Kind) (events : List (External n × External n))
    (clock : ℕ) (states : States n) (state : WeightedMemory.State (External n))
    (history : LabelHistory.History (External n)) (current : LabelHistory.current history = state.label)
    (prefixLabels : ∀ index, index ≤ events.length →
      (run state (program comparator.externalDepth kind (events.take index))).label = labels comparator K
        (runLinks source sourceSide (fun _ current => GreedyMerge.StateLabels.label comparator.externalDepth K current)
          clock states (events.take index))) :
    let finalHistory := LabelSnapshots.accessHistory comparator K source sourceSide clock states events history
    LabelHistory.current finalHistory = (run state (program comparator.externalDepth kind events)).label ∧
      LabelHistory.variation finalHistory = LabelHistory.variation history + total absoluteChange state (program comparator.externalDepth kind events) := by
  induction events generalizing clock states state history with
  | nil => exact ⟨current, by simp [LabelSnapshots.accessHistory, program, total]⟩
  | cons event rest ih =>
      let entry := arrivalEntry (GreedyMerge.StateLabels.label comparator.externalDepth K states) event.1 event.2 clock
      let next := linkState states source event.1 event.2 (sourceSide event) (targetSide event) entry
      let nextState := advance comparator.externalDepth kind state event
      let nextHistory := LabelHistory.update history clock (labels comparator K next)
      have firstLabels := prefixLabels 1 (by simp)
      change nextState.label = labels comparator K next at firstLabels
      have nextCurrent : LabelHistory.current nextHistory = nextState.label :=
        (LabelHistory.current_update ..).trans firstLabels.symm
      have headVariation : LabelHistory.variation nextHistory = LabelHistory.variation history +
          |(contractedGap (comparator.externalDepth event.2.val - comparator.externalDepth event.1.val) : ℤ) - state.label event.2| := by
        change LabelHistory.variation (LabelHistory.update history clock (labels comparator K next)) = _
        rw [← firstLabels]
        exact LabelHistory.update_single_variation history clock state event.2 _ current
      have tailLabels : ∀ index, index ≤ rest.length →
          (run nextState (program comparator.externalDepth kind (rest.take index))).label = labels comparator K
            (runLinks source sourceSide (fun _ current => GreedyMerge.StateLabels.label comparator.externalDepth K current)
              (clock+1) next (rest.take index)) := by
        intro index inside
        have previous := prefixLabels (index+1) (by simp only [List.length_cons]; omega)
        simpa only [List.take_succ_cons, program, run, runLinks, nextState, advance, next, entry] using previous
      have tail := ih (clock+1) next nextState nextHistory nextCurrent tailLabels
      dsimp only
      refine ⟨tail.1, ?_⟩
      change LabelHistory.variation
        (LabelSnapshots.accessHistory comparator K source sourceSide (clock+1) next rest nextHistory) = _
      rw [tail.2, headVariation]
      change LabelHistory.variation history + _ + total absoluteChange nextState (program comparator.externalDepth kind rest) =
        LabelHistory.variation history + (0 + (_ + total absoluteChange nextState (program comparator.externalDepth kind rest)))
      simp only [zero_add, add_assoc, absoluteChange, step, EntryJournal.encode, WeightedMemory.step]

theorem actual_history_agrees {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (geometry : AccessTrace.Geometry data source) (K : ℤ) (clock : ℕ)
    (states : States n) (ready : Ready comparator oldTree states)
    (empty : ∀ side, growerEntries (states source side).grower = [])
    (state : WeightedMemory.State (External n)) (agree : state.label = labels comparator K states)
    (history : LabelHistory.History (External n)) (current : LabelHistory.current history = state.label) :
    let finalHistory := LabelSnapshots.accessHistory comparator K source (fun event => decide (event.2.val < source.val)) clock states data.events history
    let actions := program comparator.externalDepth (AccessTrace.kind states source) data.events
    LabelHistory.current finalHistory = (run state actions).label ∧
      LabelHistory.variation finalHistory = LabelHistory.variation history + total absoluteChange state actions :=
  history_program_agrees comparator K source _ _ data.events clock states state history current
    (actual_prefix data source geometry K clock states ready empty state agree)

end Greedy.AccessJournal
