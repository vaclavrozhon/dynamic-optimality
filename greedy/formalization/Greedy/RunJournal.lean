import Greedy.AccessCensus
import Greedy.RotationJournal
import Greedy.ExecutionRun

/-!
# A chronological label and entry journal for a whole shared execution

The journal executes all actual access links and all administrative
restorations, preserving exact state labels at every macro boundary.
Its ordinary-entry count is derived from the comparator rotation count;
access links never count as ordinary administrative entries.
-/

namespace Greedy.RunJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau
open EntryJournal RestorationJournal

noncomputable def prepared {n : ℕ} (state : Execution.State n) (request : Fin n) : HeapSides n :=
  (convertHeap state.comparator.externalDepth
    (fun owner _ => decide (owner = Execution.source request)) state.next state.blocks).1

noncomputable def access {n : ℕ} (state : Execution.State n) (request : Fin n)
    (decomposition : Decomposition state.refined.tree request.val)
    (data : AccessScheduleData state.comparator state.refined.tree (Execution.afterRefinement state request).tree decomposition) :
    List (Action (External n)) :=
  AccessJournal.program state.comparator.externalDepth
    (AccessTrace.kind (prepared state request) (Execution.source request)) data.events

theorem access_spec {n : ℕ} (state : Execution.State n) (request : Fin n)
    (decomposition : Decomposition state.refined.tree request.val)
    (data : AccessScheduleData state.comparator state.refined.tree (Execution.afterRefinement state request).tree decomposition)
    (H : ℕ) (height : state.comparator.height ≤ H) (valid : state.Valid)
    (root : state.comparator.HasRoot request.val)
    (journalState : WeightedMemory.State (External n))
    (agree : journalState.label = labels state.comparator (contractedGap H) state.blocks) :
    let actions := access state request decomposition data
    let after := Execution.afterAccess state request (contractedGap H) decomposition data
    EntryJournal.Valid (contractedGap H) journalState actions ∧
      (run journalState actions).label = labels after.comparator (contractedGap H) after.blocks ∧
      total ordinary journalState actions = 0 := by
  let source := Execution.source request
  have convertEq := convertRoot_eq_convertHeap state.comparator.externalDepth source state.next state.blocks
  change convertRoot state.comparator.externalDepth source (rootNames source state.next)
    (rootNames source state.next) state.blocks = prepared state request at convertEq
  have ready : Ready state.comparator state.refined.tree (prepared state request) := by
    rw [← convertEq]
    exact convertRoot_ready state.comparator state.refined.tree source (rootNames source state.next)
      (rootNames source state.next) state.blocks valid.1
  have empty : ∀ side, growerEntries (prepared state request source side).grower = [] := by
    intro side
    rw [← convertEq]
    exact convertRoot_empty state.comparator.externalDepth source _ _ state.blocks side
  have preparedAgree : journalState.label = labels state.comparator (contractedGap H) (prepared state request) := by
    rw [agree]
    funext record
    change GreedyMerge.StateLabels.label _ _ _ record.val = GreedyMerge.StateLabels.label _ _ _ record.val
    rw [← convertEq, convertRoot_labels]
  have geometry := AccessTrace.geometry data source rfl (Execution.root_minimum _ request root)
  have validJournal := AccessJournal.actual_valid data source geometry H state.clock height
    (prepared state request) ready empty journalState preparedAgree
  have finalLabels := AccessJournal.actual_prefix data source geometry (contractedGap H) state.clock
    (prepared state request) ready empty journalState preparedAgree data.events.length (le_refl _)
  simp only [List.take_length] at finalLabels
  refine ⟨validJournal, ?_, ?_⟩
  · simpa only [AccessTrace.current, List.take_length, access, Execution.afterAccess, source, prepared] using finalLabels
  · exact AccessJournal.program_ordinary_zero _ _ data.events
      (fun event _ => AccessTrace.kind_not_ordinary _ _ event) journalState

theorem initial_height {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)}
    (run : Execution.Run K first last requests) (H : ℕ) (bounded : run.Bounded H) : first.comparator.height ≤ H := by
  cases run with
  | done => exact bounded
  | rotate => exact bounded.1
  | access => exact bounded.1

/-- This constructs the journal from the retained execution, rather than
requiring one as a certificate. The initial creator memory may be arbitrary;
initial memberships are installed separately before applying this theorem. -/
theorem exists_journal {n : ℕ} {first last : Execution.State n} {requests : List (Fin n)}
    (H : ℕ) (execution : Execution.Run (contractedGap H) first last requests)
    (bounded : execution.Bounded H) (valid : first.Valid)
    (state : WeightedMemory.State (External n))
    (agree : state.label = labels first.comparator (contractedGap H) first.blocks) :
    ∃ actions : List (Action (External n)),
      EntryJournal.Valid (contractedGap H) state actions ∧
      (run state actions).label = labels last.comparator (contractedGap H) last.blocks ∧
      total ordinary state actions ≤ 11 * execution.rotations ∧
      total internal state actions + total boundary state actions = execution.links := by
  induction execution generalizing state with
  | done initial => exact ⟨[], trivial, agree, by simp [total, Execution.Run.rotations], by simp [total, Execution.Run.links]⟩
  | @rotate first last after depth requests rotation data afterValid rest ih =>
      obtain ⟨head, headValid, headLabels, headOrdinary, _headPositive, headKinds⟩ :=
        RotationJournal.complete_rotation first after rotation H bounded.1 (initial_height rest H bounded.2)
          valid data state agree
      obtain ⟨tail, tailValid, tailLabels, tailOrdinary, tailCount⟩ := ih bounded.2 afterValid (run state head) headLabels
      refine ⟨head ++ tail, (valid_append ..).mpr ⟨headValid, tailValid⟩, ?_, ?_, ?_⟩
      · rw [run_append]; exact tailLabels
      · rw [total_append]
        simp only [Execution.Run.rotations, Nat.cast_add, Nat.cast_one]
        linarith
      · rw [total_append, total_append, ordinaryOnly_internal_zero state head headKinds,
          ordinaryOnly_boundary_zero state head headKinds, zero_add, zero_add]
        exact tailCount
  | @access first last requests request root decomposition data afterValid rest ih =>
      let head := access first request decomposition data
      have firstSpec := access_spec first request decomposition data H bounded.1 valid root state agree
      obtain ⟨tail, tailValid, tailLabels, tailOrdinary, tailCount⟩ := ih bounded.2 afterValid (run state head) firstSpec.2.1
      refine ⟨head ++ tail, (valid_append ..).mpr ⟨firstSpec.1, tailValid⟩, ?_, ?_, ?_⟩
      · rw [run_append]; exact tailLabels
      · rw [total_append]
        have zero : total ordinary state head = 0 := firstSpec.2.2
        rw [zero, zero_add]
        exact tailOrdinary

      · rw [total_append, total_append]
        have headCount : total internal state head + total boundary state head = data.events.length :=
          AccessJournal.program_link_count _ _ data.events
            (fun event _ => AccessTrace.kind_not_ordinary _ _ event) state
        simp only [Execution.Run.links, Nat.cast_add]
        linarith

end Greedy.RunJournal
