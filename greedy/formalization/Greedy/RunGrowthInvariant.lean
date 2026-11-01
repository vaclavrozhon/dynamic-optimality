import Greedy.GrowthAdministrationInvariant
import Greedy.ExecutionRun

/-!
# Full historical family coverage for a shared execution

Every live frozen fragment either has one constant join time or is covered
by the preserved chronological batch of its actual creator. This invariant
is constructed from initialization and preserved through all literal
access, comparator, and recanonicalization operations.
-/

namespace Greedy.GrowthJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.GrowthBook GreedyMerge.GrowthWindows
open FreshRecanonicalization

theorem refinement_execution_history {n count : ℕ} (comparator : BST 0 n) (reader : Reader n)
    {first last : Frame n} {births : List ℕ}
    (execution : FreshRecanonicalization.Execution comparator reader count first last births)
    (books : HeapBooks n) (good : Invariant first.clock first.next first.states books) :
    ∃ finalBooks, Invariant last.clock last.next last.states finalBooks ∧ HeapExtends books finalBooks := by
  induction execution generalizing books with
  | nil => exact ⟨books, good, HeapExtends.refl _⟩
  | @cons count depth first last middle births rotation rest ih =>
      let ports := refinementRotationPorts (Snapshot.ofTree comparator) rotation
      let nextBooks := refinementBooks comparator middle ports (reader first.clock) first.next first.states books
      have head := refinementBooks_invariant comparator middle ports (reader first.clock) first.clock first.next first.states books good
      have advanced : Invariant (first.clock+5)
          (FreshRecanonicalization.allocate comparator middle ports (reader first.clock) first.next first.states).next
          (FreshRecanonicalization.allocate comparator middle ports (reader first.clock) first.next first.states).states nextBooks :=
        Invariant.advance head _ _ (by omega) (le_refl _)
      obtain ⟨finalBooks, finalGood, tail⟩ := ih nextBooks advanced
      exact ⟨finalBooks, finalGood, (refinementBooks_extends comparator middle ports (reader first.clock)
        first.next first.states books).trans tail⟩

theorem complete_rotation_history {n depth : ℕ} (before : Greedy.Execution.State n) (after : BST 0 n)
    (rotation : RotationAt depth before.comparator after) (K : ℤ)
    (data : Greedy.Execution.RotationData before after rotation K)
    (books : HeapBooks n) (good : Invariant before.clock before.next before.blocks books) :
    ∃ finalBooks, Invariant data.state.clock data.state.next data.state.blocks finalBooks ∧ HeapExtends books finalBooks := by
  let input := comparatorInput rotation
  let plan := GreedyMerge.ComparatorOuter.rotationPlan input.step before.refined.tree
  let reader := Greedy.Execution.entryReader after K before.clock
  let nextBooks := comparatorBooks input.profile before.refined.tree plan reader before.next before.blocks books
  have head := comparatorBooks_invariant input.profile before.refined.tree plan reader before.clock before.next before.blocks books good
  have advanced : Invariant (before.clock+4) (Greedy.Execution.rotationPrefix before after rotation K).next
      (Greedy.Execution.rotationPrefix before after rotation K).states nextBooks :=
    Invariant.advance head _ _ (by omega) (le_refl _)
  obtain ⟨finalBooks, finalGood, tail⟩ :=
    refinement_execution_history after (Greedy.Execution.entryReader after K) data.executed nextBooks advanced
  exact ⟨finalBooks, finalGood,
    (comparatorBooks_extends input.profile before.refined.tree plan reader before.next before.blocks books).trans tail⟩

theorem access_history {n : ℕ} (before : Greedy.Execution.State n) (request : Fin n) (K : ℤ)
    (decomposition : GreedyMerge.PathPlateau.Decomposition before.refined.tree request.val)
    (data : GreedyMerge.ActualLinks.AccessScheduleData before.comparator before.refined.tree
      (Greedy.Execution.afterRefinement before request).tree decomposition)
    (books : HeapBooks n) (good : Invariant before.clock before.next before.blocks books) :
    ∃ finalBooks, Invariant (Greedy.Execution.afterAccess before request K decomposition data).clock
      (Greedy.Execution.afterAccess before request K decomposition data).next
      (Greedy.Execution.afterAccess before request K decomposition data).blocks finalBooks ∧ HeapExtends books finalBooks := by
  let selected := fun (owner : External n) (_ : Bool) => decide (owner = Greedy.Execution.source request)
  let converted := (convertHeap before.comparator.externalDepth selected before.next before.blocks).1
  let nextBooks := convertHeapBooks selected before.next before.blocks books
  have convertedGood := convertHeap_invariant before.comparator.externalDepth selected before.next before.blocks books good
  exact ⟨runBook before.clock nextBooks data.events,
    runBook_invariant (Greedy.Execution.source request) _ _ before.clock _ converted nextBooks data.events convertedGood,
    (convertHeapBooks_extends selected before.next before.blocks books).trans (runBook_extends before.clock nextBooks data.events)⟩

/-- The book is built from the entire retained execution, including all
administrative steps, rather than supplied as a growth-overlap premise. -/
theorem exists_history {n : ℕ} {K : ℤ} {first last : Greedy.Execution.State n} {requests : List (Fin n)}
    (execution : Greedy.Execution.Run K first last requests)
    (books : HeapBooks n) (good : Invariant first.clock first.next first.blocks books) :
    ∃ finalBooks, Invariant last.clock last.next last.blocks finalBooks ∧ HeapExtends books finalBooks := by
  induction execution generalizing books with
  | done => exact ⟨books, good, HeapExtends.refl _⟩
  | @rotate first last after depth requests rotation data valid rest ih =>
      obtain ⟨nextBooks, nextGood, head⟩ := complete_rotation_history first after rotation K data books good
      obtain ⟨finalBooks, finalGood, tail⟩ := ih nextBooks nextGood
      exact ⟨finalBooks, finalGood, head.trans tail⟩
  | @access first last requests request root decomposition data valid rest ih =>
      obtain ⟨nextBooks, nextGood, head⟩ := access_history first request K decomposition data books good
      obtain ⟨finalBooks, finalGood, tail⟩ := ih nextBooks nextGood
      exact ⟨finalBooks, finalGood, head.trans tail⟩

theorem initialized_history {n : ℕ} (initial comparator : BST 0 n) (K : ℤ)
    {last : Greedy.Execution.State n} {requests : List (Fin n)}
    (execution : Greedy.Execution.Run K (Greedy.Execution.initial initial comparator K) last requests) :
    ∃ finalBooks, Invariant last.clock last.next last.blocks finalBooks ∧
      HeapExtends (GreedyMerge.GrowthBook.initial (Snapshot.ofTree comparator)
        (Greedy.Execution.initial initial comparator K).refined.tree K) finalBooks :=
  exists_history execution (GreedyMerge.GrowthBook.initial (Snapshot.ofTree comparator)
    (Greedy.Execution.initial initial comparator K).refined.tree K)
    (initial_invariant (Snapshot.ofTree comparator) _ K)

end Greedy.GrowthJournal
