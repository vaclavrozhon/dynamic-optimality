import Greedy.ExecutionState

/-!
# Executing a comparator rotation and its recanonicalization

One actual comparator rotation first runs the fresh comparator macro.
The canonical-surface theorem then constructs at most two fixed-rank
refinement rotations. Their fresh executions are retained in the returned
witness. All final invariants refer to the resulting literal block state.
-/

namespace Greedy.Execution

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks

noncomputable def rotatedRefinement {n : ℕ} (state : State n) (after : BST 0 n) :
    Refinement state.surface after := refinement state.surface after

noncomputable def rotationPrefix {n depth : ℕ} (state : State n) (after : BST 0 n)
    (rotation : RotationAt depth state.comparator after) (K : ℤ) : FreshRecanonicalization.Frame n :=
  let result := FreshComparator.allocate rotation state.refined.tree
    (entryReader after K state.clock) state.next state.blocks
  ⟨state.refined.tree, result.states, state.clock+4, result.next⟩

noncomputable def rotationBirths {n depth : ℕ} (state : State n) (after : BST 0 n)
    (rotation : RotationAt depth state.comparator after) (K : ℤ) : List ℕ :=
  FreshComparator.birthJournal rotation state.refined.tree
    (entryReader after K state.clock) state.next state.blocks

structure RotationData {n depth : ℕ} (state : State n) (after : BST 0 n)
    (rotation : RotationAt depth state.comparator after) (K : ℤ) where
  steps : ℕ
  fewSteps : steps ≤ 2
  finalFrame : FreshRecanonicalization.Frame n
  refinementJournal : List ℕ
  executed : FreshRecanonicalization.Execution after (entryReader after K) steps
    (rotationPrefix state after rotation K) finalFrame refinementJournal
  finalTree : finalFrame.tree = (rotatedRefinement state after).tree

noncomputable def RotationData.state {n depth : ℕ} {before : State n} {after : BST 0 n}
    {rotation : RotationAt depth before.comparator after} {K : ℤ}
    (data : RotationData before after rotation K) : State n :=
  ⟨before.surface, before.time, after, rotatedRefinement before after,
    data.finalFrame.states, data.finalFrame.clock, data.finalFrame.next⟩

noncomputable def RotationData.journal {n depth : ℕ} {before : State n} {after : BST 0 n}
    {rotation : RotationAt depth before.comparator after} {K : ℤ}
    (data : RotationData before after rotation K) : List ℕ :=
  rotationBirths before after rotation K ++ data.refinementJournal

theorem rotation_exists {n depth : ℕ} (state : State n) (after : BST 0 n)
    (rotation : RotationAt depth state.comparator after) (K : ℤ) (valid : state.Valid) :
    ∃ data : RotationData state after rotation K, data.state.Valid ∧
      state.next ≤ data.state.next ∧ data.journal.length ≤ 4*(depth+2)^2+63 ∧
      data.state.clock ≤ state.clock+14 ∧ SupportsIds state.blocks data.state.blocks data.journal := by
  let preparedFrame := rotationPrefix state after rotation K
  have first := FreshComparator.rotation_spec rotation state.refined.tree (entryReader after K state.clock)
    (fun _ _ _ _ => rfl) (state.clock+1) (fun _ _ _ _ => rfl) state.next state.blocks valid.1
    (valid.2.1.mono (by omega)) valid.2.2.1
  have prefixValid : preparedFrame.Valid after := ⟨first.1, first.2.1, first.2.2.1⟩
  let refined := rotatedRefinement state after
  obtain ⟨steps, few, rotations⟩ := GreedyMerge.CanonicalBridge.actual_canonical_rotationAt rotation
    state.refined.owner refined.owner state.refined.owners refined.owners state.refined.tree refined.tree
    state.refined.canonical refined.canonical
  obtain ⟨last, journal, execution, treeEq, finalValid, clockEq, counter, budget, support⟩ :=
    FreshRecanonicalization.execute_steps after (entryReader after K)
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) preparedFrame refined.tree rotations prefixValid
  let data : RotationData state after rotation K := ⟨steps, few, last, journal, execution, treeEq⟩
  refine ⟨data, ?_, first.2.2.2.1.trans counter, ?_, ?_, supportsIds_trans first.2.2.2.2.2 support⟩
  · refine ⟨?_, finalValid.2.1, finalValid.2.2, valid.2.2.2⟩
    change Ready after refined.tree last.states
    rw [← treeEq]
    exact finalValid.1
  · have firstBudget : (rotationBirths state after rotation K).length ≤ 4*(depth+2)^2+23 :=
      first.2.2.2.2.1
    change (rotationBirths state after rotation K ++ journal).length ≤ _
    simp only [List.length_append]
    omega
  · change last.clock ≤ state.clock+14
    change last.clock = state.clock+4+5*steps at clockEq
    omega

end Greedy.Execution
