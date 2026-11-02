import DynamicOptimality.GeometricOnlineSimulation.Component
import DynamicOptimality.GeometricOnlineSimulation.AbsorbFragment

/-!
# Splitting a perfect block at the first deque gap

The block path is exposed inside the literal existing gap. Its selected key
crosses a port of depth at most two. Newly exposed sibling blocks are then
absorbed into the old deque, whose other gaps remain unchanged.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR ChaCha.MTR.Pointer SearchRotation DynamicOptimality.SingleFinger
open DynamicOptimality.MultiFinger.TendonDeque

theorem BlockCut.connecting_count {level : Nat} {tree : RawTree Nat} {key : Nat}
    (cut : BlockCut level tree key) :
    cut.left.marked.skeleton.size + cut.right.marked.skeleton.size + 1 = cut.steps := by
  have keys := congrArg List.length cut.same_keys
  simp only [List.length_append, List.length_singleton, Tree.length_inorder, cut.source_size] at keys
  omega

theorem cut_first_gap (queue : Queue Nat) {level key : Nat}
    (cut : BlockCut level queue.firstGap key) :
    ∃ (left right : Queue Nat) (count : Nat),
      left.marked.holes = cut.left.marked.holes ∧
      right.marked.holes = cut.right.marked.holes ++ queue.cells.map Prod.snd ∧
      Rotations queue.tree (.node left.tree key right.tree) count ∧
      count + left.potential + right.potential ≤ queue.potential + 20 * cut.steps + 20 := by
  have size := cut.connecting_count
  obtain ⟨split, splitBound, splitRun⟩ := cut.rotations
  obtain ⟨left, leftCount, leftHoles, leftKeys, leftRun, leftBound⟩ := cut.left.to_queue
  cases queue with
  | gap tree =>
      obtain ⟨right, rightCount, rightHoles, rightKeys, rightRun, rightBound⟩ := cut.right.to_queue
      have leftLift := leftRun.plug [Pointer.Frame.left key cut.right.marked.erase]
      have rightLift := rightRun.plug [Pointer.Frame.right left.tree key]
      refine ⟨left, right, split + leftCount + rightCount, leftHoles, ?_,
        (splitRun.append leftLift).append rightLift, ?_⟩
      · simpa only [Queue.cells, List.map_nil, List.append_nil] using rightHoles
      · change split + leftCount + rightCount + left.potential + right.potential ≤
          0 + 20 * cut.steps + 20
        omega
  | deque layout =>
      let outer := asLeft layout
      let chain := Chain.ofMarked cut.right.marked
      let right := Queue.deque ((outer.absorb chain.cells).fill chain.first)
      obtain ⟨extract, extractBound, extractRun⟩ :=
        outer.port.extract cut.left.marked.erase cut.right.marked.erase key
      obtain ⟨rightCount, rightRun, rightBound⟩ := outer.absorb_fragment cut.right
      have source : (outer.fill layout.gap).tree = layout.tree := by rw [asLeft_fill]
      have splitLift : Rotations layout.tree
          (outer.fill (.node cut.left.marked.erase key cut.right.marked.erase)).tree split := by
        have lifted := outer.port.lift splitRun
        simpa only [← OpenDeque.Left.fill_tree, Queue.firstGap, source] using lifted
      have expose : Rotations (outer.fill (.node cut.left.marked.erase key cut.right.marked.erase)).tree
          (.node cut.left.marked.erase key (outer.fill cut.right.marked.erase).tree) extract := by
        simpa only [OpenDeque.Left.fill_tree] using extractRun
      have leftLift := leftRun.plug [Pointer.Frame.left key (outer.fill cut.right.marked.erase).tree]
      have rightLift := rightRun.plug [Pointer.Frame.right left.tree key]
      have rightHoles : right.marked.holes = cut.right.marked.holes ++ layout.cells.map Prod.snd := by
        change ((Queue.deque ((outer.absorb chain.cells).fill chain.first)).marked).holes = _
        rw [Queue.marked_holes]
        change chain.first :: (((outer.absorb chain.cells).fill chain.first).cells.map Prod.snd) = _
        rw [OpenDeque.Left.absorb_cells]
        have cells : (outer.fill chain.first).cells = layout.cells := rfl
        rw [cells, List.map_append, ← List.cons_append]
        rw [Chain.holes_ofMarked]
      have rightPotential : right.potential = (outer.absorb chain.cells).potential :=
        OpenDeque.Left.fill_potential _ _
      have oldPotential : outer.potential = layout.potential := asLeft_potential layout
      refine ⟨left, right, split + extract + leftCount + rightCount, leftHoles, rightHoles,
        ((splitLift.append expose).append leftLift).append rightLift, ?_⟩
      change split + extract + leftCount + rightCount + left.potential + right.potential ≤
        layout.potential + 20 * cut.steps + 20
      rw [rightPotential]
      change rightCount + (outer.absorb chain.cells).potential ≤
        outer.potential + 11 * cut.right.marked.skeleton.size at rightBound
      rw [oldPotential] at rightBound
      omega

end DynamicOptimality.GeometricOnlineSimulation
