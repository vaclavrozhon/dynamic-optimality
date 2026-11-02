import DynamicOptimality.GeometricOnlineSimulation.GapBoundary

/-! The symmetric physical split at the last deque gap. -/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR ChaCha.MTR.Pointer SearchRotation DynamicOptimality.SingleFinger
open DynamicOptimality.MultiFinger.TendonDeque

def Queue.lastGap (queue : Queue Nat) : RawTree Nat := trailing queue.firstGap queue.cells

@[simp] theorem OpenDeque.Right.fill_gap (outer : OpenDeque.Right Nat) (gap : RawTree Nat) :
    (outer.fill gap).gap = outer.gap := by
  cases outer with
  | mk first front pivot back => cases back <;> rfl

def OpenDeque.Right.prior (outer : OpenDeque.Right Nat) : List (RawTree Nat) :=
  outer.gap :: outer.front.map Prod.snd ++ match outer.back with
    | none => []
    | some (afterGap, back, _) => afterGap :: back.map Prod.snd

theorem OpenDeque.Right.holes (outer : OpenDeque.Right Nat) (gap : RawTree Nat) :
    (Queue.deque (outer.fill gap)).marked.holes = outer.prior ++ [gap] := by
  cases outer with
  | mk first front pivot back =>
      cases back with
      | none =>
          simp [Queue.marked_holes, Queue.firstGap, Queue.cells, OpenDeque.Right.fill,
            OpenDeque.Right.prior, Deque.Layout.cells, List.append_assoc]
      | some data =>
          rcases data with ⟨afterGap, back, last⟩
          simp [Queue.marked_holes, Queue.firstGap, Queue.cells, OpenDeque.Right.fill,
            OpenDeque.Right.prior, Deque.Layout.cells, List.append_assoc]

theorem cut_last_gap (queue : Queue Nat) {level key : Nat}
    (cut : BlockCut level queue.lastGap key) :
    ∃ (left right : Queue Nat) (count : Nat) (prior : List (RawTree Nat)),
      queue.marked.holes = prior ++ [queue.lastGap] ∧
      left.marked.holes = prior ++ cut.left.marked.holes ∧
      right.marked.holes = cut.right.marked.holes ∧
      Rotations queue.tree (.node left.tree key right.tree) count ∧
      count + left.potential + right.potential ≤ queue.potential + 20 * cut.steps + 20 := by
  have size := cut.connecting_count
  cases queue with
  | gap tree =>
      obtain ⟨left, right, count, leftHoles, rightHoles, run, cost⟩ := cut_first_gap (.gap tree) cut
      exact ⟨left, right, count, [], rfl, leftHoles,
        by simpa only [Queue.cells, List.map_nil, List.append_nil] using rightHoles, run, cost⟩
  | deque layout =>
      obtain ⟨outer, filled, oldPotential⟩ := open_right layout
      let chain := Chain.ofMarked cut.left.marked
      let left := Queue.deque ((outer.absorb chain.first chain.cells).fill (trailing chain.first chain.cells))
      obtain ⟨split, splitBound, splitRun⟩ := cut.rotations
      obtain ⟨extract, extractBound, extractRun⟩ :=
        outer.port.extract cut.left.marked.erase cut.right.marked.erase key
      obtain ⟨leftCount, leftRun, leftBound⟩ := outer.absorb_fragment cut.left
      obtain ⟨right, rightCount, rightHoles, rightKeys, rightRun, rightBound⟩ := cut.right.to_queue
      have splitLift : Rotations layout.tree
          (outer.fill (.node cut.left.marked.erase key cut.right.marked.erase)).tree split := by
        have lifted := outer.port.lift splitRun
        have initial : (outer.fill (Queue.deque layout).lastGap).tree = layout.tree := by
          change (outer.fill (terminal layout)).tree = layout.tree
          rw [filled]
        simpa only [← OpenDeque.Right.fill_tree, initial] using lifted
      have expose : Rotations (outer.fill (.node cut.left.marked.erase key cut.right.marked.erase)).tree
          (.node (outer.fill cut.left.marked.erase).tree key cut.right.marked.erase) extract := by
        simpa only [OpenDeque.Right.fill_tree] using extractRun
      have leftLift := leftRun.plug [Pointer.Frame.left key cut.right.marked.erase]
      have rightLift := rightRun.plug [Pointer.Frame.right left.tree key]
      have leftHoles : left.marked.holes = outer.prior ++ cut.left.marked.holes := by
        rw [Queue.marked_holes]
        change ((outer.absorb chain.first chain.cells).fill (trailing chain.first chain.cells)).gap ::
          (((outer.absorb chain.first chain.cells).fill (trailing chain.first chain.cells)).cells.map Prod.snd) = _
        rw [OpenDeque.Right.fill_gap, OpenDeque.Right.absorb_gap, OpenDeque.Right.absorb_cells,
          List.map_append, ← List.cons_append]
        have first : outer.gap :: (outer.fill chain.first).cells.map Prod.snd =
            outer.prior ++ [chain.first] := by
          have same := outer.holes chain.first
          rw [Queue.marked_holes] at same
          simpa only [Queue.firstGap, Queue.cells, OpenDeque.Right.fill_gap] using same
        rw [first, List.append_assoc, List.singleton_append, Chain.holes_ofMarked]
      have beforeHoles : (Queue.deque layout).marked.holes = outer.prior ++ [(Queue.deque layout).lastGap] := by
        rw [← filled]
        have terminalEq : (Queue.deque (outer.fill (terminal layout))).lastGap = terminal layout :=
          right_terminal outer _
        rw [terminalEq]
        exact outer.holes _
      have leftPotential : left.potential = (outer.absorb chain.first chain.cells).potential :=
        OpenDeque.Right.fill_potential _ _
      refine ⟨left, right, split + extract + leftCount + rightCount, outer.prior,
        beforeHoles, leftHoles, rightHoles,
        ((splitLift.append expose).append leftLift).append rightLift, ?_⟩
      change split + extract + leftCount + rightCount + left.potential + right.potential ≤
        layout.potential + 20 * cut.steps + 20
      rw [leftPotential]
      change leftCount + (outer.absorb chain.first chain.cells).potential ≤
        outer.potential + 11 * cut.left.marked.skeleton.size at leftBound
      rw [oldPotential] at leftBound
      omega

end DynamicOptimality.GeometricOnlineSimulation
