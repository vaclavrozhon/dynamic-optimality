import DynamicOptimality.GeometricOnlineSimulation.Queue

/-!
# Splitting at an existing separator

Pop from the nearer end, then insert the removed separators into the new
component while unwinding. All intermediate endpoints are literal trees.
The two output deque potentials are charged against the input potential.
-/

namespace DynamicOptimality.GeometricOnlineSimulation.Queue

open ChaCha.MTR SearchRotation DynamicOptimality.SingleFinger

variable {α : Type*}

theorem split_from_left (queue : Queue α) (before after : List (Spine.Cell α))
    (pivot : α) (gap : RawTree α) (word : queue.cells = before ++ (pivot, gap) :: after) :
    ∃ (left right : Queue α) (count : Nat),
      left.firstGap = queue.firstGap ∧ left.cells = before ∧
      right.firstGap = gap ∧ right.cells = after ∧
      Rotations queue.tree (.node left.tree pivot right.tree) count ∧
      count + left.potential + right.potential ≤ queue.potential + 20 * (before.length + 1) := by
  induction before generalizing queue with
  | nil =>
      obtain ⟨right, key, count, cells, run, bound⟩ := queue.pop_min (by simp [word])
      have equal := List.cons.inj (cells.symm.trans word)
      have keyEq : key = pivot := congrArg Prod.fst equal.1
      have gapEq : right.firstGap = gap := congrArg Prod.snd equal.1
      subst key
      exact ⟨.gap queue.firstGap, right, count, rfl, rfl, gapEq, equal.2, run, by
        change count + 0 + right.potential ≤ queue.potential + 20 * (0 + 1)
        omega⟩
  | cons cell before ih =>
      rcases cell with ⟨first, next⟩
      obtain ⟨rest, key, pop, cells, firstRun, firstBound⟩ := queue.pop_min (by simp [word])
      have equal := List.cons.inj (cells.symm.trans word)
      have keyEq : key = first := congrArg Prod.fst equal.1
      have gapEq : rest.firstGap = next := congrArg Prod.snd equal.1
      subst key
      obtain ⟨left, right, split, sameFirst, leftCells, rightFirst, rightCells, middleRun, middleBound⟩ :=
        ih rest equal.2
      obtain ⟨push, pushBound, lastRun, lastBound⟩ := left.push_min first queue.firstGap
      refine ⟨left.pushMin first queue.firstGap, right, pop + split + 1 + push,
        pushMin_first _ _ _, ?_, rightFirst, rightCells, ?_, ?_⟩
      · simp only [pushMin_cells, sameFirst, gapEq, leftCells]
      · have inside := middleRun.plug [Pointer.Frame.right queue.firstGap first]
        have promoted : Rotations (.node queue.firstGap first (.node left.tree pivot right.tree))
            (.node (.node queue.firstGap first left.tree) pivot right.tree) 1 :=
          .singleton (.rootLeft _ _ _ _ _)
        have outside := lastRun.plug [Pointer.Frame.left pivot right.tree]
        exact ((firstRun.append inside).append promoted).append outside
      · simp only [List.length_cons]
        omega

theorem split_from_right (queue : Queue α) (before after : List (Spine.Cell α))
    (pivot : α) (gap : RawTree α) (word : queue.cells = before ++ (pivot, gap) :: after) :
    ∃ (left right : Queue α) (count : Nat),
      left.firstGap = queue.firstGap ∧ left.cells = before ∧
      right.firstGap = gap ∧ right.cells = after ∧
      Rotations queue.tree (.node left.tree pivot right.tree) count ∧
      count + left.potential + right.potential ≤ queue.potential + 20 * (after.length + 1) := by
  induction after using List.reverseRecOn generalizing queue with
  | nil =>
      obtain ⟨left, key, lastGap, count, cells, sameFirst, run, bound⟩ :=
        queue.pop_max (by simp [word])
      have equal := List.append_inj' (cells.symm.trans word) (by rfl)
      have pair : (key, lastGap) = (pivot, gap) := List.cons.inj equal.2 |>.1
      have keyEq : key = pivot := congrArg Prod.fst pair
      have gapEq : lastGap = gap := congrArg Prod.snd pair
      subst key
      subst lastGap
      exact ⟨left, .gap gap, count, sameFirst, equal.1, rfl, rfl, run, by
        change count + left.potential + 0 ≤ queue.potential + 20 * (0 + 1)
        omega⟩
  | append_singleton after cell ih =>
      rcases cell with ⟨last, lastGap⟩
      obtain ⟨rest, key, endGap, pop, cells, sameStart, firstRun, firstBound⟩ :=
        queue.pop_max (by simp [word])
      have expanded : rest.cells ++ [(key, endGap)] =
          (before ++ (pivot, gap) :: after) ++ [(last, lastGap)] := by
        simpa only [List.append_assoc, List.cons_append] using cells.symm.trans word
      have equal := List.append_inj' expanded (by rfl)
      have pair : (key, endGap) = (last, lastGap) := List.cons.inj equal.2 |>.1
      have keyEq : key = last := congrArg Prod.fst pair
      have gapEq : endGap = lastGap := congrArg Prod.snd pair
      subst key
      subst endGap
      obtain ⟨left, right, split, sameFirst, leftCells, rightFirst, rightCells, middleRun, middleBound⟩ :=
        ih rest equal.1
      obtain ⟨push, pushBound, lastRun, lastBound⟩ := right.push_max last lastGap
      refine ⟨left, right.pushMax last lastGap, pop + split + 1 + push,
        sameFirst.trans sameStart, leftCells, ?_, ?_, ?_, ?_⟩
      · simpa only [pushMax_first] using rightFirst
      · simp only [pushMax_cells, rightCells]
      · have inside := middleRun.plug [Pointer.Frame.left last lastGap]
        have promoted : Rotations (.node (.node left.tree pivot right.tree) last lastGap)
            (.node left.tree pivot (.node right.tree last lastGap)) 1 :=
          .singleton (.rootRight _ _ _ _ _)
        have outside := lastRun.plug [Pointer.Frame.right left.tree pivot]
        exact ((firstRun.append inside).append promoted).append outside
      · simp only [List.length_append, List.length_singleton]
        omega

theorem split (queue : Queue α) (before after : List (Spine.Cell α))
    (pivot : α) (gap : RawTree α) (word : queue.cells = before ++ (pivot, gap) :: after) :
    ∃ (left right : Queue α) (count : Nat),
      left.firstGap = queue.firstGap ∧ left.cells = before ∧
      right.firstGap = gap ∧ right.cells = after ∧
      Rotations queue.tree (.node left.tree pivot right.tree) count ∧
      count + left.potential + right.potential ≤
        queue.potential + 20 * (min before.length after.length + 1) := by
  rcases le_total before.length after.length with smaller | smaller
  · rw [min_eq_left smaller]
    exact split_from_left queue before after pivot gap word
  · rw [min_eq_right smaller]
    exact split_from_right queue before after pivot gap word

end DynamicOptimality.GeometricOnlineSimulation.Queue
