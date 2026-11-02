import DynamicOptimality.GeometricOnlineSimulation.GapTerminal

/-!
# Exposing an arbitrary block from the nearer deque end

Each transferred old separator costs at most twenty amortized rotations.
Only the selected block is expanded. Both output lists of untouched holes
are tracked exactly, so their perfect-block invariants can be transported.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR ChaCha.MTR.Pointer SearchRotation DynamicOptimality.SingleFinger
open DynamicOptimality.MultiFinger.TendonDeque

theorem cut_gap_left (queue : Queue Nat) (before after : List (RawTree Nat))
    {level key : Nat} {block : RawTree Nat} (cut : BlockCut level block key)
    (word : queue.marked.holes = before ++ block :: after) :
    ∃ (left right : Queue Nat) (count : Nat),
      left.marked.holes = before ++ cut.left.marked.holes ∧
      right.marked.holes = cut.right.marked.holes ++ after ∧
      Rotations queue.tree (.node left.tree key right.tree) count ∧
      count + left.potential + right.potential ≤
        queue.potential + 20 * cut.steps + 20 * (before.length + 1) := by
  induction before generalizing queue with
  | nil =>
      have equal := List.cons.inj ((Queue.marked_holes queue).symm.trans word)
      have selected : queue.firstGap = block := equal.1
      subst block
      obtain ⟨left, right, count, leftHoles, rightHoles, run, bound⟩ := cut_first_gap queue cut
      refine ⟨left, right, count, leftHoles, ?_, run, ?_⟩
      · simpa only [equal.2] using rightHoles
      · simpa only [List.length_nil] using bound
  | cons first before ih =>
      have nonempty : queue.cells ≠ [] := by
        intro empty
        have lengths := congrArg List.length word
        simp only [Queue.marked_holes, empty, List.map_nil, List.length_cons,
          List.length_nil, List.length_append] at lengths
        omega
      obtain ⟨rest, pivot, pop, cells, popRun, popBound⟩ := queue.pop_min nonempty
      have holes : queue.marked.holes = queue.firstGap :: rest.marked.holes := by
        simp only [Queue.marked_holes, cells, List.map_cons]
      have equal := List.cons.inj (holes.symm.trans word)
      obtain ⟨left, right, split, leftHoles, rightHoles, splitRun, splitBound⟩ := ih rest equal.2
      obtain ⟨push, pushCount, pushRun, pushBound⟩ := left.push_min pivot queue.firstGap
      refine ⟨left.pushMin pivot queue.firstGap, right, pop + split + 1 + push,
        ?_, rightHoles, ?_, ?_⟩
      · simp only [Queue.marked_holes, Queue.pushMin_first, Queue.pushMin_cells, List.map_cons]
        rw [← Queue.marked_holes, leftHoles, equal.1]
        rfl
      · have inside := splitRun.plug [Pointer.Frame.right queue.firstGap pivot]
        have promote : Rotations (.node queue.firstGap pivot (.node left.tree key right.tree))
            (.node (.node queue.firstGap pivot left.tree) key right.tree) 1 :=
          .singleton (.rootLeft _ _ _ _ _)
        have outside := pushRun.plug [Pointer.Frame.left key right.tree]
        exact ((popRun.append inside).append promote).append outside
      · simp only [List.length_cons]
        omega

private theorem trailing_of_holes (first : RawTree Nat) (cells : List (Spine.Cell Nat))
    (prior : List (RawTree Nat)) (last : RawTree Nat)
    (word : first :: cells.map Prod.snd = prior ++ [last]) : trailing first cells = last := by
  induction cells generalizing first prior with
  | nil =>
      have lengths := congrArg List.length word
      simp only [List.map_nil, List.length_cons, List.length_nil, List.length_append,
        List.length_singleton] at lengths
      have empty : prior = [] := by simpa using (show prior.length = 0 by omega)
      subst prior
      exact List.cons.inj word |>.1
  | cons cell cells ih =>
      cases prior with
      | nil =>
          have lengths := congrArg List.length word
          simp only [List.map_cons, List.length_cons, List.length_map, List.nil_append,
            List.length_singleton, List.length_nil] at lengths
          omega
      | cons head prior =>
          have tail := List.cons.inj word |>.2
          exact ih cell.2 prior tail

theorem Queue.lastGap_of_holes (queue : Queue Nat) (prior : List (RawTree Nat)) (last : RawTree Nat)
    (word : queue.marked.holes = prior ++ [last]) : queue.lastGap = last :=
  trailing_of_holes queue.firstGap queue.cells prior last ((Queue.marked_holes queue).symm.trans word)

theorem cut_gap_right (queue : Queue Nat) (before after : List (RawTree Nat))
    {level key : Nat} {block : RawTree Nat} (cut : BlockCut level block key)
    (word : queue.marked.holes = before ++ block :: after) :
    ∃ (left right : Queue Nat) (count : Nat),
      left.marked.holes = before ++ cut.left.marked.holes ∧
      right.marked.holes = cut.right.marked.holes ++ after ∧
      Rotations queue.tree (.node left.tree key right.tree) count ∧
      count + left.potential + right.potential ≤
        queue.potential + 20 * cut.steps + 20 * (after.length + 1) := by
  induction after using List.reverseRecOn generalizing queue with
  | nil =>
      have selected : queue.lastGap = block := queue.lastGap_of_holes before block word
      subst block
      obtain ⟨left, right, count, prior, oldHoles, leftHoles, rightHoles, run, bound⟩ := cut_last_gap queue cut
      have same : prior = before := List.append_cancel_right (oldHoles.symm.trans word)
      refine ⟨left, right, count, ?_, ?_, run, ?_⟩
      · simpa only [same] using leftHoles
      · simpa only [List.append_nil] using rightHoles
      · simpa only [List.length_nil] using bound
  | append_singleton after last ih =>
      have nonempty : queue.cells ≠ [] := by
        intro empty
        have lengths := congrArg List.length word
        simp only [Queue.marked_holes, empty, List.map_nil, List.length_cons,
          List.length_nil, List.length_append, List.length_singleton] at lengths
        omega
      obtain ⟨rest, pivot, endGap, pop, cells, firstSame, popRun, popBound⟩ := queue.pop_max nonempty
      have holes : queue.marked.holes = rest.marked.holes ++ [endGap] := by
        simp only [Queue.marked_holes, cells, firstSame, List.map_append, List.map_cons,
          List.map_nil, List.cons_append]
      have expanded : rest.marked.holes ++ [endGap] = (before ++ block :: after) ++ [last] := by
        simpa only [List.append_assoc, List.cons_append] using holes.symm.trans word
      have equal := List.append_inj' expanded (by rfl)
      have gapEq : endGap = last := List.cons.inj equal.2 |>.1
      subst endGap
      obtain ⟨left, right, split, leftHoles, rightHoles, splitRun, splitBound⟩ := ih rest equal.1
      obtain ⟨push, pushCount, pushRun, pushBound⟩ := right.push_max pivot last
      refine ⟨left, right.pushMax pivot last, pop + split + 1 + push,
        leftHoles, ?_, ?_, ?_⟩
      · simp only [Queue.marked_holes, Queue.pushMax_first, Queue.pushMax_cells,
          List.map_append, List.map_cons, List.map_nil, ← List.cons_append]
        rw [← Queue.marked_holes, rightHoles, List.append_assoc]
      · have inside := splitRun.plug [Pointer.Frame.left pivot last]
        have promote : Rotations (.node (.node left.tree key right.tree) pivot last)
            (.node left.tree key (.node right.tree pivot last)) 1 :=
          .singleton (.rootRight _ _ _ _ _)
        have outside := pushRun.plug [Pointer.Frame.right left.tree key]
        exact ((popRun.append inside).append promote).append outside
      · simp only [List.length_append, List.length_singleton]
        omega

theorem cut_gap (queue : Queue Nat) (before after : List (RawTree Nat))
    {level key : Nat} {block : RawTree Nat} (cut : BlockCut level block key)
    (word : queue.marked.holes = before ++ block :: after) :
    ∃ (left right : Queue Nat) (count : Nat),
      left.marked.holes = before ++ cut.left.marked.holes ∧
      right.marked.holes = cut.right.marked.holes ++ after ∧
      Rotations queue.tree (.node left.tree key right.tree) count ∧
      count + left.potential + right.potential ≤
        queue.potential + 20 * cut.steps + 20 * (min before.length after.length + 1) := by
  rcases le_total before.length after.length with smaller | smaller
  · rw [min_eq_left smaller]
    exact cut_gap_left queue before after cut word
  · rw [min_eq_right smaller]
    exact cut_gap_right queue before after cut word

end DynamicOptimality.GeometricOnlineSimulation
