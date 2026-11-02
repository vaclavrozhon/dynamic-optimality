import DynamicOptimality.MultiFinger.Deque

/-!
# A deque including its zero-separator case

The empty queue is one literal gap subtree. A nonempty queue reuses the
existing two-spine layout and its checked endpoint operations. This wrapper
also handles removal of the last separator, with zero rotations.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR SearchRotation DynamicOptimality.SingleFinger

variable {α : Type*}

inductive Queue (α : Type*)
  | gap (tree : RawTree α)
  | deque (layout : Deque.Layout α)

namespace Queue

def tree : Queue α → RawTree α
  | .gap tree => tree
  | .deque layout => layout.tree

def firstGap : Queue α → RawTree α
  | .gap tree => tree
  | .deque layout => layout.gap

def cells : Queue α → List (Spine.Cell α)
  | .gap _ => []
  | .deque layout => layout.cells

def potential : Queue α → Nat
  | .gap _ => 0
  | .deque layout => layout.potential

def pushMin (queue : Queue α) (key : α) (before : RawTree α) : Queue α :=
  match queue with
  | .gap after => .deque ⟨before, [], key, after, []⟩
  | .deque layout => .deque (Deque.pushMinLayout layout key before)

def pushMax (queue : Queue α) (key : α) (after : RawTree α) : Queue α :=
  match queue with
  | .gap before => .deque ⟨before, [], key, after, []⟩
  | .deque layout => .deque (Deque.pushMaxLayout layout key after)

@[simp] theorem pushMin_cells (queue : Queue α) (key : α) (before : RawTree α) :
    (queue.pushMin key before).cells = (key, queue.firstGap) :: queue.cells := by
  cases queue <;> rfl

@[simp] theorem pushMin_first (queue : Queue α) (key : α) (before : RawTree α) :
    (queue.pushMin key before).firstGap = before := by cases queue <;> rfl

@[simp] theorem pushMax_cells (queue : Queue α) (key : α) (after : RawTree α) :
    (queue.pushMax key after).cells = queue.cells ++ [(key, after)] := by
  cases queue with
  | gap => rfl
  | deque layout =>
      simp only [pushMax, cells, Deque.pushMaxLayout, Deque.Layout.cells,
        List.append_assoc, List.cons_append]

@[simp] theorem pushMax_first (queue : Queue α) (key : α) (after : RawTree α) :
    (queue.pushMax key after).firstGap = queue.firstGap := by cases queue <;> rfl

theorem push_min (queue : Queue α) (key : α) (before : RawTree α) :
    ∃ count ≤ 1, Rotations (.node before key queue.tree) (queue.pushMin key before).tree count ∧
      count + (queue.pushMin key before).potential ≤ queue.potential + 5 := by
  cases queue with
  | gap after => exact ⟨0, by omega, .refl _, by simp [potential, pushMin, Deque.Layout.potential, Deque.potential]⟩
  | deque layout =>
      have result := MultiFinger.Deque.push_min layout key before
      exact ⟨1, le_rfl, result⟩

theorem push_max (queue : Queue α) (key : α) (after : RawTree α) :
    ∃ count ≤ 1, Rotations (.node queue.tree key after) (queue.pushMax key after).tree count ∧
      count + (queue.pushMax key after).potential ≤ queue.potential + 5 := by
  cases queue with
  | gap before => exact ⟨0, by omega, .refl _, by simp [potential, pushMax, Deque.Layout.potential, Deque.potential]⟩
  | deque layout =>
      have result := MultiFinger.Deque.push_max layout key after
      exact ⟨1, le_rfl, result⟩

theorem pop_min (queue : Queue α) (nonempty : queue.cells ≠ []) :
    ∃ (after : Queue α) (key : α) (count : Nat),
      queue.cells = (key, after.firstGap) :: after.cells ∧
      Rotations queue.tree (.node queue.firstGap key after.tree) count ∧
      count + after.potential ≤ queue.potential + 14 := by
  cases queue with
  | gap => exact (nonempty rfl).elim
  | deque layout =>
      by_cases enough : 2 ≤ layout.cells.length
      · obtain ⟨after, key, count, word, run, bound⟩ := MultiFinger.Deque.pop_min layout enough
        exact ⟨.deque after, key, count, word, run, bound⟩
      · have lengths : layout.front.length = 0 ∧ layout.back.length = 0 := by
          simp only [Deque.Layout.cells, List.length_append, List.length_cons] at enough
          omega
        have front : layout.front = [] := by simpa using lengths.1
        have back : layout.back = [] := by simpa using lengths.2
        refine ⟨.gap layout.afterGap, layout.pivot, 0, ?_, ?_, ?_⟩
        · simp only [cells, firstGap, Deque.Layout.cells, front, back, List.nil_append]
        · simpa only [tree, firstGap, Deque.Layout.tree, front, back,
            Spine.rightSpine, Spine.leftSpine] using Rotations.refl
              (.node layout.gap layout.pivot layout.afterGap)
        · simp [potential]

theorem pop_max (queue : Queue α) (nonempty : queue.cells ≠ []) :
    ∃ (after : Queue α) (key : α) (lastGap : RawTree α) (count : Nat),
      queue.cells = after.cells ++ [(key, lastGap)] ∧ after.firstGap = queue.firstGap ∧
      Rotations queue.tree (.node after.tree key lastGap) count ∧
      count + after.potential ≤ queue.potential + 14 := by
  cases queue with
  | gap => exact (nonempty rfl).elim
  | deque layout =>
      by_cases enough : 2 ≤ layout.cells.length
      · obtain ⟨after, key, lastGap, count, word, first, run, bound⟩ :=
          MultiFinger.Deque.pop_max layout enough
        exact ⟨.deque after, key, lastGap, count, word, first, run, bound⟩
      · have lengths : layout.front.length = 0 ∧ layout.back.length = 0 := by
          simp only [Deque.Layout.cells, List.length_append, List.length_cons] at enough
          omega
        have front : layout.front = [] := by simpa using lengths.1
        have back : layout.back = [] := by simpa using lengths.2
        refine ⟨.gap layout.gap, layout.pivot, layout.afterGap, 0, ?_, rfl, ?_, ?_⟩
        · simp only [cells, Deque.Layout.cells, front, back, List.nil_append]
        · simpa only [tree, Deque.Layout.tree, front, back,
            Spine.rightSpine, Spine.leftSpine] using Rotations.refl
              (.node layout.gap layout.pivot layout.afterGap)
        · simp [potential]

theorem cells_empty {queue : Queue α} (empty : queue.cells = []) :
    queue = .gap queue.firstGap := by
  cases queue with
  | gap => rfl
  | deque layout => simp [cells, Deque.Layout.cells] at empty

theorem potential_le (queue : Queue α) : queue.potential ≤ 4 * queue.cells.length := by
  cases queue with
  | gap => exact Nat.le_refl 0
  | deque layout =>
      simp only [potential, cells, Deque.Layout.potential, Deque.potential,
        Deque.Layout.cells, List.length_append, List.length_cons]
      omega

end Queue

end DynamicOptimality.GeometricOnlineSimulation
