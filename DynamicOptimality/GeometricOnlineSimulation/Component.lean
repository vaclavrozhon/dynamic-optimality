import DynamicOptimality.GeometricOnlineSimulation.InitializeBlocks
import DynamicOptimality.GeometricOnlineSimulation.Linearize
import DynamicOptimality.GeometricOnlineSimulation.Graft
import DynamicOptimality.GeometricOnlineSimulation.Budget
import DynamicOptimality.GeometricOnlineSimulation.QueueSplit
import Mathlib.Data.List.Forall2

/-!
# Valid physical split-tree components

The component consists of a genuine deque of perfect block subtrees. Its
level list is paired with its literal inorder holes. The mountain invariant
bounds transfers, and the stored credit combines both structural budgets
with the actual deque imbalance.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR ChaCha.MTR.Pointer SearchRotation DynamicOptimality.SingleFinger

variable {α : Type*}

theorem rotations_inorder {before after : RawTree α} {count : Nat}
    (run : Rotations before after count) : before.inorder = after.inorder := by
  induction run with
  | refl => rfl
  | step first rest ih => exact (rotation_inorder first).trans ih

theorem rotations_size {before after : RawTree α} {count : Nat}
    (run : Rotations before after count) : before.size = after.size := by
  simpa only [Tree.length_inorder] using congrArg List.length (rotations_inorder run)

theorem marked_size (marked : MarkedTree α) :
    marked.erase.size = marked.skeleton.size + (marked.holes.map Tree.size).sum := by
  induction marked with
  | hole => simp [MarkedTree.erase, MarkedTree.skeleton, MarkedTree.holes, Tree.size]
  | node left key right ihl ihr =>
      simp only [MarkedTree.erase, MarkedTree.skeleton, MarkedTree.holes, Tree.size,
        List.map_append, List.sum_append, ihl, ihr]
      omega

theorem perfect_list_credit {levels : List Nat} {holes : List (RawTree α)}
    (perfect : List.Forall₂ Perfect levels holes) :
    Dyadic.credit levels = (holes.map Tree.size).sum := by
  induction perfect with
  | nil => rfl
  | cons first rest ih =>
      simp only [Dyadic.credit_cons, List.map_cons, List.sum_cons, ← first.keys, ih]

theorem Fragment.perfect (fragment : Fragment α) :
    List.Forall₂ Perfect fragment.levels fragment.marked.holes := by
  induction fragment with
  | block level tree perfect => exact .cons perfect .nil
  | node left key right ihl ihr => exact List.rel_append ihl ihr

structure Component where
  queue : Queue Nat
  levels : List Nat
  perfect : List.Forall₂ Perfect levels queue.marked.holes
  mountain : Dyadic.Mountain levels

namespace Component

def tree (component : Component) : RawTree Nat := component.queue.tree

def credit (component : Component) : Nat :=
  blockBudget component.levels component.tree.size component.queue.potential

theorem levels_length (component : Component) :
    component.levels.length = component.queue.cells.length + 1 := by
  have same := component.perfect.length_eq
  rw [MarkedTree.holes_length, Queue.marked_size] at same
  exact same

theorem size_exact (component : Component) :
    component.tree.size = component.queue.cells.length + Dyadic.credit component.levels := by
  have sizes := marked_size component.queue.marked
  rw [Queue.marked_erase, Queue.marked_size, ← perfect_list_credit component.perfect] at sizes
  exact sizes

theorem weight_eq (component : Component) :
    Dyadic.weight component.levels = component.tree.size + 1 := by
  have accounting := Dyadic.credit_exact component.levels
  rw [component.levels_length] at accounting
  rw [component.size_exact]
  omega

theorem credit_bound (component : Component) : component.credit ≤ 184 * component.tree.size := by
  have blocks : Dyadic.credit component.levels ≤ component.tree.size := by
    rw [component.size_exact]
    omega
  have imbalance := component.queue.potential_le
  have size := component.size_exact
  exact blockBudget_initial blocks (by omega)

/-- Initialization is available on every supplied inorder word. The choice
of this representation can be fixed once per current word. -/
theorem exists_initial (word : List Nat) :
    ∃ component : Component, component.tree.inorder = word ∧ component.credit ≤ 184 * word.length := by
  obtain ⟨fragment, keys, mountain, blocks⟩ := Fragment.initial word
  obtain ⟨queue, count, holes, skeleton, run, cost⟩ := fragment.to_queue
  let component : Component := {
    queue := queue
    levels := fragment.levels
    perfect := by rw [holes]; exact fragment.perfect
    mountain := mountain }
  have wordEq : component.tree.inorder = word := (rotations_inorder run).symm.trans keys
  have size : component.tree.size = word.length := by rw [← Tree.length_inorder, wordEq]
  exact ⟨component, wordEq, by simpa only [size] using component.credit_bound⟩

/-- The complete split and credit bound when the selected key is already
one of the separators between perfect blocks. -/
theorem cut_separator (component : Component) (before after : List (Spine.Cell Nat))
    (key : Nat) (gap : RawTree Nat)
    (word : component.queue.cells = before ++ (key, gap) :: after) :
    ∃ (left right : Component) (count : Nat),
      Rotations component.tree (.node left.tree key right.tree) count ∧
      count + left.credit + right.credit ≤ component.credit := by
  obtain ⟨leftQueue, rightQueue, count, first, leftCells, rightFirst, rightCells, run, charge⟩ :=
    component.queue.split before after key gap word
  have holes : component.queue.marked.holes = leftQueue.marked.holes ++ rightQueue.marked.holes := by
    simp only [Queue.marked_holes, word, first, leftCells, rightFirst, rightCells,
      List.map_append, List.map_cons, List.cons_append]
  have together : List.Forall₂ Perfect component.levels
      (leftQueue.marked.holes ++ rightQueue.marked.holes) := holes ▸ component.perfect
  let leftLevels := component.levels.take leftQueue.marked.holes.length
  let rightLevels := component.levels.drop leftQueue.marked.holes.length
  have allLevels : leftLevels ++ rightLevels = component.levels := List.take_append_drop _ _
  have oldMountain : Dyadic.Mountain (leftLevels ++ rightLevels) := allLevels.symm ▸ component.mountain
  let left : Component := {
    queue := leftQueue
    levels := leftLevels
    perfect := List.forall₂_take_append _ _ _ together
    mountain := oldMountain.prefix }
  let right : Component := {
    queue := rightQueue
    levels := rightLevels
    perfect := List.forall₂_drop_append _ _ _ together
    mountain := oldMountain.suffix }
  have leftLength : leftLevels.length = before.length + 1 := by
    have count := left.levels_length
    change leftLevels.length = leftQueue.cells.length + 1 at count
    simpa only [leftCells] using count
  have rightLength : rightLevels.length = after.length + 1 := by
    have count := right.levels_length
    change rightLevels.length = rightQueue.cells.length + 1 at count
    simpa only [rightCells] using count
  have transfer := separator_transfer_bound oldMountain leftLength rightLength
  have leftWeight : Dyadic.weight leftLevels = left.tree.size + 1 := left.weight_eq
  have rightWeight : Dyadic.weight rightLevels = right.tree.size + 1 := right.weight_eq
  rw [leftWeight, rightWeight] at transfer
  have credits : Dyadic.credit leftLevels + Dyadic.credit rightLevels + 0 =
      Dyadic.credit component.levels := by rw [← allLevels, Dyadic.credit_append]; omega
  have physical : count + leftQueue.potential + rightQueue.potential ≤ component.queue.potential +
      100 * 0 + 40 * (Nat.log 2 (min (left.tree.size + 1) (right.tree.size + 1)) + 1) := by omega
  have paid := blockBudget_split credits physical
  have sizes : component.tree.size = left.tree.size + right.tree.size + 1 := by
    have same := rotations_size run
    change component.tree.size = left.tree.size + 1 + right.tree.size at same
    omega
  refine ⟨left, right, count, run, ?_⟩
  change count + blockBudget leftLevels left.tree.size leftQueue.potential +
      blockBudget rightLevels right.tree.size rightQueue.potential ≤
      blockBudget component.levels component.tree.size component.queue.potential
  rw [sizes]
  exact paid

end Component

end DynamicOptimality.GeometricOnlineSimulation
