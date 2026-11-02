import DynamicOptimality.ReferenceClosure.Geometry

/-!
# Fixed ancestor guards do not preserve arboral satisfaction

The perfect 31-key reference is the example in the geometric-closure note,
with every key shifted down by one to the shared universe 0,...,30.
Both original rows are NCA-closed. Adding each key's nearest strict lower
and upper reference ancestors creates an empty rectangle.
-/

namespace DynamicOptimality.Geometry.ReferenceClosure.GuardCounterexample

open Splay.Tree

def lowerGuard {lo hi : Nat} : BST lo hi → Nat → Option Nat
  | .empty _, _ => none
  | .node (root := pivot) left right, key =>
      if key < pivot then lowerGuard left key
      else if pivot < key then (lowerGuard right key).or (some pivot) else none

def upperGuard {lo hi : Nat} : BST lo hi → Nat → Option Nat
  | .empty _, _ => none
  | .node (root := pivot) left right, key =>
      if key < pivot then (upperGuard left key).or (some pivot)
      else if pivot < key then upperGuard right key else none

def guardRow {lo hi : Nat} (tree : BST lo hi) (keys : Finset Nat) : Finset Nat :=
  keys ∪ keys.biUnion fun key =>
    (lowerGuard tree key).toFinset ∪ (upperGuard tree key).toFinset

def reference : BST 0 31 :=
  .node
    (.node
      (.node
        (.node
          (.node (.empty 0) (.empty 1))
          (.node (.empty 2) (.empty 3)))
        (.node
          (.node (.empty 4) (.empty 5))
          (.node (.empty 6) (.empty 7))))
      (.node
        (.node
          (.node (.empty 8) (.empty 9))
          (.node (.empty 10) (.empty 11)))
        (.node
          (.node (.empty 12) (.empty 13))
          (.node (.empty 14) (.empty 15)))))
    (.node
      (.node
        (.node
          (.node (.empty 16) (.empty 17))
          (.node (.empty 18) (.empty 19)))
        (.node
          (.node (.empty 20) (.empty 21))
          (.node (.empty 22) (.empty 23))))
      (.node
        (.node
          (.node (.empty 24) (.empty 25))
          (.node (.empty 26) (.empty 27)))
        (.node
          (.node (.empty 28) (.empty 29))
          (.node (.empty 30) (.empty 31)))))

def original : Finset Point := {(21,1), (22,1), (22,2), (23,2)}

def guarded : Finset Point :=
  {(19,1), (21,1), (22,1), (23,1), (15,2), (21,2), (22,2), (23,2)}

theorem first_row_closed : row reference {21,22} = {21,22} := by decide

theorem second_row_closed : row reference {22,23} = {22,23} := by decide

theorem first_row_guards : guardRow reference {21,22} = {19,21,22,23} := by decide

theorem second_row_guards : guardRow reference {22,23} = {15,21,22,23} := by decide

theorem original_satisfied : ArborallySatisfied original := by
  unfold ArborallySatisfied original GreedyMerge.Geometry.Between
  decide

theorem guarded_not_satisfied : ¬ArborallySatisfied guarded := by
  intro satisfied
  obtain ⟨r, hr, nrp, nrq, between, lower, upper⟩ :=
    satisfied (19,1) (by simp [guarded]) (15,2) (by simp [guarded])
      (by decide) (by decide)
  simp only [guarded, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [GreedyMerge.Geometry.Between]

end DynamicOptimality.Geometry.ReferenceClosure.GuardCounterexample
