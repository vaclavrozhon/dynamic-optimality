import DynamicOptimality.HullPriorityUpdate

/-!
# Rearranging a marked rooted prefix

The marked nodes are the keys charged in one geometric row. Holes are
whole untouched subtrees. Move-to-root on the marked skeleton preserves
the inorder sequence of both keys and holes.
-/

namespace DynamicOptimality.Geometry

open TangoSquared TangoSquared.MTR TangoSquared.MTR.Tree
open TangoSquared.MTR.Pointer TangoSquared.MTR.Tree.PriorityHull

namespace Marked

def rotateRight : MarkedTree Nat → MarkedTree Nat
  | .node (.node a x b) y c => .node a x (.node b y c)
  | t => t

def rotateLeft : MarkedTree Nat → MarkedTree Nat
  | .node a x (.node b y c) => .node (.node a x b) y c
  | t => t

def moveToRoot (x : Nat) : MarkedTree Nat → MarkedTree Nat
  | .hole t => .hole t
  | .node l y r =>
      if x < y then rotateRight (.node (moveToRoot x l) y r)
      else if y < x then rotateLeft (.node l y (moveToRoot x r))
      else .node l y r

@[simp] theorem skeleton_rotateRight (t : MarkedTree Nat) :
    (rotateRight t).skeleton = Tree.rotateRight t.skeleton := by
  cases t with
  | hole t => rfl
  | node l y r => cases l <;> rfl

@[simp] theorem skeleton_rotateLeft (t : MarkedTree Nat) :
    (rotateLeft t).skeleton = Tree.rotateLeft t.skeleton := by
  cases t with
  | hole t => rfl
  | node l y r => cases r <;> rfl

@[simp] theorem holes_rotateRight (t : MarkedTree Nat) :
    (rotateRight t).holes = t.holes := by
  cases t with
  | hole t => rfl
  | node l y r => cases l <;> simp [rotateRight, MarkedTree.holes, List.append_assoc]

@[simp] theorem holes_rotateLeft (t : MarkedTree Nat) :
    (rotateLeft t).holes = t.holes := by
  cases t with
  | hole t => rfl
  | node l y r => cases r <;> simp [rotateLeft, MarkedTree.holes, List.append_assoc]

@[simp] theorem inorder_rotateRight (t : MarkedTree Nat) :
    (rotateRight t).erase.inorder = t.erase.inorder := by
  cases t with
  | hole t => rfl
  | node l y r => cases l <;> simp [rotateRight, MarkedTree.erase, inorder, List.append_assoc]

@[simp] theorem inorder_rotateLeft (t : MarkedTree Nat) :
    (rotateLeft t).erase.inorder = t.erase.inorder := by
  cases t with
  | hole t => rfl
  | node l y r => cases r <;> simp [rotateLeft, MarkedTree.erase, inorder, List.append_assoc]

@[simp] theorem skeleton_moveToRoot (x : Nat) (t : MarkedTree Nat) :
    (moveToRoot x t).skeleton = Tree.moveToRoot x t.skeleton := by
  induction t with
  | hole t => rfl
  | node l y r ihl ihr =>
      simp only [moveToRoot, MarkedTree.skeleton, Tree.moveToRoot]
      split
      · simp [MarkedTree.skeleton, ihl]
      · split <;> simp [MarkedTree.skeleton, ihr]

@[simp] theorem holes_moveToRoot (x : Nat) (t : MarkedTree Nat) :
    (moveToRoot x t).holes = t.holes := by
  induction t with
  | hole t => rfl
  | node l y r ihl ihr =>
      simp only [moveToRoot]
      split
      · simp [MarkedTree.holes, ihl]
      · split <;> simp [MarkedTree.holes, ihr]

@[simp] theorem inorder_moveToRoot (x : Nat) (t : MarkedTree Nat) :
    (moveToRoot x t).erase.inorder = t.erase.inorder := by
  induction t with
  | hole t => rfl
  | node l y r ihl ihr =>
      simp only [moveToRoot]
      split
      · simp [MarkedTree.erase, inorder, ihl]
      · split <;> simp [MarkedTree.erase, inorder, ihr]

theorem skeleton_sublist (t : MarkedTree Nat) :
    t.skeleton.inorder.Sublist t.erase.inorder := by
  rw [← t.graft_gapArray]
  exact inorder_sublist_graft _ _ _

theorem moveToRoot_node (t : MarkedTree Nat) (x : Nat)
    (ordered : Ordered t.erase) (member : x ∈ t.skeleton.inorder) :
    ∃ left right, moveToRoot x t = .node left x right := by
  have skeletonOrdered : Ordered t.skeleton :=
    List.Pairwise.sublist (skeleton_sublist t) ordered
  obtain ⟨depth, search⟩ := searchDepth_exists_of_mem skeletonOrdered member
  have root := rootKey_moveToRoot_of_searchDepth x t.skeleton depth search
  rw [← skeleton_moveToRoot] at root
  cases equal : moveToRoot x t with
  | hole tree => simp [equal, MarkedTree.skeleton, rootKey] at root
  | node left y right =>
      have keyEq : y = x := by simpa [equal, MarkedTree.skeleton, rootKey] using root
      subst y
      exact ⟨left, right, rfl⟩

/-- Subtree intervals, obtained from the actual ordered inorder word. -/
theorem node_intervals {left right : RawTree Nat} {root lo hi : Nat}
    (ordered : Ordered (.node left root right))
    (keys : ∀ key, key ∈ (TangoSquared.MTR.Tree.node left root right).inorder ↔ lo ≤ key ∧ key < hi) :
    (lo ≤ root ∧ root < hi) ∧
      (∀ key, key ∈ left.inorder ↔ lo ≤ key ∧ key < root) ∧
      (∀ key, key ∈ right.inorder ↔ root + 1 ≤ key ∧ key < hi) := by
  obtain ⟨orderedLeft, orderedRight, leftLt, rightGt⟩ := ordered_node_parts ordered
  have rootBounds := (keys root).mp (by simp [inorder])
  refine ⟨rootBounds, ?_, ?_⟩
  · intro key
    constructor
    · intro member
      exact ⟨((keys key).mp (by simp [inorder, member])).1, leftLt key member⟩
    · intro bounds
      have member := (keys key).mpr ⟨bounds.1, bounds.2.trans rootBounds.2⟩
      simp only [inorder, List.mem_append, List.mem_singleton] at member
      rcases member with (member | equal) | member
      · exact member
      · omega
      · have := rightGt key member; omega
  · intro key
    constructor
    · intro member
      have larger := rightGt key member
      exact ⟨by omega, ((keys key).mp (by simp [inorder, member])).2⟩
    · intro bounds
      have member := (keys key).mpr ⟨by omega, bounds.2⟩
      simp only [inorder, List.mem_append, List.mem_singleton] at member
      rcases member with (member | equal) | member
      · have := leftLt key member; omega
      · omega
      · exact member

theorem node_selected {left right : MarkedTree Nat} {root : Nat} {row : Finset Nat}
    (ordered : Ordered (MarkedTree.node left root right).erase)
    (selected : ∀ key ∈ (MarkedTree.node left root right).erase.inorder,
      key ∈ (MarkedTree.node left root right).skeleton.inorder ↔ key ∈ row) :
    (∀ key ∈ left.erase.inorder, key ∈ left.skeleton.inorder ↔ key ∈ row) ∧
      (∀ key ∈ right.erase.inorder, key ∈ right.skeleton.inorder ↔ key ∈ row) := by
  obtain ⟨orderedLeft, orderedRight, leftLt, rightGt⟩ := ordered_node_parts ordered
  constructor
  · intro key member
    constructor
    · intro marked
      exact (selected key (by simp [MarkedTree.erase, inorder, member])).mp
        (by simp [MarkedTree.skeleton, inorder, marked])
    · intro touched
      have marked := (selected key (by simp [MarkedTree.erase, inorder, member])).mpr touched
      simp only [MarkedTree.skeleton, inorder, List.mem_append, List.mem_singleton] at marked
      rcases marked with (marked | equal) | marked
      · exact marked
      · have := leftLt key member; omega
      · have h1 := leftLt key member
        have h2 := rightGt key ((skeleton_sublist right).subset marked)
        omega
  · intro key member
    constructor
    · intro marked
      exact (selected key (by simp [MarkedTree.erase, inorder, member])).mp
        (by simp [MarkedTree.skeleton, inorder, marked])
    · intro touched
      have marked := (selected key (by simp [MarkedTree.erase, inorder, member])).mpr touched
      simp only [MarkedTree.skeleton, inorder, List.mem_append, List.mem_singleton] at marked
      rcases marked with (marked | equal) | marked
      · have h1 := rightGt key member
        have h2 := leftLt key ((skeleton_sublist left).subset marked)
        omega
      · have := rightGt key member; omega
      · exact marked

end Marked

end DynamicOptimality.Geometry
