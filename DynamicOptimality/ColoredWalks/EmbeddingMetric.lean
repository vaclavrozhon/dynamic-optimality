import DynamicOptimality.Basic

/-! # Distances in the existing ordinary key tree

These path certificates refer to `RawTree`; they do not define another BST
cost model. A distance bound supplies actual adjacent pointer moves in the
same physical tree, with no rotations and no request service charged.
-/

namespace DynamicOptimality.ColoredWalks

open ChaCha.MTR

variable {α : Type*}

def treeHeight : RawTree α → Nat
  | .empty => 0
  | .node left _ right => max (treeHeight left) (treeHeight right) + 1

/-- An actual downward path to a present key, measured in edges. -/
inductive RootPath : RawTree α → α → Nat → Prop
  | root (left : RawTree α) (key : α) (right : RawTree α) :
      RootPath (.node left key right) key 0
  | left {tree : RawTree α} {key : α} {depth : Nat} (path : RootPath tree key depth)
      (parent : α) (right : RawTree α) : RootPath (.node tree parent right) key (depth+1)
  | right (left : RawTree α) (parent : α) {tree : RawTree α} {key : α} {depth : Nat}
      (path : RootPath tree key depth) : RootPath (.node left parent tree) key (depth+1)

theorem RootPath.nonempty {tree : RawTree α} {key : α} {depth : Nat}
    (path : RootPath tree key depth) : tree ≠ .empty := by
  cases path <;> simp

theorem RootPath.mem {tree : RawTree α} {key : α} {depth : Nat}
    (path : RootPath tree key depth) : key ∈ tree.inorder := by
  induction path <;> simp [Tree.inorder, *]

theorem RootPath.depth_lt_height {tree : RawTree α} {key : α} {depth : Nat}
    (path : RootPath tree key depth) : depth < treeHeight tree := by
  induction path <;> simp only [treeHeight] <;> omega

theorem exists_rootPath {tree : RawTree α} {key : α} (member : key ∈ tree.inorder) :
    ∃ depth, RootPath tree key depth := by
  induction tree with
  | empty => simp [Tree.inorder] at member
  | node left parent right leftIH rightIH =>
    simp only [Tree.inorder,List.mem_append,List.mem_singleton] at member
    rcases member with (member | rfl) | member
    · obtain ⟨depth,path⟩ := leftIH member
      exact ⟨depth+1,.left path parent right⟩
    · exact ⟨0,.root left key right⟩
    · obtain ⟨depth,path⟩ := rightIH member
      exact ⟨depth+1,.right left parent path⟩

/-- Every step is the existing pointer operation and preserves the entire
physical tree. This subrelation excludes restructuring. -/
inductive Moves : Pointer.Cursor α → Pointer.Cursor α → Nat → Prop
  | refl (cursor : Pointer.Cursor α) : Moves cursor cursor 0
  | step {first middle last : Pointer.Cursor α} {cost : Nat}
      (move : Pointer.Step first middle) (same : first.tree = middle.tree)
      (rest : Moves middle last cost) : Moves first last (cost+1)

theorem Moves.singleton {first last : Pointer.Cursor α}
    (move : Pointer.Step first last) (same : first.tree = last.tree) : Moves first last 1 :=
  .step move same (.refl last)

theorem Moves.append {first middle last : Pointer.Cursor α} {a b : Nat}
    (front : Moves first middle a) (back : Moves middle last b) : Moves first last (a+b) := by
  induction front with
  | refl => simpa using back
  | step move same rest ih =>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Moves.step move same (ih back)

theorem Moves.tree_eq {first last : Pointer.Cursor α} {cost : Nat}
    (moves : Moves first last cost) : first.tree = last.tree := by
  induction moves with
  | refl => rfl
  | step _ same _ ih => exact same.trans ih

theorem Moves.toTrace {first last : Pointer.Cursor α} {cost : Nat}
    (moves : Moves first last cost) : Pointer.Trace first [] last cost := by
  induction moves with
  | refl => exact .nil _
  | step move _ _ ih => exact .step move ih

/-- Both directions of the same unchanged-tree pointer path are certified. -/
theorem RootPath.visit {tree : RawTree α} {key : α} {depth : Nat}
    (path : RootPath tree key depth) (frames : List (Pointer.Frame α)) :
    ∃ cursor : Pointer.Cursor α, cursor.focus.rootKey = some key ∧
      cursor.tree = Pointer.plug tree frames ∧
      Moves ⟨tree,frames⟩ cursor depth ∧ Moves cursor ⟨tree,frames⟩ depth := by
  induction path generalizing frames with
  | root left key right => exact ⟨⟨.node left key right,frames⟩,rfl,rfl,.refl _,.refl _⟩
  | @left tree key depth path parent right ih =>
    obtain ⟨cursor,atKey,same,down,up⟩ := ih (.left parent right::frames)
    have nonempty := path.nonempty
    cases tree with
    | empty => exact (nonempty rfl).elim
    | node a pivot b =>
      refine ⟨cursor,atKey,same,?_,?_⟩
      · simpa only [Nat.add_comm] using
          (Moves.singleton (.left a b right pivot parent frames) rfl).append down
      · exact up.append (Moves.singleton (.upLeft (.node a pivot b) right parent frames) rfl)
  | @right left parent tree key depth path ih =>
    obtain ⟨cursor,atKey,same,down,up⟩ := ih (.right left parent::frames)
    have nonempty := path.nonempty
    cases tree with
    | empty => exact (nonempty rfl).elim
    | node a pivot b =>
      refine ⟨cursor,atKey,same,?_,?_⟩
      · simpa only [Nat.add_comm] using
          (Moves.singleton (.right left a b parent pivot frames) rfl).append down
      · exact up.append (Moves.singleton (.upRight left (.node a pivot b) parent frames) rfl)

/-- A common ancestor with two short downward paths certifies a short
ordinary tree path. The ancestor may lie in either child subtree. -/
inductive DistanceLE : RawTree α → α → α → Nat → Prop
  | viaRoot {tree : RawTree α} {first last : α} {a b budget : Nat}
      (front : RootPath tree first a) (back : RootPath tree last b)
      (paid : a+b ≤ budget) : DistanceLE tree first last budget
  | left {tree : RawTree α} {first last : α} {budget : Nat}
      (path : DistanceLE tree first last budget) (parent : α) (right : RawTree α) :
      DistanceLE (.node tree parent right) first last budget
  | right (left : RawTree α) (parent : α) {tree : RawTree α} {first last : α} {budget : Nat}
      (path : DistanceLE tree first last budget) : DistanceLE (.node left parent tree) first last budget

theorem DistanceLE.mono {tree : RawTree α} {first last : α} {a b : Nat}
    (path : DistanceLE tree first last a) (bound : a ≤ b) : DistanceLE tree first last b := by
  induction path with
  | viaRoot front back paid => exact .viaRoot front back (paid.trans bound)
  | left _ parent right ih => exact .left (ih bound) parent right
  | right left parent _ ih => exact .right left parent (ih bound)

theorem DistanceLE.symm {tree : RawTree α} {first last : α} {budget : Nat}
    (path : DistanceLE tree first last budget) : DistanceLE tree last first budget := by
  induction path with
  | viaRoot front back paid => exact .viaRoot back front (by omega)
  | left _ parent right ih => exact .left ih parent right
  | right left parent _ ih => exact .right left parent ih

theorem RootPath.distance_self {tree : RawTree α} {key : α} {depth : Nat}
    (path : RootPath tree key depth) : DistanceLE tree key key 0 := by
  induction path with
  | root left key right => exact .viaRoot (.root left key right) (.root left key right) (by decide)
  | left _ parent right ih => exact .left ih parent right
  | right left parent _ ih => exact .right left parent ih

/-- The metric certificate supplies a legal adjacent-pointer trace. It works
under every fixed ancestor context, as required for persistent fingers. -/
theorem DistanceLE.moves {tree : RawTree α} {first last : α} {budget : Nat}
    (path : DistanceLE tree first last budget) (frames : List (Pointer.Frame α)) :
    ∃ (a b : Pointer.Cursor α) (cost : Nat), a.tree = Pointer.plug tree frames ∧
      b.tree = Pointer.plug tree frames ∧ a.focus.rootKey = some first ∧
      b.focus.rootKey = some last ∧ Moves a b cost ∧ cost ≤ budget := by
  induction path generalizing frames with
  | viaRoot front back paid =>
    obtain ⟨a,atFirst,aTree,_,up⟩ := front.visit frames
    obtain ⟨b,atLast,bTree,down,_⟩ := back.visit frames
    exact ⟨a,b,_,aTree,bTree,atFirst,atLast,up.append down,paid⟩
  | left _ parent right ih => exact ih (.left parent right::frames)
  | right left parent _ ih => exact ih (.right left parent::frames)

end DynamicOptimality.ColoredWalks
