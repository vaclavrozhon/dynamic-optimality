import DynamicOptimality.GeometricOnlineSimulation.Interface

/-!
# Physical trees of equal-time classes

Each nonempty class stores a split-tree state. A binary frame has exactly
that state's skeleton, and its external holes hold older classes. Keeping
frames indexed by their literal skeleton lets ordinary rotations preserve
all hanging subtrees without changing or renumbering them.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR

mutual
  inductive ClassTree (system : SplitTreeSystem) : Type
    | empty : ClassTree system
    | node (time : Int) (state : system.State) (nonempty : system.tree state ≠ .empty)
        (frame : ClassFrame system (system.tree state)) : ClassTree system

  inductive ClassFrame (system : SplitTreeSystem) : RawTree Nat → Type
    | hole (child : ClassTree system) : ClassFrame system .empty
    | node {left right : RawTree Nat} (front : ClassFrame system left) (key : Nat)
        (back : ClassFrame system right) : ClassFrame system (.node left key right)
end

mutual
  def ClassTree.tree {system : SplitTreeSystem} : ClassTree system → RawTree Nat
    | .empty => .empty
    | .node _ _ _ frame => frame.tree

  def ClassFrame.tree {system : SplitTreeSystem} {skeleton : RawTree Nat} :
      ClassFrame system skeleton → RawTree Nat
    | .hole child => child.tree
    | .node front key back => .node front.tree key back.tree
end

mutual
  def ClassTree.credit {system : SplitTreeSystem} : ClassTree system → Nat
    | .empty => 0
    | .node _ state _ frame => system.credit state + frame.credit

  def ClassFrame.credit {system : SplitTreeSystem} {skeleton : RawTree Nat} :
      ClassFrame system skeleton → Nat
    | .hole child => child.credit
    | .node front _ back => front.credit + back.credit
end

set_option inductive.autoPromoteIndices false in
mutual
  /-- The class tree contains exactly the key interval `[lower,upper)` and
  realizes the supplied last-touch height at every physical key. -/
  inductive ClassTree.Realizes {system : SplitTreeSystem} (height : Nat → Int) :
      Nat → Nat → ClassTree system → Prop
    | empty (boundary : Nat) : ClassTree.Realizes height boundary boundary .empty
    | node {lower upper : Nat} {time : Int} {state : system.State}
        {nonempty : system.tree state ≠ .empty} {frame : ClassFrame system (system.tree state)}
        (valid : ClassFrame.Realizes height time lower upper frame) :
        ClassTree.Realizes height lower upper (.node time state nonempty frame)

  /-- Skeleton keys have the class's exact time; every key in a hole has
  strictly smaller last-touch time. Every interval is represented in full. -/
  inductive ClassFrame.Realizes {system : SplitTreeSystem} (height : Nat → Int) :
      Int → Nat → Nat → {skeleton : RawTree Nat} → ClassFrame system skeleton → Prop
    | hole {time : Int} {lower upper : Nat} {child : ClassTree system}
        (valid : ClassTree.Realizes height lower upper child)
        (older : ∀ key, lower ≤ key → key < upper → height key < time) :
        ClassFrame.Realizes height time lower upper (.hole child)
    | node {time : Int} {lower key upper : Nat} {left right : RawTree Nat}
        {front : ClassFrame system left} {back : ClassFrame system right}
        (lowerBound : lower ≤ key) (upperBound : key < upper)
        (first : ClassFrame.Realizes height time lower key front)
        (last : ClassFrame.Realizes height time (key+1) upper back)
        (sameTime : height key = time) :
        ClassFrame.Realizes height time lower upper (.node front key back)
end

end DynamicOptimality.GeometricOnlineSimulation
