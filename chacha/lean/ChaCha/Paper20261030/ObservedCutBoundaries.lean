import ChaCha.Paper20261030.DepartureSelection
import ChaCha.Paper20261030.ContextPortWords

/-!
# Reading the exact cut boundaries of a preferred descendant

The observed departure record supplies the original split interval.
Searching its lower endpoint returns the last outside record below that
interval; searching its upper endpoint returns the first outside record
above it. These are exactly the optional boundary records used by the
four physical context-repair cases. In particular, endpoint zero is
handled by a strict-lower search without predecessor subtraction.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

theorem context_boundary_neighbors {x y : Nat} (subtree : DepthTree x y) (p : DepthSplit → Bool)
    (c sub : AuxiliaryComponent Nat Nat (Tagged Payload))
    (frames : List (ContextFrame (α := Nat) followsRight))
    (same : Equivalent c (PreferredContext.wrap sub frames)) (ordered : c.core.Ordered)
    (representedSub : Represents followsRight (source subtree p) sub) (hxy : x ≤ y)
    (beforeBound : ∀ e ∈ PreferredContext.before frames, e.1 < x)
    (afterBound : ∀ e ∈ PreferredContext.after frames, y ≤ e.1) :
    (neighbors x c.core).1 = (PreferredContext.before frames).getLast? ∧
      (neighbors y c.core).2 = (PreferredContext.after frames).head? := by
  have subBounds : ∀ e ∈ sub.core.toListModel, x ≤ e.1 ∧ e.1 < y := by
    intro e he
    rw [represented_word subtree p sub representedSub] at he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    exact SeparatorPath.key_bounds subtree p hf
  have lowerBefore : (PreferredContext.before frames).filter (belowQuery x) = PreferredContext.before frames := by
    apply List.filter_eq_self.mpr
    intro e he
    exact decide_eq_true (beforeBound e he)
  have lowerMiddle : sub.core.toListModel.filter (belowQuery x) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he hx
    have := (subBounds e he).1
    have : e.1 < x := of_decide_eq_true hx
    omega
  have lowerAfter : (PreferredContext.after frames).filter (belowQuery x) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he hx
    have := afterBound e he
    have : e.1 < x := of_decide_eq_true hx
    omega
  have upperBefore : (PreferredContext.before frames).filter (aboveQuery y) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he hy
    have := beforeBound e he
    have : y ≤ e.1 := of_decide_eq_true hy
    omega
  have upperMiddle : sub.core.toListModel.filter (aboveQuery y) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he hy
    have := (subBounds e he).2
    have : y ≤ e.1 := of_decide_eq_true hy
    omega
  have upperAfter : (PreferredContext.after frames).filter (aboveQuery y) = PreferredContext.after frames := by
    apply List.filter_eq_self.mpr
    intro e he
    exact decide_eq_true (afterBound e he)
  rw [(neighbors_correct x c.core ordered).1,(neighbors_correct y c.core ordered).2,
    same.word,PreferredContext.word]
  simp only [List.filter_append,lowerBefore,lowerMiddle,lowerAfter,upperBefore,upperMiddle,upperAfter,
    List.append_nil,List.nil_append]
  constructor <;> trivial

end ChaCha.Paper20261030.SecondaryDecomposition
