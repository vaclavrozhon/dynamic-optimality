import TangoSquared.Paper20261030.LocalReferenceSize
import TangoSquared.Reference

/-!
# Construction of the completed secondary reference

The ordinary depth reference has one leaf per internal primary depth.
`completedReference` adds the completion leaf as the right child of a new
root, exactly as in the algorithm. All local references are obtained by
actual restriction of this tree.
-/

namespace TangoSquared.Paper20261030.LocalReferences

open RouterProjection PreferredProjection

def depthReference : {a b : Nat} → DepthTree a b → Router Nat
  | _, _, .leaf a => .leaf a
  | _, _, .node _ _ _ left right => .fork (depthReference left) (depthReference right)

theorem depthReference_nonempty {a b : Nat} (t : DepthTree a b) : depthReference t ≠ .empty := by
  cases t <;> simp [depthReference]

theorem depthReference_full {a b : Nat} (t : DepthTree a b) :
    Paper20261030.Router.Full (depthReference t) := by
  induction t with
  | leaf a => trivial
  | node c ha hb left right ihl ihr =>
    exact ⟨depthReference_nonempty left,depthReference_nonempty right,ihl,ihr⟩

theorem depthReference_leaves {a b : Nat} (t : DepthTree a b) :
    (depthReference t).leaves = List.range' a (b + 1 - a) := by
  induction t with
  | leaf a => simp [depthReference,Router.leaves,List.range']
  | @node a b c ha hb left right ihl ihr =>
    simp only [depthReference,Router.leaves,ihl,ihr]
    have hstart : a + (c + 1 - a) = c + 1 := by omega
    have hlength : (c + 1 - a) + (b + 1 - (c + 1)) = b + 1 - a := by omega
    calc
      _ = List.range' a (c + 1 - a) ++
          List.range' (a + (c + 1 - a)) (b + 1 - (c + 1)) := by rw [hstart]
      _ = List.range' a ((c + 1 - a) + (b + 1 - (c + 1))) := List.range'_append_1
      _ = _ := by rw [hlength]

def completedReference {h : Nat} (t : DepthTree 0 h) : Router Nat :=
  .fork (depthReference t) (.leaf (h + 1))

theorem completedReference_full {h : Nat} (t : DepthTree 0 h) :
    Paper20261030.Router.Full (completedReference t) :=
  ⟨depthReference_nonempty t,by simp,depthReference_full t,True.intro⟩

theorem completedReference_leaves {h : Nat} (t : DepthTree 0 h) :
    (completedReference t).leaves = List.range ((h + 1) + 1) := by
  simp only [completedReference,Router.leaves,depthReference_leaves,Nat.sub_zero]
  rw [← List.range_eq_range']
  exact List.range_succ.symm

/-- Actual completed and suffix-restricted references have exactly `5n-4`
vertices for every primary preference assignment. -/
theorem completed_localReferences_total_size {α : Type*} {h : Nat}
    (secondary : DepthTree 0 h) {primary : PrefRouter α} (hp : primary.Perfect (h + 1)) :
    ((localReferences (h + 1) (completedReference secondary) primary).map vertices).sum + 4 =
      5 * primary.leaves.length :=
  localReferences_total_size hp (completedReference_full secondary) (completedReference_leaves secondary)

end TangoSquared.Paper20261030.LocalReferences
