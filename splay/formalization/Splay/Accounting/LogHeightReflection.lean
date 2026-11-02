import Splay.Accounting.LogHeightChocolateGeometry
import Splay.Accounting.OfflineReflection

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree OfflineNormalForm

namespace LogHeightChocolate

/-- An unlabelled shape is used only to compare reflected payload frontiers.
The physical trees and all rotations continue to use the original indexed BST. -/
inductive SkeletonShape
  | empty
  | node (left right : SkeletonShape)
  deriving DecidableEq

namespace SkeletonShape

def size : SkeletonShape → ℕ
  | .empty => 0
  | .node left right => left.size + 1 + right.size

def mirror : SkeletonShape → SkeletonShape
  | .empty => .empty
  | .node left right => .node right.mirror left.mirror

end SkeletonShape

def treeShape {lower upper : ℕ} : BST lower upper → SkeletonShape
  | .empty _ => .empty
  | .node left right => .node (treeShape left) (treeShape right)

@[simp] theorem treeShape_size {lower upper : ℕ} (tree : BST lower upper) :
    (treeShape tree).size = tree.size := by
  induction tree <;> simp [treeShape, SkeletonShape.size, BST.size, *]

theorem treeShape_injective {lower upper : ℕ} {a b : BST lower upper}
    (same : treeShape a = treeShape b) : a = b := by
  induction a with
  | empty boundary =>
      cases b with
      | empty => rfl
      | node => cases same
  | @node lower root upper left right ihL ihR =>
      cases b with
      | empty => cases same
      | @node _ other _ otherLeft otherRight =>
          simp only [treeShape, SkeletonShape.node.injEq] at same
          have sizeEq := congrArg SkeletonShape.size same.1
          simp only [treeShape_size] at sizeEq
          have leftInterval := left.size_add_lower_eq_upper
          have otherInterval := otherLeft.size_add_lower_eq_upper
          have roots : root = other := by omega
          subst other
          cases ihL same.1
          cases ihR same.2
          rfl

def frontierShapes {lower upper : ℕ} : SupportFrontier lower upper → List SkeletonShape
  | .last tree => [treeShape tree]
  | .next tree tail => treeShape tree :: frontierShapes tail

theorem frontierShapes_nonempty {lower upper : ℕ} (frontier : SupportFrontier lower upper) :
    frontierShapes frontier ≠ [] := by cases frontier <;> simp [frontierShapes]

@[simp] theorem frontierShapes_append {lower root upper : ℕ}
    (a : SupportFrontier lower root) (b : SupportFrontier (root + 1) upper) :
    frontierShapes (a.append b) = frontierShapes a ++ frontierShapes b := by
  induction a with
  | last => rfl
  | next first tail ih => simp [SupportFrontier.append, frontierShapes, ih]

theorem frontierShapes_injective {lower upper : ℕ} {a b : SupportFrontier lower upper}
    (same : frontierShapes a = frontierShapes b) : a = b := by
  induction a with
  | last tree =>
      cases b with
      | last other =>
          have eqTree : tree = other := treeShape_injective (by simpa [frontierShapes] using same)
          cases eqTree
          rfl
      | next first tail =>
          have zero : frontierShapes tail = [] := by simpa [frontierShapes] using (List.cons.inj same).2.symm
          exact False.elim (frontierShapes_nonempty tail zero)
  | @next lower root upper first tail ih =>
      cases b with
      | last tree =>
          have zero : frontierShapes tail = [] := (List.cons.inj same).2
          exact False.elim (frontierShapes_nonempty tail zero)
      | @next _ other _ next rest =>
          have headEq := (List.cons.inj same).1
          have tailEq := (List.cons.inj same).2
          have sizeEq := congrArg SkeletonShape.size headEq
          simp only [treeShape_size] at sizeEq
          have firstInterval := first.size_add_lower_eq_upper
          have nextInterval := next.size_add_lower_eq_upper
          have roots : root = other := by omega
          subst other
          cases treeShape_injective headEq
          cases ih tailEq
          rfl

end LogHeightChocolate

namespace Reflection

open LogHeightChocolate

def symm : {beforeLower beforeUpper afterLower afterUpper : ℕ} →
    {before : BST beforeLower beforeUpper} → {after : BST afterLower afterUpper} →
    Reflection before after → Reflection after before
  | _, _, _, _, _, _, .leaf a b => .leaf b a
  | _, _, _, _, _, _, .node left right => .node right.symm left.symm

/-- Unselected payloads stay literal under reflection. -/
@[simp] theorem restrict_none {beforeLower beforeUpper afterLower afterUpper : ℕ}
    {before : BST beforeLower beforeUpper} {after : BST afterLower afterUpper}
    (reflection : Reflection before after) :
    reflection.restrict (.none before) = .none after := by
  cases reflection <;> rfl

theorem restrict_symm {beforeLower beforeUpper afterLower afterUpper : ℕ}
    {before : BST beforeLower beforeUpper} {after : BST afterLower afterUpper}
    (reflection : Reflection before after) (selected : RootPrefix before) :
    reflection.symm.restrict (reflection.restrict selected) = selected := by
  induction reflection with
  | leaf => cases selected; rfl
  | node left right ihL ihR =>
      cases selected with
      | none => rfl
      | node a b => simp only [symm, restrict, ihL, ihR]

theorem shape_eq_mirror {beforeLower beforeUpper afterLower afterUpper : ℕ}
    {before : BST beforeLower beforeUpper} {after : BST afterLower afterUpper}
    (reflection : Reflection before after) : treeShape after = (treeShape before).mirror := by
  induction reflection <;> simp [treeShape, SkeletonShape.mirror, *]

theorem frontierShapes_restrict {beforeLower beforeUpper afterLower afterUpper : ℕ}
    {before : BST beforeLower beforeUpper} {after : BST afterLower afterUpper}
    (reflection : Reflection before after) (selected : RootPrefix before) :
    frontierShapes (reflection.restrict selected).frontier =
      (frontierShapes selected.frontier).reverse.map SkeletonShape.mirror := by
  induction reflection with
  | leaf => cases selected; rfl
  | node left right ihL ihR =>
      cases selected with
      | none =>
          simp [restrict, RootPrefix.frontier, frontierShapes, treeShape,
            left.shape_eq_mirror, right.shape_eq_mirror, SkeletonShape.mirror]
      | node a b =>
          simp [restrict, RootPrefix.frontier, ihL a, ihR b, List.reverse_append]

/-- Equal ordered ghost payloads give equal literal physical payloads after
reflection. This transports stack endpoints without any extra rotations. -/
theorem frontier_eq_of_reflected {beforeLower beforeUpper afterLower afterUpper : ℕ}
    {before other : BST beforeLower beforeUpper} {after otherAfter : BST afterLower afterUpper}
    (first : Reflection before after) (second : Reflection other otherAfter)
    (a : RootPrefix before) (b : RootPrefix other) (same : a.frontier = b.frontier) :
    (first.restrict a).frontier = (second.restrict b).frontier := by
  apply frontierShapes_injective
  rw [first.frontierShapes_restrict, second.frontierShapes_restrict, same]

theorem weightedHeight_restrict {beforeLower beforeUpper afterLower afterUpper : ℕ}
    {before : BST beforeLower beforeUpper} {after : BST afterLower afterUpper}
    (reflection : Reflection before after) (selected : RootPrefix before) :
    weightedHeight (reflection.restrict selected) = weightedHeight selected := by
  induction reflection with
  | leaf => cases selected; simp [restrict, weightedHeight, logMass, mass, BST.size]
  | node left right ihL ihR =>
      cases selected with
      | none =>
          simp only [restrict, weightedHeight, logMass, mass, BST.size,
            left.size_eq, right.size_eq]
          congr 2
          omega
      | node a b => simp [restrict, weightedHeight, ihL a, ihR b, Nat.max_comm]

end Reflection

end Splay.Accounting.OfflineConnectedSupport
