import DynamicOptimality.Basic
import Splay.Tree.SplayExecution

/-!
# Standard splaying on a component's own ordered alphabet

Preferred paths need not be intervals of the original keys. We therefore use
the shared raw tree, and retain the exact bottom-up zig/zig-zig/zig-zag rules.
The bridge `of_indexed` proves that these rules include the existing concrete
splay execution, with exactly the same number of rotations. No BST or optimum
is redefined.
-/

namespace MultiSplay.Auxiliary

open DynamicOptimality (RawTree)
open TangoSquared.MTR.Tree (inorder rootKey Ordered size)

variable {α : Type*}

inductive Double (key : α) : RawTree α → RawTree α → Prop
  | leftLeft (a b c d : RawTree α) (y z : α) :
      Double key (.node (.node (.node a key b) y c) z d)
        (.node a key (.node b y (.node c z d)))
  | rightRight (a b c d : RawTree α) (x y : α) :
      Double key (.node a x (.node b y (.node c key d)))
        (.node (.node (.node a x b) y c) key d)
  | leftRight (a b c d : RawTree α) (x z : α) :
      Double key (.node (.node a x (.node b key c)) z d)
        (.node (.node a x b) key (.node c z d))
  | rightLeft (a b c d : RawTree α) (x z : α) :
      Double key (.node a x (.node (.node b key c) z d))
        (.node (.node a x b) key (.node c z d))
  | leftContext {a b : RawTree α} (step : Double key a b) (x : α) (r : RawTree α) :
      Double key (.node a x r) (.node b x r)
  | rightContext (l : RawTree α) (x : α) {a b : RawTree α} (step : Double key a b) :
      Double key (.node l x a) (.node l x b)

inductive Step (key : α) : RawTree α → RawTree α → Nat → Prop
  | zigLeft (a b c : RawTree α) (y : α) :
      Step key (.node (.node a key b) y c) (.node a key (.node b y c)) 1
  | zigRight (a b c : RawTree α) (x : α) :
      Step key (.node a x (.node b key c)) (.node (.node a x b) key c) 1
  | double {a b : RawTree α} (step : Double key a b) : Step key a b 2

/-- A splay stops precisely at the accessed root. The final index is the
actual number of rotations, not a supplied upper-bound certificate. -/
inductive Splay (key : α) : RawTree α → RawTree α → Nat → Prop
  | done (l r : RawTree α) : Splay key (.node l key r) (.node l key r) 0
  | next {a b c : RawTree α} {head tail : Nat}
      (step : Step key a b head) (rest : Splay key b c tail) : Splay key a c (head + tail)

theorem Double.inorder_eq {key : α} {a b : RawTree α} (step : Double key a b) :
    inorder a = inorder b := by
  induction step <;> simp_all [inorder, List.append_assoc]

theorem Step.inorder_eq {key : α} {a b : RawTree α} {rotations : Nat}
    (step : Step key a b rotations) : inorder a = inorder b := by
  cases step with
  | zigLeft => simp [inorder, List.append_assoc]
  | zigRight => simp [inorder, List.append_assoc]
  | double step => exact step.inorder_eq

theorem Splay.inorder_eq {key : α} {a b : RawTree α} {rotations : Nat}
    (execution : Splay key a b rotations) : inorder a = inorder b := by
  induction execution with
  | done => rfl
  | next step rest ih => exact step.inorder_eq.trans ih

theorem Splay.root_after {key : α} {a b : RawTree α} {rotations : Nat}
    (execution : Splay key a b rotations) : rootKey b = some key := by
  induction execution with
  | done => rfl
  | next step rest ih => exact ih

theorem Splay.ordered_after [LinearOrder α] {key : α} {a b : RawTree α} {rotations : Nat}
    (execution : Splay key a b rotations) (ordered : Ordered a) : Ordered b := by
  unfold Ordered at *
  rw [← execution.inorder_eq]
  exact ordered

theorem Splay.size_eq {key : α} {a b : RawTree α} {rotations : Nat}
    (execution : Splay key a b rotations) : size a = size b := by
  rw [← TangoSquared.MTR.Tree.length_inorder, ← TangoSquared.MTR.Tree.length_inorder,
    execution.inorder_eq]

/-- Relabeling keys preserves the full splay transcript. This is the
alphabet-independent interface needed when a component is split or joined. -/
def map (f : α → β) : RawTree α → RawTree β
  | .empty => .empty
  | .node l x r => .node (map f l) (f x) (map f r)

theorem Double.map {key : α} {a b : RawTree α} (step : Double key a b) (f : α → β) :
    Double (f key) (map f a) (map f b) := by
  induction step with
  | leftLeft a b c d y z => exact .leftLeft _ _ _ _ _ _
  | rightRight a b c d x y => exact .rightRight _ _ _ _ _ _
  | leftRight a b c d x z => exact .leftRight _ _ _ _ _ _
  | rightLeft a b c d x z => exact .rightLeft _ _ _ _ _ _
  | leftContext step x r ih => exact .leftContext ih _ _
  | rightContext l x step ih => exact .rightContext _ _ ih

theorem Step.map {key : α} {a b : RawTree α} {rotations : Nat}
    (step : Step key a b rotations) (f : α → β) :
    Step (f key) (map f a) (map f b) rotations := by
  cases step with
  | zigLeft => exact .zigLeft _ _ _ _
  | zigRight => exact .zigRight _ _ _ _
  | double step => exact .double (step.map f)

theorem Splay.map {key : α} {a b : RawTree α} {rotations : Nat}
    (execution : Splay key a b rotations) (f : α → β) :
    Splay (f key) (map f a) (map f b) rotations := by
  induction execution with
  | done => exact .done _ _
  | next step rest ih => exact .next (step.map f) ih

theorem Double.of_indexed_root {key lower upper : Nat} {a b : Splay.Tree.BST lower upper}
    (step : Splay.Tree.BST.DoubleRotation key a b) :
    Double key (DynamicOptimality.BST.toRaw a) (DynamicOptimality.BST.toRaw b) := by
  cases step with
  | zigZigLeft => exact .leftLeft _ _ _ _ _ _
  | zigZigRight => exact .rightRight _ _ _ _ _ _
  | zigZagLeftRight => exact .leftRight _ _ _ _ _ _
  | zigZagRightLeft => exact .rightLeft _ _ _ _ _ _

theorem Double.of_indexed {depth key lower upper : Nat} {a b : Splay.Tree.BST lower upper}
    (step : Splay.Tree.BST.DoubleRotationAt depth key a b) :
    Double key (DynamicOptimality.BST.toRaw a) (DynamicOptimality.BST.toRaw b) := by
  induction step with
  | root step => exact .of_indexed_root step
  | leftContext step r ih => exact .leftContext ih _ _
  | rightContext l step ih => exact .rightContext _ _ ih

theorem Step.of_indexed {key lower upper : Nat} {a b : Splay.Tree.BST lower upper}
    (step : Splay.Tree.BST.SplayStep key a b) :
    ∃ rotations, Step key (DynamicOptimality.BST.toRaw a) (DynamicOptimality.BST.toRaw b) rotations ∧
      a.depth key = rotations + b.depth key := by
  cases step with
  | zig step =>
      refine ⟨1, ?_, ?_⟩
      · cases step with
        | fromLeft => exact .zigLeft _ _ _ _
        | fromRight => exact .zigRight _ _ _ _
      · rw [step.depth_before_eq_one, step.depth_after_eq_zero]
  | double step =>
      refine ⟨2, .double (.of_indexed step), ?_⟩
      rw [step.depth_before_eq, step.depth_after_eq]
      omega

theorem Splay.of_indexed {key lower upper : Nat} {a b : Splay.Tree.BST lower upper}
    (execution : Splay.Tree.BST.SplayExecution key a b) :
    Splay key (DynamicOptimality.BST.toRaw a) (DynamicOptimality.BST.toRaw b) (a.depth key) := by
  induction execution with
  | done root =>
      obtain ⟨l, r, rfl⟩ := root
      rw [Splay.Tree.BST.depth_root]
      exact .done _ _
  | next step rest ih =>
      obtain ⟨rotations, raw, depth_eq⟩ := Step.of_indexed step
      rw [depth_eq]
      exact .next raw ih

/-- The existing total-correctness theorem supplies an actual execution on
every relabeled indexed component, retaining its exact rotation count. -/
theorem exists_on_alphabet {lower upper key : Nat} (tree : Splay.Tree.BST lower upper)
    (insideLower : lower ≤ key) (insideUpper : key < upper) (alphabet : Nat → α) :
    ∃ after, Splay (alphabet key) (map alphabet (DynamicOptimality.BST.toRaw tree)) after
      (tree.depth key) := by
  obtain ⟨after, execution⟩ := Splay.Tree.BST.SplayExecution.exists_splay tree insideLower insideUpper
  exact ⟨map alphabet (DynamicOptimality.BST.toRaw after), execution |> Splay.of_indexed |> (·.map alphabet)⟩

end MultiSplay.Auxiliary
