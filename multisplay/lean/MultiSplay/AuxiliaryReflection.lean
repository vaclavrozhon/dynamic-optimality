import MultiSplay.AuxiliarySplay

namespace MultiSplay.Auxiliary

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder)

variable {α : Type*}

def mirror : RawTree α → RawTree α
  | .empty => .empty
  | .node l x r => .node (mirror r) x (mirror l)

@[simp] theorem mirror_mirror (tree : RawTree α) : mirror (mirror tree) = tree := by
  induction tree <;> simp [mirror, *]

theorem inorder_mirror (tree : RawTree α) : inorder (mirror tree) = (inorder tree).reverse := by
  induction tree <;> simp [mirror, inorder, List.reverse_append, List.append_assoc, *]

theorem Double.mirror {key : α} {a b : RawTree α} (step : Double key a b) :
    Double key (mirror a) (mirror b) := by
  induction step with
  | leftLeft => exact .rightRight _ _ _ _ _ _
  | rightRight => exact .leftLeft _ _ _ _ _ _
  | leftRight => exact .rightLeft _ _ _ _ _ _
  | rightLeft => exact .leftRight _ _ _ _ _ _
  | leftContext step x r ih => exact .rightContext _ _ ih
  | rightContext l x step ih => exact .leftContext ih _ _

theorem Step.mirror {key : α} {a b : RawTree α} {rotations : Nat}
    (step : Step key a b rotations) : Step key (mirror a) (mirror b) rotations := by
  cases step with
  | zigLeft => exact .zigRight _ _ _ _
  | zigRight => exact .zigLeft _ _ _ _
  | double step => exact .double step.mirror

theorem Splay.mirror {key : α} {a b : RawTree α} {rotations : Nat}
    (execution : Splay key a b rotations) : Splay key (mirror a) (mirror b) rotations := by
  induction execution with
  | done => exact .done _ _
  | next step rest ih => exact .next step.mirror ih

end MultiSplay.Auxiliary
