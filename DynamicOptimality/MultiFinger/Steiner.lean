import DynamicOptimality.Basic
import Mathlib.Data.List.Count

/-! The reduced Steiner skeleton of a marked ordinary BST.
Only marked keys and genuine branching vertices survive. A separate
physical representation stores suppressed unary chains as tendons. -/

namespace DynamicOptimality.MultiFinger.Steiner

open ChaCha.MTR

variable {α : Type*}

def markedCount (marked : α → Bool) : RawTree α → Nat
  | .empty => 0
  | .node left key right => (if marked key then 1 else 0)+markedCount marked left+markedCount marked right

def present : RawTree α → Bool
  | .empty => false
  | .node _ _ _ => true

def merge (marked : Bool) (left : RawTree α) (key : α) (right : RawTree α) : RawTree α :=
  if marked || (present left && present right) then .node left key right
  else if present left then left else right

def skeleton (marked : α → Bool) : RawTree α → RawTree α
  | .empty => .empty
  | .node left key right => merge (marked key) (skeleton marked left) key (skeleton marked right)

 theorem merge_word_sublist (marked : Bool) (left : RawTree α) (key : α) (right : RawTree α) :
    (merge marked left key right).inorder.Sublist (ChaCha.MTR.Tree.node left key right).inorder := by
  unfold merge
  split
  · exact .refl _
  · split
    · exact (List.sublist_append_left _ _).trans (List.sublist_append_left _ _)
    · exact List.sublist_append_right _ _

 theorem skeleton_word_sublist (marked : α → Bool) (tree : RawTree α) :
    (skeleton marked tree).inorder.Sublist tree.inorder := by
  induction tree with
  | empty => exact .refl _
  | node left key right ihl ihr =>
    exact (merge_word_sublist _ _ _ _).trans ((ihl.append (.refl [key])).append ihr)

 theorem skeleton_present (marked : α → Bool) (tree : RawTree α) :
    present (skeleton marked tree) = decide (0 < markedCount marked tree) := by
  induction tree with
  | empty => rfl
  | node left key right ihl ihr =>
    cases leftShape : skeleton marked left <;> cases rightShape : skeleton marked right <;>
      cases root : marked key <;>
      simp_all [skeleton,merge,present,markedCount] <;> omega

/-- There are fewer than twice as many skeleton vertices as marks.
The inequality also treats the empty marked set exactly. -/
 theorem branching_bound (marked : α → Bool) (tree : RawTree α) :
    (skeleton marked tree).size+(if present (skeleton marked tree) then 1 else 0) ≤
      2*markedCount marked tree := by
  induction tree with
  | empty => simp [skeleton,present,markedCount,Tree.size]
  | node left key right ihl ihr =>
    cases leftShape : skeleton marked left <;> cases rightShape : skeleton marked right <;>
      cases root : marked key <;>
      simp_all [skeleton,merge,present,markedCount,Tree.size] <;> omega

 theorem markedCount_word (marked : α → Bool) (tree : RawTree α) :
    markedCount marked tree = (tree.inorder.filter marked).length := by
  induction tree <;> simp_all [markedCount,Tree.inorder,List.filter_append] <;>
    split <;> simp_all <;> omega

/-- For distinct reference keys, k marked keys give at most 2k skeleton
vertices. Coincident fingers can therefore only decrease this bound. -/
 theorem size_le_marks (marked : α → Bool) (tree : RawTree α) :
    (skeleton marked tree).size ≤ 2*(tree.inorder.filter marked).length := by
  have bound := branching_bound marked tree
  rw [markedCount_word] at bound
  omega

end DynamicOptimality.MultiFinger.Steiner
