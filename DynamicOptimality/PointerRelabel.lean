import DynamicOptimality.Basic

/-! Relabeling the existing ordinary BST and its adjacent-pointer execution.
Every operation and its cost is preserved. Strictly increasing relabelings
also preserve BST order; no second tree or execution model is introduced. -/

namespace DynamicOptimality.Relabel

open TangoSquared.MTR

variable {α β γ : Type*}

def tree (f : α → β) : RawTree α → RawTree β
  | .empty => .empty
  | .node l x r => .node (tree f l) (f x) (tree f r)

@[simp] theorem tree_word (f : α → β) (t : RawTree α) :
    (tree f t).inorder = t.inorder.map f := by
  induction t <;> simp [tree,Tree.inorder , *]

@[simp] theorem tree_size (f : α → β) (t : RawTree α) : (tree f t).size = t.size := by
  induction t <;> simp [tree,Tree.size , *]

@[simp] theorem tree_root (f : α → β) (t : RawTree α) :
    (tree f t).rootKey = t.rootKey.map f := by cases t <;> rfl

theorem tree_comp (f : α → β) (g : β → γ) (t : RawTree α) :
    tree g (tree f t) = tree (g ∘ f) t := by
  induction t <;> simp [tree , *]

@[simp] theorem tree_id (t : RawTree α) : tree id t = t := by
  induction t <;> simp [tree , *]

theorem tree_leftInverse (f : α → β) (g : β → α) (inverse : Function.LeftInverse g f)
    (t : RawTree α) : tree g (tree f t) = t := by
  rw [tree_comp]
  have functions : g ∘ f = id := funext inverse
  rw [functions,tree_id]

theorem tree_ordered [LinearOrder α] [LinearOrder β] (f : α → β)
    (increasing : StrictMono f) {t : RawTree α} (ordered : t.Ordered) :
    (tree f t).Ordered := by
  change ((tree f t).inorder).Pairwise _
  rw [tree_word,List.pairwise_map]
  exact ordered.imp (fun h => increasing h)

def frame (f : α → β) : Pointer.Frame α → Pointer.Frame β
  | .left x r => .left (f x) (tree f r)
  | .right l x => .right (tree f l) (f x)

def cursor (f : α → β) (c : Pointer.Cursor α) : Pointer.Cursor β :=
  ⟨tree f c.focus,c.ancestors.map (frame f)⟩

theorem plug (f : α → β) (t : RawTree α) (frames : List (Pointer.Frame α)) :
    Pointer.plug (tree f t) (frames.map (frame f)) = tree f (Pointer.plug t frames) := by
  induction frames generalizing t with
  | nil => rfl
  | cons first rest ih =>
    cases first with
    | left parent right => exact ih (.node t parent right)
    | right left parent => exact ih (.node left parent t)

@[simp] theorem cursor_tree (f : α → β) (c : Pointer.Cursor α) :
    (cursor f c).tree = tree f c.tree := plug f c.focus c.ancestors

@[simp] theorem cursor_root (f : α → β) (t : RawTree α) :
    cursor f (.atRoot t) = .atRoot (tree f t) := rfl

theorem step (f : α → β) {c d : Pointer.Cursor α} (move : Pointer.Step c d) :
    Pointer.Step (cursor f c) (cursor f d) := by
  cases move with
  | left => exact .left _ _ _ _ _ _
  | right => exact .right _ _ _ _ _ _
  | upLeft => exact .upLeft _ _ _ _
  | upRight => exact .upRight _ _ _ _
  | rotateRight => exact .rotateRight _ _ _ _ _ _
  | rotateLeft => exact .rotateLeft _ _ _ _ _ _

theorem trace (f : α → β) {c d : Pointer.Cursor α} {requests : List α} {cost : Nat}
    (run : Pointer.Trace c requests d cost) :
    Pointer.Trace (cursor f c) (requests.map f) (cursor f d) cost := by
  induction run with
  | nil => exact .nil _
  | step move rest ih => exact .step (step f move) ih
  | serve atKey rest ih =>
    apply Pointer.Trace.serve _ ih
    change (tree f _).rootKey = _
    rw [tree_root,atKey]
    rfl

theorem access (f : α → β) {x : α} {before after : RawTree α} {cost : Nat}
    (run : Pointer.Access x before after cost) :
    Pointer.Access (f x) (tree f before) (tree f after) cost := by
  obtain ⟨last,finalTree,run⟩ := run
  refine ⟨cursor f last,?_,?_⟩
  · rw [cursor_tree,finalTree]
  · simpa only [cursor_root,List.map_cons,List.map_nil] using trace f run

theorem execution (f : α → β) {before after : RawTree α} {requests : List α} {cost : Nat}
    (run : Pointer.Execution before requests after cost) :
    Pointer.Execution (tree f before) (requests.map f) (tree f after) cost := by
  induction run with
  | nil => exact .nil _
  | cons first rest ih => exact .cons (access f first) ih

end DynamicOptimality.Relabel
