import DynamicOptimality.MultiFinger.HandMovesCompression
import DynamicOptimality.MultiFinger.StaticEdges

/-! # Actual adjacent key pairs in the fixed reference tree -/

namespace DynamicOptimality.MultiFinger.Hand

open ChaCha.MTR

variable {α : Type*}

inductive Adjacent : RawTree α → α → α → Prop
  | downLeft (a b c : RawTree α) (child parent : α) :
      Adjacent (.node (.node a child b) parent c) parent child
  | downRight (a b c : RawTree α) (parent child : α) :
      Adjacent (.node a parent (.node b child c)) parent child
  | upLeft (a b c : RawTree α) (child parent : α) :
      Adjacent (.node (.node a child b) parent c) child parent
  | upRight (a b c : RawTree α) (parent child : α) :
      Adjacent (.node a parent (.node b child c)) child parent
  | left {tree : RawTree α} {first last : α} (edge : Adjacent tree first last)
      (key : α) (right : RawTree α) : Adjacent (.node tree key right) first last
  | right {tree : RawTree α} {first last : α} (edge : Adjacent tree first last)
      (left : RawTree α) (key : α) : Adjacent (.node left key tree) first last

theorem Adjacent.members {tree : RawTree α} {first last : α}
    (edge : Adjacent tree first last) : first ∈ tree.inorder ∧ last ∈ tree.inorder := by
  induction edge <;> simp_all [Tree.inorder]

theorem Adjacent.symm {tree : RawTree α} {first last : α}
    (edge : Adjacent tree first last) : Adjacent tree last first := by
  induction edge with
  | downLeft => exact .upLeft ..
  | downRight => exact .upRight ..
  | upLeft => exact .downLeft ..
  | upRight => exact .downRight ..
  | left edge key right ih => exact .left ih key right
  | right edge left key ih => exact .right ih left key

theorem Adjacent.plug {tree : RawTree α} {first last : α}
    (edge : Adjacent tree first last) (frames : List (Pointer.Frame α)) :
    Adjacent (Pointer.plug tree frames) first last := by
  induction frames generalizing tree with
  | nil => exact edge
  | cons frame rest ih =>
      cases frame with
      | left key right => exact ih (.left edge key right)
      | right left key => exact ih (.right edge left key)

/-- A static pointer move between actual keys gives an adjacent key pair. -/
theorem adjacent_of_edge {before after : Pointer.Cursor α}
    (edge : Edge before after) {first last : α}
    (firstKey : before.focus.rootKey = some first)
    (lastKey : after.focus.rootKey = some last) : Adjacent before.tree first last := by
  cases edge with
  | left a b c x y frames =>
      simp only [Tree.rootKey, Option.some.injEq] at firstKey lastKey
      subst first; subst last
      exact (Adjacent.downLeft a b c x y).plug frames
  | right a b c x y frames =>
      simp only [Tree.rootKey, Option.some.injEq] at firstKey lastKey
      subst first; subst last
      exact (Adjacent.downRight a b c x y).plug frames
  | upLeft a b key frames =>
      cases a with
      | empty => simp [Tree.rootKey] at firstKey
      | node left root right =>
          simp only [Tree.rootKey, Option.some.injEq] at firstKey lastKey
          subst first; subst last
          exact (Adjacent.upLeft left right b root key).plug frames
  | upRight a b key frames =>
      cases b with
      | empty => simp [Tree.rootKey] at firstKey
      | node left root right =>
          simp only [Tree.rootKey, Option.some.injEq] at firstKey lastKey
          subst first; subst last
          exact (Adjacent.upRight a left right key root).plug frames

theorem node_distinct {left right : RawTree α} {root : α}
    (distinct : (Tree.inorder (.node left root right)).Nodup) :
    left.inorder.Nodup ∧ right.inorder.Nodup ∧ root ∉ left.inorder ∧
      root ∉ right.inorder ∧ ∀ key ∈ left.inorder, key ∉ right.inorder := by
  have outer := List.nodup_append.mp distinct
  have inner := List.nodup_append.mp outer.1
  refine ⟨inner.1, outer.2.1, ?_, ?_, ?_⟩
  · intro member
    exact inner.2.2 root member root (by simp) rfl
  · intro member
    exact outer.2.2 root (by simp) root member rfl
  · intro key leftMember rightMember
    exact outer.2.2 key (by simp [leftMember]) key rightMember rfl

end DynamicOptimality.MultiFinger.Hand
