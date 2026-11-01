import MultiSplay.OrdinalShift
import MultiSplay.SupportedPointer
import Mathlib.Data.List.Sort

/-!
# Interpreting sparse component alphabets

An indexed component uses consecutive ordinal positions internally. Its physical
keys are obtained by an arbitrary interpretation `alphabet`. Pointer operations
commute with this interpretation, including inside an unrelated outside context.
-/

namespace MultiSplay.Alphabet

open DynamicOptimality (RawTree)
open Splay.Tree (BST)
open TangoSquared.MTR (Tree)
open TangoSquared.MTR.Pointer (Frame Cursor Step Trace)
open TangoSquared.Paper20261030.Auxiliary (Rearranges)

variable {α β : Type*}

@[simp] theorem map_size (f : α → β) (source : RawTree α) :
    Tree.size (Auxiliary.map f source) = Tree.size source := by
  induction source <;> simp_all [Auxiliary.map, Tree.size]

@[simp] theorem map_inorder (f : α → β) (source : RawTree α) :
    Tree.inorder (Auxiliary.map f source) = (Tree.inorder source).map f := by
  induction source <;> simp_all [Auxiliary.map, Tree.inorder]

theorem map_congr {f g : α → β} (source : RawTree α)
    (same : ∀ key ∈ Tree.inorder source, f key = g key) :
    Auxiliary.map f source = Auxiliary.map g source := by
  induction source with
  | empty => rfl
  | node left key right ihl ihr =>
      simp only [Auxiliary.map]
      congr 1
      · exact ihl (fun x hx => same x (by simp [Tree.inorder, hx]))
      · exact same key (by simp [Tree.inorder])
      · exact ihr (fun x hx => same x (by simp [Tree.inorder, hx]))

theorem indexed_congr {lower upper : Nat} (source : BST lower upper) {f g : Nat → α}
    (same : ∀ key, lower ≤ key → key < upper → f key = g key) :
    Auxiliary.map f (DynamicOptimality.BST.toRaw source) =
      Auxiliary.map g (DynamicOptimality.BST.toRaw source) :=
  map_congr _ (fun key member =>
    same key ((DynamicOptimality.BST.toRaw_mem source).mp member).1
      ((DynamicOptimality.BST.toRaw_mem source).mp member).2)

theorem indexed_inorder_eq {lower upper : Nat} (source target : BST lower upper)
    (alphabet : Nat → α) :
    Tree.inorder (Auxiliary.map alphabet (DynamicOptimality.BST.toRaw source)) =
      Tree.inorder (Auxiliary.map alphabet (DynamicOptimality.BST.toRaw target)) := by
  rw [map_inorder, map_inorder]
  congr 1
  exact (DynamicOptimality.BST.toRaw_ordered source).eq_of_mem_iff
    (DynamicOptimality.BST.toRaw_ordered target)
    (fun key => (DynamicOptimality.BST.toRaw_mem source).trans
      (DynamicOptimality.BST.toRaw_mem target).symm)

def frame (f : α → β) : Frame α → Frame β
  | .left key right => .left (f key) (Auxiliary.map f right)
  | .right left key => .right (Auxiliary.map f left) (f key)

def cursor (f : α → β) (outside : List (Frame β)) (source : Cursor α) : Cursor β :=
  ⟨Auxiliary.map f source.focus, source.ancestors.map (frame f) ++ outside⟩

theorem step (f : α → β) (outside : List (Frame β)) {a b : Cursor α} (move : Step a b) :
    Step (cursor f outside a) (cursor f outside b) := by
  cases move <;> simp only [cursor, Auxiliary.map, List.map_cons, List.cons_append, frame]
  · exact .left _ _ _ _ _ _
  · exact .right _ _ _ _ _ _
  · exact .upLeft _ _ _ _
  · exact .upRight _ _ _ _
  · exact .rotateRight _ _ _ _ _ _
  · exact .rotateLeft _ _ _ _ _ _

theorem trace (f : α → β) (outside : List (Frame β))
    {a b : Cursor α} {word : List α} {work : Nat} (run : Trace a word b work) :
    Trace (cursor f outside a) (word.map f) (cursor f outside b) work := by
  induction run with
  | nil => exact .nil _
  | step move remaining ih => exact .step (step f outside move) ih
  | @serve a b key word work atKey remaining ih =>
      apply Trace.serve ?_ ih
      cases a with
      | mk focus ancestors =>
          cases focus with
          | empty => simp [Tree.rootKey] at atKey
          | node left root right =>
              simp only [Tree.rootKey, Option.some.injEq] at atKey
              simpa [cursor, Auxiliary.map, Tree.rootKey] using congrArg (fun x => some (f x)) atKey

/-- No surjectivity is needed: the surrounding tree can have unrelated keys. -/
theorem rearranges (f : α → β) {a b : RawTree α} {work : Nat} (run : Rearranges a b work) :
    Rearranges (Auxiliary.map f a) (Auxiliary.map f b) work := by
  intro outside
  obtain ⟨cost, execution, bound⟩ := run []
  exact ⟨cost, by simpa [cursor] using trace f outside execution, bound⟩

/-- Piecewise interpretation for the ordinal interval of a new common root. -/
def join (pivot : Nat) (key : α) (left right : Nat → α) (index : Nat) : α :=
  if index < pivot then left index else if index = pivot then key else right index

@[simp] theorem join_root (pivot : Nat) (key : α) (left right : Nat → α) :
    join pivot key left right pivot = key := by simp [join]

theorem join_left {lower pivot : Nat} (source : BST lower pivot)
    (key : α) (left right : Nat → α) :
    Auxiliary.map (join pivot key left right) (DynamicOptimality.BST.toRaw source) =
      Auxiliary.map left (DynamicOptimality.BST.toRaw source) :=
  indexed_congr source (fun _ _ smaller => by simp [join, smaller])

theorem join_right {pivot upper : Nat} (source : BST (pivot + 1) upper)
    (key : α) (left right : Nat → α) :
    Auxiliary.map (join pivot key left right) (DynamicOptimality.BST.toRaw source) =
      Auxiliary.map right (DynamicOptimality.BST.toRaw source) :=
  indexed_congr source (fun index larger _ => by
    simp [join, show ¬ index < pivot by omega, show index ≠ pivot by omega])

end MultiSplay.Alphabet
