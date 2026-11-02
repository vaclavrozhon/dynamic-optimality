import MultiSplay.Alphabet

/-!
# Dense local ordinals for arbitrary component alphabets

The encoding retains the exact physical tree shape. Its interpretation can be
sparse or nonnumeric; local ordinal positions only record inorder positions.
An inhabitant is used solely for interpretation outside the component interval.
-/

namespace MultiSplay.Alphabet

open DynamicOptimality (RawTree)
open Splay.Tree (BST)
open ChaCha.MTR.Tree (size)

/-- Encode a physical component without changing a single edge or key. -/
theorem exists_encoding {α : Type*} [Inhabited α] (physical : RawTree α) :
    ∃ upper : Nat, ∃ source : BST 0 upper, ∃ alphabet : Nat → α,
      Auxiliary.map alphabet (DynamicOptimality.BST.toRaw source) = physical ∧ upper = size physical := by
  induction physical with
  | empty => exact ⟨0, .empty 0, fun _ => default, rfl, rfl⟩
  | node left key right ihl ihr =>
      obtain ⟨leftUpper, leftTree, leftAlphabet, leftEq, leftSize⟩ := ihl
      obtain ⟨rightUpper, rightTree, rightAlphabet, rightEq, rightSize⟩ := ihr
      let shiftedRight := OrdinalShift.tree (leftUpper + 1) rightTree
      let shiftedAlphabet := fun index => rightAlphabet (index - (leftUpper + 1))
      let alphabet := join leftUpper key leftAlphabet shiftedAlphabet
      refine ⟨leftUpper + 1 + rightUpper, .node leftTree shiftedRight, alphabet, ?_, ?_⟩
      · simp only [alphabet, DynamicOptimality.BST.toRaw, Auxiliary.map, join_left, join_right, join_root]
        rw [leftEq]
        exact congrArg (fun tree => ChaCha.MTR.Tree.node left key tree)
          ((OrdinalShift.tree_alphabet (leftUpper + 1) rightTree rightAlphabet).trans rightEq)
      · simp [size, leftSize, rightSize]

end MultiSplay.Alphabet
