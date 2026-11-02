import MultiSplay.Alphabet

/-!
# Lifting rotations of sparse physical trees

`Rotation depth` is one ordinary BST rotation, at the displayed depth from the
component root. `lift` pulls it back through an arbitrary ordinal interpretation;
the untouched ordinal children are retained literally.
-/

namespace MultiSplay

open DynamicOptimality (RawTree)
open Splay.Tree (BST)

variable {α : Type*}

inductive Rotation : Nat → RawTree α → RawTree α → Prop
  | right (a b c : RawTree α) (x y : α) :
      Rotation 0 (.node (.node a x b) y c) (.node a x (.node b y c))
  | left (a b c : RawTree α) (x y : α) :
      Rotation 0 (.node a x (.node b y c)) (.node (.node a x b) y c)
  | leftContext {depth : Nat} {a b : RawTree α} (step : Rotation depth a b)
      (key : α) (right : RawTree α) :
      Rotation (depth + 1) (.node a key right) (.node b key right)
  | rightContext {depth : Nat} {a b : RawTree α} (left : RawTree α) (key : α)
      (step : Rotation depth a b) :
      Rotation (depth + 1) (.node left key a) (.node left key b)

theorem Rotation.lift {depth : Nat} {a b : RawTree α} (rotation : Rotation depth a b)
    {lower upper : Nat} (source : BST lower upper) (alphabet : Nat → α)
    (same : Auxiliary.map alphabet (DynamicOptimality.BST.toRaw source) = a) :
    ∃ target : BST lower upper, BST.RotationAt depth source target ∧
      Auxiliary.map alphabet (DynamicOptimality.BST.toRaw target) = b := by
  induction rotation generalizing lower upper with
  | right a b c x y =>
      cases source with
      | empty => simp [DynamicOptimality.BST.toRaw, Auxiliary.map] at same
      | node left right =>
          cases left with
          | empty => simp [DynamicOptimality.BST.toRaw, Auxiliary.map] at same
          | node ll lr =>
              simp only [DynamicOptimality.BST.toRaw, Auxiliary.map, ChaCha.MTR.Tree.node.injEq] at same
              refine ⟨.node ll (.node lr right), .root (.right ll lr right), ?_⟩
              simp only [DynamicOptimality.BST.toRaw, Auxiliary.map, same.1.1, same.1.2.1,
                same.1.2.2, same.2.1, same.2.2]
  | left a b c x y =>
      cases source with
      | empty => simp [DynamicOptimality.BST.toRaw, Auxiliary.map] at same
      | node left right =>
          cases right with
          | empty => simp [DynamicOptimality.BST.toRaw, Auxiliary.map] at same
          | node rl rr =>
              simp only [DynamicOptimality.BST.toRaw, Auxiliary.map, ChaCha.MTR.Tree.node.injEq] at same
              refine ⟨.node (.node left rl) rr, .root (.left left rl rr), ?_⟩
              simp only [DynamicOptimality.BST.toRaw, Auxiliary.map, same.1, same.2.1,
                same.2.2.1, same.2.2.2.1, same.2.2.2.2]
  | leftContext rotation key right ih =>
      cases source with
      | empty => simp [DynamicOptimality.BST.toRaw, Auxiliary.map] at same
      | node left other =>
          simp only [DynamicOptimality.BST.toRaw, Auxiliary.map, ChaCha.MTR.Tree.node.injEq] at same
          obtain ⟨target, step, targetEq⟩ := ih left same.1
          exact ⟨.node target other, .leftContext step other, by
            simp [DynamicOptimality.BST.toRaw, Auxiliary.map, targetEq, same.2.1, same.2.2]⟩
  | rightContext left key rotation ih =>
      cases source with
      | empty => simp [DynamicOptimality.BST.toRaw, Auxiliary.map] at same
      | node other right =>
          simp only [DynamicOptimality.BST.toRaw, Auxiliary.map, ChaCha.MTR.Tree.node.injEq] at same
          obtain ⟨target, step, targetEq⟩ := ih right same.2.2
          exact ⟨.node other target, .rightContext other step, by
            simp [DynamicOptimality.BST.toRaw, Auxiliary.map, targetEq, same.1, same.2.1]⟩

end MultiSplay
