import MultiSplay.PackedProgram
import MultiSplay.ForestProgram

/-! # Exact physical trees represented by the packed local ordinals -/

namespace MultiSplay.PackedSplay

open DynamicOptimality (RawTree)
open Splay.Interface (Element)
open Splay.Tree (BST)

variable {n m l r : Nat}

/-- Internal key k occupies external position 2k+1. The value outside the
local key interval is irrelevant to the interpretation of a valid tree. -/
def label (element : Element n → Element m) (key : Nat) : Element m :=
  if inside : key < n then element ⟨2*key+1, by omega⟩ else element ⟨0, by omega⟩

theorem label_inside (element : Element n → Element m) (key : Nat) (inside : key < n) :
    label element key = element ⟨2*key+1, by omega⟩ := by simp [label, inside]

def physical (element : Element n → Element m) (tree : BST 0 n) : RawTree (Element m) :=
  Auxiliary.map (label element) (DynamicOptimality.BST.toRaw tree)

def Trees.physical (trees : Trees m) : RawTree (Element m) := PackedSplay.physical trees.element trees.splay
def Trees.comparator (trees : Trees m) : RawTree (Element m) := PackedSplay.physical trees.element trees.comparison

theorem shifted_physical (offset : Nat) {size : Nat} (fits : offset + size ≤ n)
    (element : Element n → Element m) (tree : BST 0 size) :
    Auxiliary.map (label element) (DynamicOptimality.BST.toRaw (OrdinalShift.tree offset tree)) =
      physical (element ∘ RankEmbedding.external offset fits) tree := by
  calc
    _ = Auxiliary.map (fun key => label (element ∘ RankEmbedding.external offset fits) (key-offset))
        (DynamicOptimality.BST.toRaw (OrdinalShift.tree offset tree)) := by
      apply Alphabet.indexed_congr
      intro key lower upper
      rw [label_inside element key (by omega), label_inside _ (key-offset) (by omega)]
      apply congrArg element
      apply Fin.ext
      dsimp [RankEmbedding.external]
      omega
    _ = _ := OrdinalShift.tree_alphabet offset tree (label (element ∘ RankEmbedding.external offset fits))

theorem physical_join (element : Element (0+l+1+r) → Element m) (left : BST 0 l) (right : BST 0 r) :
    physical element (JoinRanks.tree left right) =
      .node (physical (element ∘ JoinIntervals.leftEmbedding l r) left) (element (JoinRanks.pivot l r))
        (physical (element ∘ JoinIntervals.rightEmbedding l r) right) := by
  simp only [physical, JoinRanks.tree, DynamicOptimality.BST.toRaw, Auxiliary.map]
  rw [shifted_physical 0 (by omega), shifted_physical (0+l+1) (by omega)]
  rw [label_inside element (0+l) (by omega)]
  rfl

theorem physical_inorder (element : Element n → Element m) (before after : BST 0 n) :
    ChaCha.MTR.Tree.inorder (physical element before) = ChaCha.MTR.Tree.inorder (physical element after) :=
  Alphabet.indexed_inorder_eq before after (label element)

theorem rotation_physical {lower upper depth : Nat} {before after : BST lower upper}
    (rotation : BST.RotationAt depth before after) (alphabet : Nat → α) :
    MultiSplay.Rotation depth (Auxiliary.map alphabet (DynamicOptimality.BST.toRaw before))
      (Auxiliary.map alphabet (DynamicOptimality.BST.toRaw after)) := by
  induction rotation with
  | root step =>
      cases step with
      | right a b c => exact .right _ _ _ _ _
      | left a b c => exact .left _ _ _ _ _
  | leftContext step right ih => exact .leftContext ih _ _
  | rightContext left step ih => exact .rightContext _ _ ih

end MultiSplay.PackedSplay
