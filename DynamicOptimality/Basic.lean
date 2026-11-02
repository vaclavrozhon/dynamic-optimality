import Splay.Tree.Basic
import Splay.Tree.Rotation
import ChaCha.Paper20261030.AuxiliaryRotations

/-!
# Shared BST definitions and the indexed-to-pointer representation

`BST lower upper` is the existing splay library's tree containing exactly
the natural keys in `[lower, upper)`. `RawTree` and `Pointer` are the
existing Cha-Cha library's ordinary key tree and adjacent-pointer model.
These are aliases, not duplicate inductive definitions. The conversion
below forgets interval indices while preserving every key and child.
-/

namespace DynamicOptimality

abbrev BST := Splay.Tree.BST
abbrev RawTree := ChaCha.MTR.Tree
abbrev PointerCursor := ChaCha.MTR.Pointer.Cursor
abbrev PointerStep := @ChaCha.MTR.Pointer.Step
abbrev PointerExecution := @ChaCha.MTR.Pointer.Execution
abbrev RotationAt := @Splay.Tree.BST.RotationAt

namespace BST

def toRaw : {lower upper : Nat} → BST lower upper → RawTree Nat
  | _, _, .empty _ => .empty
  | _, _, .node (root := key) l r => .node (toRaw l) key (toRaw r)

theorem toRaw_size {lower upper : Nat} (t : BST lower upper) :
    ChaCha.MTR.Tree.size (toRaw t) = t.size := by
  induction t <;> simp [toRaw,ChaCha.MTR.Tree.size,Splay.Tree.BST.size, *]

theorem toRaw_mem {lower upper key : Nat} (t : BST lower upper) :
    key ∈ ChaCha.MTR.Tree.inorder (toRaw t) ↔ lower ≤ key ∧ key < upper := by
  induction t with
  | empty boundary => simp [toRaw,ChaCha.MTR.Tree.inorder]
  | @node lower root upper l r ihl ihr =>
    have hl := l.lower_le_upper
    have hr := r.lower_le_upper
    simp only [toRaw,ChaCha.MTR.Tree.inorder,List.mem_append,List.mem_singleton,ihl,ihr]
    omega

theorem toRaw_ordered {lower upper : Nat} (t : BST lower upper) :
    ChaCha.MTR.Tree.Ordered (toRaw t) := by
  induction t with
  | empty boundary => exact List.Pairwise.nil
  | @node lower root upper l r ihl ihr =>
    unfold ChaCha.MTR.Tree.Ordered at *
    simp only [toRaw,ChaCha.MTR.Tree.inorder,List.pairwise_append,List.pairwise_singleton,
      List.mem_append,List.mem_singleton]
    refine ⟨⟨ihl,True.intro,?_⟩,ihr,?_⟩
    · intro a ha b hb
      subst b
      exact (toRaw_mem l |>.mp ha).2
    · intro a ha b hb
      have hbr := (toRaw_mem r |>.mp hb).1
      rcases ha with ha | rfl
      · have hal := (toRaw_mem l |>.mp ha).2
        omega
      · omega

/-- A rotation at depth `d` is performed by walking to its actual pivot,
rotating once, and walking back. The cost is at most `2*d+1`. -/
theorem rotation_pointer {depth lower upper : Nat} {t u : BST lower upper}
    (h : Splay.Tree.BST.RotationAt depth t u) :
    ChaCha.Paper20261030.Auxiliary.Rearranges (toRaw t) (toRaw u) (2 * depth + 1) := by
  induction h with
  | root h =>
    cases h with
    | right a b c =>
      intro ancestors
      exact ⟨1,.step (.rotateRight (toRaw a) (toRaw b) (toRaw c) _ _ ancestors) (.nil _),le_rfl⟩
    | left a b c =>
      intro ancestors
      exact ⟨1,.step (.rotateLeft (toRaw a) (toRaw b) (toRaw c) _ _ ancestors) (.nil _),le_rfl⟩
  | leftContext step r ih =>
    refine (ih.left ?_).mono (by omega)
    · cases step with
      | root h => cases h <;> simp [toRaw]
      | leftContext => simp [toRaw]
      | rightContext => simp [toRaw]
  | rightContext l step ih =>
    refine (ih.right ?_).mono (by omega)
    · cases step with
      | root h => cases h <;> simp [toRaw]
      | leftContext => simp [toRaw]
      | rightContext => simp [toRaw]

end BST
end DynamicOptimality
