import MultiSplay.Obstructions.ClassicalBalancedFamily
import MultiSplay.GlobalSwitchPhysical

/-! Ordered ordinary BST witnesses for the classical-potential obstruction.
The auxiliary contains H = 2^(2s+1)-1 distinct keys. The trace keeps its
maximum at the root while splaying the predecessor in the left subtree. -/

namespace MultiSplay.Obstructions.Classical

open DynamicOptimality (RawTree)
open DynamicOptimality.SearchRotation
open ChaCha.MTR.Tree

 theorem perfect_word (height key : Nat) (enough : 2^height ≤ key) :
    (perfect height key).inorder = List.range' (key+2-2^height) (2^height-1) := by
  induction height generalizing key with
  | zero => simp [perfect,inorder]
  | succ height ih =>
    have positive : 0 < 2^height := by positivity
    have bound : 2*2^height ≤ key := by simpa only [pow_succ,Nat.mul_comm] using enough
    rw [perfect,inorder,ih (key-2^height) (by omega),ih key (by omega)]
    rw [show key-2^height+2-2^height = key+2-2^(height+1) by rw [pow_succ]; omega]
    rw [show key+1-2^height = (key+2-2^(height+1))+(2^height-1) by rw [pow_succ]; omega]
    rw [show key+2-2^height = (key+2-2^(height+1))+((2^height-1)+1) by rw [pow_succ]; omega]
    change List.range' (key+2-2^(height+1)) (2^height-1) ++
      List.range' ((key+2-2^(height+1))+(2^height-1)) 1 ++
      List.range' ((key+2-2^(height+1))+((2^height-1)+1)) (2^height-1) = _
    rw [List.range'_append_1,List.range'_append_1]
    congr 1
    rw [pow_succ]
    omega

 theorem perfect_ordered (height key : Nat) (enough : 2^height ≤ key) :
    (perfect height key).Ordered := by
  unfold Ordered
  rw [perfect_word height key enough]
  exact List.pairwise_lt_range'

/-- A fully specified, arbitrarily large ordered auxiliary family. The
labels start at 2 merely to keep all subtractions total; this shift has
no effect on shapes, rotations, or the subtree-size potential. -/
 theorem ordered_family (s : Nat) (positive : 0 < s) :
    ∃ (before after : RawTree Nat),
      before.Ordered ∧ after.Ordered ∧
      before.inorder = List.range' 2 (2^(2*s+1)-1) ∧ after.inorder = before.inorder ∧
      before.size = 2^(2*s+1)-1 ∧
      Rotations before after (3*s-1) ∧
      potential before+(s : ℝ)*Real.logb 2 6 < potential after := by
  let key := 2^(2*s+1)
  obtain ⟨finalLeft,first,last,count,gain⟩ := two_splay_family s key positive
  let before := perfect (2*s+1) key
  let after := node (node finalLeft (key-1) empty) key empty
  have ordered := perfect_ordered (2*s+1) key le_rfl
  have word : before.inorder = List.range' 2 (2^(2*s+1)-1) := by
    simpa only [before,key,Nat.add_sub_cancel_left] using perfect_word (2*s+1) key le_rfl
  have physical := Global.pivot_then_left_right first (Global.splay_rotations last) (Rotations.refl empty)
  have trace : Rotations before after (3*s-1) := by
    simpa only [Nat.add_zero,count] using physical
  have same : after.inorder = before.inorder := by
    have firstWord := first.inorder_eq
    have lastWord := last.inorder_eq
    change (node (node finalLeft (key-1) empty) key empty).inorder = _
    change (node (node finalLeft (key-1) empty) key empty).inorder = (perfect (2*s+1) key).inorder
    rw [firstWord]
    simp only [inorder] at lastWord ⊢
    rw [lastWord]
  have afterOrdered : after.Ordered := by unfold Ordered; rw [same]; exact ordered
  have length := perfect_size (2*s+1) key
  refine ⟨before,after,ordered,afterOrdered,word,same,by dsimp [before]; omega,trace,gain⟩

end MultiSplay.Obstructions.Classical
