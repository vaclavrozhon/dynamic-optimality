import ChaCha.Paper20261030.ChargedWeightedJoin

/-! The number of recursive levels of the concrete local join controller.
Its size-sensitive estimate reuses the same sixth-power weight decay as
the charged trace proof. This keeps the telescoping split estimate intact
when the auxiliary routines are implemented by local programs. -/

namespace ChaCha.Paper20261030.Auxiliary.JoinController

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl

variable {α ρ : Type*}

def recursionDepth (left right : Impl α (fun _ => ρ)) : Nat :=
  match left,right with
  | .leaf,right => height right
  | left,.leaf => height left
  | .inner sl lk lv ll lr,.inner sr rk rv rl rr =>
      if delta*sl < sr then recursionDepth (.inner sl lk lv ll lr) rl+1
      else if delta*sr < sl then recursionDepth lr (.inner sr rk rv rl rr)+1
      else 0
termination_by sizeOf left+sizeOf right

theorem recursionDepth_height (left right : Impl α (fun _ => ρ)) :
    recursionDepth left right ≤ height left+height right := by
  cases left with
  | leaf => simp only [recursionDepth,height,Nat.zero_add,le_refl]
  | inner sl lk lv ll lr =>
    cases right with
    | leaf => simp only [recursionDepth,height,Nat.add_zero,le_refl]
    | inner sr rk rv rl rr =>
      rw [recursionDepth]
      split
      · have bound := recursionDepth_height (.inner sl lk lv ll lr) rl
        simp only [height] at bound ⊢
        omega
      · split
        · have bound := recursionDepth_height lr (.inner sr rk rv rl rr)
          simp only [height] at bound ⊢
          omega
        · omega
termination_by sizeOf left+sizeOf right

theorem recursionDepth_right_weight (left right : Impl α (fun _ => ρ))
    (leftBalanced : left.Balanced) (rightBalanced : right.Balanced) (order : left.size ≤ delta*right.size) :
    2^recursionDepth left right*(left.size+1)^6 ≤ (left.size+right.size+2)^6 := by
  cases left with
  | leaf =>
    have bound := balanced_height_power rightBalanced
    have growth : (right.size+1)^3 ≤ (right.size+2)^6 :=
      (Nat.pow_le_pow_left (by omega : right.size+1 ≤ right.size+2) 3).trans
        (Nat.pow_le_pow_right (by omega : 0 < right.size+2) (by decide : 3 ≤ 6))
    simpa only [recursionDepth,Impl.size_leaf,Nat.zero_add,one_pow,Nat.mul_one] using bound.trans growth
  | inner sl lk lv ll lr =>
    cases right with
    | leaf =>
      have positive := leftBalanced.one_le
      simp only [Impl.size_leaf,Impl.size_inner,Nat.mul_zero] at order
      omega
    | inner sr rk rv rl rr =>
      by_cases hright : delta*sl < sr
      · have decay := join_weight_decay sl rl.size rr.size sr leftBalanced.one_le
          rightBalanced.eq rightBalanced.at_root hright
        have child := recursionDepth_right_weight (.inner sl lk lv ll lr) rl
          leftBalanced rightBalanced.left decay.1
        have contraction := sixth_weight _ _ decay.2
        rw [recursionDepth,if_pos hright]
        simp only [Impl.size_inner] at child ⊢
        calc
          2^(recursionDepth (.inner sl lk lv ll lr) rl+1)*(sl+1)^6 =
              2*(2^recursionDepth (.inner sl lk lv ll lr) rl*(sl+1)^6) := by
                simp [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
          _ ≤ 2*(sl+rl.size+2)^6 := Nat.mul_le_mul_left 2 child
          _ ≤ (sl+sr+2)^6 := contraction
      · have hleft : ¬delta*sr < sl := by
          simp only [Impl.size_inner] at order
          omega
        rw [recursionDepth,if_neg hright,if_neg hleft]
        simp only [pow_zero,one_mul]
        exact Nat.pow_le_pow_left (by omega) 6
termination_by sizeOf left+sizeOf right

theorem recursionDepth_left_weight (left right : Impl α (fun _ => ρ))
    (leftBalanced : left.Balanced) (rightBalanced : right.Balanced) (order : right.size ≤ delta*left.size) :
    2^recursionDepth left right*(right.size+1)^6 ≤ (left.size+right.size+2)^6 := by
  cases right with
  | leaf =>
    have depth : recursionDepth left (.leaf : Impl α (fun _ => ρ)) = height left := by
      cases left <;> simp [recursionDepth]
    have bound := balanced_height_power leftBalanced
    have growth : (left.size+1)^3 ≤ (left.size+2)^6 :=
      (Nat.pow_le_pow_left (by omega : left.size+1 ≤ left.size+2) 3).trans
        (Nat.pow_le_pow_right (by omega : 0 < left.size+2) (by decide : 3 ≤ 6))
    simpa only [depth,Impl.size_leaf,Nat.add_zero,Nat.zero_add,one_pow,Nat.mul_one] using bound.trans growth
  | inner sr rk rv rl rr =>
    cases left with
    | leaf =>
      have positive := rightBalanced.one_le
      simp only [Impl.size_leaf,Impl.size_inner,Nat.mul_zero] at order
      omega
    | inner sl lk lv ll lr =>
      have hright : ¬delta*sl < sr := by
        simp only [Impl.size_inner] at order
        omega
      by_cases hleft : delta*sr < sl
      · have size : sl = lr.size+1+ll.size := by have := leftBalanced.eq; omega
        have decay := join_weight_decay sr lr.size ll.size sl rightBalanced.one_le size leftBalanced.at_root.symm hleft
        have child := recursionDepth_left_weight lr (.inner sr rk rv rl rr)
          leftBalanced.right rightBalanced decay.1
        have contraction := sixth_weight _ _ decay.2
        rw [recursionDepth,if_neg hright,if_pos hleft]
        simp only [Impl.size_inner] at child ⊢
        calc
          2^(recursionDepth lr (.inner sr rk rv rl rr)+1)*(sr+1)^6 =
              2*(2^recursionDepth lr (.inner sr rk rv rl rr)*(sr+1)^6) := by
                simp [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
          _ ≤ 2*(lr.size+sr+2)^6 := Nat.mul_le_mul_left 2 child
          _ ≤ (sl+sr+2)^6 := by simpa [Nat.add_comm] using contraction
      · rw [recursionDepth,if_neg hright,if_neg hleft]
        simp only [pow_zero,one_mul]
        exact Nat.pow_le_pow_left (by omega) 6
termination_by sizeOf left+sizeOf right

end ChaCha.Paper20261030.Auxiliary.JoinController
