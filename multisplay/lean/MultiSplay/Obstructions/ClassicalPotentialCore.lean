import MultiSplay.AuxiliarySplay
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! The classical real sum-of-log-subtree-sizes potential. These local
identities refer to literal ordinary rotations with arbitrary hanging
subtrees, not to an assumed amortized interface. -/

namespace MultiSplay.Obstructions.Classical

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree

variable {α : Type*}

noncomputable def rank (size : Nat) : ℝ := Real.logb 2 size

noncomputable def potential : RawTree α → ℝ
  | .empty => 0
  | .node left _ right => potential left+potential right+rank (left.size+1+right.size)

theorem rank_mono {a b : Nat} (positive : 0 < a) (bound : a ≤ b) : rank a ≤ rank b := by
  apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
  · exact_mod_cast positive
  · exact_mod_cast bound

theorem zig_identity (a b : RawTree α) (x key : α) :
    potential (.node (.node a x b) key .empty)+rank (b.size+1) =
      potential (.node a x (.node b key .empty))+rank (a.size+1+b.size) := by
  simp only [potential,size,Nat.add_zero,Nat.add_assoc]
  ring

theorem zig_nondecrease (a b : RawTree α) (x key : α) :
    potential (.node a x (.node b key .empty)) ≤ potential (.node (.node a x b) key .empty) := by
  have identity := zig_identity a b x key
  have ranks := rank_mono (a := b.size+1) (b := a.size+1+b.size) (by omega) (by omega)
  linarith

theorem double_identity (a b c : RawTree α) (x y key : α) :
    potential (.node (.node (.node a x b) y c) key .empty)+
        rank (b.size+1+(c.size+1))+rank (c.size+1) =
      potential (.node a x (.node b y (.node c key .empty)))+
        rank (a.size+1+b.size)+rank ((a.size+1+b.size)+1+c.size) := by
  have total : ((a.size+1+b.size)+1+c.size)+1 = a.size+1+(b.size+1+(c.size+1)) := by omega
  simp only [potential,size,Nat.add_zero,total]
  ring

theorem double_nondecrease (a b c : RawTree α) (x y key : α)
    (heavy : b.size+1+(c.size+1) ≤ a.size) :
    potential (.node a x (.node b y (.node c key .empty))) ≤
      potential (.node (.node (.node a x b) y c) key .empty) := by
  have identity := double_identity a b c x y key
  have first := rank_mono (a := b.size+1+(c.size+1)) (b := a.size+1+b.size) (by omega) (by omega)
  have second := rank_mono (a := c.size+1) (b := (a.size+1+b.size)+1+c.size) (by omega) (by omega)
  linarith

/-- Each balanced-family right-right double increases the potential by
strictly more than log₂ 6. This is a general algebraic lemma, not a finite
numerical test. -/
theorem double_increase (a b c : RawTree α) (x y key : α)
    (leftSize : a.size = 2*b.size+1) (targetSize : c.size+1 = b.size) :
    potential (.node a x (.node b y (.node c key .empty)))+Real.logb 2 6 <
      potential (.node (.node (.node a x b) y c) key .empty) := by
  have identity := double_identity a b c x y key
  have oldParent : b.size+1+(c.size+1) = 2*b.size+1 := by omega
  have newChild : a.size+1+b.size = 3*b.size+2 := by omega
  have newParent : (a.size+1+b.size)+1+c.size = 4*b.size+2 := by omega
  rw [oldParent,targetSize,newParent,newChild] at identity
  have positive : (0 : ℝ) < b.size := by exact_mod_cast (show 0 < b.size by omega)
  have product : (6 : ℝ)*((2*b.size+1)*b.size) < (3*b.size+2)*(4*b.size+2) := by nlinarith
  have logs := Real.logb_lt_logb (b := 2) (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < 6*((2*b.size+1)*b.size)) product
  rw [Real.logb_mul (by norm_num : (6 : ℝ) ≠ 0) (by positivity),
    Real.logb_mul (by positivity : (2*(b.size : ℝ)+1) ≠ 0) (ne_of_gt positive),
    Real.logb_mul (by positivity : (3*(b.size : ℝ)+2) ≠ 0) (by positivity)] at logs
  simp only [rank,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at identity
  linarith

/-- All nodes on the current right spine have at least as many nodes on
the left as on the right. No condition is imposed off that spine. -/
def RightHeavy : RawTree α → Prop
  | .empty => True
  | .node left _ right => right.size ≤ left.size ∧ RightHeavy right

inductive MaxDouble (key : α) : RawTree α → RawTree α → Prop
  | root (a b c : RawTree α) (x y : α) :
    MaxDouble key (.node a x (.node b y (.node c key .empty)))
      (.node (.node (.node a x b) y c) key .empty)
  | right {before after : RawTree α} (left : RawTree α) (root : α)
      (step : MaxDouble key before after) : MaxDouble key (.node left root before) (.node left root after)

 theorem MaxDouble.ordinary {key : α} {before after : RawTree α} (step : MaxDouble key before after) :
    Auxiliary.Double key before after := by
  induction step with
  | root => exact .rightRight _ _ _ _ _ _
  | right left root step ih => exact .rightContext left root ih

 theorem MaxDouble.size {key : α} {before after : RawTree α} (step : MaxDouble key before after) :
    after.size = before.size := by
  have word := step.ordinary.inorder_eq
  rw [← length_inorder,← length_inorder,word]

 theorem MaxDouble.heavy {key : α} {before after : RawTree α} (step : MaxDouble key before after)
    (heavy : RightHeavy before) : RightHeavy after := by
  induction step with
  | root => exact ⟨Nat.zero_le _,trivial⟩
  | right left root step ih =>
    exact ⟨by simpa only [step.size] using heavy.1,ih heavy.2⟩

 theorem MaxDouble.potential {key : α} {before after : RawTree α} (step : MaxDouble key before after)
    (heavy : RightHeavy before) : potential before ≤ potential after := by
  induction step with
  | root a b c x y => exact double_nondecrease a b c x y key (by simpa only [ChaCha.MTR.Tree.size,Nat.add_zero] using heavy.1)
  | right left root step ih =>
    simp only [Classical.potential,step.size]
    linarith [ih heavy.2]

inductive MaxDoubles (key : α) : RawTree α → RawTree α → Nat → Prop
  | refl (tree : RawTree α) : MaxDoubles key tree tree 0
  | step {before middle after : RawTree α} {count : Nat}
      (first : MaxDouble key before middle) (rest : MaxDoubles key middle after count) :
      MaxDoubles key before after (count+1)

 theorem MaxDoubles.append {key : α} {before middle after : RawTree α} {front back : Nat}
    (first : MaxDoubles key before middle front) (last : MaxDoubles key middle after back) :
    MaxDoubles key before after (front+back) := by
  induction first with
  | refl => simpa using last
  | step first rest ih => simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using MaxDoubles.step first (ih last)

 theorem MaxDoubles.right {key : α} {before after : RawTree α} {count : Nat}
    (trace : MaxDoubles key before after count) (left : RawTree α) (root : α) :
    MaxDoubles key (.node left root before) (.node left root after) count := by
  induction trace with
  | refl => exact .refl _
  | step first rest ih => exact .step (.right left root first) ih

 theorem MaxDoubles.follow {key : α} {before middle after : RawTree α} {count cost : Nat}
    (trace : MaxDoubles key before middle count) (last : Auxiliary.Splay key middle after cost) :
    Auxiliary.Splay key before after (2*count+cost) := by
  induction trace with
  | refl => simpa using last
  | step first rest ih =>
    simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      Auxiliary.Splay.next (.double first.ordinary) (ih last)

 theorem MaxDoubles.finish {key : α} {before left : RawTree α} {count : Nat}
    (trace : MaxDoubles key before (.node left key .empty) count) :
    Auxiliary.Splay key before (.node left key .empty) (2*count) := by
  simpa only [Nat.add_zero] using trace.follow (Auxiliary.Splay.done left .empty)

 theorem MaxDoubles.heavy {key : α} {before after : RawTree α} {count : Nat}
    (trace : MaxDoubles key before after count) (heavy : RightHeavy before) : RightHeavy after := by
  induction trace with
  | refl => exact heavy
  | step first rest ih => exact ih (first.heavy heavy)

 theorem MaxDoubles.potential {key : α} {before after : RawTree α} {count : Nat}
    (trace : MaxDoubles key before after count) (heavy : RightHeavy before) : potential before ≤ potential after := by
  induction trace with
  | refl => exact le_rfl
  | step first rest ih => exact (first.potential heavy).trans (ih (first.heavy heavy))

end MultiSplay.Obstructions.Classical
