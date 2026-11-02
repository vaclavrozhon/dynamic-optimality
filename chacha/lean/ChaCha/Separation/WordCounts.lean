import ChaCha.AnchorPrimary
import Mathlib.Tactic.Linarith

/-!
# Repeated bit reversal with the first-visit-free convention

The complete Boolean reference counter here is the existing `primaryCount`.
The identity retains the exact initialization correction `2^height-1`.
Transferring this word to the sparse numeric keys is a separate step.
-/

namespace ChaCha.Separation

open Primary BitReversal

/-- Repeated bit reversal, constructed recursively without dropping any
occurrences. Height zero contains the requested number of empty keys. -/
def repeatedWord : Nat → Nat → List Key
  | 0, copies => List.replicate copies []
  | height+1, copies =>
      (repeatedWord height copies).flatMap (fun key => [false::key,true::key])

theorem repeatedWord_length (height copies : Nat) :
    (repeatedWord height copies).length = copies * 2^height := by
  induction height with
  | zero => simp [repeatedWord]
  | succ height ih =>
      rw [repeatedWord,length_flatMap_pairs,ih,pow_succ]
      ac_rfl

theorem repeatedWord_add (height a b : Nat) :
    repeatedWord height (a+b) = repeatedWord height a ++ repeatedWord height b := by
  induction height with
  | zero => exact List.replicate_add _ _ _
  | succ height ih => simp only [repeatedWord,ih,List.flatMap_append]

theorem repeatedWord_one (height : Nat) : repeatedWord height 1 = word height := by
  induction height with
  | zero => rfl
  | succ height ih => simp only [repeatedWord,word,ih]

theorem repeatedWord_zero (height : Nat) : repeatedWord height 0 = [] := by
  induction height with
  | zero => rfl
  | succ height ih => simp only [repeatedWord,ih,List.flatMap_nil]

theorem repeatedWord_eq_periods (height copies : Nat) :
    repeatedWord height copies = (List.replicate copies (word height)).flatten := by
  induction copies with
  | zero => exact repeatedWord_zero height
  | succ copies ih =>
      conv_lhs => rw [show copies+1 = 1+copies by omega,repeatedWord_add,repeatedWord_one,ih]
      simp [List.replicate_succ]

theorem pairs_alternations (copies : Nat) : alternations (pairs copies) = 2*copies-1 := by
  cases copies with
  | zero => rfl
  | succ copies =>
      change changesFrom false (true::pairs copies) = _
      rw [changesFrom_cons,edgeChange_of_ne (by decide : (false : Bool) ≠ true),changes_pairs]
      omega

theorem repeatedWord_primary_step (height copies : Nat) :
    primaryCount (height+1) (repeatedWord (height+1) copies) =
      (2*(copies*2^height)-1)+2*primaryCount height (repeatedWord height copies) := by
  unfold primaryCount primaryAlternations
  rw [owners_sum_succ]
  simp only [repeatedWord,root_projection,pairs_alternations,child_projection,repeatedWord_length]
  omega

/-- The linear counter equals `height*length-(2^height-1)` for every
positive number of complete periods. No cyclic boundary is charged. -/
theorem repeatedWord_primary_exact (height copies : Nat) (positive : 0 < copies) :
    primaryCount height (repeatedWord height copies)+2^height =
      height*(copies*2^height)+1 := by
  induction height with
  | zero => simp [primaryCount,primaryAlternations,owners]
  | succ height ih =>
      have powerPositive : 0 < 2^height := pow_pos (by decide) _
      have lengthPositive : 0 < copies*2^height := Nat.mul_pos positive powerPositive
      rw [repeatedWord_primary_step,pow_succ]
      have subtraction : 2*(copies*2^height)-1+1 = 2*(copies*2^height) := by omega
      nlinarith

end ChaCha.Separation
