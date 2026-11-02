import ChaCha.Entropy.WeightedMedianSelection
import ChaCha.Entropy.WeightedMedianAnalytic

/-! # Assemble the binary auxiliary reference around a weighted median

The larger of the two outer intervals is isolated by the first binary
split. A second split, when needed, separates the pivot from the smaller
interval. This is an ordinary ordered leaf reference on exactly the
original keys, with no positive-weight assumption on a whole side.
-/

namespace ChaCha.Entropy

open PreferredProjection

def optionalLeaves : Option (PrefRouter Int) → List Int
  | none => []
  | some tree => tree.leaves

noncomputable def optionalMass (f : Int → Nat) : Option (PrefRouter Int) → ℝ
  | none => 0
  | some tree => alternationMass f tree

def aroundMedian (f : Int → Nat) (pivot : Int) :
    Option (PrefRouter Int) → Option (PrefRouter Int) → PrefRouter Int
  | none,none => .leaf pivot
  | some left,none => .fork false left (.leaf pivot)
  | none,some right => .fork false (.leaf pivot) right
  | some left,some right =>
      if weight f left.leaves ≤ weight f right.leaves then
        .fork false (.fork false left (.leaf pivot)) right
      else .fork false left (.fork false (.leaf pivot) right)

theorem aroundMedian_leaves (f : Int → Nat) (pivot : Int)
    (left right : Option (PrefRouter Int)) :
    (aroundMedian f pivot left right).leaves = optionalLeaves left ++ pivot::optionalLeaves right := by
  cases left <;> cases right <;> simp [aroundMedian,optionalLeaves,PrefRouter.leaves]
  split <;> simp [PrefRouter.leaves,List.append_assoc]

theorem aroundMedian_charge (f : Int → Nat) (pivot : Int)
    (left right : Option (PrefRouter Int)) (pivotPositive : 0 < f pivot)
    (leftSmall : 2*weight f (optionalLeaves left) ≤
      weight f (optionalLeaves left)+f pivot+weight f (optionalLeaves right))
    (rightSmall : 2*weight f (optionalLeaves right) ≤
      weight f (optionalLeaves left)+f pivot+weight f (optionalLeaves right)) :
    (weight f (optionalLeaves left):ℝ)+(f pivot:ℝ)+(weight f (optionalLeaves right):ℝ)+
      2*optionalMass f left+2*optionalMass f right ≤
        2*alternationMass f (aroundMedian f pivot left right)+(f pivot:ℝ) := by
  have pivotReal : 0 < (f pivot:ℝ) := by exact_mod_cast pivotPositive
  have leftReal : 2*(weight f (optionalLeaves left):ℝ) ≤
      (weight f (optionalLeaves left):ℝ)+(f pivot:ℝ)+(weight f (optionalLeaves right):ℝ) := by
    exact_mod_cast leftSmall
  have rightReal : 2*(weight f (optionalLeaves right):ℝ) ≤
      (weight f (optionalLeaves left):ℝ)+(f pivot:ℝ)+(weight f (optionalLeaves right):ℝ) := by
    exact_mod_cast rightSmall
  cases left with
  | none =>
      cases right with
      | none => simp [optionalLeaves,optionalMass,aroundMedian,alternationMass]
      | some right =>
          have charge := median_right_charge (left := 0) (pivot := (f pivot:ℝ))
            (right := (weight f right.leaves:ℝ)) (by rfl) pivotReal (Nat.cast_nonneg _)
            (by simpa only [optionalLeaves,weight_nil,Nat.cast_zero,zero_add] using rightReal) (Nat.cast_nonneg _)
          simp only [optionalLeaves,optionalMass,aroundMedian,alternationMass,PrefRouter.leaves,
            weight_cons,weight_nil,Nat.cast_zero,zero_add,add_zero,mul_zero] at charge ⊢
          linarith
  | some left =>
      cases right with
      | none =>
          have charge := median_left_charge (left := (weight f left.leaves:ℝ)) (pivot := (f pivot:ℝ))
            (right := 0) (Nat.cast_nonneg _) pivotReal (by rfl)
            (by simpa only [optionalLeaves,weight_nil,Nat.cast_zero,add_zero] using leftReal) (Nat.cast_nonneg _)
          simp only [optionalLeaves,optionalMass,aroundMedian,alternationMass,PrefRouter.leaves,
            weight_cons,weight_nil,Nat.cast_zero,zero_add,add_zero,mul_zero] at charge ⊢
          linarith
      | some right =>
          by_cases first : weight f left.leaves ≤ weight f right.leaves
          · have charge := median_right_charge (Nat.cast_nonneg (weight f left.leaves)) pivotReal
              (Nat.cast_nonneg (weight f right.leaves)) rightReal (by exact_mod_cast first)
            have extra := binary_toll_nonnegative (Nat.cast_nonneg (weight f left.leaves)) pivotReal.le
            simp only [optionalLeaves,optionalMass,aroundMedian,if_pos first,alternationMass,PrefRouter.leaves,
              weight_append,weight_cons,weight_nil,Nat.cast_add,Nat.cast_zero,add_zero] at charge ⊢
            nlinarith
          · have charge := median_left_charge (Nat.cast_nonneg (weight f left.leaves)) pivotReal
              (Nat.cast_nonneg (weight f right.leaves)) leftReal (by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge first)))
            have extra := binary_toll_nonnegative pivotReal.le (Nat.cast_nonneg (weight f right.leaves))
            simp only [optionalLeaves,optionalMass,aroundMedian,if_neg first,alternationMass,PrefRouter.leaves,
              weight_append,weight_cons,weight_nil,Nat.cast_add,Nat.cast_zero,add_zero] at charge ⊢
            nlinarith

theorem aroundMedian_entropy (f : Int → Nat) (pivot : Int)
    (left right : Option (PrefRouter Int)) (pivotPositive : 0 < f pivot)
    (leftSmall : 2*weight f (optionalLeaves left) ≤
      weight f (optionalLeaves left)+f pivot+weight f (optionalLeaves right))
    (rightSmall : 2*weight f (optionalLeaves right) ≤
      weight f (optionalLeaves left)+f pivot+weight f (optionalLeaves right))
    (leftBound : entropyMass f (optionalLeaves left) ≤
      Real.log 3*(2*optionalMass f left+(weight f (optionalLeaves left):ℝ)))
    (rightBound : entropyMass f (optionalLeaves right) ≤
      Real.log 3*(2*optionalMass f right+(weight f (optionalLeaves right):ℝ))) :
    entropyMass f (aroundMedian f pivot left right).leaves ≤
      Real.log 3*(2*alternationMass f (aroundMedian f pivot left right)+
        (weight f (aroundMedian f pivot left right).leaves:ℝ)) := by
  have ternary := ternary_entropy_le (Nat.cast_nonneg (weight f (optionalLeaves left)))
    (show 0 < (f pivot:ℝ) by exact_mod_cast pivotPositive) (Nat.cast_nonneg (weight f (optionalLeaves right)))
  have charge := mul_le_mul_of_nonneg_left
    (aroundMedian_charge f pivot left right pivotPositive leftSmall rightSmall) log_three_nonnegative
  rw [aroundMedian_leaves,entropyMass_split]
  simp only [weight_append,weight_cons,Nat.cast_add]
  nlinarith

end ChaCha.Entropy
