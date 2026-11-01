import MultiSplay.JoinIntervals
import MultiSplay.PackedPhysicalTrees

/-! # Constructing a common parent location from arbitrary child locations -/

noncomputable section

namespace MultiSplay.JoinLocation

open Splay.Interface (Element)

variable {l r m : Nat}

/-- Existing child elements keep their global identities. Only the new pivot
uses a new slot; no historical record is renamed or reinitialized. -/
def element (left : Element l → Element m) (right : Element r → Element m) (pivot : Element m) :
    Element (0+l+1+r) → Element m :=
  Function.extend (JoinIntervals.leftEmbedding l r) left
    (Function.extend (JoinIntervals.rightEmbedding l r) right (fun _ => pivot))

theorem left (a : Element l → Element m) (b : Element r → Element m) (pivot : Element m) (x : Element l) :
    element a b pivot (JoinIntervals.leftEmbedding l r x) = a x :=
  (RankEmbedding.external_injective _ _).extend_apply _ _ _

theorem right (a : Element l → Element m) (b : Element r → Element m) (pivot : Element m) (x : Element r) :
    element a b pivot (JoinIntervals.rightEmbedding l r x) = b x := by
  unfold element
  rw [Function.extend_apply' _ _ _ (by rintro ⟨y, same⟩; exact JoinIntervals.disjoint l r y x same)]
  exact (RankEmbedding.external_injective _ _).extend_apply _ _ _

theorem pivot (a : Element l → Element m) (b : Element r → Element m) (root : Element m) :
    element a b root (JoinRanks.pivot l r) = root := by
  unfold element
  rw [Function.extend_apply' _ _ _ (by rintro ⟨y, same⟩; exact JoinIntervals.left_ne_pivot l r y same),
    Function.extend_apply' _ _ _ (by rintro ⟨y, same⟩; exact JoinIntervals.right_ne_pivot l r y same)]

theorem injective (a : Element l → Element m) (b : Element r → Element m) (root : Element m)
    (aInj : Function.Injective a) (bInj : Function.Injective b)
    (separate : ∀ x y, a x ≠ b y) (leftFree : ∀ x, a x ≠ root) (rightFree : ∀ y, b y ≠ root) :
    Function.Injective (element a b root) := by
  intro x y same
  rcases JoinIntervals.cases_element l r x with ⟨x, rfl⟩ | rfl | ⟨x, rfl⟩ <;>
    rcases JoinIntervals.cases_element l r y with ⟨y, rfl⟩ | rfl | ⟨y, rfl⟩
  · rw [left, left] at same
    exact congrArg _ (aInj same)
  · rw [left, pivot] at same
    exact False.elim (leftFree x same)
  · rw [left, right] at same
    exact False.elim (separate x y same)
  · rw [pivot, left] at same
    exact False.elim (leftFree y same.symm)
  · rfl
  · rw [pivot, right] at same
    exact False.elim (rightFree y same.symm)
  · rw [right, left] at same
    exact False.elim (separate y x same.symm)
  · rw [right, pivot] at same
    exact False.elim (rightFree x same)
  · rw [right, right] at same
    exact congrArg _ (bInj same)

theorem separate (a : Element l → Element m) (b : Element r → Element m) (root : Element m)
    {n : Nat} (other : Element n → Element m)
    (leftSeparate : ∀ x y, a x ≠ other y) (rightSeparate : ∀ x y, b x ≠ other y)
    (rootSeparate : ∀ y, root ≠ other y) :
    ∀ x y, element a b root x ≠ other y := by
  intro x y
  rcases JoinIntervals.cases_element l r x with ⟨x, rfl⟩ | rfl | ⟨x, rfl⟩
  · rw [left]
    exact leftSeparate x y
  · rw [pivot]
    exact rootSeparate y
  · rw [right]
    exact rightSeparate x y

theorem bounded (a : Element l → Element m) (b : Element r → Element m) (root : Element m) (limit : Nat)
    (leftBound : ∀ x, (a x).val < limit) (rightBound : ∀ y, (b y).val < limit)
    (rootBound : root.val < limit) : ∀ x, (element a b root x).val < limit := by
  intro x
  rcases JoinIntervals.cases_element l r x with ⟨x, rfl⟩ | rfl | ⟨x, rfl⟩
  · rw [left]
    exact leftBound x
  · rw [pivot]
    exact rootBound
  · rw [right]
    exact rightBound x

end MultiSplay.JoinLocation
