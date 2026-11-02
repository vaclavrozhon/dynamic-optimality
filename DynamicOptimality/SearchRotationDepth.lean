import DynamicOptimality.SearchRotationModel
import ChaCha.CachePortDepth

/-! # Search depth under arbitrary rotations of an ordered raw BST

These lemmas apply to any linearly ordered key type. They retain the
actual input and output trees and distinguish a failed search from depth
zero. They are useful when an access exposes its requested key only at
the end of a rotation trace.
-/

namespace DynamicOptimality.SearchRotation.RawDepth

open ChaCha.MTR ChaCha.MTR.Tree ChaCha.CachePortDepth

variable {α : Type*} [LinearOrder α]

theorem node_parts {left right : RawTree α} {key : α}
    (ordered : Ordered (.node left key right)) :
    Ordered left ∧ Ordered right ∧
      (∀ x ∈ left.inorder, x < key) ∧ (∀ x ∈ right.inorder, key < x) := by
  have outer := List.pairwise_append.mp ordered
  have inner := List.pairwise_append.mp outer.1
  refine ⟨inner.1,outer.2.1,?_,?_⟩
  · intro x member
    exact inner.2.2 x member key (by simp)
  · intro x member
    exact outer.2.2 key (by simp) x member

theorem rotation_inorder {before after : RawTree α} (move : Rotation before after) :
    after.inorder = before.inorder := by
  induction move with
  | rootRight | rootLeft => simp only [inorder,List.append_assoc]
  | leftContext move key right ih => simp only [inorder,ih]
  | rightContext left key move ih => simp only [inorder,ih]

theorem rotation_ordered {before after : RawTree α} (ordered : Ordered before)
    (move : Rotation before after) : Ordered after := by
  unfold Ordered
  rw [rotation_inorder move]
  exact ordered

theorem closeDepth_rootRight (a b c : RawTree α) (x y key : α) (smaller : x < y) :
    CloseDepth (searchDepth key (.node (.node a x b) y c))
      (searchDepth key (.node a x (.node b y c))) := by
  rcases lt_trichotomy key x with before | same | beyond
  · have beforeY := lt_trans before smaller
    simp only [searchDepth,beforeY,before,↓reduceIte]
    cases searchDepth key a <;> simp [CloseDepth]
  · subst key
    simp [searchDepth,smaller,not_lt_of_gt smaller,CloseDepth]
  · have notBefore := not_lt_of_gt beyond
    rcases lt_trichotomy key y with before | same | beyondY
    · simp [searchDepth,before,beyond,notBefore,CloseDepth.refl]
    · subst key
      simp [searchDepth,smaller,notBefore,CloseDepth]
    · have notBeforeY := not_lt_of_gt beyondY
      simp only [searchDepth,notBeforeY,beyondY,notBefore,beyond,↓reduceIte]
      cases searchDepth key c <;> simp [CloseDepth]

theorem rotation_closeDepth {before after : RawTree α} (move : Rotation before after)
    (ordered : Ordered before) (key : α) :
    CloseDepth (searchDepth key before) (searchDepth key after) := by
  induction move with
  | rootRight a b c x y =>
      exact closeDepth_rootRight a b c x y key ((node_parts ordered).2.2.1 x (by simp [inorder]))
  | rootLeft a b c x y =>
      exact (closeDepth_rootRight a b c x y key ((node_parts ordered).2.2.2 y (by simp [inorder]))).symm
  | leftContext move root right ih =>
      have child := ih (node_parts ordered).1
      by_cases before : key < root
      · simpa only [searchDepth,before,↓reduceIte] using child.succ
      · simp only [searchDepth,before,↓reduceIte]
        split <;> exact CloseDepth.refl _
  | rightContext left root move ih =>
      have child := ih (node_parts ordered).2.1
      by_cases before : key < root
      · simp only [searchDepth,before,↓reduceIte]
        exact CloseDepth.refl _
      · by_cases beyond : root < key
        · simpa only [searchDepth,before,beyond,↓reduceIte] using child.succ
        · simp [searchDepth,before,beyond,CloseDepth]

theorem rotations_initial_depth {before after : RawTree α} {count depth : Nat}
    (trace : Rotations before after count) (ordered : Ordered before)
    (key : α) (found : searchDepth key after = some depth) :
    ∃ initial, searchDepth key before = some initial ∧ initial ≤ depth+count := by
  induction trace with
  | refl tree => exact ⟨depth,found,by omega⟩
  | step head tail ih =>
      obtain ⟨middle,foundMiddle,bound⟩ := ih (rotation_ordered ordered head) found
      have close := rotation_closeDepth head ordered key
      rw [foundMiddle] at close
      cases initialFound : searchDepth key _ with
      | none => simp [initialFound,CloseDepth] at close
      | some initial =>
          refine ⟨initial,rfl,?_⟩
          simp only [initialFound,CloseDepth] at close
          omega

theorem access_of_final_depth {before after : RawTree α} {count depth : Nat}
    (trace : Rotations before after count) (ordered : Ordered before)
    (key : α) (found : searchDepth key after = some depth) :
    ∃ cost, Access key before after cost ∧ cost ≤ 2*count+depth+1 := by
  obtain ⟨initial,search,bound⟩ := rotations_initial_depth trace ordered key found
  exact ⟨initial+1+count,⟨initial,count,search,trace,rfl⟩,by omega⟩

end DynamicOptimality.SearchRotation.RawDepth
