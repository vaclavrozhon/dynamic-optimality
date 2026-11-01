import Splay.Tree.RotationDepthBound
import Mathlib.Data.List.Basic

namespace Splay.Tree.BST

/-- Numerical cuts for one comparison rotation, with an adjacent border
whose depth is bounded at both endpoints. Uniformity concerns the exact
signed depth difference, so no choice of a shift function is hidden. -/
structure RotationCutProfile {lower upper : ℕ} (before after : BST lower upper) (depth : ℕ) where
  entries : List (ℕ × ℕ)
  length_le : entries.length ≤ depth + 2
  borders : ∀ entry ∈ entries, 2 * lower ≤ entry.2 ∧ entry.2 ≤ 2 * upper ∧
    (entry.2 = entry.1 ∨ entry.2 + 1 = entry.1) ∧
    before.externalDepth entry.2 ≤ depth + 1 ∧ after.externalDepth entry.2 ≤ depth + 1
  uniform : ∀ first second : ℕ,
    (∀ entry ∈ entries, first < entry.1 ↔ second < entry.1) →
    (after.externalDepth first : ℤ) - before.externalDepth first =
      (after.externalDepth second : ℤ) - before.externalDepth second

namespace RotationCutProfile

def symm {lower upper depth : ℕ} {before after : BST lower upper}
    (profile : RotationCutProfile before after depth) : RotationCutProfile after before depth where
  entries := profile.entries
  length_le := profile.length_le
  borders := by
    intro entry member
    obtain ⟨low, high, adjacent, beforeBound, afterBound⟩ := profile.borders entry member
    exact ⟨low, high, adjacent, afterBound, beforeBound⟩
  uniform := by
    intro first second same
    have equal := profile.uniform first second same
    omega

def rightRoot {lower promoted demoted upper : ℕ}
    (a : BST lower promoted) (b : BST (promoted + 1) demoted) (c : BST (demoted + 1) upper) :
    RotationCutProfile (.node (.node a b) c) (.node a (.node b c)) 0 where
  entries := [(2 * promoted + 2, 2 * promoted + 1), (2 * demoted + 1, 2 * demoted + 1)]
  length_le := by simp
  borders := by
    intro entry member
    have lowerBound := a.lower_le_upper
    have middleBound := b.lower_le_upper
    have upperBound := c.lower_le_upper
    have promotedLess : promoted < demoted := by omega
    rcases List.mem_cons.mp member with equal | inTail
    · subst entry
      simp only [Prod.fst, Prod.snd]
      refine ⟨by omega, by omega, by simp, ?_, ?_⟩
      · rw [externalDepth_node_of_lt_root (.node a b) c (by omega), externalDepth_root a b]
      · simp
    · have equal := List.mem_singleton.mp inTail
      subst entry
      simp only [Prod.fst, Prod.snd]
      refine ⟨by omega, by omega, by simp, ?_, ?_⟩
      · simp
      · rw [externalDepth_node_of_root_lt a (.node b c) (by omega), externalDepth_root b c]
  uniform := by
    intro first second same
    have lowSame := same (2 * promoted + 2, 2 * promoted + 1) (by simp)
    have highSame := same (2 * demoted + 1, 2 * demoted + 1) (by simp)
    dsimp only at lowSame highSame
    by_cases low : first ≤ 2 * promoted + 1
    · have otherLow : second ≤ 2 * promoted + 1 := by omega
      have firstDepth := RootRotation.right_externalDepth_promotedSector a b c low
      have secondDepth := RootRotation.right_externalDepth_promotedSector a b c otherLow
      omega
    · by_cases middle : first < 2 * demoted + 1
      · have otherAbove : 2 * promoted + 1 < second := by omega
        have otherBelow : second < 2 * demoted + 1 := by omega
        have firstDepth := RootRotation.right_externalDepth_middleSector a b c (by omega) middle
        have secondDepth := RootRotation.right_externalDepth_middleSector a b c otherAbove otherBelow
        omega
      · have otherHigh : 2 * demoted + 1 ≤ second := by omega
        have firstDepth := RootRotation.right_externalDepth_demotedSector (position := first) a b c (by omega)
        have secondDepth := RootRotation.right_externalDepth_demotedSector a b c otherHigh
        omega

def leftContext {depth lower root upper : ℕ} {before after : BST lower root}
    (profile : RotationCutProfile before after depth) (right : BST (root + 1) upper) :
    RotationCutProfile (.node before right) (.node after right) (depth + 1) where
  entries := (2 * root + 1, 2 * root + 1) :: profile.entries
  length_le := by have bound := profile.length_le; simp only [List.length_cons]; omega
  borders := by
    intro entry member
    rcases List.mem_cons.mp member with equal | inTail
    · subst entry
      have lowerBound := before.lower_le_upper
      have upperBound := right.lower_le_upper
      refine ⟨by dsimp; omega, by dsimp; omega, Or.inl rfl, ?_, ?_⟩ <;> simp
    · obtain ⟨low, high, adjacent, beforeBound, afterBound⟩ := profile.borders entry inTail
      have upperBound := right.lower_le_upper
      refine ⟨low, by omega, adjacent, ?_, ?_⟩
      · rw [externalDepth_node_of_lt_root before right (by omega)]
        omega
      · rw [externalDepth_node_of_lt_root after right (by omega)]
        omega
  uniform := by
    intro first second same
    have rootSame := same (2 * root + 1, 2 * root + 1) (by simp)
    dsimp only at rootSame
    by_cases firstLeft : first < 2 * root + 1
    · have secondLeft : second < 2 * root + 1 := rootSame.mp firstLeft
      have inner := profile.uniform first second (fun entry member => same entry (List.mem_cons_of_mem _ member))
      rw [externalDepth_node_of_lt_root before right firstLeft,
        externalDepth_node_of_lt_root after right firstLeft,
        externalDepth_node_of_lt_root before right secondLeft,
        externalDepth_node_of_lt_root after right secondLeft]
      omega
    · have secondNotLeft : ¬ second < 2 * root + 1 := fun left => firstLeft (rootSame.mpr left)
      have unchanged (position : ℕ) (notLeft : ¬ position < 2 * root + 1) :
          (BST.node before right).externalDepth position = (BST.node after right).externalDepth position := by
        by_cases atRoot : position = 2 * root + 1
        · subst position
          simp
        · rw [externalDepth_node_of_root_lt before right (by omega), externalDepth_node_of_root_lt after right (by omega)]
      rw [unchanged first firstLeft, unchanged second secondNotLeft]
      omega

def rightContext {depth lower root upper : ℕ} (left : BST lower root) {before after : BST (root + 1) upper}
    (profile : RotationCutProfile before after depth) :
    RotationCutProfile (.node left before) (.node left after) (depth + 1) where
  entries := (2 * root + 2, 2 * root + 1) :: profile.entries
  length_le := by have bound := profile.length_le; simp only [List.length_cons]; omega
  borders := by
    intro entry member
    rcases List.mem_cons.mp member with equal | inTail
    · subst entry
      have lowerBound := left.lower_le_upper
      have upperBound := before.lower_le_upper
      refine ⟨by dsimp; omega, by dsimp; omega, Or.inr rfl, ?_, ?_⟩ <;> simp
    · obtain ⟨low, high, adjacent, beforeBound, afterBound⟩ := profile.borders entry inTail
      have lowerBound := left.lower_le_upper
      refine ⟨by omega, high, adjacent, ?_, ?_⟩
      · rw [externalDepth_node_of_root_lt left before (by omega)]
        omega
      · rw [externalDepth_node_of_root_lt left after (by omega)]
        omega
  uniform := by
    intro first second same
    have rootSame := same (2 * root + 2, 2 * root + 1) (by simp)
    dsimp only at rootSame
    by_cases firstRight : 2 * root + 1 < first
    · have secondRight : 2 * root + 1 < second := by omega
      have inner := profile.uniform first second (fun entry member => same entry (List.mem_cons_of_mem _ member))
      rw [externalDepth_node_of_root_lt left before firstRight,
        externalDepth_node_of_root_lt left after firstRight,
        externalDepth_node_of_root_lt left before secondRight,
        externalDepth_node_of_root_lt left after secondRight]
      omega
    · have secondNotRight : ¬ 2 * root + 1 < second := by omega
      have unchanged (position : ℕ) (notRight : ¬ 2 * root + 1 < position) :
          (BST.node left before).externalDepth position = (BST.node left after).externalDepth position := by
        by_cases atRoot : position = 2 * root + 1
        · subst position
          simp
        · rw [externalDepth_node_of_lt_root left before (by omega), externalDepth_node_of_lt_root left after (by omega)]
      rw [unchanged first firstRight, unchanged second secondNotRight]
      omega

end RotationCutProfile

/-- Every contextual rotation has a concrete depth-bounded cut profile. -/
theorem RotationAt.exists_cutProfile {lower upper depth : ℕ} {before after : BST lower upper}
    (rotation : RotationAt depth before after) : Nonempty (RotationCutProfile before after depth) := by
  induction rotation with
  | root rootStep =>
      cases rootStep with
      | right a b c => exact ⟨RotationCutProfile.rightRoot a b c⟩
      | left a b c => exact ⟨(RotationCutProfile.rightRoot a b c).symm⟩
  | leftContext rotation right ih =>
      obtain ⟨profile⟩ := ih
      exact ⟨profile.leftContext right⟩
  | rightContext left rotation ih =>
      obtain ⟨profile⟩ := ih
      exact ⟨profile.rightContext left⟩

end Splay.Tree.BST
