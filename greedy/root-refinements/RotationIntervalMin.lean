import Splay.Tree.Rotation
import Splay.Tree.ExternalDepthMin

/-!
Independent structural verification for the Greedy candidate.
This file concerns comparator interval minima, not the complete competitive
theorem. It imports the indexed BST and external-depth definitions from the
existing splay development, without modifying that development.
-/

namespace GreedyMerge

open Splay.Tree
open Splay.Tree.BST

theorem intervalMin_node_left_iff
    {lo root hi l u z : ℕ} (a : BST lo root) (b : BST (root + 1) hi)
    (hu : u < 2 * root + 1) :
    IsIntervalMin (externalDepth (.node a b)) l u z ↔
      IsIntervalMin (externalDepth a) l u z := by
  apply (isIntervalMin_congrOn ?_).trans isIntervalMin_succ_iff
  intro x _ hx
  exact externalDepth_node_of_lt_root a b (by omega)

theorem intervalMin_node_right_iff
    {lo root hi l u z : ℕ} (a : BST lo root) (b : BST (root + 1) hi)
    (hl : 2 * root + 1 < l) :
    IsIntervalMin (externalDepth (.node a b)) l u z ↔
      IsIntervalMin (externalDepth b) l u z := by
  apply (isIntervalMin_congrOn ?_).trans isIntervalMin_succ_iff
  intro x hx _
  exact externalDepth_node_of_root_lt a b (by omega)

theorem intervalMin_node_root
    {lo root hi l u : ℕ} (a : BST lo root) (b : BST (root + 1) hi)
    (hl : l ≤ 2 * root + 1) (hu : 2 * root + 1 ≤ u) :
    IsIntervalMin (externalDepth (.node a b)) l u (2 * root + 1) := by
  refine ⟨hl, hu, ?_⟩
  intro x _ _
  simp

theorem intervalMin_node_eq_root
    {lo root hi l u z : ℕ} (a : BST lo root) (b : BST (root + 1) hi)
    (hl : l ≤ 2 * root + 1) (hu : 2 * root + 1 ≤ u)
    (hz : IsIntervalMin (externalDepth (.node a b)) l u z) :
    z = 2 * root + 1 := by
  have hzero := hz.2.2 (2 * root + 1) hl hu
  simp only [externalDepth_root] at hzero
  by_contra hne
  have hpos : 0 < externalDepth (.node a b) z := by
    by_cases hlt : z < 2 * root + 1
    · rw [externalDepth_node_of_lt_root a b hlt]
      omega
    · rw [externalDepth_node_of_root_lt a b (by omega)]
      omega
  omega

/-- A right root rotation changes any interval-minimum identity only from
the old root to the promoted root. No bound on the interval is needed. -/
theorem rightRotation_intervalMin
    {lo promoted demoted hi l u z : ℕ}
    (a : BST lo promoted) (b : BST (promoted + 1) demoted)
    (c : BST (demoted + 1) hi)
    (hz : IsIntervalMin (externalDepth (.node (.node a b) c)) l u z) :
    IsIntervalMin (externalDepth (.node a (.node b c))) l u z ∨
      (z = 2 * demoted + 1 ∧
        IsIntervalMin (externalDepth (.node a (.node b c))) l u
          (2 * promoted + 1)) := by
  have horder := b.lower_le_upper
  by_cases hp : l ≤ 2 * promoted + 1 ∧ 2 * promoted + 1 ≤ u
  · have hnew := intervalMin_node_root a (.node b c) hp.1 hp.2
    by_cases hq : l ≤ 2 * demoted + 1 ∧ 2 * demoted + 1 ≤ u
    · exact Or.inr ⟨intervalMin_node_eq_root (.node a b) c hq.1 hq.2 hz, hnew⟩
    · have hu : u < 2 * demoted + 1 := by omega
      have hsub := (intervalMin_node_left_iff (.node a b) c hu).1 hz
      have heq := intervalMin_node_eq_root a b hp.1 hp.2 hsub
      exact Or.inl (heq ▸ hnew)
  · by_cases hup : u < 2 * promoted + 1
    · have huq : u < 2 * demoted + 1 := by omega
      have hsub := (intervalMin_node_left_iff (.node a b) c huq).1 hz
      have ha := (intervalMin_node_left_iff a b hup).1 hsub
      exact Or.inl ((intervalMin_node_left_iff a (.node b c) hup).2 ha)
    · have hlp : 2 * promoted + 1 < l := by omega
      by_cases hq : l ≤ 2 * demoted + 1 ∧ 2 * demoted + 1 ≤ u
      · have heq := intervalMin_node_eq_root (.node a b) c hq.1 hq.2 hz
        have hsub := intervalMin_node_root b c hq.1 hq.2
        have hnew := (intervalMin_node_right_iff a (.node b c) hlp).2 hsub
        exact Or.inl (heq ▸ hnew)
      · by_cases huq : u < 2 * demoted + 1
        · have hsub := (intervalMin_node_left_iff (.node a b) c huq).1 hz
          have hb := (intervalMin_node_right_iff a b hlp).1 hsub
          have hnewSub := (intervalMin_node_left_iff b c huq).2 hb
          exact Or.inl ((intervalMin_node_right_iff a (.node b c) hlp).2 hnewSub)
        · have hlq : 2 * demoted + 1 < l := by omega
          have hc := (intervalMin_node_right_iff (.node a b) c hlq).1 hz
          have hnewSub := (intervalMin_node_right_iff b c hlq).2 hc
          exact Or.inl ((intervalMin_node_right_iff a (.node b c) hlp).2 hnewSub)

/-- The symmetric interval-minimum statement for a left root rotation. -/
theorem leftRotation_intervalMin
    {lo demoted promoted hi l u z : ℕ}
    (a : BST lo demoted) (b : BST (demoted + 1) promoted)
    (c : BST (promoted + 1) hi)
    (hz : IsIntervalMin (externalDepth (.node a (.node b c))) l u z) :
    IsIntervalMin (externalDepth (.node (.node a b) c)) l u z ∨
      (z = 2 * demoted + 1 ∧
        IsIntervalMin (externalDepth (.node (.node a b) c)) l u
          (2 * promoted + 1)) := by
  have horder := b.lower_le_upper
  by_cases hq : l ≤ 2 * promoted + 1 ∧ 2 * promoted + 1 ≤ u
  · have hnew := intervalMin_node_root (.node a b) c hq.1 hq.2
    by_cases hp : l ≤ 2 * demoted + 1 ∧ 2 * demoted + 1 ≤ u
    · exact Or.inr ⟨intervalMin_node_eq_root a (.node b c) hp.1 hp.2 hz, hnew⟩
    · have hl : 2 * demoted + 1 < l := by omega
      have hsub := (intervalMin_node_right_iff a (.node b c) hl).1 hz
      have heq := intervalMin_node_eq_root b c hq.1 hq.2 hsub
      exact Or.inl (heq ▸ hnew)
  · by_cases hlq : 2 * promoted + 1 < l
    · have hlp : 2 * demoted + 1 < l := by omega
      have hsub := (intervalMin_node_right_iff a (.node b c) hlp).1 hz
      have hc := (intervalMin_node_right_iff b c hlq).1 hsub
      exact Or.inl ((intervalMin_node_right_iff (.node a b) c hlq).2 hc)
    · have huq : u < 2 * promoted + 1 := by omega
      by_cases hp : l ≤ 2 * demoted + 1 ∧ 2 * demoted + 1 ≤ u
      · have heq := intervalMin_node_eq_root a (.node b c) hp.1 hp.2 hz
        have hsub := intervalMin_node_root a b hp.1 hp.2
        have hnew := (intervalMin_node_left_iff (.node a b) c huq).2 hsub
        exact Or.inl (heq ▸ hnew)
      · by_cases hlp : 2 * demoted + 1 < l
        · have hsub := (intervalMin_node_right_iff a (.node b c) hlp).1 hz
          have hb := (intervalMin_node_left_iff b c huq).1 hsub
          have hnewSub := (intervalMin_node_right_iff a b hlp).2 hb
          exact Or.inl ((intervalMin_node_left_iff (.node a b) c huq).2 hnewSub)
        · have hup : u < 2 * demoted + 1 := by omega
          have ha := (intervalMin_node_left_iff a (.node b c) hup).1 hz
          have hnewSub := (intervalMin_node_left_iff a b hup).2 ha
          exact Or.inl ((intervalMin_node_left_iff (.node a b) c huq).2 hnewSub)

/-- A rotation retaining the identities of the demoted and promoted keys.
The existing `RotationAt` relation records only its depth. -/
inductive KeyRotationAt :
    (demoted promoted depth : ℕ) → {lo hi : ℕ} → BST lo hi → BST lo hi → Prop
  | right {lo promoted demoted hi : ℕ}
      (a : BST lo promoted) (b : BST (promoted + 1) demoted)
      (c : BST (demoted + 1) hi) :
      KeyRotationAt demoted promoted 0 (.node (.node a b) c) (.node a (.node b c))
  | left {lo demoted promoted hi : ℕ}
      (a : BST lo demoted) (b : BST (demoted + 1) promoted)
      (c : BST (promoted + 1) hi) :
      KeyRotationAt demoted promoted 0 (.node a (.node b c)) (.node (.node a b) c)
  | leftContext {demoted promoted depth lo root hi : ℕ}
      {before after : BST lo root}
      (step : KeyRotationAt demoted promoted depth before after)
      (right : BST (root + 1) hi) :
      KeyRotationAt demoted promoted (depth + 1) (.node before right) (.node after right)
  | rightContext {demoted promoted depth lo root hi : ℕ}
      (left : BST lo root) {before after : BST (root + 1) hi}
      (step : KeyRotationAt demoted promoted depth before after) :
      KeyRotationAt demoted promoted (depth + 1) (.node left before) (.node left after)

namespace KeyRotationAt

theorem toRotationAt {demoted promoted depth lo hi : ℕ}
    {before after : BST lo hi}
    (step : KeyRotationAt demoted promoted depth before after) :
    RotationAt depth before after := by
  induction step with
  | right a b c => exact .root (.right a b c)
  | left a b c => exact .root (.left a b c)
  | leftContext _ right ih => exact .leftContext ih right
  | rightContext left _ ih => exact .rightContext left ih

/-- At arbitrary comparator depth, no fixed external interval changes its
minimum identity except from the demoted key to the promoted key. -/
theorem intervalMin {demoted promoted depth lo hi : ℕ}
    {before after : BST lo hi}
    (step : KeyRotationAt demoted promoted depth before after)
    {l u z : ℕ}
    (hz : IsIntervalMin before.externalDepth l u z) :
    IsIntervalMin after.externalDepth l u z ∨
      (z = 2 * demoted + 1 ∧
        IsIntervalMin after.externalDepth l u (2 * promoted + 1)) := by
  induction step with
  | right a b c => exact rightRotation_intervalMin a b c hz
  | left a b c => exact leftRotation_intervalMin a b c hz
  | @leftContext demoted promoted depth lo root hi before after step right ih =>
      by_cases hleft : u < 2 * root + 1
      · rcases ih ((intervalMin_node_left_iff before right hleft).1 hz) with hm | ⟨heq, hm⟩
        · exact Or.inl ((intervalMin_node_left_iff after right hleft).2 hm)
        · exact Or.inr ⟨heq, (intervalMin_node_left_iff after right hleft).2 hm⟩
      · by_cases hright : 2 * root + 1 < l
        · have hm := (intervalMin_node_right_iff before right hright).1 hz
          exact Or.inl ((intervalMin_node_right_iff after right hright).2 hm)
        · have hl : l ≤ 2 * root + 1 := by omega
          have hu : 2 * root + 1 ≤ u := by omega
          have heq := intervalMin_node_eq_root before right hl hu hz
          exact Or.inl (heq ▸ intervalMin_node_root after right hl hu)
  | @rightContext demoted promoted depth lo root hi left before after step ih =>
      by_cases hright : 2 * root + 1 < l
      · rcases ih ((intervalMin_node_right_iff left before hright).1 hz) with hm | ⟨heq, hm⟩
        · exact Or.inl ((intervalMin_node_right_iff left after hright).2 hm)
        · exact Or.inr ⟨heq, (intervalMin_node_right_iff left after hright).2 hm⟩
      · by_cases hleft : u < 2 * root + 1
        · have hm := (intervalMin_node_left_iff left before hleft).1 hz
          exact Or.inl ((intervalMin_node_left_iff left after hleft).2 hm)
        · have hl : l ≤ 2 * root + 1 := by omega
          have hu : 2 * root + 1 ≤ u := by omega
          have heq := intervalMin_node_eq_root left before hl hu hz
          exact Or.inl (heq ▸ intervalMin_node_root left after hl hu)

end KeyRotationAt

theorem exists_keyRotationAt {depth lo hi : ℕ} {before after : BST lo hi}
    (step : RotationAt depth before after) :
    ∃ demoted promoted, KeyRotationAt demoted promoted depth before after := by
  induction step with
  | root step =>
      cases step with
      | right a b c => exact ⟨_, _, .right a b c⟩
      | left a b c => exact ⟨_, _, .left a b c⟩
  | leftContext _ right ih =>
      obtain ⟨a, b, h⟩ := ih
      exact ⟨a, b, .leftContext h right⟩
  | rightContext left _ ih =>
      obtain ⟨a, b, h⟩ := ih
      exact ⟨a, b, .rightContext left h⟩

/-- A single pair of endpoint identities controls all interval-minimum
changes of a comparator rotation, simultaneously over every interval. -/
theorem rotation_intervalMin_changes {depth lo hi : ℕ} {before after : BST lo hi}
    (step : RotationAt depth before after) :
    ∃ demoted promoted, ∀ l u z,
      IsIntervalMin before.externalDepth l u z →
        IsIntervalMin after.externalDepth l u z ∨
          (z = 2 * demoted + 1 ∧
            IsIntervalMin after.externalDepth l u (2 * promoted + 1)) := by
  obtain ⟨a, b, h⟩ := exists_keyRotationAt step
  exact ⟨a, b, fun _ _ _ hz => h.intervalMin hz⟩

end GreedyMerge

#print axioms GreedyMerge.KeyRotationAt.intervalMin
#print axioms GreedyMerge.rotation_intervalMin_changes
