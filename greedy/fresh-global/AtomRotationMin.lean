import Splay.Tree.Rotation
import Splay.Tree.DepthMin

/-!
Independent structural verification for the Greedy candidate.
Adapted independently from root-refinements/RotationIntervalMin.lean to
ordinary node depths on the alternating-atom BST. This is the input-rotation
interface for the sharp separator projection theorem. It uses concrete
indexed BSTs and does not modify the existing splay development.
-/

namespace GreedyMerge.AtomRotationMin

open Splay.Tree
open Splay.Tree.BST

theorem intervalMin_node_left_iff
    {lo root hi l u z : ℕ} (a : BST lo root) (b : BST (root + 1) hi)
    (hu : u < root) :
    IsIntervalMin (depth (.node a b)) l u z ↔
      IsIntervalMin (depth a) l u z := by
  apply (isIntervalMin_congrOn ?_).trans isIntervalMin_succ_iff
  intro x _ hx
  exact depth_node_of_lt_root a b (by omega)

theorem intervalMin_node_right_iff
    {lo root hi l u z : ℕ} (a : BST lo root) (b : BST (root + 1) hi)
    (hl : root < l) :
    IsIntervalMin (depth (.node a b)) l u z ↔
      IsIntervalMin (depth b) l u z := by
  apply (isIntervalMin_congrOn ?_).trans isIntervalMin_succ_iff
  intro x hx _
  exact depth_node_of_root_lt a b (by omega)

theorem intervalMin_node_root
    {lo root hi l u : ℕ} (a : BST lo root) (b : BST (root + 1) hi)
    (hl : l ≤ root) (hu : root ≤ u) :
    IsIntervalMin (depth (.node a b)) l u (root) := by
  refine ⟨hl, hu, ?_⟩
  intro x _ _
  simp

theorem intervalMin_node_eq_root
    {lo root hi l u z : ℕ} (a : BST lo root) (b : BST (root + 1) hi)
    (hl : l ≤ root) (hu : root ≤ u)
    (hz : IsIntervalMin (depth (.node a b)) l u z) :
    z = root := by
  have hzero := hz.2.2 (root) hl hu
  simp only [depth_root] at hzero
  by_contra hne
  have hpos : 0 < depth (.node a b) z := by
    by_cases hlt : z < root
    · rw [depth_node_of_lt_root a b hlt]
      omega
    · rw [depth_node_of_root_lt a b (by omega)]
      omega
  omega

/-- A right root rotation changes any interval-minimum identity only from
the old root to the promoted root. No bound on the interval is needed. -/
theorem rightRotation_intervalMin
    {lo promoted demoted hi l u z : ℕ}
    (a : BST lo promoted) (b : BST (promoted + 1) demoted)
    (c : BST (demoted + 1) hi)
    (hz : IsIntervalMin (depth (.node (.node a b) c)) l u z) :
    IsIntervalMin (depth (.node a (.node b c))) l u z ∨
      (z = demoted ∧
        IsIntervalMin (depth (.node a (.node b c))) l u
          (promoted)) := by
  have horder := b.lower_le_upper
  by_cases hp : l ≤ promoted ∧ promoted ≤ u
  · have hnew := intervalMin_node_root a (.node b c) hp.1 hp.2
    by_cases hq : l ≤ demoted ∧ demoted ≤ u
    · exact Or.inr ⟨intervalMin_node_eq_root (.node a b) c hq.1 hq.2 hz, hnew⟩
    · have hu : u < demoted := by omega
      have hsub := (intervalMin_node_left_iff (.node a b) c hu).1 hz
      have heq := intervalMin_node_eq_root a b hp.1 hp.2 hsub
      exact Or.inl (heq ▸ hnew)
  · by_cases hup : u < promoted
    · have huq : u < demoted := by omega
      have hsub := (intervalMin_node_left_iff (.node a b) c huq).1 hz
      have ha := (intervalMin_node_left_iff a b hup).1 hsub
      exact Or.inl ((intervalMin_node_left_iff a (.node b c) hup).2 ha)
    · have hlp : promoted < l := by omega
      by_cases hq : l ≤ demoted ∧ demoted ≤ u
      · have heq := intervalMin_node_eq_root (.node a b) c hq.1 hq.2 hz
        have hsub := intervalMin_node_root b c hq.1 hq.2
        have hnew := (intervalMin_node_right_iff a (.node b c) hlp).2 hsub
        exact Or.inl (heq ▸ hnew)
      · by_cases huq : u < demoted
        · have hsub := (intervalMin_node_left_iff (.node a b) c huq).1 hz
          have hb := (intervalMin_node_right_iff a b hlp).1 hsub
          have hnewSub := (intervalMin_node_left_iff b c huq).2 hb
          exact Or.inl ((intervalMin_node_right_iff a (.node b c) hlp).2 hnewSub)
        · have hlq : demoted < l := by omega
          have hc := (intervalMin_node_right_iff (.node a b) c hlq).1 hz
          have hnewSub := (intervalMin_node_right_iff b c hlq).2 hc
          exact Or.inl ((intervalMin_node_right_iff a (.node b c) hlp).2 hnewSub)

/-- The symmetric interval-minimum statement for a left root rotation. -/
theorem leftRotation_intervalMin
    {lo demoted promoted hi l u z : ℕ}
    (a : BST lo demoted) (b : BST (demoted + 1) promoted)
    (c : BST (promoted + 1) hi)
    (hz : IsIntervalMin (depth (.node a (.node b c))) l u z) :
    IsIntervalMin (depth (.node (.node a b) c)) l u z ∨
      (z = demoted ∧
        IsIntervalMin (depth (.node (.node a b) c)) l u
          (promoted)) := by
  have horder := b.lower_le_upper
  by_cases hq : l ≤ promoted ∧ promoted ≤ u
  · have hnew := intervalMin_node_root (.node a b) c hq.1 hq.2
    by_cases hp : l ≤ demoted ∧ demoted ≤ u
    · exact Or.inr ⟨intervalMin_node_eq_root a (.node b c) hp.1 hp.2 hz, hnew⟩
    · have hl : demoted < l := by omega
      have hsub := (intervalMin_node_right_iff a (.node b c) hl).1 hz
      have heq := intervalMin_node_eq_root b c hq.1 hq.2 hsub
      exact Or.inl (heq ▸ hnew)
  · by_cases hlq : promoted < l
    · have hlp : demoted < l := by omega
      have hsub := (intervalMin_node_right_iff a (.node b c) hlp).1 hz
      have hc := (intervalMin_node_right_iff b c hlq).1 hsub
      exact Or.inl ((intervalMin_node_right_iff (.node a b) c hlq).2 hc)
    · have huq : u < promoted := by omega
      by_cases hp : l ≤ demoted ∧ demoted ≤ u
      · have heq := intervalMin_node_eq_root a (.node b c) hp.1 hp.2 hz
        have hsub := intervalMin_node_root a b hp.1 hp.2
        have hnew := (intervalMin_node_left_iff (.node a b) c huq).2 hsub
        exact Or.inl (heq ▸ hnew)
      · by_cases hlp : demoted < l
        · have hsub := (intervalMin_node_right_iff a (.node b c) hlp).1 hz
          have hb := (intervalMin_node_left_iff b c huq).1 hsub
          have hnewSub := (intervalMin_node_right_iff a b hlp).2 hb
          exact Or.inl ((intervalMin_node_left_iff (.node a b) c huq).2 hnewSub)
        · have hup : u < demoted := by omega
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

/-- At arbitrary comparator depth, no fixed ordinary key interval changes its
minimum identity except from the demoted key to the promoted key. -/
theorem intervalMin {demoted promoted depth lo hi : ℕ}
    {before after : BST lo hi}
    (step : KeyRotationAt demoted promoted depth before after)
    {l u z : ℕ}
    (hz : IsIntervalMin before.depth l u z) :
    IsIntervalMin after.depth l u z ∨
      (z = demoted ∧
        IsIntervalMin after.depth l u (promoted)) := by
  induction step with
  | right a b c => exact rightRotation_intervalMin a b c hz
  | left a b c => exact leftRotation_intervalMin a b c hz
  | @leftContext demoted promoted depth lo root hi before after step right ih =>
      by_cases hleft : u < root
      · rcases ih ((intervalMin_node_left_iff before right hleft).1 hz) with hm | ⟨heq, hm⟩
        · exact Or.inl ((intervalMin_node_left_iff after right hleft).2 hm)
        · exact Or.inr ⟨heq, (intervalMin_node_left_iff after right hleft).2 hm⟩
      · by_cases hright : root < l
        · have hm := (intervalMin_node_right_iff before right hright).1 hz
          exact Or.inl ((intervalMin_node_right_iff after right hright).2 hm)
        · have hl : l ≤ root := by omega
          have hu : root ≤ u := by omega
          have heq := intervalMin_node_eq_root before right hl hu hz
          exact Or.inl (heq ▸ intervalMin_node_root after right hl hu)
  | @rightContext demoted promoted depth lo root hi left before after step ih =>
      by_cases hright : root < l
      · rcases ih ((intervalMin_node_right_iff left before hright).1 hz) with hm | ⟨heq, hm⟩
        · exact Or.inl ((intervalMin_node_right_iff left after hright).2 hm)
        · exact Or.inr ⟨heq, (intervalMin_node_right_iff left after hright).2 hm⟩
      · by_cases hleft : u < root
        · have hm := (intervalMin_node_left_iff left before hleft).1 hz
          exact Or.inl ((intervalMin_node_left_iff left after hleft).2 hm)
        · have hl : l ≤ root := by omega
          have hu : root ≤ u := by omega
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
      IsIntervalMin before.depth l u z →
        IsIntervalMin after.depth l u z ∨
          (z = demoted ∧
            IsIntervalMin after.depth l u (promoted)) := by
  obtain ⟨a, b, h⟩ := exists_keyRotationAt step
  exact ⟨a, b, fun _ _ _ hz => h.intervalMin hz⟩

end GreedyMerge.AtomRotationMin

#print axioms GreedyMerge.AtomRotationMin.KeyRotationAt.intervalMin
#print axioms GreedyMerge.AtomRotationMin.rotation_intervalMin_changes
