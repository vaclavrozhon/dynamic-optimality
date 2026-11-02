import DynamicOptimality.ReferenceClosure.Rows

/-!+# Nearest common ancestors and row closure

`nca` descends into a child only when both keys belong to that child.
For keys in the indexed reference interval this is the ordinary nearest
common ancestor, including the convention `nca a a = a`.
-/

namespace DynamicOptimality.Geometry.ReferenceClosure

open Splay.Tree

def nca {lo hi : Nat} : BST lo hi → Nat → Nat → Nat
  | .empty boundary, _, _ => boundary
  | .node (root := pivot) left right, a, b =>
      if a < pivot ∧ b < pivot then nca left a b
      else if pivot < a ∧ pivot < b then nca right a b else pivot

theorem nca_self {lo hi key : Nat} (tree : BST lo hi)
    (lower : lo ≤ key) (upper : key < hi) : nca tree key key = key := by
  induction tree with
  | empty => omega
  | @node lo pivot hi left right ihl ihr =>
    by_cases before : key < pivot
    · simpa [nca, before] using ihl lower before
    · by_cases after : pivot < key
      · simpa [nca, before, after] using ihr (by omega) upper
      · have eq : key = pivot := by omega
        simp [nca, eq]

theorem mem_row_left {lo pivot hi key : Nat} (left : BST lo pivot)
    (right : BST (pivot + 1) hi) (original : Finset Nat) (before : key < pivot) :
    key ∈ row (.node left right) original ↔ key ∈ row left original := by
  constructor
  · intro h
    simp only [row, Finset.mem_union] at h
    rcases h with (h | h) | h
    · exact h
    · have := row_bounded right original key h; omega
    · split at h
      · have := Finset.mem_singleton.mp h; omega
      · simp at h
  · intro h
    exact Finset.mem_union_left _ (Finset.mem_union_left _ h)

theorem mem_row_right {lo pivot hi key : Nat} (left : BST lo pivot)
    (right : BST (pivot + 1) hi) (original : Finset Nat) (after : pivot < key) :
    key ∈ row (.node left right) original ↔ key ∈ row right original := by
  constructor
  · intro h
    simp only [row, Finset.mem_union] at h
    rcases h with (h | h) | h
    · have := row_bounded left original key h; omega
    · exact h
    · split at h
      · have := Finset.mem_singleton.mp h; omega
      · simp at h
  · intro h
    exact Finset.mem_union_left _ (Finset.mem_union_right _ h)

/-- Applying nearest common ancestor again adds no further keys. -/
theorem nca_mem_row {lo hi : Nat} (tree : BST lo hi) (original : Finset Nat)
    {a b : Nat} (ha : a ∈ row tree original) (hb : b ∈ row tree original) :
    nca tree a b ∈ row tree original := by
  induction tree with
  | empty => simp [row] at ha
  | @node lo pivot hi left right ihl ihr =>
    by_cases bothLeft : a < pivot ∧ b < pivot
    · have haL := (mem_row_left left right original bothLeft.1).mp ha
      have hbL := (mem_row_left left right original bothLeft.2).mp hb
      simpa only [nca, if_pos bothLeft] using
        (mem_row_left left right original
          (row_bounded left original _ (ihl haL hbL)).2).mpr (ihl haL hbL)
    · by_cases bothRight : pivot < a ∧ pivot < b
      · have haR := (mem_row_right left right original bothRight.1).mp ha
        have hbR := (mem_row_right left right original bothRight.2).mp hb
        have inner := ihr haR hbR
        have after : pivot < nca right a b := by
          have := (row_bounded right original _ inner).1
          omega
        simpa only [nca, if_neg bothLeft, if_pos bothRight] using
          (mem_row_right left right original after).mpr inner
      · simp only [nca, if_neg bothLeft, if_neg bothRight]
        by_cases aRoot : a = pivot
        · simpa [aRoot] using ha
        · by_cases bRoot : b = pivot
          · simpa [bRoot] using hb
          · have mixed : (a < pivot ∧ pivot < b) ∨ (b < pivot ∧ pivot < a) := by omega
            have nonempty : (row left original).Nonempty ∧ (row right original).Nonempty := by
              rcases mixed with ⟨al, br⟩ | ⟨bl, ar⟩
              · exact ⟨⟨a, (mem_row_left left right original al).mp ha⟩,
                  ⟨b, (mem_row_right left right original br).mp hb⟩⟩
              · exact ⟨⟨b, (mem_row_left left right original bl).mp hb⟩,
                  ⟨a, (mem_row_right left right original ar).mp ha⟩⟩
            simp [row, nonempty]

/-- Every new key is already the nearest common ancestor of two original
keys. Thus `row` is exactly the pairwise NCA closure, not an overestimate. -/
theorem mem_row_original_or_nca {lo hi : Nat} (tree : BST lo hi) (original : Finset Nat)
    {key : Nat} (member : key ∈ row tree original) :
    key ∈ selected tree original ∨
      ∃ a ∈ selected tree original, ∃ b ∈ selected tree original, nca tree a b = key := by
  induction tree with
  | empty => simp [row] at member
  | @node lo pivot hi left right ihl ihr =>
    have hl := left.lower_le_upper
    have hr := right.lower_le_upper
    have liftLeft : ∀ a ∈ selected left original, a ∈ selected (.node left right) original := by
      intro a ha
      obtain ⟨old, lower, upper⟩ := (mem_selected left original).mp ha
      exact (mem_selected (.node left right) original).mpr ⟨old, lower, by omega⟩
    have liftRight : ∀ a ∈ selected right original, a ∈ selected (.node left right) original := by
      intro a ha
      obtain ⟨old, lower, upper⟩ := (mem_selected right original).mp ha
      exact (mem_selected (.node left right) original).mpr ⟨old, by omega, upper⟩
    simp only [row, Finset.mem_union] at member
    rcases member with (member | member) | member
    · rcases ihl member with old | ⟨a, ha, b, hb, eq⟩
      · exact Or.inl (liftLeft key old)
      · have al := ((mem_selected left original).mp ha).2.2
        have bl := ((mem_selected left original).mp hb).2.2
        exact Or.inr ⟨a, liftLeft a ha, b, liftLeft b hb, by simpa [nca, al, bl] using eq⟩
    · rcases ihr member with old | ⟨a, ha, b, hb, eq⟩
      · exact Or.inl (liftRight key old)
      · have al := ((mem_selected right original).mp ha).2.1
        have bl := ((mem_selected right original).mp hb).2.1
        have ar : pivot < a := by omega
        have br : pivot < b := by omega
        exact Or.inr ⟨a, liftRight a ha, b, liftRight b hb,
          by simpa [nca, ar, br, not_lt.mpr ar.le] using eq⟩
    · split at member
      next rootPresent =>
        have eq : key = pivot := Finset.mem_singleton.mp member
        subst key
        rcases rootPresent with old | ⟨ln, rn⟩
        · exact Or.inl ((mem_selected (.node left right) original).mpr ⟨old, hl, by omega⟩)
        · obtain ⟨a, ha⟩ := (row_nonempty_iff left original).mp ln
          obtain ⟨b, hb⟩ := (row_nonempty_iff right original).mp rn
          have al := ((mem_selected left original).mp ha).2.2
          have bl := ((mem_selected right original).mp hb).2.1
          have br : pivot < b := by omega
          exact Or.inr ⟨a, liftLeft a ha, b, liftRight b hb,
            by simp [nca, al, br, not_lt.mpr al.le, not_lt.mpr br.le]⟩
      next => simp at member

theorem mem_row_iff {lo hi : Nat} (tree : BST lo hi) (original : Finset Nat) {key : Nat} :
    key ∈ row tree original ↔ key ∈ selected tree original ∨
      ∃ a ∈ selected tree original, ∃ b ∈ selected tree original, nca tree a b = key := by
  constructor
  · exact mem_row_original_or_nca tree original
  · rintro (old | ⟨a, ha, b, hb, rfl⟩)
    · exact selected_subset_row tree original old
    · exact nca_mem_row tree original (selected_subset_row tree original ha)
        (selected_subset_row tree original hb)

theorem row_idempotent {lo hi : Nat} (tree : BST lo hi) (original : Finset Nat) :
    row tree (row tree original) = row tree original := by
  apply Finset.Subset.antisymm
  · intro key member
    rcases (mem_row_iff tree _).mp member with old | ⟨a, ha, b, hb, rfl⟩
    · exact ((mem_selected tree _).mp old).1
    · exact nca_mem_row tree original ((mem_selected tree _).mp ha).1
        ((mem_selected tree _).mp hb).1
  · intro key member
    exact selected_subset_row tree _ ((mem_selected tree _).mpr
      ⟨member, row_bounded tree original key member⟩)

end DynamicOptimality.Geometry.ReferenceClosure
