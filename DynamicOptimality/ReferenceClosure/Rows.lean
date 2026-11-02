import Splay.Tree.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

/-!+# Reference closure of a row

The reference is the same indexed ordinary BST used by the shared models.
`row tree original` keeps the original keys in the reference interval and
adds exactly the branching vertices of their connecting reference subtree.
No balancing assumption is used.
-/

namespace DynamicOptimality.Geometry.ReferenceClosure

open Splay.Tree

def selected {lo hi : Nat} (_tree : BST lo hi) (original : Finset Nat) : Finset Nat :=
  original.filter fun key => lo ≤ key ∧ key < hi

def row {lo hi : Nat} : BST lo hi → Finset Nat → Finset Nat
  | .empty _, _ => ∅
  | .node (root := pivot) left right, original =>
      let l := row left original
      let r := row right original
      l ∪ r ∪ if pivot ∈ original ∨ (l.Nonempty ∧ r.Nonempty) then {pivot} else ∅

@[simp] theorem mem_selected {lo hi key : Nat} (tree : BST lo hi) (original : Finset Nat) :
    key ∈ selected tree original ↔ key ∈ original ∧ lo ≤ key ∧ key < hi := by
  simp [selected]

theorem row_bounded {lo hi : Nat} (tree : BST lo hi) (original : Finset Nat) :
    ∀ key ∈ row tree original, lo ≤ key ∧ key < hi := by
  induction tree with
  | empty => simp [row]
  | @node lo pivot hi left right ihl ihr =>
    intro key member
    have hl := left.lower_le_upper
    have hr := right.lower_le_upper
    simp only [row, Finset.mem_union] at member
    rcases member with (member | member) | member
    · have := ihl key member; omega
    · have := ihr key member; omega
    · split at member
      · have : key = pivot := Finset.mem_singleton.mp member
        omega
      · simp at member

theorem selected_subset_row {lo hi : Nat} (tree : BST lo hi) (original : Finset Nat) :
    selected tree original ⊆ row tree original := by
  induction tree with
  | empty => simp [selected, row]
  | @node lo pivot hi left right ihl ihr =>
    intro key member
    obtain ⟨old, lower, upper⟩ := (mem_selected (.node left right) original).mp member
    by_cases equal : key = pivot
    · subst key
      simp [row, old]
    · by_cases before : key < pivot
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (ihl ((mem_selected left original).mpr ⟨old, lower, before⟩)))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (ihr ((mem_selected right original).mpr ⟨old, by omega, upper⟩)))

theorem row_nonempty_iff {lo hi : Nat} (tree : BST lo hi) (original : Finset Nat) :
    (row tree original).Nonempty ↔ (selected tree original).Nonempty := by
  induction tree with
  | empty => simp [row, selected]
  | @node lo pivot hi left right ihl ihr =>
    constructor
    · rintro ⟨key, member⟩
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      simp only [row, Finset.mem_union] at member
      rcases member with (member | member) | member
      · obtain ⟨a, ha⟩ := ihl.mp ⟨key, member⟩
        obtain ⟨old, lower, upper⟩ := (mem_selected left original).mp ha
        exact ⟨a, (mem_selected (.node left right) original).mpr ⟨old, lower, by omega⟩⟩
      · obtain ⟨a, ha⟩ := ihr.mp ⟨key, member⟩
        obtain ⟨old, lower, upper⟩ := (mem_selected right original).mp ha
        exact ⟨a, (mem_selected (.node left right) original).mpr ⟨old, by omega, upper⟩⟩
      · split at member
        next h =>
          rcases h with old | ⟨nonempty, _⟩
          · exact ⟨pivot, (mem_selected (.node left right) original).mpr ⟨old, hl, by omega⟩⟩
          · obtain ⟨a, ha⟩ := ihl.mp nonempty
            obtain ⟨old, lower, upper⟩ := (mem_selected left original).mp ha
            exact ⟨a, (mem_selected (.node left right) original).mpr ⟨old, lower, by omega⟩⟩
        next => simp at member
    · exact Finset.Nonempty.mono (selected_subset_row (.node left right) original)

theorem row_eq_empty_iff {lo hi : Nat} (tree : BST lo hi) (original : Finset Nat) :
    row tree original = ∅ ↔ selected tree original = ∅ := by
  simpa only [Finset.not_nonempty_iff_eq_empty] using
    not_congr (row_nonempty_iff tree original)

theorem row_congr {lo hi : Nat} (tree : BST lo hi) {a b : Finset Nat}
    (same : ∀ key, lo ≤ key → key < hi → (key ∈ a ↔ key ∈ b)) : row tree a = row tree b := by
  induction tree with
  | empty => rfl
  | @node lo pivot hi left right ihl ihr =>
    have hl := left.lower_le_upper
    have hr := right.lower_le_upper
    have eqLeft := ihl (fun key lower upper => same key lower (by omega))
    have eqRight := ihr (fun key lower upper => same key (by omega) upper)
    simp only [row, eqLeft, eqRight, same pivot hl (by omega)]

private theorem selected_node_card {lo pivot hi : Nat} (left : BST lo pivot)
    (right : BST (pivot + 1) hi) (original : Finset Nat) :
    (selected (.node left right) original).card =
      (selected left original).card + (selected right original).card +
        if pivot ∈ original then 1 else 0 := by
  have hl := left.lower_le_upper
  have hr := right.lower_le_upper
  have parts : selected (.node left right) original =
      selected left original ∪ selected right original ∪
        if pivot ∈ original then {pivot} else ∅ := by
    ext key
    by_cases old : pivot ∈ original
    · simp only [if_pos old, Finset.mem_union, Finset.mem_singleton, mem_selected]
      constructor
      · rintro ⟨member, lower, upper⟩
        by_cases eq : key = pivot
        · exact Or.inr eq
        · by_cases lt : key < pivot
          · exact Or.inl (Or.inl ⟨member, lower, lt⟩)
          · exact Or.inl (Or.inr ⟨member, by omega, upper⟩)
      · rintro ((⟨member, lower, upper⟩ | ⟨member, lower, upper⟩) | eq)
        · exact ⟨member, lower, by omega⟩
        · exact ⟨member, by omega, upper⟩
        · subst key; exact ⟨old, hl, by omega⟩
    · simp only [if_neg old, Finset.union_empty, Finset.mem_union, mem_selected]
      constructor
      · rintro ⟨member, lower, upper⟩
        have ne : key ≠ pivot := by rintro rfl; exact old member
        by_cases lt : key < pivot
        · exact Or.inl ⟨member, lower, lt⟩
        · exact Or.inr ⟨member, by omega, upper⟩
      · rintro (⟨member, lower, upper⟩ | ⟨member, lower, upper⟩)
        · exact ⟨member, lower, by omega⟩
        · exact ⟨member, by omega, upper⟩
  have disjointLR : Disjoint (selected left original) (selected right original) := by
    apply Finset.disjoint_left.mpr
    intro key hk₁ hk₂
    have h₁ := (mem_selected left original).mp hk₁
    have h₂ := (mem_selected right original).mp hk₂
    omega
  have disjointRoot : Disjoint (selected left original ∪ selected right original)
      (if pivot ∈ original then {pivot} else ∅) := by
    by_cases old : pivot ∈ original
    · simp only [if_pos old, Finset.disjoint_singleton_right, Finset.mem_union,
        mem_selected]
      omega
    · simp [old]
  rw [parts, Finset.card_union_of_disjoint disjointRoot,
    Finset.card_union_of_disjoint disjointLR]
  by_cases old : pivot ∈ original <;> simp [old]

/-- The sharp `2r-1` bound; natural subtraction covers the empty row too. -/
theorem row_card_le {lo hi : Nat} (tree : BST lo hi) (original : Finset Nat) :
    (row tree original).card ≤ 2 * (selected tree original).card - 1 := by
  induction tree with
  | empty => simp [row]
  | @node lo pivot hi left right ihl ihr =>
    have cardParts := selected_node_card left right original
    have unionBound := Finset.card_union_le (row left original) (row right original)
    by_cases old : pivot ∈ original
    · have bound := Finset.card_union_le (row left original ∪ row right original) {pivot}
      simp only [row, if_pos (Or.inl old), Finset.card_singleton] at bound ⊢
      simp only [if_pos old] at cardParts
      omega
    · simp only [if_neg old] at cardParts
      by_cases leftEmpty : selected left original = ∅
      · have rowEmpty := (row_eq_empty_iff left original).mpr leftEmpty
        simp only [row, rowEmpty, Finset.empty_union, Finset.not_nonempty_empty,
          false_and, or_self, old, if_false, Finset.union_empty]
        simp only [leftEmpty, Finset.card_empty] at cardParts
        omega
      · by_cases rightEmpty : selected right original = ∅
        · have rowEmpty := (row_eq_empty_iff right original).mpr rightEmpty
          simp only [row, rowEmpty, Finset.union_empty, Finset.not_nonempty_empty,
            and_false, or_false, old, if_false]
          simp only [rightEmpty, Finset.card_empty] at cardParts
          omega
        · have lpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr leftEmpty)
          have rpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr rightEmpty)
          have ln := (row_nonempty_iff left original).mpr (Finset.card_pos.mp lpos)
          have rn := (row_nonempty_iff right original).mpr (Finset.card_pos.mp rpos)
          have addRoot : pivot ∈ original ∨
              (row left original).Nonempty ∧ (row right original).Nonempty := Or.inr ⟨ln, rn⟩
          have bound := Finset.card_union_le (row left original ∪ row right original) {pivot}
          simp only [row, if_pos addRoot, Finset.card_singleton] at bound ⊢
          omega

end DynamicOptimality.Geometry.ReferenceClosure
