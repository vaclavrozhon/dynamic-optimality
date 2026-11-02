import DynamicOptimality.ReferenceClosure.Cut
import DynamicOptimality.ReferenceClosure.NCA
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!+# Reference closure of an arborally satisfied point set

The construction fills the reference cuts from the children upward.
`closePoints_mem` identifies its rows with the pairwise NCA closure from
`NCA.lean`. Each individual cut preserves the usual rectangle condition.
-/

namespace DynamicOptimality.Geometry.ReferenceClosure

open Splay.Tree

def rowAt (points : Finset Point) (time : Int) : Finset Nat :=
  (points.filter fun p => p.2 = time).image Prod.fst

@[simp] theorem mem_rowAt {points : Finset Point} {time : Int} {key : Nat} :
    key ∈ rowAt points time ↔ (key, time) ∈ points := by
  simp only [rowAt, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨k, t⟩, ⟨member, rfl⟩, rfl⟩
    exact member
  · intro member
    exact ⟨(key, time), ⟨member, rfl⟩, rfl⟩

noncomputable def closePoints {lo hi : Nat} : BST lo hi → Finset Point → Finset Point
  | .empty _, points => points
  | .node (root := pivot) (lower := lo) (upper := hi) left right, points =>
      fillCut (closePoints right (closePoints left points)) (Set.Ico lo hi) pivot

theorem closePoints_satisfied {lo hi : Nat} (tree : BST lo hi) {points : Finset Point}
    (satisfied : ArborallySatisfied points) : ArborallySatisfied (closePoints tree points) := by
  apply (satisfied_iff _).mp
  have h := (satisfied_iff _).mpr satisfied
  induction tree generalizing points with
  | empty => exact h
  | node left right ihl ihr =>
    apply fillCut_satisfied
    · intro a ha b hb c hac hcb
      exact ⟨ha.1.trans hac, hcb.trans_lt hb.2⟩
    · exact ihr ((satisfied_iff _).mp (ihl satisfied h)) (ihl satisfied h)

/-- Exact row semantics, including points outside a reference subtree. -/
theorem closePoints_mem {lo hi : Nat} (tree : BST lo hi) (points : Finset Point) :
    ∀ p, p ∈ closePoints tree points ↔
      (p ∈ points ∧ (p.1 < lo ∨ hi ≤ p.1)) ∨ p.1 ∈ row tree (rowAt points p.2) := by
  induction tree generalizing points with
  | empty boundary =>
    intro p
    simp only [closePoints, row]
    simp [show p.1 < boundary ∨ boundary ≤ p.1 by omega]
  | @node lo pivot hi left right ihl ihr =>
    intro p
    have hl := left.lower_le_upper
    have hr := right.lower_le_upper
    let first := closePoints left points
    let middle := closePoints right first
    let input := rowAt points p.2
    have rightInput : row right (rowAt first p.2) = row right input := by
      apply row_congr
      intro key lower upper
      simp only [mem_rowAt]
      rw [ihl]
      have outside : pivot ≤ key := by omega
      have absent : key ∉ row left (rowAt points p.2) := by
        intro member
        have := (row_bounded left _ key member).2
        omega
      simp [absent, outside, input]
    have middleMem : p ∈ middle ↔
        (p ∈ points ∧ (p.1 < lo ∨ hi ≤ p.1)) ∨
        p.1 ∈ row left input ∨ p.1 ∈ row right input ∨ (p.1 = pivot ∧ p ∈ points) := by
      change p ∈ closePoints right first ↔ _
      rw [ihr, rightInput]
      change ((p ∈ closePoints left points ∧ _) ∨ _) ↔ _
      rw [ihl]
      have lb := row_bounded left input p.1
      have rb := row_bounded right input p.1
      change (((p ∈ points ∧ (p.1 < lo ∨ pivot ≤ p.1) ∨ p.1 ∈ row left input) ∧
        (p.1 < pivot + 1 ∨ hi ≤ p.1)) ∨ p.1 ∈ row right input) ↔ _
      constructor <;> intro h
      · rcases h with ⟨old | inLeft, outside⟩ | inRight
        · rcases old with ⟨old, outsideLeft⟩
          by_cases root : p.1 = pivot
          · exact Or.inr (Or.inr (Or.inr ⟨root, old⟩))
          · exact Or.inl ⟨old, by omega⟩
        · exact Or.inr (Or.inl inLeft)
        · exact Or.inr (Or.inr (Or.inl inRight))
      · rcases h with ⟨old, outside⟩ | inLeft | inRight | ⟨root, old⟩
        · exact Or.inl ⟨Or.inl ⟨old, by omega⟩, by omega⟩
        · exact Or.inl ⟨Or.inr inLeft, Or.inl (by have := lb inLeft; omega)⟩
        · exact Or.inr inRight
        · exact Or.inl ⟨Or.inl ⟨old, by omega⟩, by omega⟩
    have leftMembers : ∀ key, lo ≤ key → key < pivot →
        ((key, p.2) ∈ middle ↔ key ∈ row left input) := by
      intro key lower upper
      change (key, p.2) ∈ closePoints right first ↔ _
      rw [ihr]
      have noRight : key ∉ row right (rowAt first p.2) := by
        intro member
        have := (row_bounded right _ key member).1
        omega
      simp only [noRight, or_false]
      change ((key, p.2) ∈ closePoints left points ∧ (key < pivot + 1 ∨ hi ≤ key)) ↔ _
      rw [ihl]
      simp only [show ¬key < lo by omega, show ¬pivot ≤ key by omega,
        or_self, and_false, false_or, show key < pivot + 1 by omega, true_or, and_true]
      rfl
    have rightMembers : ∀ key, pivot < key → key < hi →
        ((key, p.2) ∈ middle ↔ key ∈ row right input) := by
      intro key lower upper
      change (key, p.2) ∈ closePoints right first ↔ _
      rw [ihr]
      have inputEq : row right (rowAt first (key, p.2).2) = row right input := rightInput
      rw [inputEq]
      simp only [show ¬key < pivot + 1 by omega, show ¬hi ≤ key by omega,
        or_self, and_false, false_or]
    have straddle : Straddles middle (Set.Ico lo hi) pivot p.2 ↔
        (row left input).Nonempty ∧ (row right input).Nonempty := by
      constructor
      · rintro ⟨⟨a, ta⟩, ha, ⟨b, tb⟩, hb, hat, hbt, hak, hbk, hal, hbr⟩
        dsimp at hat hbt hak hbk hal hbr
        subst ta; subst tb
        exact ⟨⟨a, (leftMembers a hak.1 hal).mp ha⟩,
          ⟨b, (rightMembers b hbr hbk.2).mp hb⟩⟩
      · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        obtain ⟨al, ar⟩ := row_bounded left input a ha
        obtain ⟨bl, br⟩ := row_bounded right input b hb
        exact ⟨(a,p.2), (leftMembers a al ar).mpr ha,
          (b,p.2), (rightMembers b (by omega) br).mpr hb,
          rfl, rfl, ⟨al, by omega⟩, ⟨by omega, br⟩, ar, by omega⟩
    change p ∈ fillCut middle (Set.Ico lo hi) pivot ↔ _
    rw [fillCut_extension middle (Set.Ico lo hi) pivot p, middleMem, straddle]
    change _ ↔ (p ∈ points ∧ (p.1 < lo ∨ hi ≤ p.1)) ∨
      p.1 ∈ (row left input ∪ row right input ∪
        if pivot ∈ input ∨ (row left input).Nonempty ∧ (row right input).Nonempty
        then {pivot} else ∅)
    have rootOld : p.1 = pivot → (pivot ∈ input ↔ p ∈ points) := by
      intro eq
      change pivot ∈ rowAt points p.2 ↔ _
      rw [mem_rowAt]
      have peq : (pivot, p.2) = p := Prod.ext eq.symm rfl
      rw [peq]
    by_cases root : p.1 = pivot
    · by_cases added : pivot ∈ input ∨
          (row left input).Nonempty ∧ (row right input).Nonempty
      · simp only [if_pos added, Finset.mem_union, Finset.mem_singleton, root, true_and,
          or_true, iff_true]
        have present : p ∈ points ∨ (row left input).Nonempty ∧ (row right input).Nonempty :=
          added.imp (rootOld root).mp id
        rcases present with old | both
        · exact Or.inl (Or.inr (Or.inr (Or.inr old)))
        · exact Or.inr both
      · simp only [if_neg added, Finset.union_empty, Finset.mem_union, root, true_and]
        have absent : ¬(p ∈ points ∨ (row left input).Nonempty ∧ (row right input).Nonempty) := by
          intro h
          exact added (h.imp (rootOld root).mpr id)
        have notOld : p ∉ points := fun h => absent (Or.inl h)
        have notBoth : ¬((row left input).Nonempty ∧ (row right input).Nonempty) :=
          fun h => absent (Or.inr h)
        simp only [notOld, notBoth, or_false]
    · by_cases added : pivot ∈ input ∨
          (row left input).Nonempty ∧ (row right input).Nonempty
      · simp only [if_pos added, Finset.mem_union, Finset.mem_singleton,
          root, false_and, or_false]
      · simp only [if_neg added, Finset.union_empty, Finset.mem_union,
          root, false_and, or_false]

end DynamicOptimality.Geometry.ReferenceClosure
