import Splay.Tree.DepthMin
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

/-!
The minimum identity underlying a canonical plateau refinement. The input
atoms alternate gap minima and separator values. A separator's priority is
the minimum of its neighboring three atoms. A Cartesian BST of those
priorities has the required actual minimum at every separator subtree.

This is a concrete indexed-BST result, with Cartesian existence proved
separately. Substitution of the recursively expanded gap subtrees, and
identification with strict height neighborhoods, remain separate interfaces.
-/

namespace GreedyMerge.Plateau

open Splay.Tree
open Splay.Tree.BST

def Priority (rank : ℕ → ℕ) (separator : ℕ) : ℕ :=
  min (rank (2 * separator))
    (min (rank (2 * separator + 1)) (rank (2 * separator + 2)))

def Cartesian (priority : ℕ → ℕ) {lo hi : ℕ} : BST lo hi → Prop
  | .empty _ => True
  | .node (root := root) left right =>
      (∀ key, lo ≤ key → key < hi → priority root ≤ priority key) ∧
        Cartesian priority left ∧ Cartesian priority right

theorem priority_le_atom (rank : ℕ → ℕ) {separator atom : ℕ}
    (hl : 2 * separator ≤ atom) (hu : atom ≤ 2 * separator + 2) :
    Priority rank separator ≤ rank atom := by
  have hcases : atom = 2 * separator ∨ atom = 2 * separator + 1 ∨
      atom = 2 * separator + 2 := by omega
  rcases hcases with h | h | h
  · rw [h]
    exact Nat.min_le_left _ _
  · rw [h]
    exact (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  · rw [h]
    exact (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)

theorem priority_eq_local_min (rank : ℕ → ℕ) {separator owner : ℕ}
    (howner : IsIntervalMin rank (2 * separator) (2 * separator + 2) owner) :
    Priority rank separator = rank owner := by
  apply Nat.le_antisymm
  · exact priority_le_atom rank howner.1 howner.2.1
  · unfold Priority
    apply Nat.le_min.mpr
    constructor
    · exact howner.2.2 _ (by omega) (by omega)
    · apply Nat.le_min.mpr
      constructor
      · exact howner.2.2 _ (by omega) (by omega)
      · exact howner.2.2 _ (by omega) (by omega)

/-- The neighboring triples cover precisely the atoms of any nonempty
consecutive separator range, including both extreme gap atoms. -/
theorem atom_covered_by_separator {lo hi atom : ℕ}
    (hne : lo < hi) (hl : 2 * lo ≤ atom) (hu : atom ≤ 2 * hi) :
    ∃ separator, lo ≤ separator ∧ separator < hi ∧
      2 * separator ≤ atom ∧ atom ≤ 2 * separator + 2 := by
  by_cases hedge : atom = 2 * hi
  · refine ⟨hi - 1, ?_, ?_, ?_, ?_⟩ <;> omega
  · refine ⟨atom / 2, ?_, ?_, ?_, ?_⟩ <;> omega

/-- A minimum-priority separator has exactly its neighborhood minimum
as the minimum of the entire corresponding plateau atom interval. -/
theorem local_min_is_full_min (rank : ℕ → ℕ)
    {lo root hi owner : ℕ} (left : BST lo root) (right : BST (root + 1) hi)
    (hroot : ∀ key, lo ≤ key → key < hi →
      Priority rank root ≤ Priority rank key)
    (howner : IsIntervalMin rank (2 * root) (2 * root + 2) owner) :
    IsIntervalMin rank (2 * lo) (2 * hi) owner := by
  have hlo := left.lower_le_upper
  have hhi := right.lower_le_upper
  have hownerLo := howner.1
  have hownerHi := howner.2.1
  refine ⟨by omega, by omega, ?_⟩
  intro atom hl hu
  obtain ⟨separator, hsepLo, hsepHi, hcoverLo, hcoverHi⟩ :=
    atom_covered_by_separator (by omega : lo < hi) hl hu
  rw [← priority_eq_local_min rank howner]
  exact (hroot separator hsepLo hsepHi).trans
    (priority_le_atom rank hcoverLo hcoverHi)

def ExactMinima (rank : ℕ → ℕ) {lo hi : ℕ} : BST lo hi → Prop
  | .empty _ => True
  | .node (root := root) left right =>
      (∀ owner, IsIntervalMin rank (2 * root) (2 * root + 2) owner →
        IsIntervalMin rank (2 * lo) (2 * hi) owner) ∧
        ExactMinima rank left ∧ ExactMinima rank right

theorem cartesian_exact_minima {lo hi : ℕ} (rank : ℕ → ℕ)
    (tree : BST lo hi) (h : Cartesian (Priority rank) tree) :
    ExactMinima rank tree := by
  induction tree with
  | empty => trivial
  | node left right ihLeft ihRight =>
      obtain ⟨hroot, hleft, hright⟩ := h
      refine ⟨?_, ihLeft hleft, ihRight hright⟩
      intro owner howner
      exact local_min_is_full_min rank left right hroot howner

/-- A Cartesian refinement exists for any integer priority assignment.
This theorem does not yet specify the fixed leftmost tie-breaking rule. -/
theorem exists_cartesian (priority : ℕ → ℕ) (lo hi : ℕ) (h : lo ≤ hi) :
    ∃ tree : BST lo hi, Cartesian priority tree := by
  generalize hsize : hi - lo = size
  induction size using Nat.strong_induction_on generalizing lo hi with
  | h size ih =>
      by_cases heq : lo = hi
      · subst hi
        exact ⟨.empty lo, trivial⟩
      · have hlt : lo < hi := by omega
        have hnonempty : (Finset.Ico lo hi).Nonempty := by
          exact ⟨lo, by simp [hlt]⟩
        obtain ⟨root, hrootMem, hmin⟩ :=
          Finset.exists_min_image (Finset.Ico lo hi) priority hnonempty
        have hrootBounds := Finset.mem_Ico.mp hrootMem
        obtain ⟨left, hleft⟩ := ih (root - lo) (by omega) lo root
          hrootBounds.1 rfl
        obtain ⟨right, hright⟩ := ih (hi - (root + 1)) (by omega)
          (root + 1) hi (by omega) rfl
        refine ⟨.node left right, ?_, hleft, hright⟩
        intro key hklo hkhi
        exact hmin key (Finset.mem_Ico.mpr ⟨hklo, hkhi⟩)

theorem exists_exact_refinement (rank : ℕ → ℕ) (lo hi : ℕ) (h : lo ≤ hi) :
    ∃ tree : BST lo hi, Cartesian (Priority rank) tree ∧ ExactMinima rank tree := by
  obtain ⟨tree, htree⟩ := exists_cartesian (Priority rank) lo hi h
  exact ⟨tree, htree, cartesian_exact_minima rank tree htree⟩

end GreedyMerge.Plateau

#print axioms GreedyMerge.Plateau.cartesian_exact_minima
#print axioms GreedyMerge.Plateau.exists_exact_refinement
