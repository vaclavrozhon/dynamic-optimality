import SurfaceOwners

/-!
Exact search-path correspondence for actual strict-height neighborhoods.
This composes SurfaceOwners' derived subtree minima with a unique global
minimum-rank access key. It counts every key satisfying the strict-neighborhood
criterion and proves equality with the refinement's ordinary search-path length.

Closed-rectangle Greedy visibility is not defined in this file; the paper's
surface criterion supplies that separate identification.
-/

namespace GreedyMerge.Surface

open Splay.Tree
open Splay.Tree.BST

def UniqueGlobalMinimum (rank : ℕ → ℕ) (n access : ℕ) : Prop :=
  access < n ∧ ∀ key, key < n → key ≠ access → rank access < rank key

theorem owner_eq_iff_neighborhood {n access center : ℕ}
    (height : ℕ → ℤ) (rank owner : ℕ → ℕ)
    (owners : Owners height rank owner n)
    (global : UniqueGlobalMinimum rank n access) (hcenter : center < n) :
    owner center = access ↔ Neighborhood height n center access := by
  obtain ⟨hvisible, hmin⟩ := owners center hcenter
  constructor
  · intro heq
    simpa [heq] using hvisible
  · intro haccess
    by_contra hne
    have hlow := hmin access haccess
    have hstrict := global.2 (owner center) hvisible.2.1 hne
    omega

theorem minimum_eq_iff_inside {n lo hi access minimum : ℕ}
    (rank : ℕ → ℕ) (global : UniqueGlobalMinimum rank n access)
    (hne : lo < hi) (hhi : hi ≤ n)
    (hmin : IsIntervalMin rank lo (hi - 1) minimum) :
    minimum = access ↔ lo ≤ access ∧ access < hi := by
  obtain ⟨hminLo, hminHi, hminRank⟩ := hmin
  constructor
  · intro heq
    omega
  · intro hinside
    by_contra hneKey
    have hstrict := global.2 minimum (by omega) hneKey
    have hlow := hminRank access hinside.1 (by omega)
    omega

def OwnerCount (owner : ℕ → ℕ) (access : ℕ) {lo hi : ℕ} : BST lo hi → ℕ
  | .empty _ => 0
  | .node (root := root) left right =>
      (if owner root = access then 1 else 0) +
        OwnerCount owner access left + OwnerCount owner access right

def SearchPathLength (access : ℕ) {lo hi : ℕ} : BST lo hi → ℕ
  | .empty _ => 0
  | .node (root := root) left right =>
      if access = root then 1
      else if access < root then SearchPathLength access left + 1
      else SearchPathLength access right + 1

theorem ownerCount_zero_of_outside {lo hi access : ℕ}
    (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (exactOwners : ExactOwners rank owner tree)
    (outside : access < lo ∨ hi ≤ access) :
    OwnerCount owner access tree = 0 := by
  induction tree with
  | empty => rfl
  | @node lo root hi left right ihLeft ihRight =>
      obtain ⟨hmin, hexactLeft, hexactRight⟩ := exactOwners
      have hlo := left.lower_le_upper
      have hhi := right.lower_le_upper
      have hownerLo := hmin.1
      have hownerHi := hmin.2.1
      have hne : owner root ≠ access := by omega
      have hoffLeft : access < lo ∨ root ≤ access := by omega
      have hoffRight : access < root + 1 ∨ hi ≤ access := by omega
      simp only [OwnerCount, if_neg hne, ihLeft hexactLeft hoffLeft,
        ihRight hexactRight hoffRight]

theorem ownerCount_eq_searchPathLength {n lo hi access : ℕ}
    (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (global : UniqueGlobalMinimum rank n access)
    (exactOwners : ExactOwners rank owner tree)
    (hhi : hi ≤ n) (haccessLo : lo ≤ access) (haccessHi : access < hi) :
    OwnerCount owner access tree = SearchPathLength access tree := by
  induction tree with
  | empty => omega
  | @node lo root hi left right ihLeft ihRight =>
      obtain ⟨hmin, hexactLeft, hexactRight⟩ := exactOwners
      have hlo := left.lower_le_upper
      have hrootHi := right.lower_le_upper
      have howner : owner root = access :=
        (minimum_eq_iff_inside rank global (by omega) hhi hmin).2 ⟨haccessLo, haccessHi⟩
      by_cases heq : access = root
      · have hzLeft := ownerCount_zero_of_outside (access := access) rank owner left hexactLeft (Or.inr (by omega))
        have hzRight := ownerCount_zero_of_outside (access := access) rank owner right hexactRight (Or.inl (by omega))
        simp only [OwnerCount, SearchPathLength, if_pos howner, if_pos heq,
          hzLeft, hzRight, Nat.add_zero]
      · by_cases hleft : access < root
        · have hcount := ihLeft hexactLeft (by omega) haccessLo hleft
          have hzRight := ownerCount_zero_of_outside (access := access) rank owner right hexactRight (Or.inl (by omega))
          simp only [OwnerCount, SearchPathLength, if_pos howner, if_neg heq,
            if_pos hleft, hzRight, Nat.add_zero]
          omega
        · have hright : root + 1 ≤ access := by omega
          have hcount := ihRight hexactRight hhi hright haccessHi
          have hzLeft := ownerCount_zero_of_outside (access := access) rank owner left hexactLeft (Or.inr (by omega))
          simp only [OwnerCount, SearchPathLength, if_pos howner, if_neg heq,
            if_neg hleft, hzLeft, Nat.add_zero]
          omega

noncomputable def Indicator (p : Prop) : ℕ := @ite ℕ p (Classical.propDecidable p) 1 0

noncomputable def TouchCount (height : ℕ → ℤ) (n access : ℕ)
    {lo hi : ℕ} : BST lo hi → ℕ
  | .empty _ => 0
  | .node (root := root) left right =>
      Indicator (Neighborhood height n root access) +
        TouchCount height n access left + TouchCount height n access right

theorem touchCount_eq_ownerCount {n lo hi access : ℕ}
    (height : ℕ → ℤ) (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (owners : Owners height rank owner n)
    (global : UniqueGlobalMinimum rank n access) (hhi : hi ≤ n) :
    TouchCount height n access tree = OwnerCount owner access tree := by
  classical
  induction tree with
  | empty => rfl
  | @node lo root hi left right ihLeft ihRight =>
      have hrootHi := right.lower_le_upper
      have hiff := owner_eq_iff_neighborhood height rank owner owners global
        (by omega : root < n)
      have hleft := ihLeft (by omega : root ≤ n)
      have hright := ihRight hhi
      simp only [TouchCount, OwnerCount, Indicator, ← hiff, hleft, hright]

/-- The strict-neighborhood touch count equals the ordinary search-path
length in every valid height/owner-priority refinement. Exact subtree owners
are derived from the actual surface, not supplied as a premise. -/
theorem touchCount_eq_searchPathLength {n access : ℕ}
    (height : ℕ → ℤ) (rank owner : ℕ → ℕ) (tree : BST 0 n)
    (owners : Owners height rank owner n)
    (global : UniqueGlobalMinimum rank n access)
    (refines : Refines height rank owner tree) :
    TouchCount height n access tree = SearchPathLength access tree := by
  rw [touchCount_eq_ownerCount height rank owner tree owners global (Nat.le_refl n)]
  exact ownerCount_eq_searchPathLength rank owner tree global
    (full_refinement_exactOwners height rank owner tree owners refines)
    (Nat.le_refl n) (Nat.zero_le access) global.1

end GreedyMerge.Surface

#print axioms GreedyMerge.Surface.touchCount_eq_searchPathLength
