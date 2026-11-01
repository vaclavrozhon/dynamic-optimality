import SurfaceUpdate
import CanonicalSurface
import Splay.Tree.SubtreeAt

/-!
Discharges the inherited-subtree hypotheses of SurfaceUpdate. Every literal
subtree of a height refinement inherits boundary height barriers and exact
owners. If the access is outside its key interval, every internal height,
strict neighborhood, and comparator owner is preserved by the Greedy update.
-/

namespace GreedyMerge.Surface

open Splay.Tree
open Splay.Tree.BST

def Barriers (height : ℕ → ℤ) (n lo hi : ℕ) : Prop :=
  (lo = 0 ∨ ∀ key, lo ≤ key → key < hi → height key ≤ height (lo - 1)) ∧
  (hi = n ∨ ∀ key, lo ≤ key → key < hi → height key ≤ height hi)

theorem refines_left_barriers {n lo root hi : ℕ}
    (height : ℕ → ℤ) (rank owner : ℕ → ℕ)
    (left : BST lo root) (right : BST (root + 1) hi)
    (refines : Refines height rank owner (.node left right))
    (barriers : Barriers height n lo hi) : Barriers height n lo root := by
  have hhi := right.lower_le_upper
  constructor
  · rcases barriers.1 with h | h
    · exact Or.inl h
    · exact Or.inr (fun key hklo hkhi => h key hklo (by omega))
  · exact Or.inr (fun key hklo hkhi => refines.1 key hklo (by omega))

theorem refines_right_barriers {n lo root hi : ℕ}
    (height : ℕ → ℤ) (rank owner : ℕ → ℕ)
    (left : BST lo root) (right : BST (root + 1) hi)
    (refines : Refines height rank owner (.node left right))
    (barriers : Barriers height n lo hi) : Barriers height n (root + 1) hi := by
  have hlo := left.lower_le_upper
  constructor
  · right
    intro key hklo hkhi
    simpa using refines.1 key (by omega) hkhi
  · rcases barriers.2 with h | h
    · exact Or.inl h
    · exact Or.inr (fun key hklo hkhi => h key (by omega) hkhi)

theorem subtree_refines_barriers {n lo hi lower upper depth : ℕ}
    (height : ℕ → ℤ) (rank owner : ℕ → ℕ)
    {inner : BST lo hi} {tree : BST lower upper}
    (occurrence : SubtreeAt inner depth tree)
    (refines : Refines height rank owner tree)
    (barriers : Barriers height n lower upper) :
    Refines height rank owner inner ∧ Barriers height n lo hi := by
  induction occurrence with
  | here => exact ⟨refines, barriers⟩
  | @left lower root upper depth leftTree occurrence rightTree ih =>
      have hleft := refines.2.2.1
      exact ih hleft
        (refines_left_barriers height rank owner leftTree rightTree refines barriers)
  | @right lower root upper depth leftTree rightTree occurrence ih =>
      have hright := refines.2.2.2
      exact ih hright
        (refines_right_barriers height rank owner leftTree rightTree refines barriers)

theorem subtree_exactOwners {lo hi lower upper depth : ℕ}
    (rank owner : ℕ → ℕ) {inner : BST lo hi} {tree : BST lower upper}
    (occurrence : SubtreeAt inner depth tree) (exactOwners : ExactOwners rank owner tree) :
    ExactOwners rank owner inner := by
  induction occurrence with
  | here => exact exactOwners
  | left occurrence rightTree ih => exact ih exactOwners.2.1
  | right leftTree occurrence ih => exact ih exactOwners.2.2

theorem subtree_canonical {lo hi lower upper depth : ℕ}
    (height : ℕ → ℤ) (priority : ℕ → ℕ) {inner : BST lo hi} {tree : BST lower upper}
    (occurrence : SubtreeAt inner depth tree) (canonical : Canonical height priority tree) :
    Canonical height priority inner := by
  induction occurrence with
  | here => exact canonical
  | left occurrence rightTree ih => exact ih canonical.2.2.2.1
  | right leftTree occurrence ih => exact ih canonical.2.2.2.2

/-- All inherited assumptions of the gap-preservation theorem follow from
an actual full refinement and a literal subtree occurrence. -/
theorem disjoint_subtree_owners_preserved {n lo hi depth access center : ℕ}
    (height : ℕ → ℤ) (rank oldOwner newOwner : ℕ → ℕ)
    (tree : BST 0 n) (inner : BST lo hi) (time : ℤ)
    (occurrence : SubtreeAt inner depth tree)
    (unique : IntervalUnique rank n)
    (oldOwners : Owners height rank oldOwner n)
    (newOwners : Owners (RaiseSurface height n access time) rank newOwner n)
    (global : UniqueGlobalMinimum rank n access)
    (refines : Refines height rank oldOwner tree)
    (outside : access < lo ∨ hi ≤ access)
    (fresh : ∀ z, z < n → height z < time)
    (hcenterLo : lo ≤ center) (hcenterHi : center < hi) :
    oldOwner center = newOwner center := by
  have hbounds := occurrence.bounds
  have hinherited := subtree_refines_barriers height rank oldOwner occurrence refines
    (show Barriers height n 0 n from ⟨Or.inl rfl, Or.inl rfl⟩)
  have hexact := subtree_exactOwners rank oldOwner occurrence
    (full_refinement_exactOwners height rank oldOwner tree oldOwners refines)
  apply offPathGap_owners_preserved height rank oldOwner newOwner inner time unique
    oldOwners newOwners global hexact hbounds.2 outside fresh hcenterLo hcenterHi
  · rcases hinherited.2.1 with h | h
    · exact Or.inl h
    · exact Or.inr (h center hcenterLo hcenterHi)
  · rcases hinherited.2.2 with h | h
    · exact Or.inl h
    · exact Or.inr (h center hcenterLo hcenterHi)

/-- Recanonicalizing any old subtree disjoint from the access leaves its
whole binary shape fixed. The boundary and owner invariants are derived
from the concrete old canonical tree and its subtree occurrence. -/
theorem disjoint_subtree_shape_preserved {n lo hi depth access : ℕ}
    (height : ℕ → ℤ) (rank oldOwner newOwner : ℕ → ℕ)
    (tree : BST 0 n) (inner newInner : BST lo hi) (time : ℤ)
    (occurrence : SubtreeAt inner depth tree)
    (unique : IntervalUnique rank n)
    (oldOwners : Owners height rank oldOwner n)
    (newOwners : Owners (RaiseSurface height n access time) rank newOwner n)
    (global : UniqueGlobalMinimum rank n access)
    (canonical : Canonical height (fun key => rank (oldOwner key)) tree)
    (newCanonical : Canonical (RaiseSurface height n access time)
      (fun key => rank (newOwner key)) newInner)
    (outside : access < lo ∨ hi ≤ access)
    (fresh : ∀ z, z < n → height z < time) : inner = newInner := by
  have refines := canonical_refines height rank oldOwner tree canonical
  have hbounds := occurrence.bounds
  have hexact := subtree_exactOwners rank oldOwner occurrence
    (full_refinement_exactOwners height rank oldOwner tree oldOwners refines)
  apply canonical_eq_of_priorities_eq height (RaiseSurface height n access time)
    (fun key => rank (oldOwner key)) (fun key => rank (newOwner key)) inner newInner
  · intro key hklo hkhi
    exact (offPathGap_heights_unchanged height rank oldOwner inner time oldOwners global
      hexact hbounds.2 outside key hklo hkhi).symm
  · intro key hklo hkhi
    exact congrArg rank (disjoint_subtree_owners_preserved height rank oldOwner newOwner
      tree inner time occurrence unique oldOwners newOwners global refines outside fresh hklo hkhi)
  · exact subtree_canonical height (fun key => rank (oldOwner key)) occurrence canonical
  · exact newCanonical

end GreedyMerge.Surface

#print axioms GreedyMerge.Surface.disjoint_subtree_owners_preserved
#print axioms GreedyMerge.Surface.disjoint_subtree_shape_preserved
