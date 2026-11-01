import Splay.Accounting.WholeSplayTemporaryFocusedSpines

namespace Splay.Accounting.WholeSplayTemporarySpineRemoval

open Splay.Rank
open Splay.Tree
open Splay.Tree.BST
open Splay.Lazy.Canonical
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.WholeSplayTemporarySpineGeometry

/-!
Keys made permanently silent by the two final monotone spines.

Besides the roots on the inward spine itself, a same-direction double
rotation can retire the outer former search-path root as the root of a light
hanging subtree.  Both kinds of roots are entered without a direction
change in the final tree and hence are not bends.
-/

/-- The root key of a nonempty indexed subtree, as a singleton finite set. -/
noncomputable def rootKeySet
    {n lower upper : ℕ} (tree : BST lower upper)
    (upper_le_n : upper ≤ n) : Finset (Fin n) :=
  match tree with
  | .empty _ => ∅
  | .node (root := root) left right =>
      {⟨root, by
        have rightBounds := right.lower_le_upper
        omega⟩}

/-- A recorded subtree root lies in that subtree's indexed interval. -/
theorem mem_rootKeySet_bounds
    {n lower upper : ℕ} {tree : BST lower upper}
    {upper_le_n : upper ≤ n} {identity : Fin n}
    (member : identity ∈ rootKeySet tree upper_le_n) :
    lower ≤ identity.val ∧ identity.val < upper := by
  cases tree with
  | empty =>
      simp [rootKeySet] at member
  | @node lower root upper left right =>
      have leftBounds := left.lower_le_upper
      have rightBounds := right.lower_le_upper
      simp only [rootKeySet, Finset.mem_singleton] at member
      have valueEq := congrArg Fin.val member
      simp only at valueEq
      omega

/-- A subtree entered with no heavy edge cannot bend at its own root. -/
theorem rootKeySet_disjoint_bendsFrom_none
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (tree : BST lower upper) (upper_le_n : upper ≤ n)
    {identity : Fin n}
    (rootMember : identity ∈ rootKeySet tree upper_le_n) :
    identity ∉ bendsFrom snapshot tree upper_le_n none := by
  cases tree with
  | empty =>
      simp [rootKeySet] at rootMember
  | @node lower root upper left right =>
      have leftBounds := left.lower_le_upper
      have rightBounds := right.lower_le_upper
      simp only [rootKeySet, Finset.mem_singleton] at rootMember
      have valueEq := congrArg Fin.val rootMember
      simp only at valueEq
      intro bendMember
      simp only [bendsFrom, Finset.mem_union] at bendMember
      rcases bendMember with atRoot | inChildren
      · unfold bendAt at atRoot
        simp [Turns] at atRoot
      · rcases inChildren with inLeft | inRight
        · have bounds :=
            mem_bendsFrom_bounds snapshot left (by omega) _ inLeft
          omega
        · have bounds :=
            mem_bendsFrom_bounds snapshot right upper_le_n _ inRight
          omega

namespace RightSpine

/--
Roots silenced by a right spine: every inward spine root and the root, when
present, of every light hanging subtree.
-/
noncomputable def silentKeys
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) : Finset (Fin n) :=
  match spine with
  | .base _ => ∅
  | @RightSpine.grow _ _ _ _ _ root upper inner
      innerSpine hanging bound heavy =>
      insert
        ⟨root, by
          have hangingBounds := hanging.lower_le_upper
          omega⟩
        (silentKeys innerSpine ∪ rootKeySet hanging bound)

/-- Every silent right-spine key lies in the complete spine interval. -/
theorem mem_silentKeys_bounds
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree)
    {identity : Fin n} (member : identity ∈ silentKeys spine) :
    key + 1 ≤ identity.val ∧ identity.val < upper := by
  induction spine with
  | base bound =>
      simp [silentKeys] at member
  | @grow root upper inner innerSpine hanging bound heavy ih =>
      simp only [silentKeys, Finset.mem_insert, Finset.mem_union] at member
      rcases member with atRoot | innerMember | hangingRoot
      · have valueEq := congrArg Fin.val atRoot
        simp only at valueEq
        have innerBounds := inner.lower_le_upper
        have hangingBounds := hanging.lower_le_upper
        omega
      · have bounds := ih innerMember
        have hangingBounds := hanging.lower_le_upper
        omega
      · have bounds := mem_rootKeySet_bounds hangingRoot
        have innerBounds := inner.lower_le_upper
        omega

/--
No silent right-spine key is a bend when the spine is entered either as the
top of a heavy path or through its canonical inward-left edge.
-/
theorem silentKeys_disjoint_bendsFrom
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree)
    (incoming : Option TernaryBranch)
    (canonicalIncoming :
      incoming = none ∨ incoming = some .left) :
    Disjoint (silentKeys spine)
      (bendsFrom snapshot tree spine.upper_le_n incoming) := by
  classical
  induction spine generalizing incoming with
  | base bound =>
      simp [silentKeys]
  | @grow root upper inner innerSpine hanging bound heavy ih =>
      apply Finset.disjoint_left.mpr
      intro identity silentMember bendMember
      simp only [silentKeys, Finset.mem_insert, Finset.mem_union]
        at silentMember
      have heavy' :
          (({
            lower := key + 1
            root := root
            upper := upper
            left := inner
            right := hanging
            upper_le_n := bound
          } : AtNode n).heavyBranch snapshot) = .left := by
        exact heavy
      have bendCases :
          identity ∈
              bendsFrom snapshot inner
                innerSpine.upper_le_n (some .left) ∨
            identity ∈ bendsFrom snapshot hanging bound none := by
        rcases canonicalIncoming with rfl | rfl
        · simpa [bendsFrom, heavy', childIncoming, bendAt, Turns]
            using bendMember
        · simpa [bendsFrom, heavy', childIncoming, bendAt, Turns]
            using bendMember
      rcases bendCases with innerBend | hangingBend
      · rcases silentMember with atRoot | innerSilent | hangingRoot
        · have valueEq := congrArg Fin.val atRoot
          simp only at valueEq
          have bounds :=
            mem_bendsFrom_bounds snapshot inner
              innerSpine.upper_le_n (some .left) innerBend
          omega
        · exact
            (Finset.disjoint_left.mp
              (ih (some .left) (Or.inr rfl)))
              innerSilent innerBend
        · have silentBounds := mem_rootKeySet_bounds hangingRoot
          have bendBounds :=
            mem_bendsFrom_bounds snapshot inner
              innerSpine.upper_le_n (some .left) innerBend
          omega
      · rcases silentMember with atRoot | innerSilent | hangingRoot
        · have valueEq := congrArg Fin.val atRoot
          simp only at valueEq
          have bounds :=
            mem_bendsFrom_bounds snapshot hanging bound none hangingBend
          omega
        · have silentBounds := mem_silentKeys_bounds innerSpine innerSilent
          have bendBounds :=
            mem_bendsFrom_bounds snapshot hanging bound none hangingBend
          omega
        · exact
            rootKeySet_disjoint_bendsFrom_none
              snapshot hanging bound hangingRoot hangingBend

end RightSpine

namespace LeftSpine

/-- Mirror silent-root set for a final left spine. -/
noncomputable def silentKeys
    {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {tree : BST lower key}
    (spine : LeftSpine snapshot base tree) : Finset (Fin n) :=
  match spine with
  | .base _ => ∅
  | @LeftSpine.grow _ _ _ _ _ lower root inner
      innerSpine hanging rootBound bound heavy =>
      insert
        ⟨root, by
          have innerBounds := inner.lower_le_upper
          omega⟩
        (rootKeySet hanging rootBound ∪ silentKeys innerSpine)

/-- Every silent left-spine key lies in the complete spine interval. -/
theorem mem_silentKeys_bounds
    {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {tree : BST lower key}
    (spine : LeftSpine snapshot base tree)
    {identity : Fin n} (member : identity ∈ silentKeys spine) :
    lower ≤ identity.val ∧ identity.val < key := by
  induction spine with
  | base bound =>
      simp [silentKeys] at member
  | @grow lower root inner innerSpine hanging rootBound bound heavy ih =>
      simp only [silentKeys, Finset.mem_insert, Finset.mem_union] at member
      rcases member with atRoot | hangingRoot | innerMember
      · have valueEq := congrArg Fin.val atRoot
        simp only at valueEq
        have hangingBounds := hanging.lower_le_upper
        have innerBounds := inner.lower_le_upper
        omega
      · have bounds := mem_rootKeySet_bounds hangingRoot
        have innerBounds := inner.lower_le_upper
        omega
      · have bounds := ih innerMember
        have hangingBounds := hanging.lower_le_upper
        omega

/--
No silent left-spine key is a bend under no incoming edge or the canonical
inward-right edge.
-/
theorem silentKeys_disjoint_bendsFrom
    {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {tree : BST lower key}
    (spine : LeftSpine snapshot base tree)
    (incoming : Option TernaryBranch)
    (canonicalIncoming :
      incoming = none ∨ incoming = some .right) :
    Disjoint (silentKeys spine)
      (bendsFrom snapshot tree spine.upper_le_n incoming) := by
  classical
  induction spine generalizing incoming with
  | base bound =>
      simp [silentKeys]
  | @grow lower root inner innerSpine hanging
      rootBound bound heavy ih =>
      apply Finset.disjoint_left.mpr
      intro identity silentMember bendMember
      simp only [silentKeys, Finset.mem_insert, Finset.mem_union]
        at silentMember
      have heavy' :
          (({
            lower := lower
            root := root
            upper := key
            left := hanging
            right := inner
            upper_le_n := bound
          } : AtNode n).heavyBranch snapshot) = .right := by
        exact heavy
      have bendCases :
          identity ∈ bendsFrom snapshot hanging rootBound none ∨
            identity ∈
              bendsFrom snapshot inner
                innerSpine.upper_le_n (some .right) := by
        rcases canonicalIncoming with rfl | rfl
        · simpa [bendsFrom, heavy', childIncoming, bendAt, Turns]
            using bendMember
        · simpa [bendsFrom, heavy', childIncoming, bendAt, Turns]
            using bendMember
      rcases bendCases with hangingBend | innerBend
      · rcases silentMember with atRoot | hangingRoot | innerSilent
        · have valueEq := congrArg Fin.val atRoot
          simp only at valueEq
          have bounds :=
            mem_bendsFrom_bounds snapshot hanging rootBound none hangingBend
          omega
        · exact
            rootKeySet_disjoint_bendsFrom_none
              snapshot hanging rootBound hangingRoot hangingBend
        · have silentBounds := mem_silentKeys_bounds innerSpine innerSilent
          have bendBounds :=
            mem_bendsFrom_bounds snapshot hanging rootBound none hangingBend
          omega
      · rcases silentMember with atRoot | hangingRoot | innerSilent
        · have valueEq := congrArg Fin.val atRoot
          simp only at valueEq
          have bounds :=
            mem_bendsFrom_bounds snapshot inner
              innerSpine.upper_le_n (some .right) innerBend
          omega
        · have silentBounds := mem_rootKeySet_bounds hangingRoot
          have bendBounds :=
            mem_bendsFrom_bounds snapshot inner
              innerSpine.upper_le_n (some .right) innerBend
          omega
        · exact
            (Finset.disjoint_left.mp
              (ih (some .right) (Or.inr rfl)))
              innerSilent innerBend

end LeftSpine

end Splay.Accounting.WholeSplayTemporarySpineRemoval
