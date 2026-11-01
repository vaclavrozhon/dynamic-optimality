import Splay.Accounting.WholeSplayTemporaryFinalSpineBends
import Splay.Accounting.WholeSplayTemporaryFocusedSpines

namespace Splay.Accounting.WholeSplayTemporarySpineCreation

open Splay.Rank
open Splay.Tree.BST
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.WholeSplayTemporarySpineGeometry

/-!
Creation monotonicity for completed monotone spines.

Entering a nontrivial right spine through `.left` produces exactly the same
bend set as entering its outer root with no incoming edge; dually for a left
spine and `.right`.  Thus the only possible incoming-edge creation that can
survive at a complete spine lies in its fixed base.
-/

/--
Any incoming-left creation of a complete right spine is already an
incoming-left creation of its fixed base.
-/
theorem rightSpine_incomingLeftDelta_subset_baseDelta
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) :
    (bendsFrom snapshot tree spine.upper_le_n (some .left) \
      bendsFrom snapshot tree spine.upper_le_n none) ⊆
      (bendsFrom snapshot base spine.base_le_n (some .left) \
        bendsFrom snapshot base spine.base_le_n none) := by
  cases spine with
  | base bound =>
      exact Finset.Subset.rfl
  | @grow root upper inner innerSpine hanging bound heavy =>
      rw [innerSpine.bendsFrom_none_grow hanging bound heavy]
      rw [
        (RightSpine.grow innerSpine hanging bound heavy).bendsFrom_some_left]
      simp only [
        WholeSplayTemporarySpineGeometry.RightSpine.hangingBends]
      simp

/--
Any incoming-right creation of a complete left spine is already an
incoming-right creation of its fixed base.
-/
theorem leftSpine_incomingRightDelta_subset_baseDelta
    {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {tree : BST lower key}
    (spine : LeftSpine snapshot base tree) :
    (bendsFrom snapshot tree spine.upper_le_n (some .right) \
      bendsFrom snapshot tree spine.upper_le_n none) ⊆
      (bendsFrom snapshot base spine.base_le_n (some .right) \
        bendsFrom snapshot base spine.base_le_n none) := by
  cases spine with
  | base bound =>
      exact Finset.Subset.rfl
  | @grow lower root inner innerSpine hanging rootBound bound heavy =>
      rw [innerSpine.bendsFrom_none_grow
        hanging rootBound bound heavy]
      rw [
        WholeSplayTemporarySpineGeometry.LeftSpine.bendsFrom_some_right
          (LeftSpine.grow
            innerSpine hanging rootBound bound heavy)]
      simp only [
        WholeSplayTemporarySpineGeometry.LeftSpine.hangingBends]
      simp

/--
The complete bend set of the hanging subtree introduced by one right-spine
grow remains among the hanging bends of every later spine extension.
-/
theorem rightGrow_hangingBends_subset_of_prefix
    {n key baseUpper root upper finalUpper : ℕ}
    {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {inner : BST (key + 1) root}
    (oldSpine : RightSpine snapshot base inner)
    (hanging : BST (root + 1) upper)
    (bound : upper ≤ n)
    (heavy : _)
    {newSpine :
      RightSpine snapshot base (.node inner hanging)}
    {finalTree : BST (key + 1) finalUpper}
    {finalSpine : RightSpine snapshot base finalTree}
    (grown :
      newSpine =
        RightSpine.grow oldSpine hanging bound heavy)
    (extension :
      WholeSplayTemporaryFocusedSpines.RightSpine.IsPrefix
        newSpine finalSpine) :
    bendsFrom snapshot hanging bound none ⊆
      finalSpine.hangingBends := by
  subst newSpine
  intro identity member
  apply extension.hangingBends_subset
  simp only [
    WholeSplayTemporarySpineGeometry.RightSpine.hangingBends,
    Finset.mem_union]
  exact Or.inr member

/--
The complete bend set of the hanging subtree introduced by one left-spine
grow remains among the hanging bends of every later spine extension.
-/
theorem leftGrow_hangingBends_subset_of_prefix
    {n key baseLower lower root finalLower : ℕ}
    {snapshot : Snapshot n}
    {base : BST baseLower key}
    {inner : BST (root + 1) key}
    (oldSpine : LeftSpine snapshot base inner)
    (hanging : BST lower root)
    (rootBound : root ≤ n)
    (bound : key ≤ n)
    (heavy : _)
    {newSpine :
      LeftSpine snapshot base (.node hanging inner)}
    {finalTree : BST finalLower key}
    {finalSpine : LeftSpine snapshot base finalTree}
    (grown :
      newSpine =
        LeftSpine.grow oldSpine hanging rootBound bound heavy)
    (extension :
      WholeSplayTemporaryFocusedSpines.LeftSpine.IsPrefix
        newSpine finalSpine) :
    bendsFrom snapshot hanging rootBound none ⊆
      finalSpine.hangingBends := by
  subst newSpine
  intro identity member
  apply extension.hangingBends_subset
  simp only [
    WholeSplayTemporarySpineGeometry.LeftSpine.hangingBends,
    Finset.mem_union]
  exact Or.inl member

end Splay.Accounting.WholeSplayTemporarySpineCreation
