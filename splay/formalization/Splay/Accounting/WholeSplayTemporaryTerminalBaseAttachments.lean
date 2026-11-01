import Splay.Accounting.WholeSplayTemporaryFocusedSpines
import Splay.Accounting.WholeSplayTemporaryFinalSpineAttachments

namespace Splay.Accounting.WholeSplayTemporaryTerminalBaseAttachments

open Splay.Rank
open Splay.Tree.BST
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.WholeSplayTemporaryPriorityReduction
open Splay.Accounting.WholeSplayTemporaryCoreGeometry
open Splay.Accounting.WholeSplayTemporarySpineGeometry
open Splay.Accounting.WholeSplayTemporaryFocusedSpines
open Splay.Accounting.WholeSplayTemporaryFinalSpineAttachments

/--
Every hanging bend of a right spine lies strictly above the upper endpoint
of its fixed base.
-/
theorem rightSpine_mem_hangingBends_baseUpper_lt
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree)
    {identity : Fin n}
    (member : identity ∈ spine.hangingBends) :
    baseUpper < identity.val := by
  induction spine with
  | base bound =>
      simp [
        WholeSplayTemporarySpineGeometry.RightSpine.hangingBends]
        at member
  | @grow root upper inner innerSpine hanging bound heavy ih =>
      simp only [
        WholeSplayTemporarySpineGeometry.RightSpine.hangingBends,
        Finset.mem_union] at member
      rcases member with previous | current
      · exact ih previous
      · have currentBounds :=
          mem_bendsFrom_bounds snapshot hanging bound none current
        have baseToRoot :=
          RightSpine.baseUpper_le_upper innerSpine
        omega

/--
Every hanging bend of a left spine lies strictly below the lower endpoint
of its fixed base.
-/
theorem leftSpine_mem_hangingBends_lt_baseLower
    {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {tree : BST lower key}
    (spine : LeftSpine snapshot base tree)
    {identity : Fin n}
    (member : identity ∈ spine.hangingBends) :
    identity.val < baseLower := by
  induction spine with
  | base bound =>
      simp [
        WholeSplayTemporarySpineGeometry.LeftSpine.hangingBends]
        at member
  | @grow lower root inner innerSpine hanging
      rootBound bound heavy ih =>
      simp only [
        WholeSplayTemporarySpineGeometry.LeftSpine.hangingBends,
        Finset.mem_union] at member
      rcases member with current | previous
      · have currentBounds :=
          mem_bendsFrom_bounds
            snapshot hanging rootBound none current
        have rootToBase :=
          LeftSpine.lower_le_baseLower innerSpine
        omega
      · exact ih previous

/--
For the canonical temporary snapshot, an endpoint-created identity in the
fixed left-base incoming-right delta is automatically the terminal
slot-zero attachment.  No separate nontrivial-incoming premise is needed:
the final-root decomposition and interval separation force the final left
spine to retain that incoming edge.
-/
theorem fixedLeftBaseDelta_attachment_zero
    {n baseLower baseUpper : ℕ}
    (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    {leftBase : BST baseLower key.val}
    {rightBase : BST (key.val + 1) baseUpper}
    {finalLeftTree : BST 0 key.val}
    {finalRightTree : BST (key.val + 1) n}
    (finalLeft :
      LeftSpine
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        leftBase finalLeftTree)
    (finalRight :
      RightSpine
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        rightBase finalRightTree)
    {globalBefore : BST 0 n}
    (identity :
      CreatedIdentity
        (before := globalBefore)
        (after := .node finalLeftTree finalRightTree)
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered))
    (delta :
      identity.val ∈
        (bendsFrom
            (temporarySnapshot comparison key comparisonRoot
              leftBoundary rightBoundary ordered)
            leftBase finalLeft.base_le_n (some .right) \
          bendsFrom
            (temporarySnapshot comparison key comparisonRoot
              leftBoundary rightBoundary ordered)
            leftBase finalLeft.base_le_n none)) :
    attachment finalLeft finalRight ⟨0, by omega⟩ =
      some identity := by
  let snapshot :=
    temporarySnapshot comparison key comparisonRoot
      leftBoundary rightBoundary ordered
  have deltaMember :=
    (Finset.mem_sdiff.mp delta).1
  have deltaAbsent :=
    (Finset.mem_sdiff.mp delta).2
  have leftBounds :=
    mem_bendsFrom_bounds snapshot leftBase
      finalLeft.base_le_n (some .right) deltaMember
  let raw : Fin n := identity.val
  have finalMember :
      raw ∈
        bends snapshot (.node finalLeftTree finalRightTree) :=
    by
      simpa only [raw] using
        (Finset.mem_sdiff.mp identity.property).1
  have finalDecomposition :=
    Splay.Accounting.WholeSplayTemporaryFinalSpineBends.temporaryFinalRoot_bends_eq
      comparison key comparisonRoot leftBoundary rightBoundary
      ordered finalLeft finalRight
  rw [finalDecomposition] at finalMember
  have incomingNe :
      Splay.Accounting.WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
        finalLeft ≠ none := by
    intro incomingNone
    rcases Finset.mem_union.mp finalMember with leftPart | rightPart
    · rcases Finset.mem_union.mp leftPart with inBase | inHanging
      · rw [incomingNone] at inBase
        exact deltaAbsent inBase
      · have hangingBound :=
          leftSpine_mem_hangingBends_lt_baseLower
            finalLeft inHanging
        omega
    · rcases Finset.mem_union.mp rightPart with inBase | inHanging
      · have rightBounds :=
          mem_bendsFrom_bounds snapshot rightBase
            finalRight.base_le_n _ inBase
        omega
      · have hangingBound :=
          rightSpine_mem_hangingBends_baseUpper_lt
            finalRight inHanging
        have baseBounds := rightBase.lower_le_upper
        omega
  have incomingEq :
      Splay.Accounting.WholeSplayTemporaryFinalSpineBends.LeftSpine.incomingAtBase
          finalLeft = some .right := by
    exact
      LeftSpine.IsPrefix.incomingAtBase_eq_some_of_ne_none
        finalLeft incomingNe
  apply attachment_zero_eq_some_of_mem_left finalLeft finalRight
  apply mem_leftCandidates_iff.mpr
  simpa only [incomingEq] using delta

/--
Symmetric automatic terminal realization of a fixed right-base
incoming-left delta as attachment slot one.
-/
theorem fixedRightBaseDelta_attachment_one
    {n baseLower baseUpper : ℕ}
    (comparison : BST 0 n) (key : Fin n)
    (comparisonRoot : comparison.HasRoot key.val)
    (leftBoundary rightBoundary : External n)
    (ordered :
      leftBoundary < valuePos key ∧ valuePos key < rightBoundary)
    {leftBase : BST baseLower key.val}
    {rightBase : BST (key.val + 1) baseUpper}
    {finalLeftTree : BST 0 key.val}
    {finalRightTree : BST (key.val + 1) n}
    (finalLeft :
      LeftSpine
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        leftBase finalLeftTree)
    (finalRight :
      RightSpine
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered)
        rightBase finalRightTree)
    {globalBefore : BST 0 n}
    (identity :
      CreatedIdentity
        (before := globalBefore)
        (after := .node finalLeftTree finalRightTree)
        (temporarySnapshot comparison key comparisonRoot
          leftBoundary rightBoundary ordered))
    (delta :
      identity.val ∈
        (bendsFrom
            (temporarySnapshot comparison key comparisonRoot
              leftBoundary rightBoundary ordered)
            rightBase finalRight.base_le_n (some .left) \
          bendsFrom
            (temporarySnapshot comparison key comparisonRoot
              leftBoundary rightBoundary ordered)
            rightBase finalRight.base_le_n none)) :
    attachment finalLeft finalRight ⟨1, by omega⟩ =
      some identity := by
  let snapshot :=
    temporarySnapshot comparison key comparisonRoot
      leftBoundary rightBoundary ordered
  have deltaMember :=
    (Finset.mem_sdiff.mp delta).1
  have deltaAbsent :=
    (Finset.mem_sdiff.mp delta).2
  have rightBounds :=
    mem_bendsFrom_bounds snapshot rightBase
      finalRight.base_le_n (some .left) deltaMember
  let raw : Fin n := identity.val
  have finalMember :
      raw ∈
        bends snapshot (.node finalLeftTree finalRightTree) :=
    by
      simpa only [raw] using
        (Finset.mem_sdiff.mp identity.property).1
  have finalDecomposition :=
    Splay.Accounting.WholeSplayTemporaryFinalSpineBends.temporaryFinalRoot_bends_eq
      comparison key comparisonRoot leftBoundary rightBoundary
      ordered finalLeft finalRight
  rw [finalDecomposition] at finalMember
  have incomingNe :
      Splay.Accounting.WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
        finalRight ≠ none := by
    intro incomingNone
    rcases Finset.mem_union.mp finalMember with leftPart | rightPart
    · rcases Finset.mem_union.mp leftPart with inBase | inHanging
      · have leftBounds :=
          mem_bendsFrom_bounds snapshot leftBase
            finalLeft.base_le_n _ inBase
        omega
      · have hangingBound :=
          leftSpine_mem_hangingBends_lt_baseLower
            finalLeft inHanging
        have baseBounds := leftBase.lower_le_upper
        omega
    · rcases Finset.mem_union.mp rightPart with inBase | inHanging
      · rw [incomingNone] at inBase
        exact deltaAbsent inBase
      · have hangingBound :=
          rightSpine_mem_hangingBends_baseUpper_lt
            finalRight inHanging
        omega
  have incomingEq :
      Splay.Accounting.WholeSplayTemporaryFinalSpineBends.RightSpine.incomingAtBase
          finalRight = some .left := by
    exact
      RightSpine.IsPrefix.incomingAtBase_eq_some_of_ne_none
        finalRight incomingNe
  apply attachment_one_eq_some_of_mem_right finalLeft finalRight
  apply mem_rightCandidates_iff.mpr
  simpa only [incomingEq] using delta

end Splay.Accounting.WholeSplayTemporaryTerminalBaseAttachments
