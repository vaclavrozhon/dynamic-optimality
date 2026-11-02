import MultiSplay.ComparatorGuardBlocks

/-! # The reflected classical word on the same opaque blocks -/

namespace MultiSplay.ComparatorGuard

open ChaCha Paper20261030 ColoredStorage
open CommonForest

variable {α : Type*}

theorem right_block_checkpoints (front suffix : Block α) (old incoming : Plain α)
    (pivot upper : α) (oldLast : GapBST.lastKey old = upper)
    (incomingLast : GapBST.lastKey incoming = pivot) :
    Program [GapBST.gaps (checkpointAfter front suffix old pivot),GapBST.gaps incoming]
      (ClassicalSwitch.word true (lowerBoundary front) (upperBoundary upper suffix)
        (GapBST.gaps old).inorder (GapBST.gaps incoming).inorder pivot)
      [GapBST.gaps (checkpointBefore front suffix incoming upper),GapBST.gaps old]
      (2+2*(lowerBoundary front).count+2*(upperBoundary upper suffix).count) := by
  cases front with
  | none =>
      cases suffix with
      | none =>
          simpa [checkpointBefore,checkpointAfter,withLeft,withRight,GapBST.gaps,
            GapBST.lastKey,oldLast,incomingLast,lowerBoundary,upperBoundary,
            ClassicalSwitch.Boundary.count,ClassicalSwitch.Boundary.reflect,ClassicalSwitch.word,
            ClassicalSwitch.leftWord,Auxiliary.mirror,Auxiliary.inorder_mirror] using
            (noGuards_checkpoints (Auxiliary.mirror (GapBST.gaps old))
              (Auxiliary.mirror (GapBST.gaps incoming)) pivot).mirror
      | some suffix =>
          simpa [checkpointBefore,checkpointAfter,withLeft,withRight,GapBST.gaps,
            GapBST.lastKey,oldLast,incomingLast,lowerBoundary,upperBoundary,
            ClassicalSwitch.Boundary.count,ClassicalSwitch.Boundary.reflect,ClassicalSwitch.word,
            ClassicalSwitch.leftWord,Auxiliary.mirror,Auxiliary.inorder_mirror] using
            (noUpper_checkpoints (Auxiliary.mirror (GapBST.gaps suffix))
              (Auxiliary.mirror (GapBST.gaps old)) (Auxiliary.mirror (GapBST.gaps incoming)) upper pivot).mirror
  | some front =>
      cases suffix with
      | none =>
          simpa [checkpointBefore,checkpointAfter,withLeft,withRight,GapBST.gaps,
            GapBST.lastKey,oldLast,incomingLast,lowerBoundary,upperBoundary,
            ClassicalSwitch.Boundary.count,ClassicalSwitch.Boundary.reflect,ClassicalSwitch.word,
            ClassicalSwitch.leftWord,Auxiliary.mirror,Auxiliary.inorder_mirror] using
            (noLower_checkpoints (Auxiliary.mirror (GapBST.gaps old))
              (Auxiliary.mirror (GapBST.gaps incoming)) (Auxiliary.mirror (GapBST.gaps front)) pivot
              (GapBST.lastKey front)).mirror
      | some suffix =>
          simpa [checkpointBefore,checkpointAfter,withLeft,withRight,GapBST.gaps,
            GapBST.lastKey,oldLast,incomingLast,lowerBoundary,upperBoundary,
            ClassicalSwitch.Boundary.count,ClassicalSwitch.Boundary.reflect,ClassicalSwitch.word,
            ClassicalSwitch.leftWord,Auxiliary.mirror,Auxiliary.inorder_mirror] using
            (leftToRight_checkpoints (Auxiliary.mirror (GapBST.gaps suffix))
              (Auxiliary.mirror (GapBST.gaps old)) (Auxiliary.mirror (GapBST.gaps incoming))
              (Auxiliary.mirror (GapBST.gaps front)) upper pivot (GapBST.lastKey front)).mirror

theorem right_block_service (prefixLeft prefixRight oldLeft oldRight incomingLeft incomingRight : Block α)
    (oldTerminal incomingTerminal pivot upper : α)
    (oldLast : GapBST.lastKey (componentBlock oldLeft oldRight oldTerminal) = upper)
    (incomingLast : GapBST.lastKey (componentBlock incomingLeft incomingRight incomingTerminal) = pivot) :
    ∃ work ≤ 294,
      Program [GapBST.gaps (rightSource prefixLeft prefixRight oldLeft oldRight oldTerminal pivot),
          GapBST.gaps (componentBlock incomingLeft incomingRight incomingTerminal)]
        (ClassicalSwitch.word true (lowerBoundary prefixLeft) (upperBoundary upper prefixRight)
          (GapBST.gaps (componentBlock oldLeft oldRight oldTerminal)).inorder
          (GapBST.gaps (componentBlock incomingLeft incomingRight incomingTerminal)).inorder pivot)
        [GapBST.gaps (leftSource prefixLeft prefixRight incomingLeft incomingRight incomingTerminal upper),
          GapBST.gaps (componentBlock oldLeft oldRight oldTerminal)] work := by
  obtain ⟨first,firstBound,prepare⟩ := ComparatorGap.rearranges_program
    (rightSource_prepare prefixLeft prefixRight oldLeft oldRight oldTerminal pivot)
  obtain ⟨last,lastBound,restore⟩ := ComparatorGap.rearranges_program
    (leftSource_prepare prefixLeft prefixRight incomingLeft incomingRight incomingTerminal upper).symm
  have middle := right_block_checkpoints prefixLeft prefixRight
    (componentBlock oldLeft oldRight oldTerminal) (componentBlock incomingLeft incomingRight incomingTerminal)
    pivot upper oldLast incomingLast
  have lowerCount := (lowerBoundary prefixLeft).count_le_one
  have upperCount := (upperBoundary upper prefixRight).count_le_one
  refine ⟨first+(2+2*(lowerBoundary prefixLeft).count+2*(upperBoundary upper prefixRight).count)+last,
    by omega,?_⟩
  simpa using ((prepare.context [] [GapBST.gaps (componentBlock incomingLeft incomingRight incomingTerminal)]).append
    middle).append (restore.context [] [GapBST.gaps (componentBlock oldLeft oldRight oldTerminal)])

end MultiSplay.ComparatorGuard
