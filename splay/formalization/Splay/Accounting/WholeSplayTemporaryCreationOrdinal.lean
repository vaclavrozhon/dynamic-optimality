import Splay.Accounting.SplayDeterminism
import Splay.Accounting.WholeSplayTemporaryCreationGeometry

namespace Splay.Accounting.WholeSplayTemporaryCreationOrdinal

open Splay.Tree.BST
open Splay.Accounting.WholeSplayTemporaryCoreGeometry
open Splay.Accounting.WholeSplayTemporaryCreationGeometry

namespace ZigZigOrdinalAt

/--
One zig-zig ordinal in a fixed transcript determines a unique pair of local
endpoint trees and a unique contextual depth.

This is deliberately stated separately from the proof term witnessing the
occurrence: proof irrelevance already identifies those once their indices
have been identified.
-/
theorem source_unique
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {ordinal : ℕ}
    {firstBefore firstAfter secondBefore secondAfter : BST lower upper}
    {firstDepth secondDepth : ℕ}
    (first :
      WholeSplayTemporaryCreationGeometry.ZigZigOrdinalAt
        transcript ordinal firstBefore firstAfter firstDepth)
    (second :
      WholeSplayTemporaryCreationGeometry.ZigZigOrdinalAt
        transcript ordinal secondBefore secondAfter secondDepth) :
    firstBefore = secondBefore ∧
      firstAfter = secondAfter ∧ firstDepth = secondDepth := by
  induction first generalizing secondBefore secondAfter secondDepth with
  | here firstStep =>
      cases second with
      | here secondStep =>
          have afterEq :=
            firstStep.after_unique_any_depth secondStep
          cases afterEq
          have firstDepthEq := firstStep.depth_before_eq
          have secondDepthEq := secondStep.depth_before_eq
          exact ⟨rfl, rfl, by omega⟩
  | afterZig head tail tailTranscript firstOccurrence ih =>
      cases second with
      | afterZig secondHead secondTail secondTailTranscript
          secondOccurrence =>
          have middleEq := head.after_unique secondHead
          cases middleEq
          have tailEq : secondTail = tail := Subsingleton.elim _ _
          subst secondTail
          have transcriptEq :
              secondTailTranscript = tailTranscript :=
            Subsingleton.elim _ _
          subst secondTailTranscript
          exact ih secondOccurrence
  | afterZigZig head orientation tail tailTranscript firstOccurrence ih =>
      cases second with
      | afterZigZig secondHead secondOrientation secondTail
          secondTailTranscript secondOccurrence =>
          have middleEq :=
            head.after_unique_any_depth secondHead
          cases middleEq
          have tailEq : secondTail = tail := Subsingleton.elim _ _
          subst secondTail
          have transcriptEq :
              secondTailTranscript = tailTranscript :=
            Subsingleton.elim _ _
          subst secondTailTranscript
          exact ih secondOccurrence
  | afterZigZag head orientation tail tailTranscript firstOccurrence ih =>
      cases second with
      | afterZigZag secondHead secondOrientation secondTail
          secondTailTranscript secondOccurrence =>
          have middleEq :=
            head.after_unique_any_depth secondHead
          cases middleEq
          have tailEq : secondTail = tail := Subsingleton.elim _ _
          subst secondTail
          have transcriptEq :
              secondTailTranscript = tailTranscript :=
            Subsingleton.elim _ _
          subst secondTailTranscript
          exact ih secondOccurrence

end ZigZigOrdinalAt

end Splay.Accounting.WholeSplayTemporaryCreationOrdinal
