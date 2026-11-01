import Splay.Accounting.SplayPairingTranscript
import Splay.Lazy.NormalFormSchedule

namespace Splay.Tree.BST

namespace Zig

/-- A final zig is a partial function of its key and input tree. -/
theorem after_unique {key lower upper : ℕ}
    {before firstAfter secondAfter : BST lower upper}
    (first : Zig key before firstAfter)
    (second : Zig key before secondAfter) :
    firstAfter = secondAfter := by
  cases first with
  | fromLeft a b c =>
      cases second with
      | fromLeft _ _ _ =>
          rfl
      | fromRight d e f =>
          have bBounds := b.lower_le_upper
          have eBounds := e.lower_le_upper
          omega
  | fromRight a b c =>
      cases second with
      | fromLeft d e f =>
          have bBounds := b.lower_le_upper
          have eBounds := e.lower_le_upper
          omega
      | fromRight _ _ _ =>
          rfl

end Zig

namespace DoubleRotation

/-- A local standard double rotation is a partial function of key and input. -/
theorem after_unique {key lower upper : ℕ}
    {before firstAfter secondAfter : BST lower upper}
    (first : DoubleRotation key before firstAfter)
    (second : DoubleRotation key before secondAfter) :
    firstAfter = secondAfter := by
  cases first with
  | zigZigLeft a b c d =>
      cases second with
      | zigZigLeft _ _ _ _ =>
          rfl
      | zigZigRight e f g h =>
          have ha := a.lower_le_upper
          have hb := b.lower_le_upper
          have hc := c.lower_le_upper
          have hf := f.lower_le_upper
          have hg := g.lower_le_upper
          have hh := h.lower_le_upper
          omega
      | zigZagLeftRight e f g h =>
          have ha := a.lower_le_upper
          have hb := b.lower_le_upper
          have hf := f.lower_le_upper
          have hg := g.lower_le_upper
          omega
      | zigZagRightLeft e f g h =>
          have hb := b.lower_le_upper
          have hc := c.lower_le_upper
          have hf := f.lower_le_upper
          have hg := g.lower_le_upper
          have hh := h.lower_le_upper
          omega
  | zigZigRight a b c d =>
      cases second with
      | zigZigLeft e f g h =>
          have hb := b.lower_le_upper
          have hc := c.lower_le_upper
          have hd := d.lower_le_upper
          have he := e.lower_le_upper
          have hf := f.lower_le_upper
          have hg := g.lower_le_upper
          omega
      | zigZigRight _ _ _ _ =>
          rfl
      | zigZagLeftRight e f g h =>
          have hb := b.lower_le_upper
          have hc := c.lower_le_upper
          have he := e.lower_le_upper
          have hf := f.lower_le_upper
          have hg := g.lower_le_upper
          omega
      | zigZagRightLeft e f g h =>
          have ha := a.lower_le_upper
          have hc := c.lower_le_upper
          have hf := f.lower_le_upper
          have hg := g.lower_le_upper
          omega
  | zigZagLeftRight a b c d =>
      cases second with
      | zigZigLeft e f g h =>
          have hb := b.lower_le_upper
          have hc := c.lower_le_upper
          have he := e.lower_le_upper
          have hf := f.lower_le_upper
          omega
      | zigZigRight e f g h =>
          have hb := b.lower_le_upper
          have hc := c.lower_le_upper
          have hf := f.lower_le_upper
          have hg := g.lower_le_upper
          have hh := h.lower_le_upper
          omega
      | zigZagLeftRight _ _ _ _ =>
          rfl
      | zigZagRightLeft e f g h =>
          have ha := a.lower_le_upper
          have hb := b.lower_le_upper
          have hc := c.lower_le_upper
          have hf := f.lower_le_upper
          have hg := g.lower_le_upper
          have hh := h.lower_le_upper
          omega
  | zigZagRightLeft a b c d =>
      cases second with
      | zigZigLeft e f g h =>
          have hb := b.lower_le_upper
          have hc := c.lower_le_upper
          have hd := d.lower_le_upper
          have he := e.lower_le_upper
          have hf := f.lower_le_upper
          have hg := g.lower_le_upper
          omega
      | zigZigRight e f g h =>
          have ha := a.lower_le_upper
          have hb := b.lower_le_upper
          have hc := c.lower_le_upper
          have hg := g.lower_le_upper
          have hh := h.lower_le_upper
          omega
      | zigZagLeftRight e f g h =>
          have hb := b.lower_le_upper
          have hc := c.lower_le_upper
          have hd := d.lower_le_upper
          have he := e.lower_le_upper
          have hf := f.lower_le_upper
          have hg := g.lower_le_upper
          omega
      | zigZagRightLeft _ _ _ _ =>
          rfl

end DoubleRotation

namespace DoubleRotationAt

/--
A contextual double rotation is a partial function once its contextual depth,
key, and input tree are fixed.
-/
theorem after_unique {depth key lower upper : ℕ}
    {before firstAfter secondAfter : BST lower upper}
    (first : DoubleRotationAt depth key before firstAfter)
    (second : DoubleRotationAt depth key before secondAfter) :
    firstAfter = secondAfter := by
  induction first with
  | root first =>
      cases second with
      | root second =>
          exact first.after_unique second
  | leftContext first right ih =>
      cases second with
      | leftContext second right =>
          exact congrArg (fun child => BST.node child right) (ih second)
      | rightContext left second =>
          have firstBounds := first.key_bounds
          have secondBounds := second.key_bounds
          omega
  | rightContext left first ih =>
      cases second with
      | rightContext left second =>
          exact congrArg (fun child => BST.node left child) (ih second)
      | leftContext second right =>
          have firstBounds := first.key_bounds
          have secondBounds := second.key_bounds
          omega

/-- The contextual depth is determined by the key and input tree. -/
theorem depth_unique
    {firstDepth secondDepth key lower upper : ℕ}
    {before firstAfter secondAfter : BST lower upper}
    (first :
      DoubleRotationAt firstDepth key before firstAfter)
    (second :
      DoubleRotationAt secondDepth key before secondAfter) :
    firstDepth = secondDepth := by
  have firstDepthEq := first.depth_before_eq
  have secondDepthEq := second.depth_before_eq
  omega

/--
Even when their contextual depths are existentially hidden, two double
rotations of the same key from the same input have the same output.
-/
theorem after_unique_any_depth
    {firstDepth secondDepth key lower upper : ℕ}
    {before firstAfter secondAfter : BST lower upper}
    (first :
      DoubleRotationAt firstDepth key before firstAfter)
    (second :
      DoubleRotationAt secondDepth key before secondAfter) :
    firstAfter = secondAfter := by
  have depthEq := first.depth_unique second
  subst secondDepth
  exact first.after_unique second

end DoubleRotationAt

namespace SplayStep

/-- A standard bottom-up splay step has a unique output tree. -/
theorem after_unique {key lower upper : ℕ}
    {before firstAfter secondAfter : BST lower upper}
    (first : SplayStep key before firstAfter)
    (second : SplayStep key before secondAfter) :
    firstAfter = secondAfter := by
  cases first with
  | zig first =>
      cases second with
      | zig second =>
          exact first.after_unique second
      | double second =>
          have firstDepth := first.depth_before_eq_one
          have secondDepth := second.depth_before_eq
          omega
  | double first =>
      cases second with
      | zig second =>
          have firstDepth := first.depth_before_eq
          have secondDepth := second.depth_before_eq_one
          omega
      | double second =>
          exact first.after_unique_any_depth second

end SplayStep

namespace SplayExecution

/--
The final tree of a complete standard splay execution depends only on its
input tree and accessed key, not on the proof chosen by classical existence.
-/
theorem after_unique {key lower upper : ℕ}
    {before firstAfter secondAfter : BST lower upper}
    (first : SplayExecution key before firstAfter)
    (second : SplayExecution key before secondAfter) :
    firstAfter = secondAfter := by
  induction first generalizing secondAfter with
  | done firstRoot =>
      cases second with
      | done _ =>
          rfl
      | next head tail =>
          have beforeDepthZero :=
            depth_eq_zero_of_hasRoot firstRoot
          have decreases := head.depth_after_lt_before
          omega
  | next firstHead firstTail ih =>
      cases second with
      | done secondRoot =>
          have beforeDepthZero :=
            depth_eq_zero_of_hasRoot secondRoot
          have decreases := firstHead.depth_after_lt_before
          omega
      | next secondHead secondTail =>
          have middleEq := firstHead.after_unique secondHead
          subst middleEq
          exact ih secondTail

end SplayExecution

namespace SplaySequence

/--
The final tree of a standard splay sequence is independent of all proof
choices in the individual executions.
-/
theorem after_unique {n : ℕ} {accesses : List (Fin n)}
    {before firstAfter secondAfter : BST 0 n}
    (first : SplaySequence accesses before firstAfter)
    (second : SplaySequence accesses before secondAfter) :
    firstAfter = secondAfter := by
  induction first generalizing secondAfter with
  | done tree =>
      cases second
      rfl
  | next firstHead firstTail ih =>
      cases second with
      | next secondHead secondTail =>
          have middleEq := firstHead.after_unique secondHead
          subst middleEq
          exact ih secondTail

/-- Concatenate two dependent standard splay sequences. -/
def append {n : ℕ}
    {firstAccesses secondAccesses : List (Fin n)}
    {before middle after : BST 0 n}
    (first : SplaySequence firstAccesses before middle)
    (second : SplaySequence secondAccesses middle after) :
    SplaySequence (firstAccesses ++ secondAccesses) before after :=
  match first with
  | .done _ => second
  | .next head tail => .next head (tail.append second)

/--
All intermediate pre-access depths, and not just the final tree, are
proof-independent.
-/
theorem preAccessDepths_unique
    {n : ℕ} {accesses : List (Fin n)}
    {before firstAfter secondAfter : BST 0 n}
    (first : SplaySequence accesses before firstAfter)
    (second : SplaySequence accesses before secondAfter) :
    first.preAccessDepths = second.preAccessDepths := by
  induction first generalizing secondAfter with
  | done tree =>
      cases second
      rfl
  | next firstHead firstTail ih =>
      cases second with
      | next secondHead secondTail =>
          have middleEq := firstHead.after_unique secondHead
          subst middleEq
          simp only [preAccessDepths_next, List.cons.injEq, true_and]
          exact ih secondTail

/-- The exact ordinary-rotation cost of a request list is proof-independent. -/
theorem rotationCount_unique
    {n : ℕ} {accesses : List (Fin n)}
    {before firstAfter secondAfter : BST 0 n}
    (first : SplaySequence accesses before firstAfter)
    (second : SplaySequence accesses before secondAfter) :
    first.rotationCount = second.rotationCount := by
  exact congrArg List.sum (first.preAccessDepths_unique second)

/-- Any standard sequence reaches the concrete cost model's chosen final tree. -/
theorem after_eq_chosen
    {n : ℕ} {accesses : List (Fin n)}
    {initial final : BST 0 n}
    (sequence : SplaySequence accesses initial final) :
    final =
      (Splay.Accounting.chosenSplaySequenceWitness
        initial accesses).1 :=
  sequence.after_unique
    (Splay.Accounting.chosenSplaySequence initial accesses)

/--
Any standard sequence has exactly the ordinary-rotation count used by the
concrete cost model's classically chosen sequence.
-/
theorem rotationCount_eq_chosen
    {n : ℕ} {accesses : List (Fin n)}
    {initial final : BST 0 n}
    (sequence : SplaySequence accesses initial final) :
    sequence.rotationCount =
      (Splay.Accounting.chosenSplaySequence
        initial accesses).rotationCount :=
  sequence.rotationCount_unique
    (Splay.Accounting.chosenSplaySequence initial accesses)

end SplaySequence

end Splay.Tree.BST

namespace Splay.Accounting

open Splay.Tree.BST

/--
The orientation flag of a double step is already fixed by its key and input
tree; neither the hidden contextual depth nor the proof-selected output can
change it.
-/
theorem doubleOrientationAt_flag_unique_of_same_before
    {firstFlag secondFlag : Bool}
    {firstDepth secondDepth key lower upper : ℕ}
    {before firstAfter secondAfter : BST lower upper}
    (firstStep :
      DoubleRotationAt firstDepth key before firstAfter)
    (firstOrientation :
      DoubleOrientationAt firstFlag
        (depth := firstDepth) (key := key) before firstAfter)
    (secondStep :
      DoubleRotationAt secondDepth key before secondAfter)
    (secondOrientation :
      DoubleOrientationAt secondFlag
        (depth := secondDepth) (key := key) before secondAfter) :
    firstFlag = secondFlag := by
  have depthEq := firstStep.depth_unique secondStep
  subst secondDepth
  have afterEq := firstStep.after_unique secondStep
  subst secondAfter
  exact doubleOrientationAt_flag_unique
    firstOrientation secondOrientation

namespace SplayExecutionTranscript

/--
The chronological orientation list of one access is independent of both the
`SplayExecution` proof and the transcript-existence witness.
-/
theorem kinds_unique
    {key lower upper : ℕ}
    {before firstAfter secondAfter : BST lower upper}
    {firstExecution : SplayExecution key before firstAfter}
    {secondExecution : SplayExecution key before secondAfter}
    {firstKinds secondKinds : List SplayStepKind}
    {firstZig firstZigZig firstZigZag : ℕ}
    {secondZig secondZigZig secondZigZag : ℕ}
    (first :
      SplayExecutionTranscript key firstExecution firstKinds
        firstZig firstZigZig firstZigZag)
    (second :
      SplayExecutionTranscript key secondExecution secondKinds
        secondZig secondZigZig secondZigZag) :
    firstKinds = secondKinds := by
  induction first generalizing
      secondKinds secondZig secondZigZig secondZigZag with
  | done firstRoot =>
      cases second with
      | done _ =>
          rfl
      | zig head tail transcript =>
          have rootDepth := depth_eq_zero_of_hasRoot firstRoot
          have headDepth := head.depth_before_eq_one
          omega
      | zigZig head orientation tail transcript =>
          have rootDepth := depth_eq_zero_of_hasRoot firstRoot
          have headDepth := head.depth_before_eq
          omega
      | zigZag head orientation tail transcript =>
          have rootDepth := depth_eq_zero_of_hasRoot firstRoot
          have headDepth := head.depth_before_eq
          omega
  | zig firstHead firstTail firstTranscript ih =>
      cases second with
      | done secondRoot =>
          have rootDepth := depth_eq_zero_of_hasRoot secondRoot
          have headDepth := firstHead.depth_before_eq_one
          omega
      | zig secondHead secondTail secondTranscript =>
          have middleEq := firstHead.after_unique secondHead
          subst middleEq
          exact congrArg (SplayStepKind.zig :: ·)
            (ih secondTranscript)
      | zigZig secondHead orientation secondTail secondTranscript =>
          have firstDepth := firstHead.depth_before_eq_one
          have secondDepth := secondHead.depth_before_eq
          omega
      | zigZag secondHead orientation secondTail secondTranscript =>
          have firstDepth := firstHead.depth_before_eq_one
          have secondDepth := secondHead.depth_before_eq
          omega
  | zigZig firstHead firstOrientation firstTail firstTranscript ih =>
      cases second with
      | done secondRoot =>
          have rootDepth := depth_eq_zero_of_hasRoot secondRoot
          have headDepth := firstHead.depth_before_eq
          omega
      | zig secondHead secondTail secondTranscript =>
          have firstDepth := firstHead.depth_before_eq
          have secondDepth := secondHead.depth_before_eq_one
          omega
      | zigZig secondHead secondOrientation secondTail secondTranscript =>
          have middleEq :=
            firstHead.after_unique_any_depth secondHead
          subst middleEq
          exact congrArg (SplayStepKind.zigZig :: ·)
            (ih secondTranscript)
      | zigZag secondHead secondOrientation secondTail secondTranscript =>
          have flagEq :=
            doubleOrientationAt_flag_unique_of_same_before
              firstHead firstOrientation secondHead secondOrientation
          cases flagEq
  | zigZag firstHead firstOrientation firstTail firstTranscript ih =>
      cases second with
      | done secondRoot =>
          have rootDepth := depth_eq_zero_of_hasRoot secondRoot
          have headDepth := firstHead.depth_before_eq
          omega
      | zig secondHead secondTail secondTranscript =>
          have firstDepth := firstHead.depth_before_eq
          have secondDepth := secondHead.depth_before_eq_one
          omega
      | zigZig secondHead secondOrientation secondTail secondTranscript =>
          have flagEq :=
            doubleOrientationAt_flag_unique_of_same_before
              firstHead firstOrientation secondHead secondOrientation
          cases flagEq
      | zigZag secondHead secondOrientation secondTail secondTranscript =>
          have middleEq :=
            firstHead.after_unique_any_depth secondHead
          subst middleEq
          exact congrArg (SplayStepKind.zigZag :: ·)
            (ih secondTranscript)

/-- Consequently all three orientation counts of one access are unique. -/
theorem counts_unique
    {key lower upper : ℕ}
    {before firstAfter secondAfter : BST lower upper}
    {firstExecution : SplayExecution key before firstAfter}
    {secondExecution : SplayExecution key before secondAfter}
    {firstKinds secondKinds : List SplayStepKind}
    {firstZig firstZigZig firstZigZag : ℕ}
    {secondZig secondZigZig secondZigZag : ℕ}
    (first :
      SplayExecutionTranscript key firstExecution firstKinds
        firstZig firstZigZig firstZigZag)
    (second :
      SplayExecutionTranscript key secondExecution secondKinds
        secondZig secondZigZig secondZigZag) :
    firstZig = secondZig ∧
      firstZigZig = secondZigZig ∧
      firstZigZag = secondZigZag := by
  have kindsEq := first.kinds_unique second
  have zigEq : firstZig = secondZig := by
    rw [← first.count_zig, ← second.count_zig, kindsEq]
  have zigZigEq : firstZigZig = secondZigZig := by
    rw [← first.count_zigZig, ← second.count_zigZig, kindsEq]
  have zigZagEq : firstZigZag = secondZigZag := by
    rw [← first.count_zigZag, ← second.count_zigZag, kindsEq]
  exact ⟨zigEq, zigZigEq, zigZagEq⟩

end SplayExecutionTranscript

namespace SplaySequenceTranscript

/--
The complete chronological orientation list is independent of how the
dependent access sequence and its transcript witnesses were chosen.
-/
theorem kinds_unique
    {n : ℕ} {accesses : List (Fin n)}
    {before firstAfter secondAfter : BST 0 n}
    {firstSequence :
      SplaySequence accesses before firstAfter}
    {secondSequence :
      SplaySequence accesses before secondAfter}
    {firstKinds secondKinds : List SplayStepKind}
    {firstZig firstZigZig firstZigZag : ℕ}
    {secondZig secondZigZig secondZigZag : ℕ}
    (first :
      SplaySequenceTranscript firstSequence firstKinds
        firstZig firstZigZig firstZigZag)
    (second :
      SplaySequenceTranscript secondSequence secondKinds
        secondZig secondZigZig secondZigZag) :
    firstKinds = secondKinds := by
  induction first generalizing
      secondKinds secondZig secondZigZig secondZigZag with
  | done tree =>
      cases second
      rfl
  | next firstHead firstTail firstHeadTranscript
      firstTailTranscript ih =>
      cases second with
      | next secondHead secondTail secondHeadTranscript
          secondTailTranscript =>
          have middleEq := firstHead.after_unique secondHead
          subst middleEq
          have headKindsEq :=
            firstHeadTranscript.kinds_unique secondHeadTranscript
          have tailKindsEq := ih secondTailTranscript
          exact congrArg₂ List.append headKindsEq tailKindsEq

/-- All three accumulated orientation counts of an access sequence are unique. -/
theorem counts_unique
    {n : ℕ} {accesses : List (Fin n)}
    {before firstAfter secondAfter : BST 0 n}
    {firstSequence :
      SplaySequence accesses before firstAfter}
    {secondSequence :
      SplaySequence accesses before secondAfter}
    {firstKinds secondKinds : List SplayStepKind}
    {firstZig firstZigZig firstZigZag : ℕ}
    {secondZig secondZigZig secondZigZag : ℕ}
    (first :
      SplaySequenceTranscript firstSequence firstKinds
        firstZig firstZigZig firstZigZag)
    (second :
      SplaySequenceTranscript secondSequence secondKinds
        secondZig secondZigZig secondZigZag) :
    firstZig = secondZig ∧
      firstZigZig = secondZigZig ∧
      firstZigZag = secondZigZag := by
  have kindsEq := first.kinds_unique second
  have zigEq : firstZig = secondZig := by
    rw [← first.count_zig, ← second.count_zig, kindsEq]
  have zigZigEq : firstZigZig = secondZigZig := by
    rw [← first.count_zigZig, ← second.count_zigZig, kindsEq]
  have zigZagEq : firstZigZag = secondZigZag := by
    rw [← first.count_zigZag, ← second.count_zigZag, kindsEq]
  exact ⟨zigEq, zigZigEq, zigZagEq⟩

/--
Every transcript of a standard sequence agrees field-for-field with the
concrete cost model's chosen transcript, even when its sequence proof and
final tree were chosen independently.
-/
theorem eq_concrete
    {n : ℕ} {accesses : List (Fin n)}
    {initial final : BST 0 n}
    {sequence : SplaySequence accesses initial final}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag) :
    kinds = (concreteSplayTranscript initial accesses).kinds ∧
      zig = (concreteSplayTranscript initial accesses).zig ∧
      zigZig = (concreteSplayTranscript initial accesses).zigZig ∧
      zigZag = (concreteSplayTranscript initial accesses).zigZag := by
  let concrete := concreteSplayTranscript initial accesses
  have kindsEq := transcript.kinds_unique concrete.transcript
  have countsEq := transcript.counts_unique concrete.transcript
  exact
    ⟨kindsEq, countsEq.1, countsEq.2.1, countsEq.2.2⟩

end SplaySequenceTranscript

end Splay.Accounting

namespace Splay.Assumptions.NormalForm.ComparisonTrace.Schedule

open Splay.Tree.BST

abbrev BST := Splay.Tree.BST

/--
Forget comparison-rotation bookkeeping and concatenate all grouped splay
accesses into one genuine dependent `SplaySequence`.
-/
def toSplaySequence
    {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : BST 0 n}
    (schedule : Schedule trace groups time before after) :
    SplaySequence schedule.servedRequests before after :=
  match schedule with
  | .finish tree _ =>
      .done tree
  | .next _ _ splay tail =>
      splay.append tail.toSplaySequence

/-- Reindex the concatenated sequence by an externally proved request list. -/
def toSplaySequenceFor
    {n : ℕ} {accesses requested : List (Fin n)}
    {trace : ComparisonTrace n accesses}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : BST 0 n}
    (schedule : Schedule trace groups time before after)
    (requestsEq : schedule.servedRequests = requested) :
    SplaySequence requested before after :=
  requestsEq ▸ schedule.toSplaySequence

/--
Every normal-form schedule with the advertised request list reaches the same
tree as `chosenSplaySequence`.
-/
theorem final_eq_chosen
    {n : ℕ} {accesses requested : List (Fin n)}
    {trace : ComparisonTrace n accesses}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : BST 0 n}
    (schedule : Schedule trace groups time before after)
    (requestsEq : schedule.servedRequests = requested) :
    after =
      (Splay.Accounting.chosenSplaySequenceWitness
        before requested).1 :=
  (schedule.toSplaySequenceFor requestsEq).after_eq_chosen

/--
The schedule's concatenated standard splay cost equals the concrete chosen
sequence's cost exactly.
-/
theorem rotationCount_eq_chosen
    {n : ℕ} {accesses requested : List (Fin n)}
    {trace : ComparisonTrace n accesses}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : BST 0 n}
    (schedule : Schedule trace groups time before after)
    (requestsEq : schedule.servedRequests = requested) :
    (schedule.toSplaySequenceFor requestsEq).rotationCount =
      (Splay.Accounting.chosenSplaySequence
        before requested).rotationCount :=
  (schedule.toSplaySequenceFor requestsEq).rotationCount_eq_chosen

/--
Every orientation transcript extracted from the schedule's concatenated
sequence agrees exactly with `concreteSplayTranscript`.
-/
theorem transcript_eq_concrete
    {n : ℕ} {accesses requested : List (Fin n)}
    {trace : ComparisonTrace n accesses}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : BST 0 n}
    (schedule : Schedule trace groups time before after)
    (requestsEq : schedule.servedRequests = requested)
    {kinds : List Splay.Accounting.SplayStepKind}
    {zig zigZig zigZag : ℕ}
    (transcript :
      Splay.Accounting.SplaySequenceTranscript
        (schedule.toSplaySequenceFor requestsEq)
        kinds zig zigZig zigZag) :
    kinds =
        (Splay.Accounting.concreteSplayTranscript
          before requested).kinds ∧
      zig =
        (Splay.Accounting.concreteSplayTranscript
          before requested).zig ∧
      zigZig =
        (Splay.Accounting.concreteSplayTranscript
          before requested).zigZig ∧
      zigZag =
        (Splay.Accounting.concreteSplayTranscript
          before requested).zigZag :=
  transcript.eq_concrete

end Splay.Assumptions.NormalForm.ComparisonTrace.Schedule
