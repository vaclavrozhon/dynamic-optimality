import Splay.Accounting.SplayDeterminism

namespace Splay.Accounting

open Splay.Tree.BST

namespace SplayExecutionTranscript

/--
An actual zig-zig at one exact chronological position of a classified splay
execution.

The relation is indexed by the supplied transcript proof.  Its endpoints are
therefore the endpoints of the concrete `DoubleRotationAt` stored at that
position, rather than trees reconstructed from the list of step kinds.
-/
inductive ZigZigAt {key lower upper : ℕ} :
    {before after : BST lower upper} →
      {execution : SplayExecution key before after} →
        {kinds : List SplayStepKind} → {zig zigZig zigZag : ℕ} →
          SplayExecutionTranscript key execution kinds zig zigZig zigZag →
            ℕ → BST lower upper → BST lower upper → ℕ → Prop
  | here {before middle after : BST lower upper}
      {kinds : List SplayStepKind} {zig zigZig zigZag depth : ℕ}
      (step : DoubleRotationAt depth key before middle)
      (orientation :
        DoubleOrientationAt true
          (depth := depth) (key := key) before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag) :
      ZigZigAt
        (.zigZig step orientation tail tailTranscript)
        0 before middle depth
  | afterZig {before middle after : BST lower upper}
      {kinds : List SplayStepKind} {zig zigZig zigZag index depth : ℕ}
      (head : Zig key before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag)
      {stepBefore stepAfter : BST lower upper}
      (occurrence :
        ZigZigAt tailTranscript index stepBefore stepAfter depth) :
      ZigZigAt
        (.zig head tail tailTranscript)
        index.succ stepBefore stepAfter depth
  | afterZigZig {before middle after : BST lower upper}
      {kinds : List SplayStepKind} {zig zigZig zigZag index depth : ℕ}
      {headDepth : ℕ}
      (head : DoubleRotationAt headDepth key before middle)
      (orientation :
        DoubleOrientationAt true
          (depth := headDepth) (key := key) before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag)
      {stepBefore stepAfter : BST lower upper}
      (occurrence :
        ZigZigAt tailTranscript index stepBefore stepAfter depth) :
      ZigZigAt
        (.zigZig head orientation tail tailTranscript)
        index.succ stepBefore stepAfter depth
  | afterZigZag {before middle after : BST lower upper}
      {kinds : List SplayStepKind} {zig zigZig zigZag index depth : ℕ}
      {headDepth : ℕ}
      (head : DoubleRotationAt headDepth key before middle)
      (orientation :
        DoubleOrientationAt false
          (depth := headDepth) (key := key) before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag)
      {stepBefore stepAfter : BST lower upper}
      (occurrence :
        ZigZigAt tailTranscript index stepBefore stepAfter depth) :
      ZigZigAt
        (.zigZag head orientation tail tailTranscript)
        index.succ stepBefore stepAfter depth

namespace ZigZigAt

/-- The occurrence carries the concrete double rotation and its orientation. -/
theorem geometry
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {index depth : ℕ} {stepBefore stepAfter : BST lower upper}
    (occurrence :
      ZigZigAt transcript index stepBefore stepAfter depth) :
    DoubleRotationAt depth key stepBefore stepAfter ∧
      DoubleOrientationAt true
        (depth := depth) (key := key) stepBefore stepAfter := by
  induction occurrence with
  | here step orientation =>
      exact ⟨step, orientation⟩
  | afterZig _ _ _ _ ih =>
      exact ih
  | afterZigZig _ _ _ _ _ ih =>
      exact ih
  | afterZigZag _ _ _ _ _ ih =>
      exact ih

/-- The selected chronological position lies inside the local kind list. -/
theorem index_lt
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {index depth : ℕ} {stepBefore stepAfter : BST lower upper}
    (occurrence :
      ZigZigAt transcript index stepBefore stepAfter depth) :
    index < kinds.length := by
  induction occurrence <;> simp_all

/-- The selected kind is definitionally a genuine zig-zig. -/
theorem kind_eq
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {index depth : ℕ} {stepBefore stepAfter : BST lower upper}
    (occurrence :
      ZigZigAt transcript index stepBefore stepAfter depth) :
    kinds.get ⟨index, occurrence.index_lt⟩ = .zigZig := by
  induction occurrence with
  | here =>
      rfl
  | afterZig _ _ _ occurrence ih =>
      exact ih
  | afterZigZig _ _ _ _ occurrence ih =>
      exact ih
  | afterZigZag _ _ _ _ occurrence ih =>
      exact ih

/--
For a fixed transcript and local step number, the concrete endpoints and
contextual depth of the selected zig-zig are unique.
-/
theorem geometry_unique
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {index : ℕ}
    {firstBefore firstAfter secondBefore secondAfter : BST lower upper}
    {firstDepth secondDepth : ℕ}
    (first :
      ZigZigAt transcript index firstBefore firstAfter firstDepth)
    (second :
      ZigZigAt transcript index secondBefore secondAfter secondDepth) :
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

end ZigZigAt

/--
Every local transcript position whose kind is `zigZig` exposes the concrete
double rotation and its true orientation.
-/
theorem exists_zigZigAt_of_get
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (index : Fin kinds.length)
    (kind_eq : kinds.get index = .zigZig) :
    ∃ stepBefore stepAfter depth,
      ZigZigAt transcript index.val stepBefore stepAfter depth := by
  induction transcript with
  | done root =>
      exact Fin.elim0 index
  | zig head tail tailTranscript ih =>
      rcases index with ⟨position, inBounds⟩
      cases position with
      | zero =>
          contradiction
      | succ position =>
          have tailBounds := inBounds
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at tailBounds
          obtain ⟨stepBefore, stepAfter, depth, occurrence⟩ :=
            ih ⟨position, tailBounds⟩ kind_eq
          exact
            ⟨stepBefore, stepAfter, depth,
              .afterZig head tail tailTranscript occurrence⟩
  | zigZig head orientation tail tailTranscript ih =>
      rcases index with ⟨position, inBounds⟩
      cases position with
      | zero =>
          exact
            ⟨_, _, _, .here head orientation tail tailTranscript⟩
      | succ position =>
          have tailBounds := inBounds
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at tailBounds
          obtain ⟨stepBefore, stepAfter, depth, occurrence⟩ :=
            ih ⟨position, tailBounds⟩ kind_eq
          exact
            ⟨stepBefore, stepAfter, depth,
              .afterZigZig head orientation tail tailTranscript occurrence⟩
  | zigZag head orientation tail tailTranscript ih =>
      rcases index with ⟨position, inBounds⟩
      cases position with
      | zero =>
          contradiction
      | succ position =>
          have tailBounds := inBounds
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at tailBounds
          obtain ⟨stepBefore, stepAfter, depth, occurrence⟩ :=
            ih ⟨position, tailBounds⟩ kind_eq
          exact
            ⟨stepBefore, stepAfter, depth,
              .afterZigZag head orientation tail tailTranscript occurrence⟩

end SplayExecutionTranscript

namespace SplaySequenceTranscript

/--
An actual zig-zig at a global chronological step of a dependent splay
sequence.

Besides the global transcript position, this relation records the exact
request number, accessed key, request endpoints, local step number, local
double-rotation endpoints, and contextual depth.
-/
inductive ZigZigAt {n : ℕ} :
    {accesses : List (Fin n)} → {before after : BST 0 n} →
      {sequence : SplaySequence accesses before after} →
        {kinds : List SplayStepKind} → {zig zigZig zigZag : ℕ} →
          SplaySequenceTranscript sequence kinds zig zigZig zigZag →
            ℕ → ℕ → Fin n → BST 0 n → BST 0 n → ℕ →
              BST 0 n → BST 0 n → ℕ → Prop
  | head {access : Fin n} {accesses : List (Fin n)}
      {before middle after : BST 0 n}
      {headKinds tailKinds : List SplayStepKind}
      {headZig headZigZig headZigZag : ℕ}
      {tailZig tailZigZig tailZigZag : ℕ}
      (head : SplayExecution access.val before middle)
      (tail : SplaySequence accesses middle after)
      (headTranscript :
        SplayExecutionTranscript access.val head headKinds
          headZig headZigZig headZigZag)
      (tailTranscript :
        SplaySequenceTranscript tail tailKinds
          tailZig tailZigZig tailZigZag)
      {localIndex depth : ℕ} {stepBefore stepAfter : BST 0 n}
      (occurrence :
        SplayExecutionTranscript.ZigZigAt headTranscript localIndex
          stepBefore stepAfter depth) :
      ZigZigAt
        (.next head tail headTranscript tailTranscript)
        localIndex 0 access before middle localIndex
        stepBefore stepAfter depth
  | tail {access : Fin n} {accesses : List (Fin n)}
      {before middle after : BST 0 n}
      {headKinds tailKinds : List SplayStepKind}
      {headZig headZigZig headZigZag : ℕ}
      {tailZig tailZigZig tailZigZag : ℕ}
      (head : SplayExecution access.val before middle)
      (tail : SplaySequence accesses middle after)
      (headTranscript :
        SplayExecutionTranscript access.val head headKinds
          headZig headZigZig headZigZag)
      (tailTranscript :
        SplaySequenceTranscript tail tailKinds
          tailZig tailZigZig tailZigZag)
      {globalIndex requestIndex : ℕ} {selectedAccess : Fin n}
      {requestBefore requestAfter : BST 0 n}
      {localIndex depth : ℕ} {stepBefore stepAfter : BST 0 n}
      (occurrence :
        ZigZigAt tailTranscript globalIndex requestIndex selectedAccess
          requestBefore requestAfter localIndex
          stepBefore stepAfter depth) :
      ZigZigAt
        (.next head tail headTranscript tailTranscript)
        (headKinds.length + globalIndex) requestIndex.succ selectedAccess
        requestBefore requestAfter localIndex stepBefore stepAfter depth

namespace ZigZigAt

/-- A selected global zig-zig position lies inside the flattened kind list. -/
theorem globalIndex_lt
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {globalIndex requestIndex : ℕ} {access : Fin n}
    {requestBefore requestAfter : BST 0 n}
    {localIndex depth : ℕ} {stepBefore stepAfter : BST 0 n}
    (occurrence :
      ZigZigAt transcript globalIndex requestIndex access
        requestBefore requestAfter localIndex stepBefore stepAfter depth) :
    globalIndex < kinds.length := by
  induction occurrence with
  | head _ _ _ _ localOccurrence =>
      simp only [List.length_append]
      have localBound := localOccurrence.index_lt
      omega
  | tail _ _ _ _ nestedOccurrence ih =>
      simp only [List.length_append]
      omega

/-- The selected request number lies inside the access list. -/
theorem requestIndex_lt
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {globalIndex requestIndex : ℕ} {access : Fin n}
    {requestBefore requestAfter : BST 0 n}
    {localIndex depth : ℕ} {stepBefore stepAfter : BST 0 n}
    (occurrence :
      ZigZigAt transcript globalIndex requestIndex access
        requestBefore requestAfter localIndex stepBefore stepAfter depth) :
    requestIndex < accesses.length := by
  induction occurrence with
  | head =>
      simp
  | tail _ _ _ _ _ ih =>
      simpa only [List.length_cons, Nat.succ_lt_succ_iff] using ih

/-- The recovered key is exactly the key stored at the recovered request. -/
theorem access_eq_get
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {globalIndex requestIndex : ℕ} {access : Fin n}
    {requestBefore requestAfter : BST 0 n}
    {localIndex depth : ℕ} {stepBefore stepAfter : BST 0 n}
    (occurrence :
      ZigZigAt transcript globalIndex requestIndex access
        requestBefore requestAfter localIndex stepBefore stepAfter depth) :
    accesses.get ⟨requestIndex, occurrence.requestIndex_lt⟩ = access := by
  induction occurrence with
  | head =>
      rfl
  | tail _ _ _ _ occurrence ih =>
      exact ih

/-- The global occurrence exposes its concrete structural double rotation. -/
theorem geometry
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {globalIndex requestIndex : ℕ} {access : Fin n}
    {requestBefore requestAfter : BST 0 n}
    {localIndex depth : ℕ} {stepBefore stepAfter : BST 0 n}
    (occurrence :
      ZigZigAt transcript globalIndex requestIndex access
        requestBefore requestAfter localIndex stepBefore stepAfter depth) :
    DoubleRotationAt depth access.val stepBefore stepAfter ∧
      DoubleOrientationAt true
        (depth := depth) (key := access.val) stepBefore stepAfter := by
  induction occurrence with
  | head _ _ _ _ localOccurrence =>
      exact localOccurrence.geometry
  | tail _ _ _ _ nestedOccurrence ih =>
      exact ih

end ZigZigAt

/--
Every global kind-list position classified as `zigZig` exposes its exact
request and double-rotation geometry.
-/
theorem exists_zigZigAt_of_get
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    (index : Fin kinds.length)
    (kind_eq : kinds.get index = .zigZig) :
    ∃ requestIndex access requestBefore requestAfter localIndex
        stepBefore stepAfter depth,
      ZigZigAt transcript index.val requestIndex access
        requestBefore requestAfter localIndex stepBefore stepAfter depth := by
  induction transcript with
  | done tree =>
      exact Fin.elim0 index
  | @next access accesses before middle after
      headKinds tailKinds headZig headZigZig headZigZag
      tailZig tailZigZig tailZigZag head tail
      headTranscript tailTranscript ih =>
      by_cases inHead : index.val < headKinds.length
      · let localIndex : Fin headKinds.length :=
          ⟨index.val, inHead⟩
        have headKindEq :
            headKinds.get localIndex = .zigZig := by
          change headKinds[index.val] = .zigZig
          change (headKinds ++ tailKinds)[index.val] = .zigZig at kind_eq
          rw [List.getElem_append_left inHead] at kind_eq
          exact kind_eq
        obtain ⟨stepBefore, stepAfter, depth, occurrence⟩ :=
          headTranscript.exists_zigZigAt_of_get localIndex headKindEq
        exact
          ⟨0, access, before, middle, localIndex.val,
            stepBefore, stepAfter, depth,
            .head head tail headTranscript tailTranscript occurrence⟩
      · have tailBound :
            index.val - headKinds.length < tailKinds.length := by
          have totalBound :
              index.val < headKinds.length + tailKinds.length := by
            simpa only [List.length_append] using index.isLt
          omega
        let tailIndex : Fin tailKinds.length :=
          ⟨index.val - headKinds.length, tailBound⟩
        have globalEq :
            headKinds.length + tailIndex.val = index.val := by
          dsimp only [tailIndex]
          omega
        have tailKindEq :
            tailKinds.get tailIndex = .zigZig := by
          change tailKinds[index.val - headKinds.length] = .zigZig
          change (headKinds ++ tailKinds)[index.val] = .zigZig at kind_eq
          rw [List.getElem_append_right (by omega)] at kind_eq
          exact kind_eq
        obtain
          ⟨requestIndex, selectedAccess, requestBefore, requestAfter,
            localIndex, stepBefore, stepAfter, depth, occurrence⟩ :=
          ih tailIndex tailKindEq
        exact
          ⟨requestIndex.succ, selectedAccess, requestBefore, requestAfter,
            localIndex, stepBefore, stepAfter, depth, by
              rw [← globalEq]
              exact
                .tail head tail headTranscript tailTranscript occurrence⟩

end SplaySequenceTranscript

/--
The concrete chronological geometry selected by one abstract pairing slot.

`phase` is copied from the slot and retained alongside the structural
occurrence.  Both phases of a zig-zig consequently point to the same actual
double rotation while remaining distinct accounting occurrences.
-/
structure PairingSlotOccurrence
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    (slot : PairingSlot) where
  phase : PairingPhase
  phase_eq : phase = slot.phase
  requestIndex : ℕ
  access : Fin n
  requestBefore : BST 0 n
  requestAfter : BST 0 n
  localStepIndex : ℕ
  stepBefore : BST 0 n
  stepAfter : BST 0 n
  depth : ℕ
  step :
    DoubleRotationAt depth access.val stepBefore stepAfter
  orientation :
    DoubleOrientationAt true
      (depth := depth) (key := access.val) stepBefore stepAfter
  occurrence :
    SplaySequenceTranscript.ZigZigAt transcript slot.zigZigStep
      requestIndex access requestBefore requestAfter localStepIndex
      stepBefore stepAfter depth

namespace PairingSlotOccurrence

/-- The selected access is the request at the selected request number. -/
theorem access_eq_get
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {slot : PairingSlot}
    (occurrence : PairingSlotOccurrence transcript slot) :
    accesses.get
      ⟨occurrence.requestIndex, occurrence.occurrence.requestIndex_lt⟩ =
        occurrence.access :=
  occurrence.occurrence.access_eq_get

end PairingSlotOccurrence

private theorem zigZigStep_mem_of_pairingSlot_mem
    {kinds : List SplayStepKind} {slot : PairingSlot}
    (member : slot ∈ firstPairings kinds ++ secondPairings kinds) :
    slot.zigZigStep ∈ zigZigStepIndices kinds := by
  rw [List.mem_append] at member
  rcases member with firstMember | secondMember
  · obtain ⟨index, indexMember, slotEq⟩ :=
      List.mem_map.mp firstMember
    subst slot
    exact indexMember
  · obtain ⟨index, indexMember, slotEq⟩ :=
      List.mem_map.mp secondMember
    subst slot
    exact indexMember

/--
Every abstract pairing slot of an arbitrary concrete sequence transcript
selects an actual chronological zig-zig, including its request, exact
pre/post trees, contextual depth, `DoubleRotationAt`, true orientation, and
original phase tag.
-/
theorem exists_pairingSlotOccurrence
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    (slot : PairingSlot)
    (member : slot ∈ firstPairings kinds ++ secondPairings kinds) :
    Nonempty (PairingSlotOccurrence transcript slot) := by
  have indexMember :
      slot.zigZigStep ∈ kinds.findIdxs SplayStepKind.isZigZig :=
    zigZigStep_mem_of_pairingSlot_mem member
  obtain ⟨indexBound, isZigZig⟩ :=
    List.mem_findIdxs_iff_exists_getElem_pos.mp indexMember
  have kindEq :
      kinds.get ⟨slot.zigZigStep, indexBound⟩ = .zigZig := by
    have := isZigZig
    simp only [SplayStepKind.isZigZig] at this
    split at this <;> simp_all
  obtain
    ⟨requestIndex, access, requestBefore, requestAfter, localStepIndex,
      stepBefore, stepAfter, depth, occurrence⟩ :=
    transcript.exists_zigZigAt_of_get
      ⟨slot.zigZigStep, indexBound⟩ kindEq
  have geometry :
      DoubleRotationAt depth access.val stepBefore stepAfter ∧
        DoubleOrientationAt true
          (depth := depth) (key := access.val) stepBefore stepAfter := by
    exact occurrence.geometry
  exact
    ⟨{ phase := slot.phase
       phase_eq := rfl
       requestIndex := requestIndex
       access := access
       requestBefore := requestBefore
       requestAfter := requestAfter
       localStepIndex := localStepIndex
       stepBefore := stepBefore
       stepAfter := stepAfter
       depth := depth
       step := geometry.1
       orientation := geometry.2
       occurrence := occurrence }⟩

end Splay.Accounting
