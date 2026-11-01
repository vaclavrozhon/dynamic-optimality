import Splay.Accounting.ConcreteSplayCost

namespace Splay.Accounting

open Splay.Tree.BST

/--
The three kinds of steps that occur in a standard bottom-up splay.

Unlike the numerical decomposition alone, this list-valued transcript keeps
the chronological position of every genuine zig-zig.
-/
inductive SplayStepKind
  | zig
  | zigZig
  | zigZag
  deriving DecidableEq, Repr

namespace SplayStepKind

/-- Boolean predicate used to retain the positions of genuine zig-zigs. -/
def isZigZig : SplayStepKind → Bool
  | .zigZig => true
  | _ => false

@[simp] theorem isZigZig_zig : isZigZig .zig = false := rfl
@[simp] theorem isZigZig_zigZig : isZigZig .zigZig = true := rfl
@[simp] theorem isZigZig_zigZag : isZigZig .zigZag = false := rfl

end SplayStepKind

/-- An oriented contextual double rotation names a key in its BST interval. -/
theorem doubleOrientationAt_key_bounds
    {flag : Bool} {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (orientation :
      DoubleOrientationAt flag
        (depth := depth) (key := key) before after) :
    lower ≤ key ∧ key < upper := by
  induction orientation with
  | zigZigLeft a b c d =>
      have ha := a.lower_le_upper
      have hb := b.lower_le_upper
      have hc := c.lower_le_upper
      have hd := d.lower_le_upper
      omega
  | zigZigRight a b c d =>
      have ha := a.lower_le_upper
      have hb := b.lower_le_upper
      have hc := c.lower_le_upper
      have hd := d.lower_le_upper
      omega
  | zigZagLeftRight a b c d =>
      have ha := a.lower_le_upper
      have hb := b.lower_le_upper
      have hc := c.lower_le_upper
      have hd := d.lower_le_upper
      omega
  | zigZagRightLeft a b c d =>
      have ha := a.lower_le_upper
      have hb := b.lower_le_upper
      have hc := c.lower_le_upper
      have hd := d.lower_le_upper
      omega
  | leftContext orientation right ih =>
      have rightBounds := right.lower_le_upper
      omega
  | rightContext left orientation ih =>
      have leftBounds := left.lower_le_upper
      omega

/-- A concrete contextual double rotation has only one Boolean orientation. -/
theorem doubleOrientationAt_flag_unique
    {firstFlag secondFlag : Bool}
    {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (first :
      DoubleOrientationAt firstFlag
        (depth := depth) (key := key) before after)
    (second :
      DoubleOrientationAt secondFlag
        (depth := depth) (key := key) before after) :
    firstFlag = secondFlag := by
  induction first generalizing secondFlag with
  | zigZigLeft a b c d =>
      cases second
      rfl
  | zigZigRight a b c d =>
      cases second
      rfl
  | zigZagLeftRight a b c d =>
      cases second
      rfl
  | zigZagRightLeft a b c d =>
      cases second
      rfl
  | leftContext first right ih =>
      cases second with
      | leftContext second right =>
          exact ih second
      | rightContext left second =>
          have firstBounds := doubleOrientationAt_key_bounds first
          have secondBounds := doubleOrientationAt_key_bounds second
          omega
  | rightContext left first ih =>
      cases second with
      | rightContext left second =>
          exact ih second
      | leftContext second right =>
          have firstBounds := doubleOrientationAt_key_bounds first
          have secondBounds := doubleOrientationAt_key_bounds second
          omega

/--
Proof-relevant chronological classification of one concrete
`SplayExecution`.

The execution proof itself is an index.  Consequently the three counts below
cannot be exchanged merely because they happen to satisfy the same rotation
equation: every increment is justified by the actual local orientation of
the corresponding `DoubleRotationAt`.
-/
inductive SplayExecutionTranscript (key : ℕ) :
    {lower upper : ℕ} → {before after : BST lower upper} →
      SplayExecution key before after →
        List SplayStepKind → ℕ → ℕ → ℕ → Prop
  | done {lower upper : ℕ} {tree : BST lower upper}
      (root : tree.HasRoot key) :
      SplayExecutionTranscript key (.done root) [] 0 0 0
  | zig {lower upper : ℕ} {before middle after : BST lower upper}
      {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
      (step : Zig key before middle)
      (tail : SplayExecution key middle after)
      (transcript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag) :
      SplayExecutionTranscript key (.next (.zig step) tail)
        (.zig :: kinds) zig.succ zigZig zigZag
  | zigZig {depth lower upper : ℕ}
      {before middle after : BST lower upper}
      {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
      (step : DoubleRotationAt depth key before middle)
      (orientation :
        DoubleOrientationAt true
          (depth := depth) (key := key) before middle)
      (tail : SplayExecution key middle after)
      (transcript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag) :
      SplayExecutionTranscript key (.next (.double step) tail)
        (.zigZig :: kinds) zig zigZig.succ zigZag
  | zigZag {depth lower upper : ℕ}
      {before middle after : BST lower upper}
      {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
      (step : DoubleRotationAt depth key before middle)
      (orientation :
        DoubleOrientationAt false
          (depth := depth) (key := key) before middle)
      (tail : SplayExecution key middle after)
      (transcript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag) :
      SplayExecutionTranscript key (.next (.double step) tail)
        (.zigZag :: kinds) zig zigZig zigZag.succ

namespace SplayExecutionTranscript

/-- Every concrete execution has a chronologically classified transcript. -/
theorem exists_transcript
    {key lower upper : ℕ} {before after : BST lower upper}
    (execution : SplayExecution key before after) :
    ∃ kinds zig zigZig zigZag,
      SplayExecutionTranscript key execution kinds zig zigZig zigZag := by
  induction execution with
  | done root =>
      exact ⟨[], 0, 0, 0, .done root⟩
  | next head tail ih =>
      obtain ⟨kinds, zig, zigZig, zigZag, tailTranscript⟩ := ih
      cases head with
      | zig step =>
          exact
            ⟨.zig :: kinds, zig.succ, zigZig, zigZag,
              .zig step tail tailTranscript⟩
      | double step =>
          obtain ⟨isZigZig, orientation⟩ :=
            exists_doubleOrientationAt step
          cases isZigZig with
          | false =>
              exact
                ⟨.zigZag :: kinds, zig, zigZig, zigZag.succ,
                  .zigZag step orientation tail tailTranscript⟩
          | true =>
              exact
                ⟨.zigZig :: kinds, zig, zigZig.succ, zigZag,
                  .zigZig step orientation tail tailTranscript⟩

/--
Forgetting chronological positions recovers the existing exact orientation
count witness.
-/
theorem toExecutionCounts
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag) :
    SplayExecutionCounts key before after zig zigZig zigZag := by
  induction transcript with
  | done root =>
      exact .done root
  | zig step tail transcript ih =>
      simpa [Nat.succ_eq_add_one] using
        SplayExecutionCounts.zig step ih
  | zigZig step orientation tail transcript ih =>
      simpa [Nat.succ_eq_add_one] using
        SplayExecutionCounts.zigZig step orientation ih
  | zigZag step orientation tail transcript ih =>
      simpa [Nat.succ_eq_add_one] using
        SplayExecutionCounts.zigZag step orientation ih

/-- The transcript contains exactly the recorded number of ordinary zigs. -/
theorem count_zig
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag) :
    kinds.count .zig = zig := by
  induction transcript <;> simp_all

/-- The transcript contains exactly the recorded number of zig-zigs. -/
theorem count_zigZig
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag) :
    kinds.count .zigZig = zigZig := by
  induction transcript <;> simp_all

/-- The transcript contains exactly the recorded number of zig-zags. -/
theorem count_zigZag
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag) :
    kinds.count .zigZag = zigZag := by
  induction transcript <;> simp_all

/-- Every classified step belongs to exactly one of the three count classes. -/
theorem length_eq
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag) :
    kinds.length = zig + zigZig + zigZag := by
  induction transcript <;> simp_all <;> omega

end SplayExecutionTranscript

/-- A chosen transcript bundled with the proof that it describes `execution`. -/
structure SplayExecutionTranscriptWitness
    {key lower upper : ℕ} {before after : BST lower upper}
    (execution : SplayExecution key before after) where
  kinds : List SplayStepKind
  zig : ℕ
  zigZig : ℕ
  zigZag : ℕ
  transcript :
    SplayExecutionTranscript key execution kinds zig zigZig zigZag

/--
Canonical noncomputable extraction from the proof-valued execution API.

`SplayExecution` lives in `Prop`, so direct recursive elimination into a list
is not available.  The bundled transcript evidence keeps the result tied to
the supplied concrete execution.
-/
noncomputable def splayExecutionTranscriptWitness
    {key lower upper : ℕ} {before after : BST lower upper}
    (execution : SplayExecution key before after) :
    SplayExecutionTranscriptWitness execution := by
  let existence := SplayExecutionTranscript.exists_transcript execution
  exact
    { kinds := Classical.choose existence
      zig := Classical.choose (Classical.choose_spec existence)
      zigZig :=
        Classical.choose
          (Classical.choose_spec (Classical.choose_spec existence))
      zigZag :=
        Classical.choose
          (Classical.choose_spec
            (Classical.choose_spec (Classical.choose_spec existence)))
      transcript :=
        Classical.choose_spec
          (Classical.choose_spec
            (Classical.choose_spec
              (Classical.choose_spec existence))) }

/--
Chronological classification of a dependent sequence of real splay
executions.  Concatenation follows request order and preserves exact
orientation counts.
-/
inductive SplaySequenceTranscript {n : ℕ} :
    {accesses : List (Fin n)} → {before after : BST 0 n} →
      SplaySequence accesses before after →
        List SplayStepKind → ℕ → ℕ → ℕ → Prop
  | done (tree : BST 0 n) :
      SplaySequenceTranscript (.done tree) [] 0 0 0
  | next {access : Fin n} {accesses : List (Fin n)}
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
          tailZig tailZigZig tailZigZag) :
      SplaySequenceTranscript (.next head tail)
        (headKinds ++ tailKinds)
        (headZig + tailZig)
        (headZigZig + tailZigZig)
        (headZigZag + tailZigZag)

namespace SplaySequenceTranscript

/-- Every actual dependent splay sequence has an exact ordered transcript. -/
theorem exists_transcript
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    (sequence : SplaySequence accesses before after) :
    ∃ kinds zig zigZig zigZag,
      SplaySequenceTranscript sequence kinds zig zigZig zigZag := by
  induction sequence with
  | done tree =>
      exact ⟨[], 0, 0, 0, .done tree⟩
  | @next access accesses before middle after head tail ih =>
      obtain ⟨headKinds, headZig, headZigZig, headZigZag,
          headTranscript⟩ :=
        SplayExecutionTranscript.exists_transcript head
      obtain ⟨tailKinds, tailZig, tailZigZig, tailZigZag,
          tailTranscript⟩ := ih
      exact
        ⟨headKinds ++ tailKinds,
          headZig + tailZig,
          headZigZig + tailZigZig,
          headZigZag + tailZigZag,
          .next head tail headTranscript tailTranscript⟩

/-- The sequence transcript counts exactly its listed zig-zigs. -/
theorem count_zigZig
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag) :
    kinds.count .zigZig = zigZig := by
  induction transcript with
  | done =>
      simp
  | next head tail headTranscript tailTranscript tailIH =>
      simp [List.count_append, headTranscript.count_zigZig,
        tailIH]

/-- The sequence transcript counts exactly its listed zigs. -/
theorem count_zig
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag) :
    kinds.count .zig = zig := by
  induction transcript with
  | done =>
      simp
  | next head tail headTranscript tailTranscript tailIH =>
      simp [List.count_append, headTranscript.count_zig, tailIH]

/-- The sequence transcript counts exactly its listed zig-zags. -/
theorem count_zigZag
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag) :
    kinds.count .zigZag = zigZag := by
  induction transcript with
  | done =>
      simp
  | next head tail headTranscript tailTranscript tailIH =>
      simp [List.count_append, headTranscript.count_zigZag,
        tailIH]

/-- The transcript recovers the exact ordinary-rotation count of the sequence. -/
theorem rotationCount_eq
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag) :
    sequence.rotationCount =
      zig + 2 * zigZig + 2 * zigZag := by
  induction transcript with
  | done =>
      simp
  | @next access accesses before middle after
      headKinds tailKinds headZig headZigZig headZigZag
      tailZig tailZigZig tailZigZag head tail
      headTranscript tailTranscript tailIH =>
      have headDepth :=
        headTranscript.toExecutionCounts.depth_eq_and_zig_le_one
      rw [SplaySequence.rotationCount_next, headDepth.1, tailIH]
      omega

/-- There is still at most one final zig per served request. -/
theorem zig_le_accesses
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag) :
    zig ≤ accesses.length := by
  induction transcript with
  | done =>
      simp
  | next head tail headTranscript tailTranscript tailIH =>
      have headBound :=
        headTranscript.toExecutionCounts.depth_eq_and_zig_le_one
      simp only [List.length_cons]
      omega

end SplaySequenceTranscript

/-- A chosen ordered transcript bundled with its sequence-indexed evidence. -/
structure SplaySequenceTranscriptWitness
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    (sequence : SplaySequence accesses before after) where
  kinds : List SplayStepKind
  zig : ℕ
  zigZig : ℕ
  zigZag : ℕ
  transcript :
    SplaySequenceTranscript sequence kinds zig zigZig zigZag

noncomputable def splaySequenceTranscriptWitness
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    (sequence : SplaySequence accesses before after) :
    SplaySequenceTranscriptWitness sequence := by
  let existence := SplaySequenceTranscript.exists_transcript sequence
  exact
    { kinds := Classical.choose existence
      zig := Classical.choose (Classical.choose_spec existence)
      zigZig :=
        Classical.choose
          (Classical.choose_spec (Classical.choose_spec existence))
      zigZag :=
        Classical.choose
          (Classical.choose_spec
            (Classical.choose_spec (Classical.choose_spec existence)))
      transcript :=
        Classical.choose_spec
          (Classical.choose_spec
            (Classical.choose_spec
              (Classical.choose_spec existence))) }

/--
The concrete cost model's chosen structural sequence, now equipped with the
actual chronological orientation transcript rather than only an arithmetic
decomposition.
-/
noncomputable def concreteSplayTranscript
    {n : ℕ} (initial : BST 0 n) (accesses : List (Fin n)) :
    SplaySequenceTranscriptWitness
      (chosenSplaySequence initial accesses) :=
  splaySequenceTranscriptWitness
    (chosenSplaySequence initial accesses)

/-- The concrete transcript recovers the chosen sequence's exact rotations. -/
theorem concreteSplayTranscript_rotationCount
    {n : ℕ} (initial : BST 0 n) (accesses : List (Fin n)) :
    (chosenSplaySequence initial accesses).rotationCount =
      (concreteSplayTranscript initial accesses).zig +
        2 * (concreteSplayTranscript initial accesses).zigZig +
        2 * (concreteSplayTranscript initial accesses).zigZag :=
  (concreteSplayTranscript initial accesses).transcript.rotationCount_eq

/--
The cost decomposition is derived from the real ordered transcript.  In
particular its zig-zig and zig-zag fields cannot be swapped independently of
the actual double-rotation orientations.
-/
theorem concreteSplayTranscript_cost_decomposition
    {n : ℕ} (initial : BST 0 n) (accesses : List (Fin n)) :
    concreteSplayCost initial accesses ≤
      accesses.length + accesses.length +
        2 * (concreteSplayTranscript initial accesses).zigZig +
        2 * (concreteSplayTranscript initial accesses).zigZag := by
  have zigLe :
      (concreteSplayTranscript initial accesses).zig ≤
        accesses.length :=
    (concreteSplayTranscript initial accesses).transcript.zig_le_accesses
  rw [concreteSplayCost,
    concreteSplayTranscript_rotationCount initial accesses]
  omega

/-- The two chronological batches used by the manuscript pairing schedule. -/
inductive PairingPhase
  | first
  | second
  deriving DecidableEq, Repr

/--
One abstract pairing slot attached to the actual chronological position of a
zig-zig.  Concrete heap-child endpoints are deliberately left to the
comparison-rank/lazy-interval translation.
-/
structure PairingSlot where
  zigZigStep : ℕ
  phase : PairingPhase
  deriving DecidableEq, Repr

/-- Chronological positions occupied by genuine zig-zig steps. -/
def zigZigStepIndices (kinds : List SplayStepKind) : List ℕ :=
  kinds.findIdxs SplayStepKind.isZigZig

private theorem countP_isZigZig_eq_count
    (kinds : List SplayStepKind) :
    kinds.countP SplayStepKind.isZigZig =
      kinds.count .zigZig := by
  induction kinds with
  | nil =>
      rfl
  | cons kind kinds ih =>
      cases kind <;> simp [SplayStepKind.isZigZig, ih]

/-- One first-pairing slot for every genuine zig-zig, in execution order. -/
def firstPairings (kinds : List SplayStepKind) : List PairingSlot :=
  (zigZigStepIndices kinds).map fun step =>
    { zigZigStep := step, phase := .first }

/-- One second-pairing slot for every genuine zig-zig, in execution order. -/
def secondPairings (kinds : List SplayStepKind) : List PairingSlot :=
  (zigZigStepIndices kinds).map fun step =>
    { zigZigStep := step, phase := .second }

@[simp] theorem length_zigZigStepIndices (kinds : List SplayStepKind) :
    (zigZigStepIndices kinds).length = kinds.count .zigZig := by
  simp [zigZigStepIndices, countP_isZigZig_eq_count]

@[simp] theorem length_firstPairings (kinds : List SplayStepKind) :
    (firstPairings kinds).length = kinds.count .zigZig := by
  simp [firstPairings]

@[simp] theorem length_secondPairings (kinds : List SplayStepKind) :
    (secondPairings kinds).length = kinds.count .zigZig := by
  simp [secondPairings]

/-- First and second batches cover the same zig-zigs in the same order. -/
theorem pairingSteps_eq (kinds : List SplayStepKind) :
    (firstPairings kinds).map PairingSlot.zigZigStep =
      (secondPairings kinds).map PairingSlot.zigZigStep := by
  simp [firstPairings, secondPairings]

/-- Every genuine zig-zig contributes exactly two abstract pairing slots. -/
theorem total_pairingSlots
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag) :
    (firstPairings kinds).length + (secondPairings kinds).length =
      2 * zigZig := by
  rw [length_firstPairings, length_secondPairings,
    transcript.count_zigZig]
  omega

/-- Zig-zig positions, hence both pairing batches, are strictly chronological. -/
theorem firstPairings_ordered (kinds : List SplayStepKind) :
    (firstPairings kinds).Pairwise
      (fun first second =>
        first.zigZigStep < second.zigZigStep) := by
  rw [firstPairings, List.pairwise_map]
  exact
    List.pairwise_findIdxs
      (xs := kinds) (p := SplayStepKind.isZigZig) (s := 0)

/-- The second batch retains the same strict chronological order. -/
theorem secondPairings_ordered (kinds : List SplayStepKind) :
    (secondPairings kinds).Pairwise
      (fun first second =>
        first.zigZigStep < second.zigZigStep) := by
  rw [secondPairings, List.pairwise_map]
  exact
    List.pairwise_findIdxs
      (xs := kinds) (p := SplayStepKind.isZigZig) (s := 0)

/-- In particular, no first-pairing occurrence is repeated. -/
theorem firstPairings_nodup (kinds : List SplayStepKind) :
    (firstPairings kinds).Nodup :=
  (firstPairings_ordered kinds).imp (by
    intro first second less same
    subst second
    omega)

/-- In particular, no second-pairing occurrence is repeated. -/
theorem secondPairings_nodup (kinds : List SplayStepKind) :
    (secondPairings kinds).Nodup :=
  (secondPairings_ordered kinds).imp (by
    intro first second less same
    subst second
    omega)

/-- Every member of the first batch carries the first-phase tag. -/
theorem phase_eq_first_of_mem_firstPairings
    {kinds : List SplayStepKind} {pairing : PairingSlot}
    (member : pairing ∈ firstPairings kinds) :
    pairing.phase = .first := by
  obtain ⟨step, stepMember, rfl⟩ :=
    List.mem_map.mp member
  rfl

/-- Every member of the second batch carries the second-phase tag. -/
theorem phase_eq_second_of_mem_secondPairings
    {kinds : List SplayStepKind} {pairing : PairingSlot}
    (member : pairing ∈ secondPairings kinds) :
    pairing.phase = .second := by
  obtain ⟨step, stepMember, rfl⟩ :=
    List.mem_map.mp member
  rfl

/--
The two ordered batches are disjoint as pairing occurrences.  They still
refer to the same zig-zig positions by `pairingSteps_eq`; their distinct phase
tags say precisely which of the two chronological pairing rounds they belong
to.
-/
theorem firstPairings_disjoint_secondPairings
    (kinds : List SplayStepKind) :
    List.Disjoint (firstPairings kinds) (secondPairings kinds) := by
  rw [List.disjoint_left]
  intro pairing firstMember secondMember
  have firstPhase :=
    phase_eq_first_of_mem_firstPairings firstMember
  have secondPhase :=
    phase_eq_second_of_mem_secondPairings secondMember
  have impossible : PairingPhase.first = .second :=
    firstPhase.symm.trans secondPhase
  contradiction

end Splay.Accounting
