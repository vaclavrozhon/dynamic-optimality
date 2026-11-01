import Splay.Accounting.SplayPairingTranscript
import Splay.Lazy.ComparisonTrace

namespace Splay.Accounting

open Splay.Assumptions.NormalForm
open Splay.Tree.BST

/--
Finite constants in the bend-potential argument.

They respectively bound initial bends per key, the administrative bends
created per complete splay access, and bends created per comparison-tree
rotation.
-/
structure BendConstants where
  initial : ℕ
  splay : ℕ
  comparisonRotation : ℕ
  deriving Repr

namespace BendConstants

/--
A single coefficient which simultaneously dominates all three sources.
Using the sum rather than a maximum keeps the later natural-number
normalization completely elementary.
-/
def coefficient (constants : BendConstants) : ℕ :=
  constants.initial + constants.splay +
    constants.comparisonRotation

theorem initial_le_coefficient (constants : BendConstants) :
    constants.initial ≤ constants.coefficient := by
  unfold coefficient
  omega

theorem splay_le_coefficient (constants : BendConstants) :
    constants.splay ≤ constants.coefficient := by
  unfold coefficient
  omega

theorem comparisonRotation_le_coefficient
    (constants : BendConstants) :
    constants.comparisonRotation ≤ constants.coefficient := by
  simp [coefficient]

end BendConstants

/-- Whether one bend-potential transition comes from a splay or a comparison
rotation. -/
inductive BendActionKind
  | splay
  | comparisonRotation
  deriving DecidableEq, Repr

/--
The exact potential data of one chronological action.

For a splay action, `zigZig` and `zigZag` are the orientation counts of that
complete access.  For a comparison rotation they are required to be zero by
`LocallySound`.
-/
structure BendAction where
  kind : BendActionKind
  zigZig : ℕ
  zigZag : ℕ
  created : ℕ
  removed : ℕ
  deriving Repr

namespace BendAction

/--
The two local geometric lemmata used by the manuscript's global telescope.

* A complete splay removes at least one old bend per zig-zag and creates at
  most one bend per zig-zig plus a uniform administrative allowance.
* A comparison rotation has no splay orientations and creates at most its
  uniform allowance.

No restriction is put on removed bends of a comparison rotation: additional
removals can only help the upper bound.
-/
def LocallySound (constants : BendConstants)
    (action : BendAction) : Prop :=
  match action.kind with
  | .splay =>
      action.zigZag ≤ action.removed ∧
        action.created ≤ action.zigZig + constants.splay
  | .comparisonRotation =>
      action.zigZig = 0 ∧
        action.zigZag = 0 ∧
        action.created ≤ constants.comparisonRotation

/--
The action induced by two concrete finite bend sets.

New bends are the elements in `after \ before`; removed bends are the
elements in `before \ after`.
-/
def between {n : ℕ} (kind : BendActionKind)
    (zigZig zigZag : ℕ)
    (before after : Finset (Fin n)) : BendAction where
  kind := kind
  zigZig := zigZig
  zigZag := zigZag
  created := (after \ before).card
  removed := (before \ after).card

/-- Cardinality conservation for a transition between two actual bend sets. -/
theorem card_balance_between
    {n : ℕ} (kind : BendActionKind)
    (zigZig zigZag : ℕ)
    (before after : Finset (Fin n)) :
    before.card +
        (between kind zigZig zigZag before after).created =
      after.card +
        (between kind zigZig zigZag before after).removed := by
  have beforeParts :=
    Finset.card_sdiff_add_card_inter before after
  have afterParts :=
    Finset.card_sdiff_add_card_inter after before
  rw [Finset.inter_comm] at afterParts
  simp only [between]
  omega

end BendAction

/-- Total bends created by a chronological action list. -/
def totalBendsCreated : List BendAction → ℕ
  | [] => 0
  | action :: actions =>
      action.created + totalBendsCreated actions

/-- Total bends removed by a chronological action list. -/
def totalBendsRemoved : List BendAction → ℕ
  | [] => 0
  | action :: actions =>
      action.removed + totalBendsRemoved actions

/-- Total splay zig-zigs recorded by an action list. -/
def totalActionZigZig : List BendAction → ℕ
  | [] => 0
  | action :: actions =>
      action.zigZig + totalActionZigZig actions

/-- Total splay zig-zags recorded by an action list. -/
def totalActionZigZag : List BendAction → ℕ
  | [] => 0
  | action :: actions =>
      action.zigZag + totalActionZigZag actions

/-- Number of complete splay actions in a chronological action list. -/
def totalSplayActions : List BendAction → ℕ
  | [] => 0
  | action :: actions =>
      (if action.kind = .splay then 1 else 0) +
        totalSplayActions actions

/-- Number of comparison rotations in a chronological action list. -/
def totalComparisonRotationActions : List BendAction → ℕ
  | [] => 0
  | action :: actions =>
      (if action.kind = .comparisonRotation then 1 else 0) +
        totalComparisonRotationActions actions

/--
An exact bend-potential history.

Every constructor records the conservation equation

`before + created = after + removed`

and shares its intermediate bend count definitionally with the tail.  Thus
the global telescope below is a theorem, not an additional field of the
event-translation witness.
-/
inductive BendHistory :
    ℕ → List BendAction → ℕ → Prop
  | nil (bends : ℕ) :
      BendHistory bends [] bends
  | cons {before middle after : ℕ}
      (action : BendAction) (actions : List BendAction)
      (balance :
        before + action.created = middle + action.removed)
      (tail : BendHistory middle actions after) :
      BendHistory before (action :: actions) after

namespace BendHistory

/--
Concatenate two numerical bend histories whose intermediate potential agrees.
This is the multiplicity-preserving counterpart of
`FiniteBendHistory.append`.
-/
theorem append
    {initial middle final : ℕ}
    {prefixActions suffixActions : List BendAction}
    (first : BendHistory initial prefixActions middle)
    (second : BendHistory middle suffixActions final) :
    BendHistory initial (prefixActions ++ suffixActions) final := by
  induction first with
  | nil =>
      simpa using second
  | cons action actions balance tail ih =>
      simpa using
        BendHistory.cons action _ balance (ih second)

/-- Exact telescoping of all chronological bend transitions. -/
theorem telescope
    {initial final : ℕ} {actions : List BendAction}
    (history : BendHistory initial actions final) :
    initial + totalBendsCreated actions =
      final + totalBendsRemoved actions := by
  induction history with
  | nil bends =>
      rfl
  | cons action actions balance tail ih =>
      simp only [totalBendsCreated, totalBendsRemoved]
      omega

/-- Nonnegativity of the final potential bounds all removals by initial
potential plus all creations. -/
theorem totalBendsRemoved_le
    {initial final : ℕ} {actions : List BendAction}
    (history : BendHistory initial actions final) :
    totalBendsRemoved actions ≤
      initial + totalBendsCreated actions := by
  have exactBalance := history.telescope
  omega

end BendHistory

/--
An exact history whose states are actual finite sets of internal-node bends.

This is the semantically preferable constructor interface: both the
potential values and each action's created/removed counts are computed from
the sets, while `toBendHistory` supplies the numerical telescope
automatically.
-/
inductive FiniteBendHistory (n : ℕ) :
    Finset (Fin n) → List BendAction → Finset (Fin n) → Prop
  | nil (bends : Finset (Fin n)) :
      FiniteBendHistory n bends [] bends
  | cons {before middle after : Finset (Fin n)}
      (kind : BendActionKind) (zigZig zigZag : ℕ)
      {actions : List BendAction}
      (tail : FiniteBendHistory n middle actions after) :
      FiniteBendHistory n before
        (BendAction.between kind zigZig zigZag before middle ::
          actions)
        after

namespace FiniteBendHistory

/-- Forgetting the bend identities retains an exact numerical history. -/
theorem toBendHistory
    {n : ℕ} {initial final : Finset (Fin n)}
    {actions : List BendAction}
    (history : FiniteBendHistory n initial actions final) :
    BendHistory initial.card actions final.card := by
  induction history with
  | nil bends =>
      exact .nil bends.card
  | cons kind zigZig zigZag tail ih =>
      exact
        .cons
          (BendAction.between kind zigZig zigZag _ _)
          _
          (BendAction.card_balance_between
            kind zigZig zigZag _ _)
          ih

/--
Concatenate two chronological finite-set histories whose boundary bend set
agrees.  This is the basic composition operation used when comparison
rotations and complete splay accesses are interleaved.
-/
theorem append
    {n : ℕ}
    {initial middle final : Finset (Fin n)}
    {prefixActions suffixActions : List BendAction}
    (first : FiniteBendHistory n initial prefixActions middle)
    (second : FiniteBendHistory n middle suffixActions final) :
    FiniteBendHistory n initial (prefixActions ++ suffixActions) final := by
  induction first with
  | nil =>
      simpa using second
  | cons kind zigZig zigZag tail ih =>
      simpa using
        (FiniteBendHistory.cons kind zigZig zigZag
          (ih second))

/-- A finite set of bends indexed by internal keys has size at most `n`. -/
theorem initial_card_le
    {n : ℕ} {initial final : Finset (Fin n)}
    {actions : List BendAction}
    (_history : FiniteBendHistory n initial actions final) :
    initial.card ≤ n := by
  simpa using Finset.card_le_univ initial

end FiniteBendHistory

/-- Local removal soundness sums to the global zig-zag removal bound. -/
theorem totalActionZigZag_le_totalBendsRemoved
    {constants : BendConstants} {actions : List BendAction}
    (sound :
      ∀ action ∈ actions, action.LocallySound constants) :
    totalActionZigZag actions ≤ totalBendsRemoved actions := by
  induction actions with
  | nil =>
      exact Nat.le_refl 0
  | cons action actions ih =>
      have headSound : action.LocallySound constants :=
        sound action (by simp)
      have tailSound :
          ∀ tailAction ∈ actions,
            tailAction.LocallySound constants := by
        intro tailAction tailMember
        exact sound tailAction (by simp [tailMember])
      have tailBound := ih tailSound
      cases actionKind : action.kind with
      | splay =>
          simp [BendAction.LocallySound, actionKind] at headSound
          simp only [totalActionZigZag, totalBendsRemoved]
          omega
      | comparisonRotation =>
          simp [BendAction.LocallySound, actionKind] at headSound
          simp only [totalActionZigZag, totalBendsRemoved]
          omega

/-- Local creation bounds sum over all splay and comparison actions. -/
theorem totalBendsCreated_le
    {constants : BendConstants} {actions : List BendAction}
    (sound :
      ∀ action ∈ actions, action.LocallySound constants) :
    totalBendsCreated actions ≤
      totalActionZigZig actions +
        constants.splay * totalSplayActions actions +
        constants.comparisonRotation *
          totalComparisonRotationActions actions := by
  induction actions with
  | nil =>
      simp [totalBendsCreated, totalActionZigZig,
        totalSplayActions, totalComparisonRotationActions]
  | cons action actions ih =>
      have headSound : action.LocallySound constants :=
        sound action (by simp)
      have tailSound :
          ∀ tailAction ∈ actions,
            tailAction.LocallySound constants := by
        intro tailAction tailMember
        exact sound tailAction (by simp [tailMember])
      have tailBound := ih tailSound
      cases actionKind : action.kind with
      | splay =>
          simp [BendAction.LocallySound, actionKind] at headSound
          simp [totalBendsCreated, totalActionZigZig,
            totalSplayActions, totalComparisonRotationActions,
            actionKind, Nat.mul_add]
          omega
      | comparisonRotation =>
          simp [BendAction.LocallySound, actionKind] at headSound
          simp [totalBendsCreated, totalActionZigZig,
            totalSplayActions, totalComparisonRotationActions,
            actionKind, Nat.mul_add]
          omega

/--
The minimal precise semantic bridge still required from the heavy-path
geometry.

The action history may interleave complete splays and comparison-tree
rotations arbitrarily.  Its fields tie that history to:

* the actual proof-indexed splay transcript,
* exactly one complete splay action per request, and
* exactly one comparison action per rotation of the supplied normal-form
  comparison trace.
-/
structure ZigZagBendWitness
    (constants : BendConstants)
    {n : ℕ} {accesses : List (Fin n)}
    (comparison : ComparisonTrace n accesses)
    {before after : BST 0 n}
    (sequence : SplaySequence accesses before after)
    (transcript : SplaySequenceTranscriptWitness sequence) where
  initialBends : ℕ
  finalBends : ℕ
  actions : List BendAction
  history :
    BendHistory initialBends actions finalBends
  locallySound :
    ∀ action ∈ actions, action.LocallySound constants
  initialBends_le :
    initialBends ≤ constants.initial * n
  zigZig_eq :
    totalActionZigZig actions = transcript.zigZig
  zigZag_eq :
    totalActionZigZag actions = transcript.zigZag
  splayActions_eq :
    totalSplayActions actions = accesses.length
  comparisonRotationActions_eq :
    totalComparisonRotationActions actions =
      comparison.rotationCount

/--
Stronger witness form carrying actual finite bend sets at the two endpoints
and an exact `FiniteBendHistory`.

It has no caller-supplied initial-potential bound and no caller-supplied
numeric conservation equation; both are derived from the finite sets.
-/
structure FiniteZigZagBendWitness
    (constants : BendConstants)
    {n : ℕ} {accesses : List (Fin n)}
    (comparison : ComparisonTrace n accesses)
    {before after : BST 0 n}
    (sequence : SplaySequence accesses before after)
    (transcript : SplaySequenceTranscriptWitness sequence) where
  initialBends : Finset (Fin n)
  finalBends : Finset (Fin n)
  actions : List BendAction
  history :
    FiniteBendHistory n initialBends actions finalBends
  locallySound :
    ∀ action ∈ actions, action.LocallySound constants
  zigZig_eq :
    totalActionZigZig actions = transcript.zigZig
  zigZag_eq :
    totalActionZigZag actions = transcript.zigZag
  splayActions_eq :
    totalSplayActions actions = accesses.length
  comparisonRotationActions_eq :
    totalComparisonRotationActions actions =
      comparison.rotationCount

namespace FiniteZigZagBendWitness

/--
Finite bend identities instantiate the numerical witness whenever the initial
allowance is at least one bend per internal key.
-/
def toZigZagBendWitness
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {transcript : SplaySequenceTranscriptWitness sequence}
    (witness :
      FiniteZigZagBendWitness
        constants comparison sequence transcript)
    (initialUnit : 1 ≤ constants.initial) :
    ZigZagBendWitness constants comparison sequence transcript where
  initialBends := witness.initialBends.card
  finalBends := witness.finalBends.card
  actions := witness.actions
  history := witness.history.toBendHistory
  locallySound := witness.locallySound
  initialBends_le := by
    calc
      witness.initialBends.card ≤ n :=
        witness.history.initial_card_le
      _ = 1 * n := by simp
      _ ≤ constants.initial * n :=
        Nat.mul_le_mul_right n initialUnit
  zigZig_eq := witness.zigZig_eq
  zigZag_eq := witness.zigZag_eq
  splayActions_eq := witness.splayActions_eq
  comparisonRotationActions_eq :=
    witness.comparisonRotationActions_eq

end FiniteZigZagBendWitness

namespace ZigZagBendWitness

/--
The exact non-asymptotic bend telescope before coefficients are combined.
-/
theorem zigZag_le_detailed
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {transcript : SplaySequenceTranscriptWitness sequence}
    (witness :
      ZigZagBendWitness constants comparison sequence transcript) :
    transcript.zigZag ≤
      transcript.zigZig +
        constants.initial * n +
        constants.splay * accesses.length +
        constants.comparisonRotation *
          comparison.rotationCount := by
  have zigZagRemoval :
      totalActionZigZag witness.actions ≤
        totalBendsRemoved witness.actions :=
    totalActionZigZag_le_totalBendsRemoved
      witness.locallySound
  have removalBudget :
      totalBendsRemoved witness.actions ≤
        witness.initialBends +
          totalBendsCreated witness.actions :=
    witness.history.totalBendsRemoved_le
  have creationBudget :
      totalBendsCreated witness.actions ≤
        totalActionZigZig witness.actions +
          constants.splay *
            totalSplayActions witness.actions +
          constants.comparisonRotation *
            totalComparisonRotationActions witness.actions :=
    totalBendsCreated_le witness.locallySound
  have initialBudget := witness.initialBends_le
  rw [witness.zigZag_eq] at zigZagRemoval
  rw [witness.zigZig_eq, witness.splayActions_eq,
    witness.comparisonRotationActions_eq] at creationBudget
  omega

/--
Uniform form used by accounting: normal-form comparison cost absorbs both
the number of requests and the number of comparison rotations.
-/
theorem zigZag_le
    {constants : BendConstants}
    {n nearCost bends : ℕ}
    {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {transcript : SplaySequenceTranscriptWitness sequence}
    (witness :
      ZigZagBendWitness constants comparison sequence transcript)
    (comparisonCost_le : comparison.cost ≤ nearCost)
    (coefficient_le : constants.coefficient ≤ bends) :
    transcript.zigZag ≤
      transcript.zigZig + bends * (n + nearCost) := by
  have initialPart :
      constants.initial * n ≤ constants.coefficient * n :=
    Nat.mul_le_mul_right n constants.initial_le_coefficient
  have splayPart :
      constants.splay * accesses.length ≤
        constants.coefficient * accesses.length :=
    Nat.mul_le_mul_right accesses.length
      constants.splay_le_coefficient
  have comparisonPart :
      constants.comparisonRotation * comparison.rotationCount ≤
        constants.coefficient * comparison.rotationCount :=
    Nat.mul_le_mul_right comparison.rotationCount
      constants.comparisonRotation_le_coefficient
  have combined :
      constants.initial * n +
          constants.splay * accesses.length +
          constants.comparisonRotation * comparison.rotationCount ≤
        constants.coefficient *
          (n + comparison.cost) := by
    simp only [ComparisonTrace.cost, Nat.mul_add]
    omega
  have costAbsorbed :
      constants.coefficient * (n + comparison.cost) ≤
        constants.coefficient * (n + nearCost) :=
    Nat.mul_le_mul_left constants.coefficient
      (Nat.add_le_add_left comparisonCost_le n)
  have coefficientAbsorbed :
      constants.coefficient * (n + nearCost) ≤
        bends * (n + nearCost) :=
    Nat.mul_le_mul_right (n + nearCost) coefficient_le
  calc
    transcript.zigZag ≤
        transcript.zigZig +
          constants.initial * n +
          constants.splay * accesses.length +
          constants.comparisonRotation *
            comparison.rotationCount :=
      witness.zigZag_le_detailed
    _ ≤ transcript.zigZig +
          constants.coefficient * (n + comparison.cost) :=
      by
        simpa only [Nat.add_assoc] using
          Nat.add_le_add_left combined transcript.zigZig
    _ ≤ transcript.zigZig +
          constants.coefficient * (n + nearCost) :=
      Nat.add_le_add_left costAbsorbed transcript.zigZig
    _ ≤ transcript.zigZig + bends * (n + nearCost) :=
      Nat.add_le_add_left coefficientAbsorbed transcript.zigZig

end ZigZagBendWitness

/--
Specialization of the semantic witness to the concrete cost model's chosen
splay sequence and its proof-indexed transcript.
-/
abbrev ConcreteZigZagBendWitness
    (constants : BendConstants)
    {n : ℕ} (initial : BST 0 n) (accesses : List (Fin n))
    (comparison : ComparisonTrace n accesses) :=
  ZigZagBendWitness constants comparison
    (chosenSplaySequence initial accesses)
    (concreteSplayTranscript initial accesses)

/-- Concrete specialization retaining actual finite bend identities. -/
abbrev ConcreteFiniteZigZagBendWitness
    (constants : BendConstants)
    {n : ℕ} (initial : BST 0 n) (accesses : List (Fin n))
    (comparison : ComparisonTrace n accesses) :=
  FiniteZigZagBendWitness constants comparison
    (chosenSplaySequence initial accesses)
    (concreteSplayTranscript initial accesses)

/-- Direct discharge of the concrete accounting residue from a bend witness. -/
theorem concrete_zigZag_bends
    {constants : BendConstants}
    {n nearCost bends : ℕ}
    {initial : BST 0 n} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses}
    (witness :
      ConcreteZigZagBendWitness constants
        initial accesses comparison)
    (comparisonCost_le : comparison.cost ≤ nearCost)
    (coefficient_le : constants.coefficient ≤ bends) :
    (concreteSplayTranscript initial accesses).zigZag ≤
      (concreteSplayTranscript initial accesses).zigZig +
        bends * (n + nearCost) :=
  witness.zigZag_le comparisonCost_le coefficient_le

/--
Finite-set version of the direct concrete discharge.  The initial
`O(n)` bend bound and the potential telescope are automatic.
-/
theorem concrete_finite_zigZag_bends
    {constants : BendConstants}
    {n nearCost bends : ℕ}
    {initial : BST 0 n} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses}
    (witness :
      ConcreteFiniteZigZagBendWitness constants
        initial accesses comparison)
    (initialUnit : 1 ≤ constants.initial)
    (comparisonCost_le : comparison.cost ≤ nearCost)
    (coefficient_le : constants.coefficient ≤ bends) :
    (concreteSplayTranscript initial accesses).zigZag ≤
      (concreteSplayTranscript initial accesses).zigZig +
        bends * (n + nearCost) :=
  (witness.toZigZagBendWitness initialUnit).zigZag_le
    comparisonCost_le coefficient_le

end Splay.Accounting
