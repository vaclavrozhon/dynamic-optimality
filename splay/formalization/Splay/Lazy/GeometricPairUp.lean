import Splay.Lazy.OperationValidity

namespace Splay.Lazy

/--
Purely geometric validity of one pair-up tuple.

This is `Interface.PairingValid` with the value inequality removed.  The
manuscript first constructs pair-ups from the splay geometry and only later
temporarily lowers equal-valued winners when translating the batch to an
interface `Pass`; keeping the notions separate avoids making that argument
circular.
-/
def GeometricPairingValid {n : ℕ} (state : State n)
    (sourceId : Interface.BlockId) (source : Block n)
    (pairing : Interface.Pairing n) : Prop :=
  Interface.Adjacent source.elements pairing.winner pairing.loser ∧
    pairing.destination ≠ sourceId ∧
    ∃ destination,
      state.toInterface.block? pairing.destination = some destination ∧
        destination.mode = .growing ∧
        destination.creator = pairing.winner

/--
A simultaneous geometric pair-up batch.  It contains exactly the structural
parts of `Interface.MatchingValid`: a shrinking source, disjoint endpoints,
distinct destination growing blocks, and adjacency of every pair.

It deliberately contains neither the pass-count/fraction condition nor the
value inequality.  Those are consequences of the persistent interval
history and contracted-gap argument, respectively, and belong to the later
interface translation.
-/
def GeometricMatchingValid {n : ℕ} (state : State n)
    (sourceId : Interface.BlockId) (source : Block n)
    (matching : List (Interface.Pairing n)) : Prop :=
  source.mode = .shrinking ∧
    (matching.flatMap fun pairing =>
      [pairing.winner, pairing.loser]).Nodup ∧
    (matching.map fun pairing => pairing.destination).Nodup ∧
    ∀ pairing ∈ matching,
      GeometricPairingValid state sourceId source pairing

/--
Once the two non-geometric obligations are supplied, a geometric pair-up
batch is a legal interface matching.
-/
theorem GeometricMatchingValid.toInterface
    {n : ℕ} {params : Interface.Parameters}
    {state : State n} {sourceId : Interface.BlockId} {source : Block n}
    {matching : List (Interface.Pairing n)}
    (geometric :
      GeometricMatchingValid state sourceId source matching)
    (valueOrder :
      ∀ pairing ∈ matching,
        state.toInterface.value pairing.winner + 1 ≤
          state.toInterface.value pairing.loser)
    (largeEnough :
      source.passCount < params.exemptPasses ∨
        params.matchingNumerator * source.elements.length ≤
          params.matchingDenominator * matching.length) :
    Interface.MatchingValid params state.toInterface sourceId
      source.toInterface matching := by
  refine ⟨geometric.1, geometric.2.1, geometric.2.2.1, ?_, largeEnough⟩
  intro pairing member
  have tuple := geometric.2.2.2 pairing member
  exact
    ⟨tuple.1, valueOrder pairing member, tuple.2.1, tuple.2.2⟩

/--
The purely rich preservation data for one pass in a new heap view.

This record intentionally omits the interface matching rule.  It says that
the exact block rearrangement produced by `Pass` is a valid lazy-interval
partition of `afterView`: the shrinking remainder is consecutive with the
chosen signed minimum and every destination/untouched block is structurally
valid.  Global assignment and growing-count preservation follow generically
from legality of the abstract matching.
-/
structure PassAtViewPreservation {n : ℕ}
    (before : State n) (afterView : HeapView n)
    (sourceId : Interface.BlockId) (source : Block n)
    (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ) : Prop where
  sourceFoundAfter :
    (before.passAtView afterView sourceId source matching
      sourceIntervalGap).blocks[sourceId]? =
      some (source.afterPassSource matching sourceIntervalGap)
  sourceSegment :
    IsSegment
      (source.afterPassSource matching sourceIntervalGap).elements
      (afterView.attachedTopDown
        (before.passAtView afterView sourceId source matching
          sourceIntervalGap).allElements
        source.owner source.side)
  sourceGapValid :
    (source.afterPassSource matching sourceIntervalGap).GapValid afterView
  otherValid :
    ∀ id : Fin
        (before.passAtView afterView sourceId source matching
          sourceIntervalGap).blocks.length,
      sourceId ≠ id.val →
        ((before.passAtView afterView sourceId source matching
          sourceIntervalGap).blocks.get id).StructurallyValid
            afterView
            (before.passAtView afterView sourceId source matching
              sourceIntervalGap).allElements

namespace PassAtViewPreservation

/-- Once the two genuine placement obligations are known, stable source IDs
and the recomputed shrinking minimum complete the rich preservation record
automatically. -/
theorem exists_of_placement {n : ℕ}
    {before : State n} {afterView : HeapView n}
    {sourceId : Interface.BlockId} {source : Block n}
    {matching : List (Interface.Pairing n)}
    (sourceFound : before.blocks[sourceId]? = some source)
    (geometric : GeometricMatchingValid before sourceId source matching)
    (sourceSegment : ∀ sourceIntervalGap,
      IsSegment
        (source.afterPassSource matching sourceIntervalGap).elements
        (afterView.attachedTopDown
          (before.passAtView afterView sourceId source matching
            sourceIntervalGap).allElements
          source.owner source.side))
    (otherValid : ∀ sourceIntervalGap,
      ∀ id : Fin
          (before.passAtView afterView sourceId source matching
            sourceIntervalGap).blocks.length,
        sourceId ≠ id.val →
          ((before.passAtView afterView sourceId source matching
            sourceIntervalGap).blocks.get id).StructurallyValid
              afterView
              (before.passAtView afterView sourceId source matching
                sourceIntervalGap).allElements) :
    ∃ sourceIntervalGap,
      PassAtViewPreservation before afterView sourceId source matching
        sourceIntervalGap := by
  obtain ⟨sourceIntervalGap, gapValid⟩ :=
    source.exists_afterPassSource_gapValid afterView geometric.1 matching
  refine ⟨sourceIntervalGap, ?_⟩
  refine ⟨?_, sourceSegment sourceIntervalGap, gapValid,
    otherValid sourceIntervalGap⟩
  change
    (Block.passBlocks before.blocks sourceId source matching
      sourceIntervalGap)[sourceId]? =
      some (source.afterPassSource matching sourceIntervalGap)
  apply Block.passBlocks_source_getElem? before.blocks sourceId source
    matching sourceIntervalGap sourceFound
  intro pairing pairingMember
  exact (geometric.2.2.2 pairing pairingMember).2.1

/-- Rich preservation plus a legal matching yields the article's visible
pair-up step in the new heap view. -/
theorem step {n : ℕ} {params : Interface.Parameters}
    {before : State n} {afterView : HeapView n}
    {sourceId : Interface.BlockId} {source : Block n}
    {matching : List (Interface.Pairing n)} {sourceIntervalGap : ℤ}
    (preservation : PassAtViewPreservation before afterView sourceId source
      matching sourceIntervalGap)
    (valid : before.Valid params)
    (sourceFound : before.blocks[sourceId]? = some source)
    (matchingValid :
      Interface.MatchingValid params before.toInterface sourceId
        source.toInterface matching) :
    Step params before (.operation (.pass sourceId matching))
      (before.passAtView afterView sourceId source matching
        sourceIntervalGap) := by
  exact State.passAtView_step_of_matching before afterView sourceId source matching
    sourceIntervalGap valid sourceFound matchingValid
      preservation.sourceFoundAfter preservation.sourceSegment
      preservation.sourceGapValid preservation.otherValid

end PassAtViewPreservation

/--
One proof-relevant geometric pair-up transition.  Its state effect is already
the exact rich pass rearrangement, but no interface legality is asserted yet.
Stable block identifiers are therefore preserved exactly as they will be in
the final `Pass` trace.
-/
structure GeometricPairUp {n : ℕ} (before after : State n) where
  afterView : HeapView n
  sourceId : Interface.BlockId
  source : Block n
  matching : List (Interface.Pairing n)
  sourceIntervalGap : ℤ
  sourceFound : before.blocks[sourceId]? = some source
  matchingValid :
    GeometricMatchingValid before sourceId source matching
  after_eq :
    after = before.passAtView afterView sourceId source matching
      sourceIntervalGap

namespace GeometricPairUp

/-- A geometric pair-up exposes the same visible pass operation. -/
def operation {n : ℕ} {before after : State n}
    (pairUp : GeometricPairUp before after) : Interface.Operation n :=
  .pass pairUp.sourceId pairUp.matching

/--
Article-faithful translation of one geometric pair-up batch to one legal
rich interface step.  All list rearrangement and persistent-ID data come
from `pairUp`; the arguments after `valid` are precisely the independent
value, fraction, and rich structural preservation obligations.
-/
theorem step {n : ℕ} {params : Interface.Parameters}
    {before after : State n}
    (pairUp : GeometricPairUp before after)
    (valid : before.Valid params)
    (valueOrder :
      ∀ pairing ∈ pairUp.matching,
        before.toInterface.value pairing.winner + 1 ≤
          before.toInterface.value pairing.loser)
    (largeEnough :
      pairUp.source.passCount < params.exemptPasses ∨
        params.matchingNumerator * pairUp.source.elements.length ≤
          params.matchingDenominator * pairUp.matching.length)
    (sourceFoundAfter :
      (before.passAtView pairUp.afterView pairUp.sourceId pairUp.source
        pairUp.matching pairUp.sourceIntervalGap).blocks[pairUp.sourceId]? =
      some (pairUp.source.afterPassSource pairUp.matching
        pairUp.sourceIntervalGap))
    (sourceSegment :
      IsSegment
        (pairUp.source.afterPassSource pairUp.matching
          pairUp.sourceIntervalGap).elements
        (pairUp.afterView.attachedTopDown
          (before.passAtView pairUp.afterView pairUp.sourceId pairUp.source
            pairUp.matching pairUp.sourceIntervalGap).allElements
          pairUp.source.owner pairUp.source.side))
    (sourceGapValid :
      (pairUp.source.afterPassSource pairUp.matching
        pairUp.sourceIntervalGap).GapValid pairUp.afterView)
    (assignedPerm :
      (before.passAtView pairUp.afterView pairUp.sourceId pairUp.source
        pairUp.matching pairUp.sourceIntervalGap).allElements.Perm
        before.allElements)
    (growingCountEq :
      ∀ creator,
        (before.passAtView pairUp.afterView pairUp.sourceId pairUp.source
          pairUp.matching pairUp.sourceIntervalGap).toInterface.growingCount
            creator =
        before.toInterface.growingCount creator)
    (otherValid :
      ∀ id : Fin
          (before.passAtView pairUp.afterView pairUp.sourceId pairUp.source
            pairUp.matching pairUp.sourceIntervalGap).blocks.length,
        pairUp.sourceId ≠ id.val →
          ((before.passAtView pairUp.afterView pairUp.sourceId pairUp.source
            pairUp.matching pairUp.sourceIntervalGap).blocks.get id).StructurallyValid
            pairUp.afterView
            (before.passAtView pairUp.afterView pairUp.sourceId pairUp.source
              pairUp.matching pairUp.sourceIntervalGap).allElements) :
    Step params before (.operation pairUp.operation) after := by
  have translated :
      Step params before
        (.operation (.pass pairUp.sourceId pairUp.matching))
        (before.passAtView pairUp.afterView pairUp.sourceId pairUp.source
          pairUp.matching pairUp.sourceIntervalGap) := by
    apply State.passAtView_step before pairUp.afterView pairUp.sourceId
      pairUp.source pairUp.matching pairUp.sourceIntervalGap valid
      pairUp.sourceFound
    · exact pairUp.matchingValid.toInterface valueOrder largeEnough
    · exact sourceFoundAfter
    · exact sourceSegment
    · exact sourceGapValid
    · exact assignedPerm
    · exact growingCountEq
    · exact otherValid
  simpa only [operation, pairUp.after_eq] using translated

end GeometricPairUp

end Splay.Lazy
