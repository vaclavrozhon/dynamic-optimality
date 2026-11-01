import Splay.Accounting.CreationSideBoundaryReclassification
import Splay.Accounting.EnvelopeReduction

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

/--
The quantitative residue after chronological evidence has produced the
canonical request-start geometric boundary reclassification.

The important side deliberately asks for the exact global envelope needed by
the accounting theorem.  It does not quotient occurrences by persistent split
roots: the manuscript proves the bound by summing over created lazy-interval
identities, and a split root may contain several such interval lifetimes.

The final-block embedding remains an independent audit of the schedule's block
births.  A concrete article scheduler may use it together with per-block
multiplicity bounds to construct `importantMoveEmbedding`, but that proof
strategy is not imposed as a stronger public hypothesis.
-/
structure CreationSideBoundaryEnvelopeEmbeddings
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {initial : State n}
    {transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial}
    {provenance :
      SplaySequence.RepresentedTransitionProvenance
        sequence transition}
    {classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events}
    (provider :
      CreationBoundaryEvidenceProvider provenance classification)
    (constants : TranslationConstants)
    (nearCost height cutoff : ℕ) : Type where
  finalBlockEmbedding :
    Fin transition.final.blocks.length →
      Fin (blockEnvelope constants n nearCost)
  finalBlockEmbedding_injective :
    Function.Injective finalBlockEmbedding
  importantMoveEmbedding :
    Fin (provider.reclassification cutoff).importantMoves.length →
      Fin (importantEnvelope constants n nearCost height)
  importantMoveEmbedding_injective :
    Function.Injective importantMoveEmbedding
  unimportantActivityEmbedding :
    Fin (unimportantChargeCoefficient constants height) ×
        Fin (provider.reclassification cutoff).unimportantMoves.length →
      Fin (16 *
        Interface.totalActivity
          (Lazy.eraseOperations transition.events))
  unimportantActivityEmbedding_injective :
    Function.Injective unimportantActivityEmbedding

namespace CreationSideBoundaryEnvelopeEmbeddings

variable
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {initial : State n}
    {transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial}
    {provenance :
      SplaySequence.RepresentedTransitionProvenance
        sequence transition}
    {classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events}
    {provider :
      CreationBoundaryEvidenceProvider provenance classification}
    {constants : TranslationConstants}
    {nearCost height cutoff : ℕ}

/-- The schedule embedding gives the checked final-block budget. -/
theorem finalBlocks_le
    (embeddings :
      CreationSideBoundaryEnvelopeEmbeddings provider constants
        nearCost height cutoff) :
    transition.final.blocks.length ≤
      blockEnvelope constants n nearCost := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective embeddings.finalBlockEmbedding
      embeddings.finalBlockEmbedding_injective

/-- The direct important-occurrence embedding gives exactly the public law. -/
theorem important_le
    (embeddings :
      CreationSideBoundaryEnvelopeEmbeddings provider constants
        nearCost height cutoff) :
    (provider.reclassification cutoff).importantMoves.length ≤
      importantEnvelope constants n nearCost height := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective embeddings.importantMoveEmbedding
      embeddings.importantMoveEmbedding_injective

/-- The activity embedding gives the strong local unimportant charge. -/
theorem unimportant_local_charge
    (embeddings :
      CreationSideBoundaryEnvelopeEmbeddings provider constants
        nearCost height cutoff) :
    unimportantChargeCoefficient constants height *
        (provider.reclassification cutoff).unimportantMoves.length ≤
      16 * Interface.totalActivity
        (Lazy.eraseOperations transition.events) := by
  have cardinality :=
    Fintype.card_le_of_injective embeddings.unimportantActivityEmbedding
      embeddings.unimportantActivityEmbedding_injective
  simpa only [Fintype.card_prod, Fintype.card_fin] using cardinality

/-- Public quotient-form unimportant bound. -/
theorem unimportant_le
    (embeddings :
      CreationSideBoundaryEnvelopeEmbeddings provider constants
        nearCost height cutoff) :
    (provider.reclassification cutoff).unimportantMoves.length ≤
      unimportantEnvelope constants height
        (Interface.totalActivity
          (Lazy.eraseOperations transition.events)) :=
  le_unimportantEnvelope_of_local_charge
    embeddings.unimportant_local_charge

end CreationSideBoundaryEnvelopeEmbeddings

end Splay.Accounting
