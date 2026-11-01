import Splay.Accounting.NormalFormAutomaticBendHistory
import Splay.Accounting.RealizedWitnessedThreeLaw
import Splay.Accounting.WholeSplayRestorationGeometry
import Splay.Accounting.WholeSplayTemporaryBoundaryGeometry
import Splay.Accounting.WholeSplayTemporaryCoreClassification
import Splay.Accounting.WholeSplayTemporaryCoreGeometry
import Splay.Accounting.WholeSplayTemporaryCreationGeometry
import Splay.Accounting.WholeSplayTemporaryAutomaticPersistence
import Splay.Accounting.WholeSplayTemporaryFocusedRemoval
import Splay.Accounting.WholeSplayTemporaryRemovalGeometry

namespace Splay.Accounting.WholeSplayTemporaryGeometry

open Splay.Rank
open Splay.Tree.BST
open Splay.Assumptions.NormalForm
open Splay.Assumptions.NormalForm.ComparisonTrace
open Splay.Accounting.LocalBendGeometry
open Splay.Accounting.WholeSplayTemporaryPriorityReduction
open Splay.Accounting.WholeSplayTemporaryBoundaryGeometry
open Splay.Accounting.WholeSplayTemporaryCoreClassification
open Splay.Accounting.WholeSplayTemporaryCoreGeometry
open Splay.Accounting.WholeSplayTemporaryCreationGeometry
open Splay.Accounting.WholeSplayTemporaryFocusedRemoval
open Splay.Accounting.WholeSplayTemporaryRemovalGeometry
open Splay.Accounting.WholeSplayRestorationGeometry

/--
The proof-relevant core-splay endpoint classification after boundary
selection, preprocessing, rank restoration, and both final-spine persistence
arguments have been made automatic.

The boundary positions are definitionally the true-rank minima of the
accessed node's actual left and right child intervals in `before`.  Thus this
type cannot be instantiated with the false ordered-only weakening.
-/
abbrev CanonicalEndpointHitClassification
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : comparison.HasRoot key.val) :=
  let transcript := splayExecutionTranscriptWitness execution
  let selection :=
    KeyFocus.boundaryMinimumSelection
      (Snapshot.ofTree comparison) before key
  EndpointHitClassification transcript
    (temporarySnapshot comparison key comparisonRoot
      selection.left selection.right selection.ordered)

/--
Minimal numerical form of the canonical temporary-core theorem.

The companion classification module proves that these two sharp endpoint
cardinality inequalities are equivalent to supplying the finite
administrative/winner/victim maps used below.  Both inequalities are
constructed automatically by `CanonicalSpinePersistence.canonicalEndpointBounds`;
the structure remains as a compatibility and decomposition interface.
-/
structure CanonicalEndpointBounds
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : comparison.HasRoot key.val) : Prop where
  created_le :
    let transcript := splayExecutionTranscriptWitness execution
    let selection :=
      KeyFocus.boundaryMinimumSelection
        (Snapshot.ofTree comparison) before key
    ((bends
        (temporarySnapshot comparison key comparisonRoot
          selection.left selection.right selection.ordered)
        after) \
      (bends
        (temporarySnapshot comparison key comparisonRoot
          selection.left selection.right selection.ordered)
        before)).card ≤
      transcript.zigZig + 2
  zigZag_le_removed :
    let transcript := splayExecutionTranscriptWitness execution
    let selection :=
      KeyFocus.boundaryMinimumSelection
        (Snapshot.ofTree comparison) before key
    transcript.zigZag ≤
      ((bends
          (temporarySnapshot comparison key comparisonRoot
            selection.left selection.right selection.ordered)
          before) \
        (bends
          (temporarySnapshot comparison key comparisonRoot
          selection.left selection.right selection.ordered)
          after)).card

/--
Geometric form of canonical endpoint persistence.

Creation-side persistence and final nonmembership of the concrete search-turn
keys are both constructed automatically.  The one-field structure remains a
useful proof boundary for compatibility clients.
-/
structure CanonicalSpinePersistence
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : comparison.HasRoot key.val) : Type where
  finalSearchTurnsAbsent :
    let selection :=
      KeyFocus.boundaryMinimumSelection
        (Snapshot.ofTree comparison) before key
    ∀ turn ∈ searchTurnKeys before key.val,
      turn ∉
        bends
          (temporarySnapshot comparison key comparisonRoot
            selection.left selection.right selection.ordered)
          after

namespace CanonicalSpinePersistence

/--
Derived creation certificate.  It does not depend on the removal witness:
the canonical complete execution supplies it automatically.
-/
noncomputable def creation
    {n : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {comparisonRoot : comparison.HasRoot key.val}
    (_persistence :
      CanonicalSpinePersistence
        comparison key execution comparisonRoot) :
    let transcript := splayExecutionTranscriptWitness execution
    let selection :=
      KeyFocus.boundaryMinimumSelection
        (Snapshot.ofTree comparison) before key
    FinalSpinePersistence transcript
      (temporarySnapshot comparison key comparisonRoot
        selection.left selection.right selection.ordered) :=
  Splay.Accounting.WholeSplayTemporaryAutomaticPersistence.AutomaticCanonicalPersistence.canonicalFinalSpinePersistence
    comparison key comparisonRoot execution

/--
Construct the one-field public interface from the remaining final-search-turn
nonmembership statement.
-/
noncomputable def ofFinalSearchTurnsAbsent
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : comparison.HasRoot key.val)
    (finalSearchTurnsAbsent :
      let selection :=
        KeyFocus.boundaryMinimumSelection
          (Snapshot.ofTree comparison) before key
      ∀ turn ∈ searchTurnKeys before key.val,
        turn ∉
          bends
            (temporarySnapshot comparison key comparisonRoot
              selection.left selection.right selection.ordered)
            after) :
    CanonicalSpinePersistence
      comparison key execution comparisonRoot where
  finalSearchTurnsAbsent := finalSearchTurnsAbsent

/--
Every complete canonical splay automatically supplies both creation and
removal persistence.  No per-execution geometric premise remains.
-/
noncomputable def canonical
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : comparison.HasRoot key.val) :
    CanonicalSpinePersistence
      comparison key execution comparisonRoot :=
  ofFinalSearchTurnsAbsent
    comparison key execution comparisonRoot
      (canonical_finalSearchTurnsAbsent
        comparison key comparisonRoot execution)

/--
Automatic creation persistence plus the removal witness discharge the
minimal endpoint-bounds interface.
-/
theorem toEndpointBounds
    {n : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {comparisonRoot : comparison.HasRoot key.val}
    (persistence :
      CanonicalSpinePersistence
        comparison key execution comparisonRoot) :
    CanonicalEndpointBounds
      comparison key execution comparisonRoot where
  created_le :=
    canonical_created_le comparison key execution comparisonRoot
      persistence.creation
  zigZag_le_removed :=
    canonical_zigZag_le_removed_of_finalSearchTurnsAbsent
      comparison key execution comparisonRoot
        persistence.finalSearchTurnsAbsent

/--
Compatibility constructor: removal-side final nonmembership alone is enough
for both canonical endpoint cardinality bounds.
-/
theorem endpointBoundsOfFinalSearchTurnsAbsent
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : comparison.HasRoot key.val)
    (finalSearchTurnsAbsent :
      let selection :=
        KeyFocus.boundaryMinimumSelection
          (Snapshot.ofTree comparison) before key
      ∀ turn ∈ searchTurnKeys before key.val,
        turn ∉
          bends
            (temporarySnapshot comparison key comparisonRoot
              selection.left selection.right selection.ordered)
            after) :
    CanonicalEndpointBounds
      comparison key execution comparisonRoot :=
  (ofFinalSearchTurnsAbsent
    comparison key execution comparisonRoot
      finalSearchTurnsAbsent).toEndpointBounds

/--
The sharp canonical endpoint bounds are now theorem-level consequences of
an arbitrary complete splay execution.
-/
theorem canonicalEndpointBounds
    {n : ℕ} (comparison : BST 0 n) (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : comparison.HasRoot key.val) :
    CanonicalEndpointBounds
      comparison key execution comparisonRoot :=
  (canonical comparison key execution comparisonRoot).toEndpointBounds

end CanonicalSpinePersistence

namespace CanonicalEndpointBounds

/--
The two numerical bounds construct the proof-relevant finite classification;
no causal interpretation of the chosen finite embeddings is assumed.
-/
noncomputable def toEndpointHitClassification
    {n : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    {comparisonRoot : comparison.HasRoot key.val}
    (bounds :
      CanonicalEndpointBounds
        comparison key execution comparisonRoot) :
    CanonicalEndpointHitClassification
      comparison key execution comparisonRoot := by
  exact
    endpointHitClassificationOfBounds
      bounds.created_le bounds.zigZag_le_removed

end CanonicalEndpointBounds

/--
Assemble a complete numerical bend certificate for one access from only the
finite winner/hit classification of its temporary-priority core.

Everything else is constructed here:

* the exact `x⁻`/`x⁺` boundary minima;
* invariance of the pre-splay bend set;
* both true-rank restoration chains;
* the three-phase bend telescope; and
* the local allowance `2 + 6 * (slack + 1)`.
-/
noncomputable def completeSplayCertificate
    {constants : BendConstants}
    {n slack : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    (comparisonRoot : comparison.HasRoot key.val)
    (classification :
      CanonicalEndpointHitClassification
        comparison key execution comparisonRoot)
    (neighborBound :
      HasRelevantNeighborRankBound
        (Snapshot.ofTree comparison) slack)
    (allowance :
      2 + 6 * (slack + 1) ≤ constants.splay) :
    NormalFormChronologicalBendHistory.CompleteSplayCertificate
      constants comparison key execution := by
  let transcript := splayExecutionTranscriptWitness execution
  let selection :=
    KeyFocus.boundaryMinimumSelection
      (Snapshot.ofTree comparison) before key
  let restoration :=
    canonicalTwoBoundaryRestoration comparison key comparisonRoot
      selection.left selection.right selection.ordered after
  let core :
      TemporarySplayBendCertificate.CoreTwoCertificate
        constants comparison key execution comparisonRoot transcript
        selection.left selection.right selection.ordered
        (rightBoundaryTemporarySnapshot comparison key comparisonRoot
          selection.right selection.ordered.2) :=
    TemporarySplayBendCertificate.ofBoundaryMinima
      selection
      (before_bends_eq_temporarySnapshot
        comparison key comparisonRoot before)
      classification.created_le_zigZig_add_two
      classification.zigZag_le_removed
      restoration
  exact
    core.toCompleteSplayCertificate
      neighborBound allowance

/--
Minimal-bounds variant of `completeSplayCertificate`.

This is the weakest public per-access interface: only the two sharp endpoint
cardinality inequalities remain; all finite maps and all surrounding
geometry are reconstructed.
-/
noncomputable def completeSplayCertificateOfBounds
    {constants : BendConstants}
    {n slack : ℕ} {comparison : BST 0 n} {key : Fin n}
    {before after : BST 0 n}
    {execution : SplayExecution key.val before after}
    (comparisonRoot : comparison.HasRoot key.val)
    (bounds :
      CanonicalEndpointBounds
        comparison key execution comparisonRoot)
    (neighborBound :
      HasRelevantNeighborRankBound
        (Snapshot.ofTree comparison) slack)
    (allowance :
      2 + 6 * (slack + 1) ≤ constants.splay) :
    NormalFormChronologicalBendHistory.CompleteSplayCertificate
      constants comparison key execution :=
  completeSplayCertificate comparisonRoot
    bounds.toEndpointHitClassification neighborBound allowance

/--
The exact remaining local input, uniformly over a comparison trace.

For every complete splay carried out while a comparison state serves its
root key, this provider supplies only the canonical finite endpoint-hit
classification.  In particular, it does not expose boundary selection,
preprocessing, restoration, or comparison-segment obligations.
-/
abbrev CanonicalEndpointHitClassificationProvider
    {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses} :=
  ∀ (time : Fin (trace.rotationCount + 1))
    (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : (trace.state time).HasRoot key.val),
    CanonicalEndpointHitClassification
      (trace.state time) key execution comparisonRoot

/-- Trace-wide provider of the minimal pair of canonical endpoint bounds. -/
abbrev CanonicalEndpointBoundsProvider
    {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses} :=
  ∀ (time : Fin (trace.rotationCount + 1))
    (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : (trace.state time).HasRoot key.val),
    CanonicalEndpointBounds
      (trace.state time) key execution comparisonRoot

/-- Trace-wide provider of the sole remaining final-search-turn fact. -/
abbrev CanonicalSpinePersistenceProvider
    {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses} :=
  ∀ (time : Fin (trace.rotationCount + 1))
    (key : Fin n)
    {before after : BST 0 n}
    (execution : SplayExecution key.val before after)
    (comparisonRoot : (trace.state time).HasRoot key.val),
    CanonicalSpinePersistence
      (trace.state time) key execution comparisonRoot

/--
Every comparison trace has the canonical spine-persistence provider.  The
provider is a theorem-level consequence of each supplied complete splay
execution, not an additional normal-form assumption.
-/
noncomputable def canonicalSpinePersistenceProvider
    {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses} :
    CanonicalSpinePersistenceProvider (trace := trace) := by
  intro time key before after execution comparisonRoot
  exact
    CanonicalSpinePersistence.canonical
      (trace.state time) key execution comparisonRoot

/-- Premise-free trace-wide provider of the two sharp endpoint bounds. -/
theorem canonicalEndpointBoundsProvider
    {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses} :
    CanonicalEndpointBoundsProvider (trace := trace) := by
  intro time key before after execution comparisonRoot
  exact
    CanonicalSpinePersistence.canonicalEndpointBounds
      (trace.state time) key execution comparisonRoot

/--
Convert the geometric spine provider into the minimal numerical provider.
-/
theorem endpointBoundsProviderOfSpinePersistence
    {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses}
    (provider : CanonicalSpinePersistenceProvider (trace := trace)) :
    CanonicalEndpointBoundsProvider (trace := trace) := by
  intro time key before after execution comparisonRoot
  exact
    CanonicalSpinePersistence.toEndpointBounds
      (provider time key execution comparisonRoot)

/--
Turn the minimal numerical provider into the finite classification provider
used by the existing integration path.
-/
noncomputable def endpointHitClassificationProviderOfBounds
    {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses}
    (provider : CanonicalEndpointBoundsProvider (trace := trace)) :
    CanonicalEndpointHitClassificationProvider (trace := trace) := by
  intro time key before after execution comparisonRoot
  exact
    CanonicalEndpointBounds.toEndpointHitClassification
      (provider time key execution comparisonRoot)

/--
Premise-free trace-wide finite endpoint classification.  The finite maps are
reconstructed from the automatic sharp cardinality bounds.
-/
noncomputable def canonicalEndpointHitClassificationProvider
    {n : ℕ} {accesses : List (Fin n)}
    {trace : ComparisonTrace n accesses} :
    CanonicalEndpointHitClassificationProvider (trace := trace) :=
  endpointHitClassificationProviderOfBounds
    canonicalEndpointBoundsProvider

/--
Lift the canonical endpoint-hit provider to the complete-splay provider
consumed by the chronological normal-form scheduler.

Structural normality supplies the neighboring true-rank bound at the exact
comparison time; `completeSplayCertificate` constructs every remaining
temporary-priority phase.
-/
noncomputable def completeSplayCertificateProvider
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    (normal : IsStructurallyNormal bounds trace)
    (classificationProvider :
      CanonicalEndpointHitClassificationProvider (trace := trace))
    (allowance :
      2 + 6 * (bounds.neighborDepthSlack + 1) ≤ constants.splay) :
    NormalFormAutomaticBendHistory.SplayOnlyScheduleCertificate.CompleteSplayCertificateProvider
      constants (trace := trace) := by
  intro time key before after execution comparisonRoot
  exact
    completeSplayCertificate comparisonRoot
      (classificationProvider time key execution comparisonRoot)
      (normal.state_neighborRankBound time) allowance

/--
Trace-wide complete-splay provider from only the two canonical endpoint
cardinality inequalities at each access.
-/
noncomputable def completeSplayCertificateProviderOfBounds
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    (normal : IsStructurallyNormal bounds trace)
    (provider : CanonicalEndpointBoundsProvider (trace := trace))
    (allowance :
      2 + 6 * (bounds.neighborDepthSlack + 1) ≤ constants.splay) :
    NormalFormAutomaticBendHistory.SplayOnlyScheduleCertificate.CompleteSplayCertificateProvider
      constants (trace := trace) :=
  completeSplayCertificateProvider normal
    (endpointHitClassificationProviderOfBounds provider) allowance

/--
Complete-splay provider from final search-turn absence at each access;
creation persistence is reconstructed automatically.
-/
noncomputable def completeSplayCertificateProviderOfSpinePersistence
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    (normal : IsStructurallyNormal bounds trace)
    (provider : CanonicalSpinePersistenceProvider (trace := trace))
    (allowance :
      2 + 6 * (bounds.neighborDepthSlack + 1) ≤ constants.splay) :
    NormalFormAutomaticBendHistory.SplayOnlyScheduleCertificate.CompleteSplayCertificateProvider
      constants (trace := trace) :=
  completeSplayCertificateProviderOfBounds normal
    (endpointBoundsProviderOfSpinePersistence provider) allowance

/--
Premise-free complete-splay certificate provider.  Structural normality and
the numerical allowance are now the only inputs; all temporary endpoint
geometry is reconstructed internally.
-/
noncomputable def canonicalCompleteSplayCertificateProvider
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    (normal : IsStructurallyNormal bounds trace)
    (allowance :
      2 + 6 * (bounds.neighborDepthSlack + 1) ≤ constants.splay) :
    NormalFormAutomaticBendHistory.SplayOnlyScheduleCertificate.CompleteSplayCertificateProvider
      constants (trace := trace) :=
  completeSplayCertificateProviderOfBounds normal
    canonicalEndpointBoundsProvider allowance

/--
Attach the sole remaining endpoint-hit provider to any exact normal-form
schedule.

The schedule recursion, request-group recursion, every comparison segment,
both temporary-boundary restoration phases, and the local numerical
telescope are all reconstructed automatically.
-/
noncomputable def splayOnlyScheduleCertificate
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : BST 0 n}
    (schedule : Schedule trace groups time before after)
    (classificationProvider :
      CanonicalEndpointHitClassificationProvider (trace := trace))
    (allowance :
      2 + 6 * (bounds.neighborDepthSlack + 1) ≤ constants.splay) :
    NormalFormAutomaticBendHistory.SplayOnlyScheduleCertificate
      constants normal schedule :=
  NormalFormAutomaticBendHistory.SplayOnlyScheduleCertificate.ofScheduleWithCompleteProvider
    schedule
      (completeSplayCertificateProvider normal
        classificationProvider allowance)

/--
Minimal-bounds version of `splayOnlyScheduleCertificate`.
-/
noncomputable def splayOnlyScheduleCertificateOfBounds
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : BST 0 n}
    (schedule : Schedule trace groups time before after)
    (provider : CanonicalEndpointBoundsProvider (trace := trace))
    (allowance :
      2 + 6 * (bounds.neighborDepthSlack + 1) ≤ constants.splay) :
    NormalFormAutomaticBendHistory.SplayOnlyScheduleCertificate
      constants normal schedule :=
  NormalFormAutomaticBendHistory.SplayOnlyScheduleCertificate.ofScheduleWithCompleteProvider
    schedule
      (completeSplayCertificateProviderOfBounds normal
        provider allowance)

/--
Attach automatic complete-splay geometry to any exact normal-form schedule.
No endpoint classification or persistence provider remains in the API.
-/
noncomputable def canonicalSplayOnlyScheduleCertificate
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {before after : BST 0 n}
    (schedule : Schedule trace groups time before after)
    (allowance :
      2 + 6 * (bounds.neighborDepthSlack + 1) ≤ constants.splay) :
    NormalFormAutomaticBendHistory.SplayOnlyScheduleCertificate
      constants normal schedule :=
  NormalFormAutomaticBendHistory.SplayOnlyScheduleCertificate.ofScheduleWithCompleteProvider
    schedule (canonicalCompleteSplayCertificateProvider normal allowance)

/--
End-to-end chronological bend witness from the canonical endpoint-hit
provider and the two uniform numerical allowances.

No comparison-step certificate, boundary witness, preprocessing equality,
or restoration chain appears in this public interface.
-/
noncomputable def concreteZigZagBendWitness
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {before after : BST 0 n}
    (schedule : Schedule trace groups 0 before after)
    (classificationProvider :
      CanonicalEndpointHitClassificationProvider (trace := trace))
    (splayAllowance :
      2 + 6 * (bounds.neighborDepthSlack + 1) ≤ constants.splay)
    (comparisonAllowance : 3 ≤ constants.comparisonRotation)
    (requests_eq : schedule.servedRequests = accesses)
    (initialUnit : 1 ≤ constants.initial) :
    ConcreteZigZagBendWitness constants before accesses trace :=
  NormalFormAutomaticBendHistory.SplayOnlyScheduleCertificate.toConcreteZigZagBendWitness
      (normal := normal)
      (splayOnlyScheduleCertificate (normal := normal) schedule
        classificationProvider splayAllowance)
      comparisonAllowance requests_eq initialUnit

/--
End-to-end chronological bend witness from only the minimal endpoint-bounds
provider.
-/
noncomputable def concreteZigZagBendWitnessOfBounds
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {before after : BST 0 n}
    (schedule : Schedule trace groups 0 before after)
    (provider : CanonicalEndpointBoundsProvider (trace := trace))
    (splayAllowance :
      2 + 6 * (bounds.neighborDepthSlack + 1) ≤ constants.splay)
    (comparisonAllowance : 3 ≤ constants.comparisonRotation)
    (requests_eq : schedule.servedRequests = accesses)
    (initialUnit : 1 ≤ constants.initial) :
    ConcreteZigZagBendWitness constants before accesses trace :=
  NormalFormAutomaticBendHistory.SplayOnlyScheduleCertificate.toConcreteZigZagBendWitness
      (normal := normal)
      (splayOnlyScheduleCertificateOfBounds (normal := normal) schedule
        provider splayAllowance)
      comparisonAllowance requests_eq initialUnit

/--
End-to-end chronological bend witness with all per-access geometry supplied
automatically.
-/
noncomputable def canonicalConcreteZigZagBendWitness
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {before after : BST 0 n}
    (schedule : Schedule trace groups 0 before after)
    (splayAllowance :
      2 + 6 * (bounds.neighborDepthSlack + 1) ≤ constants.splay)
    (comparisonAllowance : 3 ≤ constants.comparisonRotation)
    (requests_eq : schedule.servedRequests = accesses)
    (initialUnit : 1 ≤ constants.initial) :
    ConcreteZigZagBendWitness constants before accesses trace :=
  NormalFormAutomaticBendHistory.SplayOnlyScheduleCertificate.toConcreteZigZagBendWitness
    (normal := normal)
    (canonicalSplayOnlyScheduleCertificate schedule splayAllowance)
    comparisonAllowance requests_eq initialUnit

/--
Specialization to the initialized rich normal-form schedule already used by
`RealizedWitnessedThreeLawCertificate`.

This closes the provenance handoff for the bend component: the returned
witness is definitionally about the same comparison trace, initial splay
tree, and request list as the realized rich execution.
-/
noncomputable def initializedRealizedBendWitness
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {params : Interface.Parameters}
    {initialTree : BST 0 n}
    (normal : IsStructurallyNormal bounds trace)
    (realized :
      InitializedRealizedNormalFormSchedule
        params initialTree trace)
    (classificationProvider :
      CanonicalEndpointHitClassificationProvider (trace := trace))
    (splayAllowance :
      2 + 6 * (bounds.neighborDepthSlack + 1) ≤ constants.splay)
    (comparisonAllowance : 3 ≤ constants.comparisonRotation)
    (initialUnit : 1 ≤ constants.initial) :
    ConcreteZigZagBendWitness
      constants initialTree accesses trace :=
  concreteZigZagBendWitness
    (normal := normal) realized.schedule
    classificationProvider splayAllowance comparisonAllowance
    realized.servedRequests_eq initialUnit

/--
Initialized-rich-schedule specialization from the minimal endpoint-bounds
provider.
-/
noncomputable def initializedRealizedBendWitnessOfBounds
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {params : Interface.Parameters}
    {initialTree : BST 0 n}
    (normal : IsStructurallyNormal bounds trace)
    (realized :
      InitializedRealizedNormalFormSchedule
        params initialTree trace)
    (provider : CanonicalEndpointBoundsProvider (trace := trace))
    (splayAllowance :
      2 + 6 * (bounds.neighborDepthSlack + 1) ≤ constants.splay)
    (comparisonAllowance : 3 ≤ constants.comparisonRotation)
    (initialUnit : 1 ≤ constants.initial) :
    ConcreteZigZagBendWitness
      constants initialTree accesses trace :=
  concreteZigZagBendWitnessOfBounds
    (normal := normal) realized.schedule
    provider splayAllowance comparisonAllowance
    realized.servedRequests_eq initialUnit

/--
Initialized realized bend witness directly from the two geometric
final-spine facts at each access.
-/
noncomputable def initializedRealizedBendWitnessOfSpinePersistence
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {params : Interface.Parameters}
    {initialTree : BST 0 n}
    (normal : IsStructurallyNormal bounds trace)
    (realized :
      InitializedRealizedNormalFormSchedule
        params initialTree trace)
    (provider : CanonicalSpinePersistenceProvider (trace := trace))
    (splayAllowance :
      2 + 6 * (bounds.neighborDepthSlack + 1) ≤ constants.splay)
    (comparisonAllowance : 3 ≤ constants.comparisonRotation)
    (initialUnit : 1 ≤ constants.initial) :
    ConcreteZigZagBendWitness
      constants initialTree accesses trace :=
  initializedRealizedBendWitnessOfBounds normal realized
    (endpointBoundsProviderOfSpinePersistence provider)
    splayAllowance comparisonAllowance initialUnit

/--
The initialized realized schedule carries a complete chronological bend
witness without any endpoint provider.
-/
noncomputable def canonicalInitializedRealizedBendWitness
    {constants : BendConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {params : Interface.Parameters}
    {initialTree : BST 0 n}
    (normal : IsStructurallyNormal bounds trace)
    (realized :
      InitializedRealizedNormalFormSchedule
        params initialTree trace)
    (splayAllowance :
      2 + 6 * (bounds.neighborDepthSlack + 1) ≤ constants.splay)
    (comparisonAllowance : 3 ≤ constants.comparisonRotation)
    (initialUnit : 1 ≤ constants.initial) :
    ConcreteZigZagBendWitness
      constants initialTree accesses trace :=
  canonicalConcreteZigZagBendWitness
    (normal := normal) realized.schedule
    splayAllowance comparisonAllowance
    realized.servedRequests_eq initialUnit

/--
Direct global zig-zag/bend inequality with the entire normal-form accounting
pipeline reconstructed from the sole canonical endpoint-hit provider.
-/
theorem concrete_zigZag_bends
    {constants : BendConstants}
    {n nearCost bendsBound : ℕ}
    {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {before after : BST 0 n}
    (schedule : Schedule trace groups 0 before after)
    (classificationProvider :
      CanonicalEndpointHitClassificationProvider (trace := trace))
    (splayAllowance :
      2 + 6 * (bounds.neighborDepthSlack + 1) ≤ constants.splay)
    (comparisonAllowance : 3 ≤ constants.comparisonRotation)
    (requests_eq : schedule.servedRequests = accesses)
    (initialUnit : 1 ≤ constants.initial)
    (comparisonCost_le : trace.cost ≤ nearCost)
    (coefficient_le : constants.coefficient ≤ bendsBound) :
    (concreteSplayTranscript before accesses).zigZag ≤
      (concreteSplayTranscript before accesses).zigZig +
        bendsBound * (n + nearCost) :=
  NormalFormAutomaticBendHistory.SplayOnlyScheduleCertificate.concrete_zigZag_bends
      (normal := normal)
      (splayOnlyScheduleCertificate (normal := normal) schedule
        classificationProvider splayAllowance)
      comparisonAllowance requests_eq initialUnit
      comparisonCost_le coefficient_le

/--
Direct global zig-zag/bend inequality from only the minimal endpoint-bounds
provider.
-/
theorem concrete_zigZag_bends_of_bounds
    {constants : BendConstants}
    {n nearCost bendsBound : ℕ}
    {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {before after : BST 0 n}
    (schedule : Schedule trace groups 0 before after)
    (provider : CanonicalEndpointBoundsProvider (trace := trace))
    (splayAllowance :
      2 + 6 * (bounds.neighborDepthSlack + 1) ≤ constants.splay)
    (comparisonAllowance : 3 ≤ constants.comparisonRotation)
    (requests_eq : schedule.servedRequests = accesses)
    (initialUnit : 1 ≤ constants.initial)
    (comparisonCost_le : trace.cost ≤ nearCost)
    (coefficient_le : constants.coefficient ≤ bendsBound) :
    (concreteSplayTranscript before accesses).zigZag ≤
      (concreteSplayTranscript before accesses).zigZig +
        bendsBound * (n + nearCost) :=
  NormalFormAutomaticBendHistory.SplayOnlyScheduleCertificate.concrete_zigZag_bends
      (normal := normal)
      (splayOnlyScheduleCertificateOfBounds (normal := normal) schedule
        provider splayAllowance)
      comparisonAllowance requests_eq initialUnit
      comparisonCost_le coefficient_le

/--
Direct global zig-zag/bend inequality with every per-access temporary
endpoint obligation discharged automatically.
-/
theorem canonical_concrete_zigZag_bends
    {constants : BendConstants}
    {n nearCost bendsBound : ℕ}
    {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    {normal : IsStructurallyNormal bounds trace}
    {groups : List (RequestGroup trace)}
    {before after : BST 0 n}
    (schedule : Schedule trace groups 0 before after)
    (splayAllowance :
      2 + 6 * (bounds.neighborDepthSlack + 1) ≤ constants.splay)
    (comparisonAllowance : 3 ≤ constants.comparisonRotation)
    (requests_eq : schedule.servedRequests = accesses)
    (initialUnit : 1 ≤ constants.initial)
    (comparisonCost_le : trace.cost ≤ nearCost)
    (coefficient_le : constants.coefficient ≤ bendsBound) :
    (concreteSplayTranscript before accesses).zigZag ≤
      (concreteSplayTranscript before accesses).zigZig +
        bendsBound * (n + nearCost) :=
  NormalFormAutomaticBendHistory.SplayOnlyScheduleCertificate.concrete_zigZag_bends
    (normal := normal)
    (canonicalSplayOnlyScheduleCertificate schedule splayAllowance)
    comparisonAllowance requests_eq initialUnit
    comparisonCost_le coefficient_le

end Splay.Accounting.WholeSplayTemporaryGeometry
