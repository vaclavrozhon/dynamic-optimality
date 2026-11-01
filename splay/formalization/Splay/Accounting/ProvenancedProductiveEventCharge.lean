import Splay.Accounting.ScheduleExecutionProvenance
import Splay.Accounting.RealizedProductiveEventCharge

namespace Splay.Accounting

open Splay.Assumptions.NormalForm

namespace ProvenancedInitializedRealizedNormalFormSchedule

/--
Canonical productive classification on the exact execution whose recursive
comparison/splay/rotation decomposition is retained by schedule provenance.
-/
def canonicalProductiveClassification
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : ComparisonTrace n accesses}
    (provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison) :
    ProductiveEventClassification
      (Lazy.eraseOperations
        provenanced.realized.execution.events) :=
  provenanced.realized.canonicalProductiveClassification

/--
Premise-free productive-event charge on the exact initialized execution
indexed by the supplied normal-form schedule provenance.
-/
theorem canonicalProductiveCharge
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : ComparisonTrace n accesses}
    (provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison) :
    ProductiveEventBudget
      (Lazy.eraseOperations
        provenanced.realized.execution.events)
      (provenanced.canonicalProductiveClassification.paidSlots.length)
      (provenanced.canonicalProductiveClassification.unimportantSlots.length) :=
  provenanced.realized.canonicalProductiveCharge

/--
Exact schedule-provenanced form of
`totalInserts + totalIncreases ≤ paid + unimportant`.
-/
theorem productiveChargeOfClassification
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : ComparisonTrace n accesses}
    (provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison)
    (classification :
      ProductiveEventClassification
        (Lazy.eraseOperations
          provenanced.realized.execution.events))
    {paid unimportant : ℕ}
    (paid_le : classification.paidSlots.length ≤ paid)
    (unimportant_le :
      classification.unimportantSlots.length ≤ unimportant) :
    ProductiveEventBudget
      (Lazy.eraseOperations
        provenanced.realized.execution.events)
      paid unimportant :=
  provenanced.realized.productiveChargeOfClassification
    classification paid_le unimportant_le

/--
Every classified productive slot is an actual visible insert/increase of the
same execution that carries the recursive schedule, splay-step, and ordinary
rotation provenance.
-/
theorem productiveSlot_richStep
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : ComparisonTrace n accesses}
    (provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison)
    (classification :
      ProductiveEventClassification
        (Lazy.eraseOperations
          provenanced.realized.execution.events))
    {index : ℕ}
    (member :
      index ∈ classification.paidSlots ∨
        index ∈ classification.unimportantSlots) :
    ∃ eventIndex before operation after,
      Lazy.Trace.VisibleStepAt
          provenanced.realized.execution.trace
          index eventIndex before operation after ∧
        Interface.Operation.Productive operation :=
  provenanced.realized.productiveSlot_richStep
    classification member

/--
Schedule-provenanced integration endpoint for the witnessed potential
residue.  The only nonautomatic data are exactly the value/gap comparison
and the two semantic envelope estimates; the operation list and rich trace
cannot be chosen independently of the realized schedule.
-/
def witnessedEnvelopePotentialResidueOfClassification
    {constants : TranslationConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : ComparisonTrace n accesses}
    (provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison)
    (nearCost height : ℕ)
    (valueBound_le : params.valueBound ≤ gapBound height)
    (classification :
      ProductiveEventClassification
        (Lazy.eraseOperations
          provenanced.realized.execution.events))
    (paid_le :
      classification.paidSlots.length ≤
        paidEnvelope constants n nearCost height
          (unimportantEnvelope constants height
            (Interface.totalActivity
              (Lazy.eraseOperations
                provenanced.realized.execution.events))))
    (unimportant_le :
      classification.unimportantSlots.length ≤
        unimportantEnvelope constants height
          (Interface.totalActivity
            (Lazy.eraseOperations
              provenanced.realized.execution.events))) :
    WitnessedEnvelopePotentialResidue constants params
      (Lazy.eraseOperations
        provenanced.realized.execution.events)
      nearCost height :=
  provenanced.realized.witnessedEnvelopePotentialResidueOfClassification
    nearCost height valueBound_le classification
      paid_le unimportant_le

end ProvenancedInitializedRealizedNormalFormSchedule

end Splay.Accounting
