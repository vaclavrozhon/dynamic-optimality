import Splay.Accounting.RealizedWitnessedThreeLaw

namespace Splay.Accounting

/-
This module closes the purely extensional part of productive-event
accounting on the exact event list of a realized schedule.  It deliberately
does not manufacture the manuscript's paid-envelope estimate: the final
section gives a checked legal-trace counterexample showing why that stronger
claim needs genuine charging semantics.
-/

namespace ProductiveEventClassification

/--
The canonical premise-free productive-event classification: charge every
actual insert/increase index to the paid class and leave the unimportant
class empty.

This is useful as the strongest unconditional classification.  It is not a
claim that all of these slots satisfy the manuscript's paid envelope.
-/
def allPaid
    {n : ℕ} (operations : List (Interface.Operation n)) :
    ProductiveEventClassification operations where
  paidSlots := productiveOperationIndices operations
  unimportantSlots := []
  partition := by simp

@[simp]
theorem allPaid_paidSlots
    {n : ℕ} (operations : List (Interface.Operation n)) :
    (allPaid operations).paidSlots =
      productiveOperationIndices operations :=
  rfl

@[simp]
theorem allPaid_unimportantSlots
    {n : ℕ} (operations : List (Interface.Operation n)) :
    (allPaid operations).unimportantSlots = [] :=
  rfl

/--
Any checked productive classification proves the exact, rather than merely
inequality-valued, productive-event charge.
-/
theorem exact_charge
    {n : ℕ} {operations : List (Interface.Operation n)}
    (classification : ProductiveEventClassification operations) :
    Interface.totalInserts operations +
        Interface.totalIncreases operations =
      classification.paidSlots.length +
        classification.unimportantSlots.length := by
  exact classification.counts_eq.symm

/-- Forget the exact partition and retain the public count-only residue. -/
theorem toProductiveEventBudget
    {n : ℕ} {operations : List (Interface.Operation n)}
    (classification : ProductiveEventClassification operations) :
    ProductiveEventBudget operations
      classification.paidSlots.length
      classification.unimportantSlots.length := by
  unfold ProductiveEventBudget
  exact Nat.le_of_eq classification.exact_charge

/--
The exact partition charges the realized productive count to any larger
semantic paid and unimportant counts.
-/
theorem toProductiveEventBudget_of_bounds
    {n : ℕ} {operations : List (Interface.Operation n)}
    (classification : ProductiveEventClassification operations)
    {paid unimportant : ℕ}
    (paid_le : classification.paidSlots.length ≤ paid)
    (unimportant_le :
      classification.unimportantSlots.length ≤ unimportant) :
    ProductiveEventBudget operations paid unimportant := by
  unfold ProductiveEventBudget
  calc
    productiveEvents operations =
        classification.paidSlots.length +
          classification.unimportantSlots.length :=
      classification.counts_eq.symm
    _ ≤ paid + unimportant :=
      Nat.add_le_add paid_le unimportant_le

/-- The premise-free all-paid classification charges every productive event. -/
theorem allPaid_toProductiveEventBudget
    {n : ℕ} (operations : List (Interface.Operation n)) :
    ProductiveEventBudget operations
      (allPaid operations).paidSlots.length
      (allPaid operations).unimportantSlots.length :=
  (allPaid operations).toProductiveEventBudget

end ProductiveEventClassification

namespace InitializedRealizedNormalFormSchedule

/--
Canonical productive classification of the exact erased event list carried
by this realized normal-form schedule.
-/
def canonicalProductiveClassification
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : Assumptions.NormalForm.ComparisonTrace n accesses}
    (realized :
      InitializedRealizedNormalFormSchedule
        params initialTree comparison) :
    ProductiveEventClassification
      (Lazy.eraseOperations realized.execution.events) :=
  ProductiveEventClassification.allPaid
    (Lazy.eraseOperations realized.execution.events)

/--
The exact realized trace satisfies the productive-event charge
unconditionally when `paid` is the length of its canonical paid-slot list
and `unimportant` is the corresponding empty list.
-/
theorem canonicalProductiveCharge
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : Assumptions.NormalForm.ComparisonTrace n accesses}
    (realized :
      InitializedRealizedNormalFormSchedule
        params initialTree comparison) :
    ProductiveEventBudget
      (Lazy.eraseOperations realized.execution.events)
      (realized.canonicalProductiveClassification.paidSlots.length)
      (realized.canonicalProductiveClassification.unimportantSlots.length) :=
  realized.canonicalProductiveClassification.toProductiveEventBudget

/--
General realized-schedule charge endpoint.  A checked classification plus
upper bounds on its two concrete slot lists proves
`totalInserts + totalIncreases ≤ paid + unimportant` on the exact realized
operation list.
-/
theorem productiveChargeOfClassification
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : Assumptions.NormalForm.ComparisonTrace n accesses}
    (realized :
      InitializedRealizedNormalFormSchedule
        params initialTree comparison)
    (classification :
      ProductiveEventClassification
        (Lazy.eraseOperations realized.execution.events))
    {paid unimportant : ℕ}
    (paid_le : classification.paidSlots.length ≤ paid)
    (unimportant_le :
      classification.unimportantSlots.length ≤ unimportant) :
    ProductiveEventBudget
      (Lazy.eraseOperations realized.execution.events)
      paid unimportant :=
  classification.toProductiveEventBudget_of_bounds
    paid_le unimportant_le

/--
Every slot of any checked productive classification on the realized event
list names a genuine visible insert/increase step of that same rich
execution, including its actual rich pre- and post-states.
-/
theorem productiveSlot_richStep
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : Assumptions.NormalForm.ComparisonTrace n accesses}
    (realized :
      InitializedRealizedNormalFormSchedule
        params initialTree comparison)
    (classification :
      ProductiveEventClassification
        (Lazy.eraseOperations realized.execution.events))
    {index : ℕ}
    (member :
      index ∈ classification.paidSlots ∨
        index ∈ classification.unimportantSlots) :
    ∃ eventIndex before operation after,
      Lazy.Trace.VisibleStepAt realized.execution.trace
          index eventIndex before operation after ∧
        Interface.Operation.Productive operation := by
  have inClasses :
      index ∈
        classification.paidSlots ++
          classification.unimportantSlots := by
    simpa only [List.mem_append] using member
  have inCanonical :
      index ∈ productiveOperationIndices
        (Lazy.eraseOperations realized.execution.events) :=
    classification.partition.mem_iff.mp inClasses
  exact
    exists_richProductiveStep
      realized.execution.trace inCanonical

/--
Exact integration endpoint for the existing witnessed potential API.

Once a semantic construction supplies the two envelope inequalities, the
classification is tied definitionally to the realized schedule's event list;
no free trace or extra count-only productive-event premise remains.
-/
def witnessedEnvelopePotentialResidueOfClassification
    {constants : TranslationConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : Assumptions.NormalForm.ComparisonTrace n accesses}
    (realized :
      InitializedRealizedNormalFormSchedule
        params initialTree comparison)
    (nearCost height : ℕ)
    (valueBound_le : params.valueBound ≤ gapBound height)
    (classification :
      ProductiveEventClassification
        (Lazy.eraseOperations realized.execution.events))
    (paid_le :
      classification.paidSlots.length ≤
        paidEnvelope constants n nearCost height
          (unimportantEnvelope constants height
            (Interface.totalActivity
              (Lazy.eraseOperations realized.execution.events))))
    (unimportant_le :
      classification.unimportantSlots.length ≤
        unimportantEnvelope constants height
          (Interface.totalActivity
            (Lazy.eraseOperations realized.execution.events))) :
    WitnessedEnvelopePotentialResidue constants params
      (Lazy.eraseOperations realized.execution.events)
      nearCost height where
  valueBound_le := valueBound_le
  productiveClassification :=
    { classification := classification
      paid_le := paid_le
      unimportant_le := unimportant_le }

end InitializedRealizedNormalFormSchedule

/-
A legal trace alone cannot provide the envelope-bounded paid/unimportant
classification.  The single productive increase below has zero activity,
while the chosen legal translation constants permit neither a paid nor an
unimportant slot.
-/
namespace ProductiveEnvelopeCounterexample

open PotentialBudgetCounterexample

def translationConstants : TranslationConstants where
  semantic := PotentialBudgetCounterexample.constants
  interface_pos := by decide

theorem no_envelopeClassification :
    ¬ Nonempty
      (EnvelopeProductiveEventClassification
        translationConstants
        ([.valueChange PotentialBudgetCounterexample.element .increase] :
          List (Interface.Operation 1))
        0 0) := by
  rintro ⟨classification⟩
  have paidZero :
      classification.classification.paidSlots.length = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa [paidEnvelope, unimportantEnvelope,
      unimportantChargeCoefficient, translationConstants,
      PotentialBudgetCounterexample.constants,
      Interface.totalActivity, Interface.Operation.activity] using
      classification.paid_le
  have unimportantZero :
      classification.classification.unimportantSlots.length = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa [unimportantEnvelope, unimportantChargeCoefficient,
      translationConstants, PotentialBudgetCounterexample.constants,
      Interface.totalActivity, Interface.Operation.activity] using
      classification.unimportant_le
  have exact :=
    classification.classification.exact_charge
  simp only [paidZero, unimportantZero, add_zero] at exact
  norm_num [Interface.totalInserts, Interface.totalIncreases,
    Interface.Operation.insertCount,
    Interface.Operation.increaseCount] at exact

/--
Kernel-checked specification boundary: even with a genuine initialized legal
trace, envelope classification is not forced without semantic charging data.
-/
theorem legalTrace_does_not_force_envelopeClassification :
    (∃ (params : Interface.Parameters)
        (initial final : Interface.State 1),
      initial.Initial params ∧
        Interface.Trace params initial
          ([.valueChange PotentialBudgetCounterexample.element .increase] :
            List (Interface.Operation 1))
          final) ∧
      ¬ Nonempty
        (EnvelopeProductiveEventClassification
          translationConstants
          ([.valueChange PotentialBudgetCounterexample.element .increase] :
            List (Interface.Operation 1))
          0 0) := by
  constructor
  · exact
      ⟨minimalParameters PotentialBudgetCounterexample.shape,
        emptyPotentialState 1,
        PotentialBudgetCounterexample.increasedState,
        emptyPotentialState_initial
          PotentialBudgetCounterexample.shape 1,
        PotentialBudgetCounterexample.increase_trace⟩
  · exact no_envelopeClassification

end ProductiveEnvelopeCounterexample

end Splay.Accounting
