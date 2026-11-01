import Splay.Accounting.ProvenancedProductiveEventObstruction

namespace Splay.Accounting

@[simp]
theorem productiveEvents_append
    {n : ℕ} (first second : List (Interface.Operation n)) :
    productiveEvents (first ++ second) =
      productiveEvents first + productiveEvents second := by
  simp [productiveEvents, Interface.totalInserts,
    Interface.totalIncreases]
  omega

@[simp]
theorem productiveEvents_eraseOperations_append
    {n : ℕ} (first second : List (Lazy.Event n)) :
    productiveEvents (Lazy.eraseOperations (first ++ second)) =
      productiveEvents (Lazy.eraseOperations first) +
        productiveEvents (Lazy.eraseOperations second) := by
  rw [Lazy.eraseOperations_append, productiveEvents_append]

open Assumptions.NormalForm
open Assumptions.NormalForm.ComparisonTrace

namespace ScheduleProductiveCost

/--
The minimal cost-sensitive strengthening of recursive schedule provenance.

For each schedule node it authenticates exactly the facts hidden by the
current existential local realizer APIs:

* the comparison prefix has productive cost proportional to the number of
  comparison rotations consumed at that node; and
* the fixed-snapshot splay prefix has no productive operations.

The recursive field excludes productive padding in every tail.  The
initialization prefix is handled separately below.
-/
def Holds
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {trace : ComparisonTrace n accesses}
    (coefficient height : ℕ)
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {beforeTree afterTree : Tree.BST 0 n}
    {schedule :
      Schedule trace groups time beforeTree afterTree}
    {initial : Lazy.State n}
    {execution :
      Lazy.RepresentedTransition params
        (Rank.Snapshot.ofTree (trace.state time)) beforeTree
        (Rank.Snapshot.ofTree trace.finalTree) afterTree initial}
    (provenance :
      Schedule.RepresentedTransitionProvenance
        schedule execution) : Prop :=
  match provenance with
  | .finish _tree _comparison comparisonTransition _ =>
      productiveEvents
          (Lazy.eraseOperations comparisonTransition.events) ≤
        coefficient * schedule.comparisonRotationCount *
          gapLog height
  | .next _ordered _comparison _splay tail
      comparisonTransition _comparisonProvenance
      splayTransition _splayProvenance
      _tailTransition tailProvenance =>
      productiveEvents
          (Lazy.eraseOperations comparisonTransition.events) ≤
          coefficient *
            (schedule.comparisonRotationCount -
              tail.comparisonRotationCount) *
            gapLog height ∧
        productiveEvents
            (Lazy.eraseOperations splayTransition.events) = 0 ∧
          Holds coefficient height tailProvenance

/--
The local cost-sensitive facts add up to the advertised global transition
bound.
-/
theorem transition_le
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {trace : ComparisonTrace n accesses}
    {coefficient height : ℕ}
    {groups : List (RequestGroup trace)}
    {time : Fin (trace.rotationCount + 1)}
    {beforeTree afterTree : Tree.BST 0 n}
    {schedule :
      Schedule trace groups time beforeTree afterTree}
    {initial : Lazy.State n}
    {execution :
      Lazy.RepresentedTransition params
        (Rank.Snapshot.ofTree (trace.state time)) beforeTree
        (Rank.Snapshot.ofTree trace.finalTree) afterTree initial}
    (provenance :
      Schedule.RepresentedTransitionProvenance
        schedule execution)
    (cost : Holds coefficient height provenance) :
    productiveEvents (Lazy.eraseOperations execution.events) ≤
      coefficient * schedule.comparisonRotationCount *
        gapLog height := by
  induction provenance with
  | finish =>
      exact cost
  | @next group groups startTime beforeTree middleTree afterTree
      ordered comparison splay tail initial
      comparisonTransition comparisonProvenance
      splayTransition splayProvenance
      tailTransition tailProvenance ih =>
      rcases cost with ⟨comparisonBound, splayZero, tailCost⟩
      have tailBound := ih tailCost
      change
        productiveEvents
          (Lazy.eraseOperations
            ((comparisonTransition.events ++
              splayTransition.events) ++
                tailTransition.events)) ≤
          coefficient *
            ((group.time.val - startTime.val) +
              tail.comparisonRotationCount) *
            gapLog height
      rw [productiveEvents_eraseOperations_append,
        productiveEvents_eraseOperations_append, splayZero,
        add_zero]
      have tailCount_le :
          tail.comparisonRotationCount ≤
            (group.time.val - startTime.val) +
              tail.comparisonRotationCount := by
        omega
      have prefixDifference :
          (group.time.val - startTime.val +
              tail.comparisonRotationCount) -
                tail.comparisonRotationCount =
            group.time.val - startTime.val := by
        omega
      simp only
        [Schedule.comparisonRotationCount,
          prefixDifference] at comparisonBound
      calc
        productiveEvents
              (Lazy.eraseOperations comparisonTransition.events) +
            productiveEvents
              (Lazy.eraseOperations tailTransition.events) ≤
            coefficient * (group.time.val - startTime.val) *
                gapLog height +
              coefficient * tail.comparisonRotationCount *
                gapLog height :=
          Nat.add_le_add comparisonBound tailBound
        _ = coefficient *
              ((group.time.val - startTime.val) +
                tail.comparisonRotationCount) *
              gapLog height := by ring

end ScheduleProductiveCost

namespace ProvenancedInitializedRealizedNormalFormSchedule

/--
Cost-sensitive productive provenance for an initialized realized schedule.

This is the exact minimal realizer change exposed by the padding obstruction:
authenticate the initialization count and the recursive local event
generators.  No semantic paid/unimportant classification is stored.
-/
structure CostSensitiveProductiveProvenance
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : ComparisonTrace n accesses}
    (provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison)
    (coefficient height : ℕ) : Prop where
  initialization_le :
    productiveEvents
        (Lazy.eraseOperations
          provenanced.realized.execution.initialization.events) ≤
      coefficient * n * gapLog height
  transition :
    ScheduleProductiveCost.Holds coefficient height
      provenanced.provenance.transitionProvenance

namespace CostSensitiveProductiveProvenance

/-- The authenticated local bounds imply one global initialized count bound. -/
theorem productiveEvents_le
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : ComparisonTrace n accesses}
    {provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison}
    {coefficient height : ℕ}
    (cost :
      CostSensitiveProductiveProvenance
        provenanced coefficient height) :
    productiveEvents
        (Lazy.eraseOperations
          provenanced.realized.execution.events) ≤
      coefficient *
        (n + provenanced.realized.schedule.comparisonRotationCount) *
        gapLog height := by
  have transitionBound :=
    ScheduleProductiveCost.transition_le
      provenanced.provenance.transitionProvenance cost.transition
  rw [Lazy.InitializedTransition.events,
    productiveEvents_eraseOperations_append]
  calc
    productiveEvents
          (Lazy.eraseOperations
            provenanced.realized.execution.initialization.events) +
        productiveEvents
          (Lazy.eraseOperations
            provenanced.realized.execution.transition.events) ≤
        coefficient * n * gapLog height +
          coefficient *
            provenanced.realized.schedule.comparisonRotationCount *
            gapLog height :=
      Nat.add_le_add cost.initialization_le transitionBound
    _ = coefficient *
          (n +
            provenanced.realized.schedule.comparisonRotationCount) *
          gapLog height := by ring

/--
Once the comparison cost is bounded by `nearCost` and the chosen semantic paid
constant dominates the local coefficient, the exact semantic productive
charge is automatic.  Its unimportant class is empty, so `local_charge` is
proved rather than assumed.
-/
def toSemanticProductiveCharge
    {constants : TranslationConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : ComparisonTrace n accesses}
    {provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison}
    {coefficient nearCost height : ℕ}
    (cost :
      CostSensitiveProductiveProvenance
        provenanced coefficient height)
    (coefficient_le :
      coefficient ≤ constants.semantic.paid)
    (comparisonCost_le : comparison.cost ≤ nearCost) :
    provenanced.SemanticProductiveCharge
      constants nearCost height := by
  apply provenanced.semanticProductiveChargeOfProductiveBound
  have rotationCount_le :
      provenanced.realized.schedule.comparisonRotationCount ≤
        nearCost := by
    rw [provenanced.realized.comparisonRotationCount_eq]
    exact
      (Nat.le_add_left comparison.rotationCount accesses.length).trans
        comparisonCost_le
  calc
    productiveEvents
          (Lazy.eraseOperations
            provenanced.realized.execution.events) ≤
        coefficient *
          (n +
            provenanced.realized.schedule.comparisonRotationCount) *
          gapLog height :=
      cost.productiveEvents_le
    _ ≤ coefficient * (n + nearCost) * gapLog height :=
      Nat.mul_le_mul_right _
        (Nat.mul_le_mul_left coefficient
          (Nat.add_le_add_left rotationCount_le n))
    _ ≤ constants.semantic.paid * (n + nearCost) *
          gapLog height :=
      Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right _ coefficient_le)

/-- Cost-sensitive schedule provenance integrates directly into the potential residue. -/
def toWitnessedEnvelopePotentialResidue
    {constants : TranslationConstants}
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {initialTree : Tree.BST 0 n}
    {comparison : ComparisonTrace n accesses}
    {provenanced :
      ProvenancedInitializedRealizedNormalFormSchedule
        params initialTree comparison}
    {coefficient nearCost height : ℕ}
    (cost :
      CostSensitiveProductiveProvenance
        provenanced coefficient height)
    (coefficient_le :
      coefficient ≤ constants.semantic.paid)
    (comparisonCost_le : comparison.cost ≤ nearCost)
    (valueBound_le : params.valueBound ≤ gapBound height) :
    WitnessedEnvelopePotentialResidue constants params
      (Lazy.eraseOperations
        provenanced.realized.execution.events)
      nearCost height :=
  provenanced.witnessedEnvelopePotentialResidueOfSemanticCharge
    nearCost height valueBound_le
    (cost.toSemanticProductiveCharge
      coefficient_le comparisonCost_le)

end CostSensitiveProductiveProvenance

end ProvenancedInitializedRealizedNormalFormSchedule

end Splay.Accounting
