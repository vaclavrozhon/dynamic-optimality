import HistoricalCompressionRealization
import HistoricalCompressionTail
import HistoricalCompressionNatEndpoint
import HistoricalCompressionRange
import Splay.Interface.InitialColumnIncidenceAssembly

/-! The compressed activity theorem for every actual initialized strict
interface trace. No temporal histories, transformed traces, or incidence
certificates are premises: all are constructed from Initial and Trace. -/

namespace Splay.Research.HistoricalCompressionInterface

open Splay.Interface
open HistoricalCompressionRange

def compressionConstant (shape : Shape) : ℕ :=
  686*((1+shape.growingLimit)*(shape.exemptPasses+shape.matchingDenominator)+1)+80

theorem numerical_budget (shape : Shape) (R I V late k newV : ℕ) (rankPositive : 1 ≤ R)
    (budget : newV ≤ 38*R*I+
      686*(((1+shape.growingLimit)*(shape.exemptPasses+shape.matchingDenominator*k)+1)*V)+
      (40*R+2)*late) :
    newV ≤ compressionConstant shape*(R*I+(k+1)*V+R*late) := by
  let B := (1+shape.growingLimit)*(shape.exemptPasses+shape.matchingDenominator)+1
  have cutoffBase : shape.exemptPasses+shape.matchingDenominator*k ≤
      (shape.exemptPasses+shape.matchingDenominator)*(k+1) := by
    nlinarith only [Nat.mul_le_mul_left shape.exemptPasses (show 1 ≤ k+1 by omega),
      Nat.zero_le shape.matchingDenominator]
  have cutoff : (1+shape.growingLimit)*(shape.exemptPasses+shape.matchingDenominator*k)+1 ≤
      B*(k+1) := by
    have scaled := Nat.mul_le_mul_left (1+shape.growingLimit) cutoffBase
    dsimp [B]
    nlinarith only [scaled, Nat.zero_le k]
  have tail : 40*R+2 ≤ 42*R := by omega
  have first : 38 ≤ compressionConstant shape := by unfold compressionConstant; omega
  have second : 686*B ≤ compressionConstant shape := by unfold compressionConstant; dsimp [B]; omega
  have third : 42 ≤ compressionConstant shape := by unfold compressionConstant; omega
  calc
    newV ≤ 38*R*I+686*(B*(k+1)*V)+(42*R)*late := by
      apply budget.trans
      gcongr
    _ = 38*(R*I)+(686*B)*((k+1)*V)+42*(R*late) := by ring
    _ ≤ compressionConstant shape*(R*I)+compressionConstant shape*((k+1)*V)+
        compressionConstant shape*(R*late) := by gcongr
    _ = _ := by ring

/-- Uniform coefficients precede the arbitrary cap and actual execution. -/
theorem activity_bound (shape : Shape) :
    ∃ C : ℕ, 0 < C ∧ ∀ params : Parameters, params.toShape = shape →
      ∀ {n : ℕ} {initial final : State n} {operations : List (Operation n)},
      initial.Initial params → Trace params initial operations final →
      totalActivity operations ≤ C*(totalInserts operations*range params.valueBound*
        logarithm params.valueBound + totalValueChanges operations*(logarithm params.valueBound)^2) := by
  obtain ⟨ci,cv,ciPositive,cvPositive,coarse⟩ := Splay.Interface.activityBound shape
  obtain ⟨C,positive,endpoint⟩ := HistoricalCompressionNatEndpoint.uniform_activity_endpoint
    ci cv (compressionConstant shape)
  refine ⟨C,positive,?_⟩
  intro params sameShape n initial final operations initialState original
  apply endpoint (totalActivity operations) (totalInserts operations)
    (totalValueChanges operations) (ActualCompressionRowBudget.cap params.valueBound)
  intro k
  let cutoff := ArbitrarySourceTail.threshold params k
  obtain ⟨finalLabels,finalLedger,finalClock,finalEvents,snapshots,liftedOperations,
      timed,newInitial,lifted,activity,growth,inserts,variation⟩ :=
    HistoricalCompressionRealization.from_initial_trace initialState original cutoff
  refine ⟨totalValueChanges liftedOperations,
    ActualCompressionRowBudget.lateCount cutoff snapshots, ?_, ?_, ?_⟩
  · have newShape : (HistoricalCompressionRealization.parameters params).toShape = shape := sameShape
    have bound := coarse _ newShape newInitial lifted
    rw [activity,inserts] at bound
    exact bound
  · have originalShape : params.growingLimit = shape.growingLimit ∧
        params.exemptPasses = shape.exemptPasses ∧
        params.matchingDenominator = shape.matchingDenominator := by
      exact ⟨congrArg Shape.growingLimit sameShape,
        congrArg Shape.exemptPasses sameShape, congrArg Shape.matchingDenominator sameShape⟩
    dsimp [cutoff, ArbitrarySourceTail.threshold] at variation
    rw [originalShape.1,originalShape.2.1,originalShape.2.2] at variation
    dsimp [cutoff, ArbitrarySourceTail.threshold]
    rw [originalShape.2.1,originalShape.2.2]
    exact numerical_budget shape _ _ _ _ k _
      (HistoricalRankCompression.natLabel_positive params.valueBound) variation
  · exact HistoricalCompressionTail.timed_tail_bound initialState timed k

#print axioms activity_bound

end Splay.Research.HistoricalCompressionInterface
