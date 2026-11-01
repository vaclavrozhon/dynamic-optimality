import SharperDyadicCompressionRealization
import HistoricalCompressionRecursion

/-! A sharper-cap unconditional coefficient recurrence using the capped dyadic
compiler. It preserves the exact shape constants and constructs an actual
initialized trace at every recursive use. -/

namespace Splay.Research.SharperDyadicCompressionRecursion

open Splay.Interface HistoricalCompressionRecursion

noncomputable section

def cutoff (b R : ℕ) : ℕ := Nat.clog 2 (2*b*(6*R-4)+1)

def insertionCoefficient (a b R : ℕ) : ℕ := 2*a+2*b*(4*R-2)+1

def variationCoefficient (shape : Shape) (b R : ℕ) : ℕ :=
  8*b*((1+shape.growingLimit)*
    (shape.exemptPasses+shape.matchingDenominator*cutoff b R)+1)

theorem numerical_transfer (shape : Shape) (a b R A I V : ℕ)
    (realizations : ∀ k : ℕ, ∃ newV late : ℕ,
      A ≤ a*I+b*newV ∧
      newV ≤ (4*R-2)*I+
        4*(((1+shape.growingLimit)*
          (shape.exemptPasses+shape.matchingDenominator*k)+1)*V)+
        (6*R-4)*late ∧
      2^k*late ≤ A+I) :
    A ≤ insertionCoefficient a b R*I+variationCoefficient shape b R*V := by
  obtain ⟨newV,late,activity,compression,tail⟩ := realizations (cutoff b R)
  have power := Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) (2*b*(6*R-4)+1)
  have coefficient : 2*b*(6*R-4) ≤ 2^cutoff b R := by
    unfold cutoff
    omega
  have scaledCompression := Nat.mul_le_mul_left b compression
  have scaledTail := Nat.mul_le_mul_right late coefficient
  unfold insertionCoefficient variationCoefficient
  nlinarith only [activity, scaledCompression, scaledTail, tail]

def boost (shape : Shape) (coefficients : ℕ → ℕ × ℕ) (G : ℕ) : ℕ × ℕ :=
  let R := SharperDyadicCompressionRowBudget.cap G
  let inner := coefficients R
  (insertionCoefficient inner.1 inner.2 R,
    variationCoefficient shape inner.2 R)

theorem transfer (shape : Shape) (coefficients : ℕ → ℕ × ℕ)
    (bound : CoefficientBound shape coefficients) :
    CoefficientBound shape (boost shape coefficients) := by
  intro params sameShape n initial final operations initialState original
  apply numerical_transfer shape
    (coefficients (SharperDyadicCompressionRowBudget.cap params.valueBound)).1
    (coefficients (SharperDyadicCompressionRowBudget.cap params.valueBound)).2
    (SharperDyadicCompressionRowBudget.cap params.valueBound)
    (totalActivity operations) (totalInserts operations) (totalValueChanges operations)
  intro k
  let cutoffValue := ArbitrarySourceTail.threshold params k
  obtain ⟨finalLabels,finalLedger,finalClock,finalEvents,snapshots,liftedOperations,
      timed,newInitial,lifted,activity,growth,inserts,variation⟩ :=
    SharperDyadicCompressionRealization.from_initial_trace initialState original cutoffValue
  refine ⟨totalValueChanges liftedOperations,
    ActualCompressionRowBudget.lateCount cutoffValue snapshots, ?_, ?_, ?_⟩
  · have newShape : (SharperDyadicCompressionRealization.parameters params).toShape = shape :=
      sameShape
    have newBound := bound _ newShape newInitial lifted
    rw [activity,inserts] at newBound
    exact newBound
  · have originalShape : params.growingLimit = shape.growingLimit ∧
        params.exemptPasses = shape.exemptPasses ∧
        params.matchingDenominator = shape.matchingDenominator := by
      exact ⟨congrArg Shape.growingLimit sameShape,
        congrArg Shape.exemptPasses sameShape,
        congrArg Shape.matchingDenominator sameShape⟩
    dsimp [cutoffValue, ArbitrarySourceTail.threshold] at variation
    rw [originalShape.1,originalShape.2.1,originalShape.2.2] at variation
    simpa [cutoffValue, ArbitrarySourceTail.threshold, originalShape.2.1,
      originalShape.2.2, DyadicCompressionRowBudget.lateCount,
      ActualCompressionRowBudget.lateCount] using variation
  · exact HistoricalCompressionTail.timed_tail_bound initialState timed k

def coefficients (shape : Shape) (ci cv : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, G => (ci*G, cv*Nat.clog 2 G)
  | depth+1, G => boost shape (coefficients shape ci cv depth) G

theorem all_depths (shape : Shape) :
    ∃ ci cv : ℕ, 0 < ci ∧ 0 < cv ∧ ∀ depth : ℕ,
      CoefficientBound shape (coefficients shape ci cv depth) := by
  obtain ⟨ci,cv,ciPositive,cvPositive,coarse⟩ := Splay.Interface.activityBound shape
  refine ⟨ci,cv,ciPositive,cvPositive,?_⟩
  intro depth
  induction depth with
  | zero => exact coarse
  | succ depth ih => exact transfer shape _ ih

end

#print axioms numerical_transfer
#print axioms transfer
#print axioms all_depths

end Splay.Research.SharperDyadicCompressionRecursion
