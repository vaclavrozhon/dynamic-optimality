import HistoricalCompressionInterface

/-!
Repeated literal compression, with all depth-dependent constants retained.

The coefficient recurrence below is a theorem for every depth, not an
assumption about projected histories. Each use constructs a new initialized
strict trace and absorbs that use's own late-source term.
-/

namespace Splay.Research.HistoricalCompressionRecursion

open Splay.Interface

noncomputable section

def cutoff (b K R : ℕ) : ℕ := Nat.clog 2 (2*b*K*R+1)

def insertionCoefficient (a b K R : ℕ) : ℕ := 2*a+2*b*K*R+1

def variationCoefficient (b K R : ℕ) : ℕ := 2*b*K*(cutoff b K R+1)

/-- One transfer step for arbitrary numerical coefficients. -/
theorem numerical_transfer (a b K R A I V : ℕ)
    (realizations : ∀ k : ℕ, ∃ newV late : ℕ,
      A ≤ a*I+b*newV ∧
      newV ≤ K*(R*I+(k+1)*V+R*late) ∧
      2^k*late ≤ A+I) :
    A ≤ insertionCoefficient a b K R*I+variationCoefficient b K R*V := by
  obtain ⟨newV,late,activity,compression,tail⟩ := realizations (cutoff b K R)
  have power := Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) (2*b*K*R+1)
  have coefficient : 2*b*K*R ≤ 2^cutoff b K R := by
    unfold cutoff
    omega
  have scaledCompression := Nat.mul_le_mul_left b compression
  have scaledTail := Nat.mul_le_mul_right late coefficient
  unfold insertionCoefficient variationCoefficient
  nlinarith only [activity, scaledCompression, scaledTail, tail]

/-- A coefficient function valid for every initialized strict interface trace
of the fixed shape. -/
def CoefficientBound (shape : Shape) (coefficients : ℕ → ℕ × ℕ) : Prop :=
  ∀ params : Parameters, params.toShape = shape →
    ∀ {n : ℕ} {initial final : State n} {operations : List (Operation n)},
    initial.Initial params → Trace params initial operations final →
    totalActivity operations ≤
      (coefficients params.valueBound).1*totalInserts operations+
      (coefficients params.valueBound).2*totalValueChanges operations

def boost (K : ℕ) (coefficients : ℕ → ℕ × ℕ) (G : ℕ) : ℕ × ℕ :=
  let inner := coefficients (HistoricalCompressionRange.range G)
  let R := ActualCompressionRowBudget.cap G
  (insertionCoefficient inner.1 inner.2 K R,
    variationCoefficient inner.2 K R)

/-- No new trace or ledger certificate is a premise. -/
theorem transfer (shape : Shape) (coefficients : ℕ → ℕ × ℕ)
    (bound : CoefficientBound shape coefficients) :
    CoefficientBound shape
      (boost (HistoricalCompressionInterface.compressionConstant shape) coefficients) := by
  intro params sameShape n initial final operations initialState original
  apply numerical_transfer
    (coefficients (HistoricalCompressionRange.range params.valueBound)).1
    (coefficients (HistoricalCompressionRange.range params.valueBound)).2
    (HistoricalCompressionInterface.compressionConstant shape)
    (ActualCompressionRowBudget.cap params.valueBound)
    (totalActivity operations) (totalInserts operations) (totalValueChanges operations)
  intro k
  let cutoffValue := ArbitrarySourceTail.threshold params k
  obtain ⟨finalLabels,finalLedger,finalClock,finalEvents,snapshots,liftedOperations,
      timed,newInitial,lifted,activity,growth,inserts,variation⟩ :=
    HistoricalCompressionRealization.from_initial_trace initialState original cutoffValue
  refine ⟨totalValueChanges liftedOperations,
    ActualCompressionRowBudget.lateCount cutoffValue snapshots, ?_, ?_, ?_⟩
  · have newShape : (HistoricalCompressionRealization.parameters params).toShape = shape :=
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
    dsimp [cutoffValue, ArbitrarySourceTail.threshold]
    rw [originalShape.2.1,originalShape.2.2]
    exact HistoricalCompressionInterface.numerical_budget shape _ _ _ _ k _
      (HistoricalRankCompression.natLabel_positive params.valueBound) variation
  · exact HistoricalCompressionTail.timed_tail_bound initialState timed k

def coefficients (ci cv K : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, G => (ci*G, cv*Nat.clog 2 G)
  | depth+1, G => boost K (coefficients ci cv K depth) G

/-- The constants ci and cv are selected once, before the depth and cap.
Consequently the exact recurrence is valid even for a depth chosen from the
cap; estimating that recurrence requires retaining its depth dependence. -/
theorem all_depths (shape : Shape) :
    ∃ ci cv : ℕ, 0 < ci ∧ 0 < cv ∧ ∀ depth : ℕ,
      CoefficientBound shape
        (coefficients ci cv (HistoricalCompressionInterface.compressionConstant shape) depth) := by
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

end Splay.Research.HistoricalCompressionRecursion
