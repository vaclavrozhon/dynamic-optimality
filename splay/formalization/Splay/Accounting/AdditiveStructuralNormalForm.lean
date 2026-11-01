import Splay.Accounting.OfflineConnectedNormalization
import Splay.Accounting.StructuralWitnessedEndpoint

/-!
# Structural normal form with initialization cost

The simulator may build its initial representation in linear time. Its cost
bound therefore includes the universe size, as the final `TargetBound` already
does. The selected comparison trace and all intermediate structural invariants
are unchanged; the new allowance occurs only in the cost inequality.
-/

namespace Splay.Assumptions.NormalForm

/-- Structural normal form allowing a linear initialization charge. -/
def AdditiveStructuralHypothesis (model : CostModel) : Prop :=
  ∃ bounds : StructuralBounds,
    ∀ (n : ℕ), 0 < n → ∀ accesses : List (Fin n),
      ∃ trace : ComparisonTrace n accesses,
        IsStructurallyNormal bounds trace ∧
          trace.cost ≤ bounds.costMultiplier * (model.optCost accesses + n)

/-- One fixed choice of traces, including their full structural certificates. -/
structure AdditiveStructuralRealization (model : CostModel) where
  bounds : StructuralBounds
  trace : ∀ (n : ℕ), 0 < n → ∀ accesses : List (Fin n), ComparisonTrace n accesses
  isStructurallyNormal : ∀ n n_pos accesses,
    IsStructurallyNormal bounds (trace n n_pos accesses)
  cost_le : ∀ n n_pos accesses,
    (trace n n_pos accesses).cost ≤ bounds.costMultiplier * (model.optCost accesses + n)

noncomputable def AdditiveStructuralHypothesis.realize {model : CostModel}
    (hypothesis : AdditiveStructuralHypothesis model) :
    AdditiveStructuralRealization model := by
  classical
  let bounds := Classical.choose hypothesis
  have certificates := Classical.choose_spec hypothesis
  exact
    { bounds
      trace := fun n n_pos accesses => Classical.choose (certificates n n_pos accesses)
      isStructurallyNormal := fun n n_pos accesses =>
        (Classical.choose_spec (certificates n n_pos accesses)).1
      cost_le := fun n n_pos accesses =>
        (Classical.choose_spec (certificates n n_pos accesses)).2 }

/-- Existing stronger realizations can be used without changing their trace. -/
def StructuralRealization.toAdditive {model : CostModel}
    (realization : StructuralRealization model) : AdditiveStructuralRealization model where
  bounds := realization.bounds
  trace := realization.trace
  isStructurallyNormal := realization.isStructurallyNormal
  cost_le := fun n n_pos accesses => (realization.cost_le n n_pos accesses).trans
    (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))

theorem StructuralHypothesis.toAdditive {model : CostModel}
    (hypothesis : StructuralHypothesis model) : AdditiveStructuralHypothesis model := by
  obtain ⟨bounds, certificates⟩ := hypothesis
  refine ⟨bounds, ?_⟩
  intro n n_pos accesses
  obtain ⟨trace, normal, cost⟩ := certificates n n_pos accesses
  exact ⟨trace, normal, cost.trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))⟩

namespace AdditiveStructuralRealization

def comparisonProfile {model : CostModel}
    (realization : AdditiveStructuralRealization model) : ComparisonProfile where
  cost := fun {n} accesses =>
    if n_pos : 0 < n then (realization.trace n n_pos accesses).cost else 0
  maxHeight := fun {n} _ => realization.bounds.heightMultiplier * Analysis.stabilizedLog n

theorem hasNormalFormBound {model : CostModel}
    (realization : AdditiveStructuralRealization model) :
    HasNormalFormBound model realization.comparisonProfile := by
  refine ⟨realization.bounds.costMultiplier, realization.bounds.costMultiplier_pos, ?_⟩
  intro n n_pos accesses
  simpa only [comparisonProfile, dif_pos n_pos] using realization.cost_le n n_pos accesses

theorem trace_height_le_profile {model : CostModel}
    (realization : AdditiveStructuralRealization model)
    {n : ℕ} (n_pos : 0 < n) (accesses : List (Fin n))
    (time : Fin ((realization.trace n n_pos accesses).rotationCount + 1)) :
    ((realization.trace n n_pos accesses).state time).height ≤
      realization.comparisonProfile.maxHeight accesses :=
  (realization.isStructurallyNormal n n_pos accesses).height_le time

theorem state_neighborRankBound {model : CostModel}
    (realization : AdditiveStructuralRealization model)
    {n : ℕ} (n_pos : 0 < n) (accesses : List (Fin n))
    (time : Fin ((realization.trace n n_pos accesses).rotationCount + 1)) :
    HasRelevantNeighborRankBound
      (Rank.Snapshot.ofTree ((realization.trace n n_pos accesses).state time))
      realization.bounds.neighborDepthSlack :=
  (realization.isStructurallyNormal n n_pos accesses).state_neighborRankBound time

theorem hasHeightFactorBound {model : CostModel}
    (realization : AdditiveStructuralRealization model) :
    HasHeightFactorBound realization.comparisonProfile := by
  refine ⟨Analysis.heightFactorConstant realization.bounds.heightMultiplier, ?_, ?_⟩
  · unfold Analysis.heightFactorConstant
    positivity
  · intro n _ accesses
    exact Analysis.heightFactor_le_targetFactor realization.bounds.heightMultiplier n
      (realization.bounds.heightMultiplier * Analysis.stabilizedLog n) le_rfl

theorem requestCostDominates {model : CostModel}
    (realization : AdditiveStructuralRealization model) :
    Accounting.RequestCostDominates realization.comparisonProfile := by
  intro n n_pos accesses
  simp [comparisonProfile, ComparisonTrace.cost, n_pos]

/-- The initialization allowance feeds the existing, unchanged target theorem. -/
theorem targetBound_of_core {model : CostModel}
    (realization : AdditiveStructuralRealization model)
    (core : HasCoreAnalysisBound model realization.comparisonProfile) :
    TargetBound model :=
  targetBound_of_conditional_layers model realization.comparisonProfile
    realization.hasNormalFormBound core realization.hasHeightFactorBound

end AdditiveStructuralRealization
end Splay.Assumptions.NormalForm

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Assumptions.NormalForm

/-- Remaining structural simulation, with its one-time initialization charge. -/
def UniformAdditiveConnectedExecutionStructuralSimulator : Prop :=
  ∃ bounds : StructuralBounds,
    ∀ (n : ℕ), 0 < n → ∀ (accesses : List (Fin n))
      (before after : BST 0 n) (rotations supportCharge : ℕ),
      ConnectedExecution accesses before after rotations supportCharge →
        ∃ target : ComparisonTrace n accesses,
          IsStructurallyNormal bounds target ∧
            target.cost ≤ bounds.costMultiplier *
              (accesses.length + rotations + supportCharge + n)

theorem UniformConnectedExecutionStructuralSimulator.toAdditive
    (simulator : UniformConnectedExecutionStructuralSimulator) :
    UniformAdditiveConnectedExecutionStructuralSimulator := by
  obtain ⟨bounds, simulate⟩ := simulator
  refine ⟨bounds, ?_⟩
  intro n n_pos accesses before after rotations charge execution
  obtain ⟨trace, normal, cost⟩ := simulate n n_pos accesses before after rotations charge execution
  exact ⟨trace, normal, cost.trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))⟩

/-- Postponement already supplies the first stage; only the structural
simulator remains as an input to this composition theorem. -/
theorem additiveStructuralHypothesis_of_simulator
    (simulator : UniformAdditiveConnectedExecutionStructuralSimulator) :
    AdditiveStructuralHypothesis OfflineOptimum.concreteOfflineCostModel := by
  obtain ⟨bounds, simulate⟩ := simulator
  let composed : StructuralBounds :=
    { bounds with
      costMultiplier := bounds.costMultiplier * 2
      costMultiplier_pos := Nat.mul_pos bounds.costMultiplier_pos (by decide) }
  refine ⟨composed, ?_⟩
  intro n n_pos accesses
  obtain ⟨before, after, rotations, execution, costEq⟩ :=
    OfflineOptimum.exists_optimalExecution_eq accesses
  obtain ⟨connectedAfter, kept, charge, connected, keptBound, chargeBound⟩ :=
    exists_connectedReordered execution
  obtain ⟨target, normal, cost⟩ :=
    simulate n n_pos accesses before connectedAfter kept charge connected
  refine ⟨target, ?_, ?_⟩
  · exact
      { normal :=
          { height_le := normal.height_le
            rotationDepth_le := normal.rotationDepth_le }
        relevantNeighborDepth_le := normal.relevantNeighborDepth_le }
  · change target.cost ≤ (bounds.costMultiplier * 2) *
      (OfflineOptimum.offlineOptCost accesses + n)
    calc
      target.cost ≤ bounds.costMultiplier * (accesses.length + kept + charge + n) := cost
      _ ≤ bounds.costMultiplier * (2 * (OfflineOptimum.offlineOptCost accesses + n)) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring

end Splay.Accounting.OfflineConnectedSupport
