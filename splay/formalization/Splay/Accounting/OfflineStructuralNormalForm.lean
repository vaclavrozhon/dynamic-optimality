import Splay.Accounting.OfflineNormalForm
import Splay.Accounting.OfflineStructuralRibBridge
import Splay.Assumptions.StructuralNormalForm

namespace Splay.Accounting.OfflineNormalForm

open Splay.Assumptions.NormalForm
open Splay.Tree.BST

/-- Uniform constants for the strengthened normal form on a finite universe. -/
def finiteStructuralUniverseBounds
    (limit : ℕ) (positive : 0 < limit) : StructuralBounds where
  heightMultiplier := limit
  maxRotationDepth := limit
  costMultiplier := 1
  heightMultiplier_pos := positive
  costMultiplier_pos := by omega
  neighborDepthSlack := limit

/--
Strengthened normal form restricted to nonempty key universes of size at
most `limit`.
-/
def StructuralHypothesisUpTo
    (model : CostModel) (limit : ℕ) : Prop :=
  ∃ bounds : StructuralBounds,
    ∀ (n : ℕ), 0 < n → n ≤ limit →
      ∀ accesses : List (Fin n),
        ∃ trace : ComparisonTrace n accesses,
          IsStructurallyNormal bounds trace ∧
            trace.cost ≤
              bounds.costMultiplier * model.optCost accesses

/--
The optimal comparison trace is structurally normal on every fixed finite
range.  The finite slack `limit` bounds both adjacent external depths because
every external depth is at most the number of keys.
-/
theorem exists_structurallyNormalOptimalTrace_of_le
    (limit : ℕ) (positive : 0 < limit)
    {n : ℕ} (n_pos : 0 < n) (n_le : n ≤ limit)
    (accesses : List (Fin n)) :
    ∃ trace : ComparisonTrace n accesses,
      IsStructurallyNormal
          (finiteStructuralUniverseBounds limit positive) trace ∧
        trace.cost ≤
          (finiteStructuralUniverseBounds limit positive).costMultiplier *
            OfflineOptimum.offlineOptCost accesses := by
  obtain ⟨trace, normal, cost⟩ :=
    exists_normalOptimalTrace_of_le
      limit positive n_pos n_le accesses
  refine ⟨trace, ?_, ?_⟩
  · refine
      { normal := ?_
        relevantNeighborDepth_le := ?_ }
    · exact normal
    · intro time key
      constructor
      · calc
          (trace.state time).externalDepth
                (Rank.leftNullPos key).val ≤
              (trace.state time).size :=
            (trace.state time).externalDepth_le_size _
          _ = n := (trace.state time).size_eq_upper
          _ ≤ limit := n_le
          _ ≤ (trace.state time).depth key.val + limit := by
            omega
      · calc
          (trace.state time).externalDepth
                (Rank.rightNullPos key).val ≤
              (trace.state time).size :=
            (trace.state time).externalDepth_le_size _
          _ = n := (trace.state time).size_eq_upper
          _ ≤ limit := n_le
          _ ≤ (trace.state time).depth key.val + limit := by
            omega
  · exact cost

/-- The concrete structural hypothesis is closed on every finite range. -/
theorem structuralHypothesisUpTo_concreteOfflineCostModel
    (limit : ℕ) (positive : 0 < limit) :
    StructuralHypothesisUpTo
      OfflineOptimum.concreteOfflineCostModel limit := by
  refine ⟨finiteStructuralUniverseBounds limit positive, ?_⟩
  intro n n_pos n_le accesses
  simpa using
    exists_structurallyNormalOptimalTrace_of_le
      limit positive n_pos n_le accesses

/--
The one-key degeneracy is completely closed in the strengthened model.

Every request may be served at the sole state, so no artificial rotation or
strict service timestamp is needed.  This is the precise Lean repair of the
`n = 1` issue noted in the manuscript.
-/
theorem exists_structurallyNormalOptimalTrace_one
    (accesses : List (Fin 1)) :
    ∃ trace : ComparisonTrace 1 accesses,
      IsStructurallyNormal
          (finiteStructuralUniverseBounds 1 (by omega)) trace ∧
        trace.cost ≤
          (finiteStructuralUniverseBounds 1 (by omega)).costMultiplier *
            OfflineOptimum.offlineOptCost accesses := by
  exact
    exists_structurallyNormalOptimalTrace_of_le
      1 (by omega) (by omega) (by omega) accesses

/--
The exact strengthened normal-form residue at optimal sources.

Compared with `UniformOptimalTraceNormalizer`, the target additionally
carries the adjacent-null depth consequence consumed by the heavy-path
translation.
-/
def UniformOptimalStructuralTraceNormalizer : Prop :=
  ∃ bounds : StructuralBounds,
    ∀ (n : ℕ), 0 < n →
      ∀ (accesses : List (Fin n))
        (source : ComparisonTrace n accesses),
        source.cost = OfflineOptimum.offlineOptCost accesses →
          ∃ target : ComparisonTrace n accesses,
            IsStructurallyNormal bounds target ∧
              target.cost ≤ bounds.costMultiplier * source.cost

/--
Forgetting the adjacent-null invariant recovers the ordinary optimal-source
normalizer with exactly the same cost, height, and rotation constants.
-/
theorem UniformOptimalStructuralTraceNormalizer.toUniformOptimalTraceNormalizer
    (normalizer : UniformOptimalStructuralTraceNormalizer) :
    UniformOptimalTraceNormalizer := by
  obtain ⟨bounds, normalize⟩ := normalizer
  refine ⟨bounds.toBounds, ?_⟩
  intro n n_pos accesses source sourceCost
  obtain ⟨target, structural, targetCost⟩ :=
    normalize n n_pos accesses source sourceCost
  exact ⟨target, structural.normal, targetCost⟩

/--
The strengthened optimal-source normalizer is exactly equivalent to the
repository's structural normal-form hypothesis for the attained offline
optimum.
-/
theorem
    uniformOptimalStructuralTraceNormalizer_iff_structuralHypothesis :
    UniformOptimalStructuralTraceNormalizer ↔
      StructuralHypothesis
        OfflineOptimum.concreteOfflineCostModel := by
  constructor
  · rintro ⟨bounds, normalize⟩
    refine ⟨bounds, ?_⟩
    intro n n_pos accesses
    obtain ⟨source, sourceCost⟩ :=
      exists_optimalComparisonTrace accesses
    obtain ⟨target, normal, targetCost⟩ :=
      normalize n n_pos accesses source sourceCost
    refine ⟨target, normal, ?_⟩
    rw [OfflineOptimum.concreteOfflineCostModel_optCost]
    simpa [sourceCost] using targetCost
  · rintro ⟨bounds, realize⟩
    refine ⟨bounds, ?_⟩
    intro n n_pos accesses source sourceCost
    obtain ⟨target, normal, targetCost⟩ :=
      realize n n_pos accesses
    refine ⟨target, normal, ?_⟩
    rw [OfflineOptimum.concreteOfflineCostModel_optCost] at targetCost
    simpa [sourceCost] using targetCost

end Splay.Accounting.OfflineNormalForm
