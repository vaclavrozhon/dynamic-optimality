import Splay.Accounting.OfflineStructuralNormalForm

namespace Splay.Accounting.OfflineNormalForm

open Splay.Assumptions.NormalForm
open Splay.Tree.BST

/--
The remaining structural normal-form theorem stated directly on the
construction-friendly offline execution type.

The equality hypothesis says that the supplied execution attains the genuine
offline optimum.  Thus the theorem is about transforming an actual sequence
of root services and rotations; it contains no trace-indexing or minimum-
attainment residue.
-/
def UniformOptimalExecutionStructuralNormalizer : Prop :=
  ∃ bounds : StructuralBounds,
    ∀ (n : ℕ), 0 < n →
      ∀ (accesses : List (Fin n))
        (before after : Splay.Tree.BST 0 n) (rotations : ℕ),
        OfflineOptimum.Execution accesses before after rotations →
          OfflineOptimum.offlineOptCost accesses =
            accesses.length + rotations →
          ∃ target : ComparisonTrace n accesses,
            IsStructurallyNormal bounds target ∧
              target.cost ≤
                bounds.costMultiplier *
                  (accesses.length + rotations)

/--
Normalizing optimal concrete executions is exactly equivalent to normalizing
optimal indexed comparison traces.

This removes a possible false lead from Appendix C: the unproved part is not
conversion between the two execution presentations.  That conversion is
already exact in both cost and request order.  The residue is the actual
Bose/Brodal/Cleary structural simulation.
-/
theorem
    uniformOptimalExecutionStructuralNormalizer_iff_traceNormalizer :
    UniformOptimalExecutionStructuralNormalizer ↔
      UniformOptimalStructuralTraceNormalizer := by
  constructor
  · rintro ⟨bounds, normalize⟩
    refine ⟨bounds, ?_⟩
    intro n n_pos accesses source sourceOptimal
    obtain
      ⟨before, after, rotations, execution, optimumCost⟩ :=
      OfflineOptimum.exists_optimalExecution_eq accesses
    obtain ⟨target, structural, targetCost⟩ :=
      normalize n n_pos accesses before after rotations execution optimumCost
    refine ⟨target, structural, ?_⟩
    calc
      target.cost ≤
          bounds.costMultiplier * (accesses.length + rotations) :=
        targetCost
      _ = bounds.costMultiplier *
            OfflineOptimum.offlineOptCost accesses := by
        rw [optimumCost]
      _ = bounds.costMultiplier * source.cost := by
        rw [sourceOptimal]
  · rintro ⟨bounds, normalize⟩
    refine ⟨bounds, ?_⟩
    intro n n_pos accesses before after rotations execution optimumCost
    obtain ⟨exactSource⟩ :=
      OfflineOptimum.Execution.exists_exactTrace execution
    let source : ComparisonTrace n accesses :=
      exactSource.toComparisonTrace
    have sourceCost :
        source.cost = accesses.length + rotations := by
      exact exactSource.toComparisonTrace_cost
    have sourceOptimal :
        source.cost = OfflineOptimum.offlineOptCost accesses := by
      rw [sourceCost, ← optimumCost]
    obtain ⟨target, structural, targetCost⟩ :=
      normalize n n_pos accesses source sourceOptimal
    refine ⟨target, structural, ?_⟩
    simpa [sourceCost] using targetCost

/--
The active rotation-only offline model permits work strictly below an already
served root.  This concrete execution performs one rotation at depth two even
though its only request, key zero, is at the root both before and after.

The witness is not claimed to be optimal—it isolates the precise reason that
the manuscript sentence “the touched nodes form a connected subtree
containing the root” cannot be obtained merely by destructing
`OfflineOptimum.Execution`.  A normalization proof must either establish a
connected optimal-execution theorem or directly handle these unrestricted
rotations.
-/
theorem exists_rootedAccessExecution_with_depthTwoPreparation :
    ∃ (before after : Splay.Tree.BST 0 4),
      RotationAt 2 before after ∧
        before.HasRoot 0 ∧
        after.HasRoot 0 ∧
        OfflineOptimum.Execution
          [⟨0, by omega⟩] before after 1 := by
  let empty0 : Splay.Tree.BST 0 0 := .empty 0
  let empty1 : Splay.Tree.BST 1 1 := .empty 1
  let empty2 : Splay.Tree.BST 2 2 := .empty 2
  let empty3 : Splay.Tree.BST 3 3 := .empty 3
  let empty4 : Splay.Tree.BST 4 4 := .empty 4
  let before : Splay.Tree.BST 0 4 :=
    .node empty0
      (.node empty1 (.node empty2 (.node empty3 empty4)))
  let after : Splay.Tree.BST 0 4 :=
    .node empty0
      (.node empty1 (.node (.node empty2 empty3) empty4))
  have rotation : RotationAt 2 before after := by
    exact
      .rightContext empty0
        (.rightContext empty1
          (.root (.left empty2 empty3 empty4)))
  have beforeRoot : before.HasRoot 0 := by
    exact
      ⟨empty0,
        .node empty1 (.node empty2 (.node empty3 empty4)),
        rfl⟩
  have afterRoot : after.HasRoot 0 := by
    exact
      ⟨empty0,
        .node empty1 (.node (.node empty2 empty3) empty4),
        rfl⟩
  have execution :
      OfflineOptimum.Execution
        [⟨0, by omega⟩] before after 1 := by
    simpa using
      OfflineOptimum.Execution.next
        (RotationExecution.singleton rotation)
        afterRoot
        (OfflineOptimum.Execution.done after)
  exact ⟨before, after, rotation, beforeRoot, afterRoot, execution⟩

end Splay.Accounting.OfflineNormalForm
