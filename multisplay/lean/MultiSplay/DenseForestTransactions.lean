import MultiSplay.DenseForestExecution

/-! # The raw services used by the common-forest compiler -/

namespace MultiSplay.DenseForest

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder)
open Splay.Accounting (articleParameters)

variable {α : Type*} {height slack : Nat}

theorem service (component : Component α) {left right : RawTree α} {key : α}
    (root : component.source = .node left key right)
    (geometry : BoundedMacros.Geometry height slack component.source) :
    ∃ result : Component α, result.source = component.source ∧
      Nonempty (Execution height slack [component] [result] [.search (inorder component.source) key] 1) := by
  obtain ⟨result, rotations, sourceEq, run, _, program, cost, requests, turns, boundaries, work⟩ := request component root geometry
  refine ⟨result, sourceEq, ⟨⟨program, by change program.comparisonCost ≤ 2; rw [work]; omega, rotations+1, ?_, ?_⟩⟩⟩
  · simpa only [List.map_cons, List.map_nil, component.inorder_eq] using
      CommonForest.Trace.single (CommonForest.Step.search (prepare := CommonForest.idle) run)
  · change rotations+1 ≤ program.splayCost+program.boundaries
    rw [cost, boundaries]

theorem split (component : Component α) {left right : RawTree α} {key : α}
    (root : component.source = .node left key right)
    (geometry : BoundedMacros.Geometry height slack component.source) :
    ∃ a b : Component α, a.source = left ∧ b.source = right ∧
      Nonempty (Execution height slack [component] [a,b] [.split (inorder left) key (inorder right)] 1) := by
  obtain ⟨middle, rotations, sourceEq, run, common, first, firstCost, _, _, firstBoundaries, firstWork⟩ := request component root geometry
  obtain ⟨a, b, leftEq, rightEq, exposed, second, secondCost, _, _, secondBoundaries, secondWork⟩ :=
    split_root (params := articleParameters height) (slack := slack) (depth := 1) middle common (sourceEq.trans root)
  refine ⟨a, b, leftEq, rightEq, ⟨⟨first.append second, ?_, rotations+1, ?_, ?_⟩⟩⟩
  · change (first.append second).sum Unlocated.Move.comparisonCost ≤ _
    rw [Unlocated.Program.sum_append]
    change first.comparisonCost+second.comparisonCost ≤ _
    rw [firstWork, secondWork]
  · rw [exposed] at run
    simpa only [List.map_cons, List.map_nil, a.inorder_eq, b.inorder_eq, leftEq, rightEq] using
      CommonForest.Trace.single (CommonForest.Step.split (prepare := CommonForest.idle) run)
  · change rotations+1 ≤ (first.append second).sum Unlocated.Move.splayCost +
      (first.append second).sum Unlocated.Move.boundaries
    rw [Unlocated.Program.sum_append, Unlocated.Program.sum_append]
    change rotations+1 ≤ (first.splayCost+second.splayCost)+(first.boundaries+second.boundaries)
    rw [firstCost, secondCost, firstBoundaries, secondBoundaries]
    omega

theorem join_service (a b : Component α) (key : α) (cap : 3 ≤ (articleParameters height).valueBound) :
    ∃ result : Component α, result.source = .node a.source key b.source ∧
      Nonempty (Execution height slack [a,b] [result] [.join (inorder a.source) key (inorder b.source)] 1) := by
  obtain ⟨result, sourceEq, actualEq, program, cost, _, _, boundaries, work⟩ :=
    join (params := articleParameters height) (slack := slack) (depth := 1) a b key (Nat.le_refl 2) cap
  refine ⟨result, sourceEq, ⟨⟨program, by change program.comparisonCost ≤ 2; rw [work]; omega, 1, ?_, ?_⟩⟩⟩
  · simpa only [List.map_cons, List.map_nil, actualEq, a.inorder_eq, b.inorder_eq] using
      CommonForest.Trace.single (CommonForest.Step.join (access := Auxiliary.Splay) (prepare := CommonForest.idle) a.actual b.actual key)
  · change 1 ≤ program.splayCost+program.boundaries
    rw [cost, boundaries]

theorem prepare_service {charge : Nat} (component : Component α) {target : RawTree α}
    (preparation : BoundedMacros.Preparation height slack component.source target charge) :
    ∃ result : Component α, result.source = target ∧ Nonempty (Execution height slack [component] [result] [] charge) := by
  obtain ⟨result, sourceEq, actualEq, program, cost, _, boundaries, work⟩ := prepare component preparation
  refine ⟨result, sourceEq, ⟨⟨program, by change program.comparisonCost ≤ 2*charge; omega, 0, ?_, ?_⟩⟩⟩
  · simpa only [List.map_cons, List.map_nil, actualEq] using (CommonForest.Trace.nil (access := Auxiliary.Splay) (prepare := CommonForest.idle) [component.actual])
  · exact Nat.zero_le _

end MultiSplay.DenseForest
