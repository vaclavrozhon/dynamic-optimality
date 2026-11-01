import MultiSplay.DenseForestPreparation
import MultiSplay.DenseForestBoundary

/-! # Coupled dense programs and raw splay executions of the same forest word -/

namespace MultiSplay.DenseForest

open Splay.Accounting (articleParameters)

variable {α : Type*} {height slack : Nat}

structure Execution (height slack : Nat) (first last : List (Component α))
    (word : List (CommonForest.Event α)) (budget : Nat) where
  program : Unlocated.Program (articleParameters height) slack 1 (first.map Component.trees) (last.map Component.trees)
  comparison : program.comparisonCost ≤ 2*budget
  cost : Nat
  actual : CommonForest.SplayTrace (first.map Component.actual) word (last.map Component.actual) cost
  paid : cost ≤ program.splayCost + program.boundaries

def Execution.done (forest : List (Component α)) : Execution height slack forest forest [] 0 :=
  ⟨.done _, Nat.le_refl _, 0, .nil _, Nat.le_refl _⟩

def Execution.reorder {first last : List (Component α)} (order : first.Perm last) :
    Execution height slack first last [] 0 :=
  ⟨.next (.reorder (order.map Component.trees)) (.done _), Nat.le_refl _, 0,
    CommonForest.Trace.single (.reorder (order.map Component.actual)), Nat.le_refl _⟩

def Execution.append {first middle last : List (Component α)} {a b : List (CommonForest.Event α)} {x y : Nat}
    (early : Execution height slack first middle a x) (late : Execution height slack middle last b y) :
    Execution height slack first last (a++b) (x+y) where
  program := early.program.append late.program
  comparison := by
    change (early.program.append late.program).sum Unlocated.Move.comparisonCost ≤ _
    rw [Unlocated.Program.sum_append]
    change early.program.comparisonCost + late.program.comparisonCost ≤ 2*(x+y)
    have first := early.comparison
    have second := late.comparison
    omega
  cost := early.cost+late.cost
  actual := early.actual.append late.actual
  paid := by
    change early.cost+late.cost ≤ (early.program.append late.program).sum Unlocated.Move.splayCost +
      (early.program.append late.program).sum Unlocated.Move.boundaries
    rw [Unlocated.Program.sum_append, Unlocated.Program.sum_append]
    change early.cost+late.cost ≤ (early.program.splayCost+late.program.splayCost) +
      (early.program.boundaries+late.program.boundaries)
    have first := early.paid
    have second := late.paid
    omega

theorem Execution.context {first last : List (Component α)} {word : List (CommonForest.Event α)} {budget : Nat}
    (execution : Execution height slack first last word budget) (front back : List (Component α)) :
    Nonempty (Execution height slack (front++first++back) (front++last++back) word budget) := by
  have context := execution.program.context (front.map Component.trees) (back.map Component.trees)
  have adjusted : ∃ program : Unlocated.Program (articleParameters height) slack 1
      ((front++first++back).map Component.trees) ((front++last++back).map Component.trees),
      program.splayCost = execution.program.splayCost ∧ program.requests = execution.program.requests ∧
      program.rotations = execution.program.rotations ∧ program.boundaries = execution.program.boundaries ∧
      program.comparisonCost = execution.program.comparisonCost := by
    have firstEq : (front++first++back).map Component.trees =
        front.map Component.trees ++ first.map Component.trees ++ back.map Component.trees := by simp
    have lastEq : (front++last++back).map Component.trees =
        front.map Component.trees ++ last.map Component.trees ++ back.map Component.trees := by simp
    exact firstEq.symm ▸ lastEq.symm ▸ context
  obtain ⟨program, cost, _, _, boundaries, comparison⟩ := adjusted
  refine ⟨⟨program, by rw [comparison]; exact execution.comparison, execution.cost, ?_, ?_⟩⟩
  · simpa only [List.map_append] using execution.actual.context (front.map Component.actual) (back.map Component.actual)
  · rw [cost, boundaries]
    exact execution.paid

end MultiSplay.DenseForest
