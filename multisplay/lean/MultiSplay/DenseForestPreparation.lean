import MultiSplay.DenseForestComponent

/-! # Lifting actual normalizer rotations through the current component alphabet -/

namespace MultiSplay.DenseForest

open Splay.Accounting (articleParameters)
open Splay.Tree (BST)

variable {α : Type*}

theorem prepare_path {height slack lower upper count : Nat} {before after : BST lower upper}
    (path : BoundedMacros.Path height slack before after count) (alphabet : Nat → α)
    (component : Component α)
    (sourceEq : component.source = Auxiliary.map alphabet (DynamicOptimality.BST.toRaw before)) :
    ∃ result : Component α, result.source = Auxiliary.map alphabet (DynamicOptimality.BST.toRaw after) ∧
      result.actual = component.actual ∧
      ∃ program : Unlocated.Program (articleParameters height) slack 1 [component.trees] [result.trees],
        program.splayCost = 0 ∧ program.requests = 0 ∧ program.rotations = count ∧
        program.boundaries = 0 ∧ program.comparisonCost ≤ 2*count := by
  induction path generalizing component with
  | nil source bounded ribs => exact ⟨component, sourceEq, rfl, .done _, rfl, rfl, rfl, rfl, Nat.le_refl _⟩
  | cons rotation shallow bounded ribs tail ih =>
      have physical := PackedSplay.rotation_physical rotation alphabet
      obtain ⟨comparison, turn, same⟩ := physical.lift component.trees.comparison component.alphabet sourceEq
      let middle : Component α := ⟨⟨_, comparison, component.trees.splay⟩, component.alphabet⟩
      obtain ⟨result, resultEq, actualEq, later, cost, requests, rotations, boundaries, work⟩ := ih middle same
      refine ⟨result, resultEq, actualEq, .next
        (.rotation component.trees.comparison comparison component.trees.splay [] turn shallow) later, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [Unlocated.Program.splayCost, Unlocated.Program.sum, Unlocated.Move.splayCost] using cost
      · simpa [Unlocated.Program.requests, Unlocated.Program.sum, Unlocated.Move.requests] using requests
      · change 1+later.rotations = _
        omega
      · simpa [Unlocated.Program.boundaries, Unlocated.Program.sum, Unlocated.Move.boundaries] using boundaries
      · change _+1+later.comparisonCost ≤ _
        omega

theorem prepare {height slack charge : Nat} (component : Component α) {target : DynamicOptimality.RawTree α}
    (preparation : BoundedMacros.Preparation height slack component.source target charge) :
    ∃ result : Component α, result.source = target ∧ result.actual = component.actual ∧
      ∃ program : Unlocated.Program (articleParameters height) slack 1 [component.trees] [result.trees],
        program.splayCost = 0 ∧ program.requests = 0 ∧ program.boundaries = 0 ∧ program.comparisonCost ≤ charge := by
  generalize sourceEq : component.source = source at preparation
  induction preparation generalizing component with
  | segment alphabet path budget =>
      obtain ⟨result, resultEq, actualEq, program, cost, requests, rotations, boundaries, work⟩ :=
        prepare_path path alphabet component sourceEq
      exact ⟨result, resultEq, actualEq, program, cost, requests, boundaries, by omega⟩
  | trans early late ihe ihl =>
      obtain ⟨middle, middleEq, middleActual, first, firstCost, firstRequests, firstBoundaries, firstWork⟩ := ihe component sourceEq
      obtain ⟨result, resultEq, resultActual, second, secondCost, secondRequests, secondBoundaries, secondWork⟩ := ihl middle middleEq
      refine ⟨result, resultEq, resultActual.trans middleActual, first.append second, ?_, ?_, ?_, ?_⟩
      · simpa only [Unlocated.Program.splayCost, Unlocated.Program.sum_append, firstCost, secondCost] using (Nat.zero_add 0)
      · simpa only [Unlocated.Program.requests, Unlocated.Program.sum_append, firstRequests, secondRequests] using (Nat.zero_add 0)
      · simpa only [Unlocated.Program.boundaries, Unlocated.Program.sum_append, firstBoundaries, secondBoundaries] using (Nat.zero_add 0)
      · change (first.append second).sum Unlocated.Move.comparisonCost ≤ _
        rw [Unlocated.Program.sum_append]
        exact Nat.add_le_add firstWork secondWork

end MultiSplay.DenseForest
