import Splay.Accounting.OfflineHeavyCost

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree FrontierFolding OfflineNormalForm.RibStack

def MinimumStack.empty (capacity boundary : ℕ) : MinimumStack capacity (.last (.empty boundary)) :=
  ⟨capacity, .empty capacity, [], .empty 0 capacity, .empty boundary,
    .leaf capacity (.empty boundary), rfl⟩

def MaximumStack.empty (capacity boundary : ℕ) : MaximumStack capacity (.last (.empty boundary)) :=
  ⟨capacity, .empty capacity, [], .empty 0 capacity, 0, .empty 0,
    .leaf capacity 0, .empty boundary, .leaf 0 (.empty boundary), rfl⟩

namespace HeavyRepresentation

/-- Joining two represented children changes only one path stack. The cost
includes every support vertex needed to connect that update to the root. -/
theorem exists_join {capacity lower root upper : ℕ}
    {left actualLeft : BST lower root} {right actualRight : BST (root + 1) upper}
    (leftRep : HeavyRepresentation capacity left actualLeft)
    (rightRep : HeavyRepresentation capacity right actualRight)
    (fits : (BST.node left right).size ≤ capacity) :
    ∃ (after : BST lower upper) (representation : HeavyRepresentation capacity (.node left right) after)
      (cost : ℕ), HasSupportedPath (.node actualLeft actualRight) after cost cost ∧
        cost ≤ heavyUnitCost capacity ∧
        cost + representation.potential ≤ leftRep.potential + rightRep.potential + 115 := by
  by_cases heavy : right.size ≤ left.size
  · cases leftRep with
    | empty boundary =>
        have emptyRight : right.size = 0 := by simpa [BST.size] using heavy
        cases rightRep with
        | empty =>
            let result : HeavyRepresentation capacity
                (.node (.empty lower) (.empty (lower + 1)))
                (.node (.empty lower) (.empty (lower + 1))) :=
              .path (.hole lower (lower + 1)) (by trivial) (MinimumStack.empty capacity lower)
                (MaximumStack.empty capacity (lower + 1))
            exact ⟨_, result, 0, .refl _, Nat.zero_le _, by
              simp [result, potential, Context.PayloadMap.heavyPotential, MinimumStack.empty,
                MaximumStack.empty, MinimumStack.potential, MaximumStack.potential, Digits.potential]⟩
        | path mapped long leftStack rightStack =>
            rename_i key original replacement
            have bound := original.word_length_add_core_size_le (leafSplit key).tree
            simp only [BST.size] at bound
            omega
    | path mapped long leftStack rightStack =>
        rename_i key original replacement
        have counts := replacement.expose_card (leafSplit key)
        rw [mapped.word_eq] at counts
        have length := original.word_length_add_core_size_le (leafSplit key).tree
        have room : (replacement.expose (leafSplit key)).rightSelected.frontier.card + 1 ≤ capacity := by
          rw [RootPrefix.frontier_card]
          simp only [RootPrefix.card, BST.size] at counts length fits
          omega
        obtain ⟨stack, _, path, amortized⟩ := rightStack.exists_push actualRight room
        let result : HeavyRepresentation capacity _ _ :=
          .path (.high mapped rightRep) ⟨heavy, long⟩ leftStack stack
        refine ⟨_, result, 16 * Digits.pushCost 0 rightStack.digits + 3, ?_, ?_, ?_⟩
        · exact ((HasSupportedPath.rootRight leftStack.tree rightStack.tree actualRight).trans
            (path.rightContext leftStack.tree)).mono (by omega) (by omega)
        · apply counterPush_le_unit
          rw [rightStack.value_eq_card]
          omega
        · simp only [result, potential, Context.PayloadMap.heavyPotential,
            MinimumStack.potential, MaximumStack.potential] at amortized ⊢
          omega
  · have heavier : left.size < right.size := by omega
    cases rightRep with
    | empty => simp [BST.size] at heavier
    | path mapped long leftStack rightStack =>
        rename_i key original replacement
        have counts := replacement.expose_card (leafSplit key)
        rw [mapped.word_eq] at counts
        have length := original.word_length_add_core_size_le (leafSplit key).tree
        have room : (replacement.expose (leafSplit key)).leftSelected.frontier.card + 1 ≤ capacity := by
          rw [RootPrefix.frontier_card]
          simp only [RootPrefix.card, BST.size] at counts length fits
          omega
        obtain ⟨stack, _, path, amortized⟩ := leftStack.exists_push actualLeft room
        let result : HeavyRepresentation capacity _ _ :=
          .path (.low leftRep mapped) ⟨heavier, long⟩ stack rightStack
        refine ⟨_, result, 16 * Digits.pushCost 0 leftStack.digits + 3, ?_, ?_, ?_⟩
        · exact ((HasSupportedPath.rootLeft actualLeft leftStack.tree rightStack.tree).trans
            (path.leftContext rightStack.tree)).mono (by omega) (by omega)
        · apply counterPush_le_unit
          rw [leftStack.value_eq_card]
          omega
        · simp only [result, potential, Context.PayloadMap.heavyPotential,
            MinimumStack.potential, MaximumStack.potential] at amortized ⊢
          omega

end HeavyRepresentation

end Splay.Accounting.OfflineConnectedSupport
