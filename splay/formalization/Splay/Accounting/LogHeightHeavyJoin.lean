import Splay.Accounting.LogHeightHeavyPotential
import Splay.Accounting.LogHeightWeightedExactPop

namespace Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate

open Splay.Tree FrontierFolding

def heavyUnitCost (capacity : ℕ) : ℕ := stackUnitCost capacity + 3

namespace HeavyRepresentation

/-- Joining represented children updates one weighted end stack, charging
both its rotations and every connector vertex in the root support. -/
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
              simp [result, potential, payloadPotential, MinimumStack.empty,
                MaximumStack.empty, MinimumStack.potential, MaximumStack.potential, Chocolate.potential]⟩
        | path mapped long leftStack rightStack =>
            rename_i key original replacement
            have bound := original.word_length_add_core_size_le (leafSplit key).tree
            simp only [BST.size] at bound
            omega
    | path mapped long leftStack rightStack =>
        rename_i key original replacement
        have sourceSize := (BST.node (original.plug (leafSplit key).tree) right).size_add_lower_eq_upper
        have partSize := (BST.node rightStack.tree actualRight).size_add_lower_eq_upper
        have lowerBound := leftStack.tree.lower_le_upper
        have room : (BST.node rightStack.tree actualRight).size ≤ capacity := by omega
        obtain ⟨stack, cost, path, amortized, worst⟩ := rightStack.exists_push actualRight room
        let result : HeavyRepresentation capacity _ _ :=
          .path (.high mapped rightRep) ⟨heavy, long⟩ leftStack stack
        refine ⟨_, result, cost + 3, ?_, ?_, ?_⟩
        · exact ((HasSupportedPath.rootRight leftStack.tree rightStack.tree actualRight).trans
            (path.rightContext leftStack.tree)).mono (by omega) (by omega)
        · dsimp [heavyUnitCost]; omega
        · simp only [result, potential, payloadPotential,
            MinimumStack.potential, MaximumStack.potential] at amortized ⊢
          omega
  · have heavier : left.size < right.size := by omega
    cases rightRep with
    | empty => simp [BST.size] at heavier
    | path mapped long leftStack rightStack =>
        rename_i key original replacement
        have sourceSize := (BST.node left (original.plug (leafSplit key).tree)).size_add_lower_eq_upper
        have partSize := (BST.node actualLeft leftStack.tree).size_add_lower_eq_upper
        have upperBound := rightStack.tree.lower_le_upper
        have room : (BST.node actualLeft leftStack.tree).size ≤ capacity := by omega
        obtain ⟨stack, cost, path, amortized, worst⟩ := leftStack.exists_push actualLeft room
        let result : HeavyRepresentation capacity _ _ :=
          .path (.low leftRep mapped) ⟨heavier, long⟩ stack rightStack
        refine ⟨_, result, cost + 3, ?_, ?_, ?_⟩
        · exact ((HasSupportedPath.rootLeft actualLeft leftStack.tree rightStack.tree).trans
            (path.leftContext rightStack.tree)).mono (by omega) (by omega)
        · dsimp [heavyUnitCost]; omega
        · simp only [result, potential, payloadPotential,
            MinimumStack.potential, MaximumStack.potential] at amortized ⊢
          omega

end HeavyRepresentation

end Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate
