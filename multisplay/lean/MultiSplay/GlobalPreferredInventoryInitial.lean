import MultiSplay.GlobalPreferredInventoryCore
import MultiSplay.ClassicalSwitchAccounting

/-! # The canonical initial forest, with its exact empty slots -/

namespace MultiSplay.Global.Preferred

open DynamicOptimality (RawTree)
open TangoSquared.MTR
open Pointer (MarkedTree)
open TangoSquared.Primary (Key)
open EndpointEncoding ClassicalSwitch

variable {α : Type*}

private theorem canonical_branches (state : State) (reference : RawTree α) :
    ∃ descendants,
      Branches state (preferredHoles state reference)
        (preferredMarked state reference).holes descendants ∧
      descendants.Perm ((otherComponents state reference).flatMap rootPart) := by
  induction reference generalizing state with
  | empty =>
      refine ⟨[],?_,List.Perm.refl []⟩
      change Branches state [([], .empty)] [.empty] []
      exact .cons (entry := ([], .empty)) (.empty state) (.nil state)
  | node left key right ihLeft ihRight =>
      obtain ⟨leftTrees,leftBranches,leftOrder⟩ := ihLeft (below state false)
      obtain ⟨rightTrees,rightBranches,rightOrder⟩ := ihRight (below state true)
      have leftCore := Core.of_branches (preferredMarked_skeleton (below state false) left ▸ rfl)
        leftBranches
      have rightCore := Core.of_branches (preferredMarked_skeleton (below state true) right ▸ rfl)
        rightBranches
      simp only [preferredMarked_erase, preferredMarked_skeleton] at leftCore rightCore
      cases direction : state [] with
      | false =>
          have front := leftBranches.prefix [false]
          have last : Branches state [([true],right)] [right]
              (rootPart (preferred (below state true) right) ++ rightTrees) := by
            simpa only [List.append_nil, restrict] using
              (Branches.cons (entry := ([true],right)) rightCore (.nil state))
          refine ⟨leftTrees ++ (rootPart (preferred (below state true) right) ++ rightTrees),?_,?_⟩
          · simpa only [preferredHoles, preferredMarked, direction, Bool.false_eq_true,
              ↓reduceIte, MarkedTree.holes] using front.append last
          · have ordered := leftOrder.append
              ((List.Perm.refl (rootPart (preferred (below state true) right))).append rightOrder)
            have swapped := (List.perm_append_comm (l₁ := (otherComponents (below state false) left).flatMap rootPart)
              (l₂ := rootPart (preferred (below state true) right))).append_right
                ((otherComponents (below state true) right).flatMap rootPart)
            simpa only [otherComponents, direction, Bool.false_eq_true, ↓reduceIte,
              List.flatMap_cons, List.flatMap_append, List.append_assoc] using
              ordered.trans (by simpa only [List.append_assoc] using swapped)
      | true =>
          have first : Branches state [([false],left)] [left]
              (rootPart (preferred (below state false) left) ++ leftTrees) := by
            simpa only [List.append_nil, restrict] using
              (Branches.cons (entry := ([false],left)) leftCore (.nil state))
          have last := rightBranches.prefix [true]
          refine ⟨(rootPart (preferred (below state false) left) ++ leftTrees) ++ rightTrees,?_,?_⟩
          · simpa only [preferredHoles, preferredMarked, direction, ↓reduceIte,
              MarkedTree.holes, List.singleton_append] using first.append last
          · simpa only [otherComponents, direction, ↓reduceIte, List.flatMap_cons,
              List.flatMap_append, List.append_assoc] using
              ((List.Perm.refl (rootPart (preferred (below state false) left))).append
                leftOrder).append rightOrder

theorem canonical_core (state : State) (reference : RawTree α) :
    ∃ trees, Core state reference reference trees ∧
      trees.Perm ((forest state reference).flatMap rootPart) := by
  obtain ⟨descendants,children,ordered⟩ := canonical_branches state reference
  have inventory := Core.of_branches
    (preferredMarked_skeleton state reference ▸ rfl) children
  simp only [preferredMarked_erase, preferredMarked_skeleton] at inventory
  exact ⟨_,inventory,by simpa only [forest,List.flatMap_cons] using
    (List.Perm.refl (rootPart (preferred state reference))).append ordered⟩

/-- The full analytical forest has exactly the canonical number of slots.
Only its nonempty entries carry physical components. The size equation
ensures that at least one empty slot remains available at every boundary. -/
def Inventory (state : State) (reference physical : RawTree α)
    (trees : List (RawTree α)) : Prop :=
  ∃ core, Core state reference physical core ∧
    (trees.flatMap rootPart).Perm core ∧
    trees.length = reference.size + 1 ∧
    (trees.map Tree.size).sum = reference.size

theorem initial_inventory (state : State) (reference : RawTree α) :
    Inventory state reference reference (forest state reference) := by
  obtain ⟨core,represented,ordered⟩ := canonical_core state reference
  exact ⟨core,represented,ordered.symm,
    Accounting.forest_length state reference,Accounting.forest_size_sum state reference⟩

end MultiSplay.Global.Preferred
