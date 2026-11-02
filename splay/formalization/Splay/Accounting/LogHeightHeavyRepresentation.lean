import Splay.Accounting.OfflineHeavyRepresentation
import Splay.Accounting.LogHeightWeightedMaximum

namespace Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate

open Splay.Tree FrontierFolding

/-- Heavy paths are represented by weighted end stacks. Literal side trees
are represented recursively, with no extra keys or assumed simulator. -/
inductive HeavyRepresentation (capacity : ℕ) : {lower upper : ℕ} → BST lower upper → BST lower upper → Type
  | empty (boundary : ℕ) : HeavyRepresentation capacity (.empty boundary) (.empty boundary)
  | path {lower root upper : ℕ}
      {original replacement : Context lower root (root + 1) upper}
      (payloads : Context.PayloadMap (@HeavyRepresentation capacity) original replacement)
      (long : original.IsLong (leafSplit root).tree)
      (left : MinimumStack capacity (replacement.expose (leafSplit root)).leftSelected.frontier)
      (right : MaximumStack capacity (replacement.expose (leafSplit root)).rightSelected.frontier) :
      HeavyRepresentation capacity (original.plug (leafSplit root).tree) (.node left.tree right.tree)

namespace HeavyRepresentation

theorem exists_representation {lower upper : ℕ} (capacity : ℕ) (before : BST lower upper)
    (fits : before.size ≤ capacity) :
    ∃ after : BST lower upper, Nonempty (HeavyRepresentation capacity before after) := by
  generalize sizeEq : before.size = count
  induction count using Nat.strong_induction_on generalizing lower upper with
  | h count ih =>
      cases before with
      | empty => exact ⟨.empty _, ⟨.empty _⟩⟩
      | node leftTree rightTree =>
          obtain ⟨key, context, same, long, sideTrees, length⟩ :=
            exists_heavyContext (.node leftTree rightTree) (by simp [BST.size])
          obtain ⟨replacement, ⟨mapped⟩⟩ :=
            Context.PayloadMap.exists_map (Relation := @HeavyRepresentation capacity) context sideTrees
              (fun payload bound => ih payload.size (by omega) payload (by omega) rfl)
          have sourceInterval := (BST.node leftTree rightTree).size_add_lower_eq_upper
          have leftInterval := (replacement.expose (leafSplit key)).leftSelected.frontier.tree.size_add_lower_eq_upper
          have rightInterval := (replacement.expose (leafSplit key)).rightSelected.frontier.tree.size_add_lower_eq_upper
          obtain ⟨left⟩ := MinimumStack.exists_initial capacity
            (replacement.expose (leafSplit key)).leftSelected.frontier (by omega)
          obtain ⟨right⟩ := MaximumStack.exists_initial capacity
            (replacement.expose (leafSplit key)).rightSelected.frontier (by omega)
          refine ⟨.node left.tree right.tree, ?_⟩
          rw [same]
          exact ⟨.path mapped long left right⟩

/-- Weighted path depths telescope against decreasing light-child mass.
This bound holds for every representation history, including frozen stacks. -/
theorem height_le {capacity lower upper : ℕ} {before after : BST lower upper}
    (representation : HeavyRepresentation capacity before after) :
    after.height ≤ 20 * logMass before := by
  generalize sizeEq : before.size = count
  induction count using Nat.strong_induction_on generalizing lower upper with
  | h count ih =>
      cases representation with
      | empty boundary => simp [BST.height, logMass, mass, BST.size]
      | path mapped long left right =>
          rename_i root original replacement
          let parent := original.plug (leafSplit root).tree
          let level := logMass parent
          let extra := 13 * (level - 1)
          have half := long.side_half
          have pathBound : original.word.length + 1 ≤ parent.size := by
            simpa [parent, BST.size] using original.word_length_add_core_size_le (leafSplit root).tree
          have positive : 0 < level := by
            have one := logMass_half (before := BST.empty 0) (after := parent)
              (by simp only [mass, BST.size]; omega)
            simp [logMass, mass, BST.size] at one
            dsimp [level, logMass, mass]
            omega
          have payloads : replacement.AllSideTrees
              (fun payload => payload.height ≤ 7 * logMass payload + extra) := by
            apply mapped.transfer half
            intro lo hi child actual childRepresentation smaller
            have childBound := ih child.size (by omega) childRepresentation rfl
            have childLog := logMass_half (before := child) (after := parent) smaller
            have massEq := Chocolate.mass_eq_of_interval child actual
            have logEq : logMass child = logMass actual := congrArg (Nat.log 2) massEq
            dsimp [extra, level]
            omega
          have fringePayloads := replacement.expose_allPayloads (leafSplit root) payloads
            (by simp [RootPrefix.frontier, SupportFrontier.AllPayloads, BST.height])
          have leftHeight := left.height_le fringePayloads.1
          have rightHeight := right.height_le fringePayloads.2
          have parentInterval := parent.size_add_lower_eq_upper
          have leftInterval := left.tree.size_add_lower_eq_upper
          have rightInterval := right.tree.size_add_lower_eq_upper
          have leftLog := logMass_mono (before := left.tree) (after := parent)
            (by dsimp [mass]; omega)
          have rightLog := logMass_mono (before := right.tree) (after := parent)
            (by dsimp [mass]; omega)
          change max left.tree.height right.tree.height + 1 ≤ 20 * level
          dsimp [extra] at leftHeight rightHeight
          dsimp [level] at *
          omega

end HeavyRepresentation

end Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate
