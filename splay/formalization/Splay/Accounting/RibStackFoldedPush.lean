import Splay.Accounting.RibStackFoldRebuild

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree OfflineConnectedSupport FrontierFolding Digits

/-- A carry descends through a bounded upper chunk at each touched class.
The extra eight units apply only to the auxiliary high-first view. -/
theorem exists_push_folded {terminalLower lower root upper level : ℕ}
    {terminal : BST terminalLower upper} {digits : List Digit}
    {left : BST lower root} {frontier : SupportFrontier (root + 1) upper}
    {tree : BST (root + 1) upper} (side : Bool)
    (classes : ClassFrontier terminal level digits frontier) (newClass : ClassTree level left)
    (folded : Fold (stackWord side digits) frontier tree) :
    ∃ (result : SupportFrontier lower upper) (after : BST lower upper),
      ClassFrontier terminal level (Digits.push digits) result ∧
      Fold (stackWord side (Digits.push digits)) result after ∧
      HasSupportedPath (.node left tree) after
        (64 * pushCost level digits + if side then 8 else 0)
        (64 * pushCost level digits + if side then 8 else 0) := by
  generalize countEq : digits.length = count
  induction count using Nat.strong_induction_on generalizing terminalLower lower root upper level digits side with
  | h count ih =>
      cases side with
      | false =>
          simp only [Bool.false_eq_true, if_false, Nat.add_zero]
          cases digits with
          | nil =>
              cases classes
              simp only [stackWord_nil] at folded
              cases folded
              refine ⟨_, _, .one newClass (.empty _), ?_, (HasSupportedPath.refl _).mono (by omega) (by omega)⟩
              simp only [push, stackWord_low, Digit.value, List.replicate_succ, List.replicate_zero,
                List.cons_append, List.nil_append, stackWord_nil]
              exact .low left (.last _)
          | cons digit digits =>
              cases classes with
              | one first rest =>
                  refine ⟨_, _, .two newClass first rest, ?_, (HasSupportedPath.refl _).mono (by omega) (by omega)⟩
                  simpa [push, stackWord_low, Digit.value, List.replicate_succ] using Fold.low left folded
              | two first second rest =>
                  refine ⟨_, _, .three newClass first second rest, ?_, (HasSupportedPath.refl _).mono (by omega) (by omega)⟩
                  simpa [push, stackWord_low, Digit.value, List.replicate_succ] using Fold.low left folded
              | three first second third rest =>
                  rename_i b c tail a
                  simp only [stackWord_low, Digit.value, List.replicate_succ, List.replicate_zero,
                    List.cons_append, List.nil_append] at folded
                  obtain ⟨oneTree, rfl, oneFold⟩ := folded.low_inv
                  obtain ⟨twoTree, rfl, twoFold⟩ := oneFold.low_inv
                  obtain ⟨tailTree, rfl, tailFold⟩ := twoFold.low_inv
                  obtain ⟨result, after, shaped, finalFold, carry⟩ :=
                    ih digits.length (by simp only [List.length_cons] at countEq; omega)
                      true rest (ClassTree.join b c second third) tailFold rfl
                  obtain ⟨ja, jb, joined, _, support, cost⟩ := exists_classJoin_path second third
                  have joinPath : HasSupportedPath (.node b c)
                      (.node (pullMin b).tree (pullMax c).tree) (4 * level + 1) (4 * level) :=
                    ⟨ja, jb, joined, support, cost⟩
                  have step := ((HasSupportedPath.rootLeft b c tailTree).trans
                    (joinPath.leftContext tailTree)).trans carry
                  refine ⟨_, .node left (.node a after), .two newClass first shaped, ?_,
                    ((step.rightContext a).rightContext left).mono ?_ ?_⟩
                  · simpa [push, stackWord_low, Digit.value, List.replicate_succ] using Fold.low left (Fold.low a finalFold)
                  · simp only [pushCost, if_true]; omega
                  · simp only [pushCost, if_true]; omega
      | true =>
          cases reverseEq : digits.reverse with
          | nil =>
              have empty : digits = [] := by simpa using congrArg List.reverse reverseEq
              subst digits
              obtain ⟨result, after, shaped, finalFold, path⟩ := exists_push_rebuild classes newClass folded true (by simp)
              exact ⟨result, after, shaped, finalFold, path.mono (by omega) (by omega)⟩
          | cons last reversed =>
              have same : digits = reversed.reverse ++ [last] := by simpa using congrArg List.reverse reverseEq
              subst digits
              let initial := reversed.reverse
              by_cases reaches : Uniform .three initial
              · have paid := length_le_pushCost_of_uniform initial last level reaches
                obtain ⟨result, after, shaped, finalFold, path⟩ := exists_push_rebuild classes newClass folded true
                  (by simpa [initial] using paid)
                exact ⟨result, after, shaped, finalFold, path.mono (by omega) (by omega)⟩
              · obtain ⟨firstLower, inner, first, context, core, coreShape, lastShape, contextLength, frontierEq⟩ :=
                  classes.exists_upperChunk
                have coreFoldExists : ∃ coreTree, tree = context.plug coreTree ∧
                    Fold (stackWord false initial) core coreTree := by
                  apply context.strip_fold
                  rw [frontierEq, contextLength]
                  simpa only [stackWord_high] using folded
                obtain ⟨coreTree, rfl, coreFold⟩ := coreFoldExists
                obtain ⟨result, after, shaped, finalFold, update⟩ :=
                  ih initial.length (by simp only [List.length_append, List.length_singleton] at countEq; dsimp [initial]; omega)
                    false coreShape newClass coreFold rfl
                obtain ⟨pushEq, costEq, lengthEq⟩ := push_locality initial [last] level reaches
                dsimp [initial] at pushEq costEq lengthEq
                have path := (context.moveLow_path left coreTree).trans (context.lift_path update)
                refine ⟨context.frontier result, context.plug after, ?_, ?_, path.mono ?_ ?_⟩
                · rw [pushEq]
                  apply shaped.attach_upper context
                  simpa only [lengthEq] using lastShape
                · rw [pushEq, stackWord_high, ← contextLength]
                  exact context.fold finalFold
                · have small : context.length ≤ 3 := by rw [contextLength]; cases last <;> decide
                  rw [costEq]
                  simp only [if_true, Bool.false_eq_true, if_false, Nat.add_zero]
                  omega
                · have small : context.length ≤ 3 := by rw [contextLength]; cases last <;> decide
                  rw [costEq]
                  simp only [if_true, Bool.false_eq_true, if_false, Nat.add_zero]
                  omega

end Splay.Accounting.OfflineNormalForm.RibStack
