import Splay.Accounting.RibStackFoldedPush

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree OfflineConnectedSupport FrontierFolding Digits

/-- Borrowing traverses the same bounded high chunks in reverse. No
historical push path is reversed, so the mixed-operation potential applies. -/
theorem exists_pop_folded {terminalLower lower upper level : ℕ}
    {terminal : BST terminalLower upper} {digits : List Digit}
    {frontier : SupportFrontier lower upper} {tree : BST lower upper} (side : Bool)
    (classes : ClassFrontier terminal level digits frontier)
    (folded : Fold (stackWord side digits) frontier tree) (nonempty : digits ≠ []) :
    ∃ (root : ℕ) (left : BST lower root) (result : SupportFrontier (root + 1) upper)
      (after : BST (root + 1) upper),
      ClassTree level left ∧ ClassFrontier terminal level (Digits.pop digits) result ∧
      Fold (stackWord side (Digits.pop digits)) result after ∧
      HasSupportedPath tree (.node left after)
        (64 * popCost level digits + if side then 8 else 0)
        (64 * popCost level digits + if side then 8 else 0) := by
  generalize countEq : digits.length = count
  induction count using Nat.strong_induction_on generalizing terminalLower lower upper level digits side with
  | h count ih =>
      cases side with
      | false =>
          simp only [Bool.false_eq_true, if_false, Nat.add_zero]
          cases digits with
          | nil => contradiction
          | cons digit digits =>
              cases classes with
              | one first rest =>
                  rename_i tail a
                  simp only [stackWord_low, Digit.value, List.replicate_succ, List.replicate_zero,
                    List.cons_append, List.nil_append] at folded
                  obtain ⟨tailTree, rfl, tailFold⟩ := folded.low_inv
                  cases digits with
                  | nil =>
                      cases rest
                      simp only [stackWord_nil] at tailFold
                      cases tailFold
                      refine ⟨_, a, _, _, first, .empty _, ?_, (HasSupportedPath.refl _).mono (by omega) (by omega)⟩
                      simpa [pop] using Fold.last _
                  | cons digit digits =>
                      obtain ⟨key, borrowed, result, after, borrowedClass, shaped, finalFold, borrow⟩ :=
                        ih (digit :: digits).length (by simp only [List.length_cons] at countEq ⊢; omega)
                          true rest tailFold (by simp) rfl
                      obtain ⟨key', b, c, classB, classC, ua, ub, unjoined, _, support, cost⟩ :=
                        borrowedClass.exists_unjoin_path
                      have unjoinPath : HasSupportedPath borrowed (.node b c) (4 * level + 1) (4 * level) :=
                        ⟨ua, ub, unjoined, support, cost⟩
                      have step := (borrow.trans (unjoinPath.leftContext after)).trans
                        (HasSupportedPath.rootRight b c after)
                      refine ⟨_, a, _, .node b (.node c after), first, .two classB classC shaped, ?_,
                        (step.rightContext a).mono ?_ ?_⟩
                      · simpa [pop, stackWord_low, Digit.value, List.replicate_succ] using Fold.low b (Fold.low c finalFold)
                      · simp only [popCost, if_true]; omega
                      · simp only [popCost, if_true]; omega
              | two first second rest =>
                  simp only [stackWord_low, Digit.value, List.replicate_succ, List.replicate_zero,
                    List.cons_append, List.nil_append] at folded
                  obtain ⟨after, rfl, finalFold⟩ := folded.low_inv
                  refine ⟨_, _, _, after, first, .one second rest, ?_, (HasSupportedPath.refl _).mono (by omega) (by omega)⟩
                  simpa [pop, stackWord_low, Digit.value, List.replicate_succ] using finalFold
              | three first second third rest =>
                  simp only [stackWord_low, Digit.value, List.replicate_succ, List.replicate_zero,
                    List.cons_append, List.nil_append] at folded
                  obtain ⟨after, rfl, finalFold⟩ := folded.low_inv
                  refine ⟨_, _, _, after, first, .two second third rest, ?_, (HasSupportedPath.refl _).mono (by omega) (by omega)⟩
                  simpa [pop, stackWord_low, Digit.value, List.replicate_succ] using finalFold
      | true =>
          cases reverseEq : digits.reverse with
          | nil => exact False.elim (nonempty (by simpa using congrArg List.reverse reverseEq))
          | cons last reversed =>
              have same : digits = reversed.reverse ++ [last] := by simpa using congrArg List.reverse reverseEq
              subst digits
              let initial := reversed.reverse
              by_cases reaches : Uniform .one initial
              · have paid := length_le_popCost_of_uniform initial last level reaches
                obtain ⟨key, left, result, after, first, shaped, finalFold, path⟩ :=
                  exists_pop_rebuild classes folded nonempty true (by simpa [initial] using paid)
                exact ⟨key, left, result, after, first, shaped, finalFold, path.mono (by omega) (by omega)⟩
              · obtain ⟨firstLower, inner, first, context, core, coreShape, lastShape, contextLength, frontierEq⟩ :=
                  classes.exists_upperChunk
                have coreFoldExists : ∃ coreTree, tree = context.plug coreTree ∧
                    Fold (stackWord false initial) core coreTree := by
                  apply context.strip_fold
                  rw [frontierEq, contextLength]
                  simpa only [stackWord_high] using folded
                obtain ⟨coreTree, rfl, coreFold⟩ := coreFoldExists
                have coreNonempty : initial ≠ [] := by intro empty; apply reaches; rw [empty]; exact uniform_nil _
                obtain ⟨key, left, result, after, leftClass, shaped, finalFold, update⟩ :=
                  ih initial.length (by simp only [List.length_append, List.length_singleton] at countEq; dsimp [initial]; omega)
                    false coreShape coreFold coreNonempty rfl
                obtain ⟨popEq, costEq, lengthEq⟩ := pop_locality initial [last] level reaches
                dsimp [initial] at popEq costEq lengthEq
                have path := (context.lift_path update).trans (context.moveLow_path left after).reverse
                refine ⟨key, left, context.frontier result, context.plug after, leftClass, ?_, ?_, path.mono ?_ ?_⟩
                · rw [popEq]
                  apply shaped.attach_upper context
                  simpa only [lengthEq] using lastShape
                · rw [popEq, stackWord_high, ← contextLength]
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
