import Splay.Accounting.RibStackFoldTransport
import Splay.Accounting.RibStackCounterLocality

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree OfflineConnectedSupport FrontierFolding Digits

/-- Select the low end first, or start with the unchanged high chunk. -/
def stackWord (highFirst : Bool) (digits : List Digit) : List Bool :=
  if highFirst then foldingWord true digits.reverse else foldingWord false digits

theorem length_stackWord (side : Bool) (digits : List Digit) :
    (stackWord side digits).length = spineNodes digits := by
  cases side <;> simp [stackWord, length_foldingWord, spineNodes_reverse]

@[simp] theorem stackWord_nil (side : Bool) : stackWord side [] = [] := by
  cases side <;> simp [stackWord, foldingWord_nil]

theorem stackWord_low (digit : Digit) (digits : List Digit) :
    stackWord false (digit :: digits) = List.replicate digit.value false ++ stackWord true digits := by
  simp [stackWord, foldingWord_cons]

theorem stackWord_high (digits : List Digit) (last : Digit) :
    stackWord true (digits ++ [last]) = List.replicate last.value true ++ stackWord false digits := by
  simp [stackWord, List.reverse_append, foldingWord_cons]

theorem exists_push_rebuild {terminalLower lower root upper level : ℕ}
    {terminal : BST terminalLower upper} {digits : List Digit}
    {left : BST lower root} {frontier : SupportFrontier (root + 1) upper}
    {tree : BST (root + 1) upper} {word : List Bool}
    (classes : ClassFrontier terminal level digits frontier) (newClass : ClassTree level left)
    (folded : Fold word frontier tree) (side : Bool)
    (paid : digits.length ≤ pushCost level digits) :
    ∃ (result : SupportFrontier lower upper) (after : BST lower upper),
      ClassFrontier terminal level (Digits.push digits) result ∧
      Fold (stackWord side (Digits.push digits)) result after ∧
      HasSupportedPath (.node left tree) after (64 * pushCost level digits) (64 * pushCost level digits) := by
  obtain ⟨result, shaped, update⟩ := classes.exists_push_unfolded newClass
  obtain ⟨after, finalFold⟩ := exists_fold result (stackWord side (Digits.push digits))
    (by rw [length_stackWord, shaped.card])
  have path := ((folded.unfold_path.rightContext left).trans update).trans finalFold.unfold_path.reverse
  have oldNodes := spineNodes_le_length digits
  have newNodes := spineNodes_le_length (Digits.push digits)
  have length := push_length_le digits
  have positive := pushCost_pos level digits
  rw [← classes.card] at oldNodes
  rw [← shaped.card] at newNodes
  exact ⟨result, after, shaped, finalFold, path.mono (by omega) (by omega)⟩

theorem exists_pop_rebuild {terminalLower lower upper level : ℕ}
    {terminal : BST terminalLower upper} {digits : List Digit}
    {frontier : SupportFrontier lower upper} {tree : BST lower upper} {word : List Bool}
    (classes : ClassFrontier terminal level digits frontier) (folded : Fold word frontier tree)
    (nonempty : digits ≠ []) (side : Bool) (paid : digits.length ≤ popCost level digits) :
    ∃ (root : ℕ) (left : BST lower root) (result : SupportFrontier (root + 1) upper)
      (after : BST (root + 1) upper),
      ClassTree level left ∧ ClassFrontier terminal level (Digits.pop digits) result ∧
      Fold (stackWord side (Digits.pop digits)) result after ∧
      HasSupportedPath tree (.node left after) (64 * popCost level digits) (64 * popCost level digits) := by
  obtain ⟨root, left, result, first, shaped, update⟩ := classes.exists_pop_unfolded nonempty
  obtain ⟨after, finalFold⟩ := exists_fold result (stackWord side (Digits.pop digits))
    (by rw [length_stackWord, shaped.card])
  have path := (folded.unfold_path.trans update).trans (finalFold.unfold_path.reverse.rightContext left)
  have oldNodes := spineNodes_le_length digits
  have newNodes := spineNodes_le_length (Digits.pop digits)
  have length := pop_length_le digits
  have positive := popCost_pos level digits nonempty
  rw [← classes.card] at oldNodes
  rw [← shaped.card] at newNodes
  exact ⟨root, left, result, after, first, shaped, finalFold, path.mono (by omega) (by omega)⟩

end Splay.Accounting.OfflineNormalForm.RibStack
