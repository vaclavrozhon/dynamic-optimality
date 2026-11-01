import Splay.Accounting.RibStackUpperChunk
import Splay.Accounting.OfflineRestrictedMacros

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree OfflineConnectedSupport FrontierFolding Digits

namespace UpperContext

theorem strip_fold {lower inner upper : ℕ} (context : UpperContext inner upper)
    {word : List Bool} {frontier : SupportFrontier lower inner} {tree : BST lower upper}
    (folded : Fold (List.replicate context.length true ++ word) (context.frontier frontier) tree) :
    ∃ core : BST lower inner, tree = context.plug core ∧ Fold word frontier core := by
  induction context generalizing lower with
  | hole => exact ⟨tree, rfl, folded⟩
  | node initial right ih =>
      generalize frontierEq : (initial.node right).frontier frontier = outer at folded
      simp only [length, List.replicate_succ, List.cons_append] at folded
      cases folded with
      | high rest payload =>
          obtain ⟨rootEq, initialEq, payloadEq⟩ :=
            SupportFrontier.append_last_injective _ _ _ _ frontierEq
          subst rootEq
          cases initialEq
          cases payloadEq
          obtain ⟨core, same, coreFold⟩ := ih rest
          exact ⟨core, by simp [plug, same], coreFold⟩

end UpperContext

theorem _root_.Splay.Accounting.OfflineConnectedSupport.FrontierFolding.Fold.low_inv
    {lower root upper : ℕ} {word : List Bool} {left : BST lower root}
    {tail : SupportFrontier (root + 1) upper} {tree : BST lower upper}
    (folded : Fold (false :: word) (.next left tail) tree) :
    ∃ rest : BST (root + 1) upper, tree = .node left rest ∧ Fold word tail rest := by
  cases folded
  exact ⟨_, rfl, by assumption⟩

/-- Rebuild a chosen skeleton while preserving every literal hanging subtree. -/
theorem path_of_sameFrontier {lower upper : ℕ} {before after : BST lower upper}
    (a : RootPrefix before) (b : RootPrefix after) (same : a.frontier = b.frontier) :
    HasSupportedPath before after a.card (4 * a.card) := by
  by_cases positive : 0 < a.card
  · obtain ⟨path, count, _, _, _, _⟩ := exists_restrictedPath_of_sameFrontier a b same positive
      (ribs_of_height (slack := max before.height after.height) (le_max_left _ _))
      (ribs_of_height (le_max_right _ _))
    exact ⟨a, b, path, le_rfl, by omega⟩
  · have cardEq : a.card = b.card := by simpa using congrArg SupportFrontier.card same
    cases a with
    | none =>
        cases b with
        | none => cases same; exact (HasSupportedPath.refl _).mono (by simp [RootPrefix.card]) (by simp [RootPrefix.card])
        | node => simp only [RootPrefix.card] at cardEq; omega
    | node => simp [RootPrefix.card] at positive

theorem _root_.Splay.Accounting.OfflineConnectedSupport.SupportFrontier.selected_frontier
    {lower upper : ℕ} (frontier : SupportFrontier lower upper) : frontier.selected.frontier = frontier := by
  induction frontier with
  | last => rfl
  | next left tail ih => simpa [SupportFrontier.selected, RootPrefix.frontier, SupportFrontier.append] using ih

theorem _root_.Splay.Accounting.OfflineConnectedSupport.FrontierFolding.Fold.unfold_path
    {lower upper : ℕ} {word : List Bool}
    {frontier : SupportFrontier lower upper} {tree : BST lower upper}
    (folded : Fold word frontier tree) :
    HasSupportedPath tree frontier.tree (4 * frontier.card) (4 * frontier.card) := by
  obtain ⟨selected, same, _⟩ := folded.exists_selected
  have count : selected.card = frontier.card := by simpa using congrArg SupportFrontier.card same
  have path := path_of_sameFrontier selected frontier.selected (by rw [same, SupportFrontier.selected_frontier])
  exact path.mono (by omega) (by omega)

end Splay.Accounting.OfflineNormalForm.RibStack
