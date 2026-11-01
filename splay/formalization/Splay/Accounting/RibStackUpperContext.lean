import Splay.Accounting.OfflineFrontierFolding
import Splay.Accounting.OfflineSupportedPath

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree OfflineConnectedSupport FrontierFolding

/-- A reversed high chunk. Its lower interval boundary belongs to the hole,
so a new smaller key can be moved through it without relabeling any payload. -/
inductive UpperContext : ℕ → ℕ → Type
  | hole (boundary : ℕ) : UpperContext boundary boundary
  | node {inner root upper : ℕ} (initial : UpperContext inner root)
      (right : BST (root + 1) upper) : UpperContext inner upper

namespace UpperContext

def length {inner upper : ℕ} : UpperContext inner upper → ℕ
  | .hole _ => 0
  | .node initial _ => initial.length + 1

def plug {lower inner upper : ℕ} (context : UpperContext inner upper)
    (core : BST lower inner) : BST lower upper :=
  match context with
  | .hole _ => core
  | .node initial right => .node (initial.plug core) right

def frontier {lower inner upper : ℕ} (context : UpperContext inner upper)
    (core : SupportFrontier lower inner) : SupportFrontier lower upper :=
  match context with
  | .hole _ => core
  | .node initial right => (initial.frontier core).append (.last right)

def liftSelected {lower inner upper : ℕ} (context : UpperContext inner upper)
    {core : BST lower inner} (selected : RootPrefix core) : RootPrefix (context.plug core) :=
  match context with
  | .hole _ => selected
  | .node initial right => .node (initial.liftSelected selected) (.none right)
termination_by structural context

theorem card_liftSelected {lower inner upper : ℕ} (context : UpperContext inner upper)
    {core : BST lower inner} (selected : RootPrefix core) :
    (context.liftSelected selected).card = context.length + selected.card := by
  induction context with
  | hole => simp only [liftSelected, length, Nat.zero_add]
            rfl
  | node initial right ih => simp [liftSelected, length, RootPrefix.card, ih]; omega

set_option backward.isDefEq.respectTransparency false in
/-- Move the incoming minimum beneath an unchanged reversed high chunk.
There is precisely one actual rotation per high-chunk node. -/
def moveLow {lower root inner upper : ℕ} (context : UpperContext inner upper)
    (left : BST lower root) (core : BST (root + 1) inner) :
    SupportedPath (.node (.none left) (context.liftSelected (.none core)))
      (context.liftSelected (.node (.none left) (.none core))) :=
  match context with
  | .hole _ => .nil _
  | .node initial right =>
      .cons (.root (.left left (initial.plug core) right))
        (.rootLeft left (initial.plug core) right (.none left) (initial.liftSelected (.none core)) (.none right))
        ((initial.moveLow left core).leftContext (.none right))
termination_by structural context

set_option backward.isDefEq.respectTransparency false in
theorem moveLow_length {lower root inner upper : ℕ} (context : UpperContext inner upper)
    (left : BST lower root) (core : BST (root + 1) inner) :
    (context.moveLow left core).length = context.length := by
  induction context with
  | hole => rfl
  | node initial right ih =>
      simp [moveLow, SupportedPath.length, SupportedPath.length_leftContext, length, ih]

theorem moveLow_support {lower root inner upper : ℕ} (context : UpperContext inner upper)
    (left : BST lower root) (core : BST (root + 1) inner) :
    (RootPrefix.node (.none left) (context.liftSelected (.none core))).card = context.length + 1 := by
  simp [RootPrefix.card, card_liftSelected, Nat.add_comm]

theorem fold {lower inner upper : ℕ} (context : UpperContext inner upper) {word : List Bool}
    {coreFrontier : SupportFrontier lower inner} {core : BST lower inner}
    (folded : Fold word coreFrontier core) :
    Fold (List.replicate context.length true ++ word) (context.frontier coreFrontier) (context.plug core) := by
  induction context with
  | hole => exact folded
  | node initial right ih =>
      simpa only [length, List.replicate_succ, List.cons_append, frontier, plug] using Fold.high ih right

end UpperContext

/-- Every initial high chunk can be detached with its payloads intact. -/
theorem exists_upperContext {lower upper count : ℕ} {word : List Bool}
    {frontier : SupportFrontier lower upper} {tree : BST lower upper}
    (folded : Fold (List.replicate count true ++ word) frontier tree) :
    ∃ (inner : ℕ) (context : UpperContext inner upper)
      (coreFrontier : SupportFrontier lower inner) (core : BST lower inner),
      context.length = count ∧ context.frontier coreFrontier = frontier ∧
      context.plug core = tree ∧ Fold word coreFrontier core := by
  induction count generalizing lower upper with
  | zero => exact ⟨upper, .hole _, frontier, tree, rfl, rfl, rfl, folded⟩
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append] at folded
      cases folded with
      | high rest right =>
          obtain ⟨inner, context, coreFrontier, core, length, same, tree, folded⟩ := ih rest
          exact ⟨inner, .node context right, coreFrontier, core,
            by simp [UpperContext.length, length], by simp [UpperContext.frontier, same],
            by simp [UpperContext.plug, tree], folded⟩

end Splay.Accounting.OfflineNormalForm.RibStack
