import Splay.Accounting.OfflineFrontierFolding
import Splay.Accounting.OfflineSupportedComposition

namespace Splay.Accounting.OfflineConnectedSupport.FrontierFolding

open Splay.Tree

/-- A finite outer part of a folded spine, with one untouched inner tree.
All side trees are actual BST payloads, not merely interval lengths. -/
inductive Context : ℕ → ℕ → ℕ → ℕ → Type
  | hole (lower upper : ℕ) : Context lower lower upper upper
  | low {lower root innerLower innerUpper upper : ℕ} (left : BST lower root)
      (tail : Context (root + 1) innerLower innerUpper upper) :
      Context lower innerLower innerUpper upper
  | high {lower innerLower innerUpper root upper : ℕ}
      (initial : Context lower innerLower innerUpper root) (right : BST (root + 1) upper) :
      Context lower innerLower innerUpper upper

namespace Context

def word {lower innerLower innerUpper upper : ℕ} : Context lower innerLower innerUpper upper → List Bool
  | .hole _ _ => []
  | .low _ tail => false :: tail.word
  | .high initial _ => true :: initial.word

def plug {lower innerLower innerUpper upper : ℕ}
    (context : Context lower innerLower innerUpper upper) (core : BST innerLower innerUpper) : BST lower upper :=
  match context with
  | .hole _ _ => core
  | .low left tail => .node left (tail.plug core)
  | .high initial right => .node (initial.plug core) right

def frontier {lower innerLower innerUpper upper : ℕ}
    (context : Context lower innerLower innerUpper upper) (core : SupportFrontier innerLower innerUpper) :
    SupportFrontier lower upper :=
  match context with
  | .hole _ _ => core
  | .low left tail => .next left (tail.frontier core)
  | .high initial right => (initial.frontier core).append (.last right)

def selected : {lower innerLower innerUpper upper : ℕ} →
    (context : Context lower innerLower innerUpper upper) → (core : BST innerLower innerUpper) →
    RootPrefix (context.plug core)
  | _, _, _, _, .hole _ _, core => .none core
  | _, _, _, _, .low left tail, core => .node (.none left) (tail.selected core)
  | _, _, _, _, .high initial right, core => .node (initial.selected core) (.none right)

theorem selected_card {lower innerLower innerUpper upper : ℕ}
    (context : Context lower innerLower innerUpper upper) (core : BST innerLower innerUpper) :
    (context.selected core).card = context.word.length := by
  induction context with
  | hole => rfl
  | low left tail ih => simp [selected, word, RootPrefix.card, ih, Nat.add_comm]
  | high initial right ih => simp [selected, word, RootPrefix.card, ih]

theorem selected_frontier {lower innerLower innerUpper upper : ℕ}
    (context : Context lower innerLower innerUpper upper) (core : BST innerLower innerUpper) :
    (context.selected core).frontier = context.frontier (.last core) := by
  induction context with
  | hole => rfl
  | low left tail ih => simp [selected, frontier, RootPrefix.frontier, SupportFrontier.append, ih]
  | high initial right ih => simp [selected, frontier, RootPrefix.frontier, ih]

def compose {lower firstLower secondLower secondUpper firstUpper upper : ℕ}
    (outer : Context lower firstLower firstUpper upper)
    (inner : Context firstLower secondLower secondUpper firstUpper) :
    Context lower secondLower secondUpper upper :=
  match outer with
  | .hole _ _ => inner
  | .low left tail => .low left (tail.compose inner)
  | .high initial right => .high (initial.compose inner) right

theorem word_compose {lower firstLower secondLower secondUpper firstUpper upper : ℕ}
    (outer : Context lower firstLower firstUpper upper)
    (inner : Context firstLower secondLower secondUpper firstUpper) :
    (outer.compose inner).word = outer.word ++ inner.word := by
  induction outer with
  | hole => rfl
  | low left tail ih => simp [compose, word, ih]
  | high initial right ih => simp [compose, word, ih]

theorem plug_compose {lower firstLower secondLower secondUpper firstUpper upper : ℕ}
    (outer : Context lower firstLower firstUpper upper)
    (inner : Context firstLower secondLower secondUpper firstUpper)
    (core : BST secondLower secondUpper) :
    (outer.compose inner).plug core = outer.plug (inner.plug core) := by
  induction outer with
  | hole => rfl
  | low left tail ih => simp [compose, plug, ih]
  | high initial right ih => simp [compose, plug, ih]

theorem lift_path {lower innerLower innerUpper upper support rotations : ℕ}
    (context : Context lower innerLower innerUpper upper) {before after : BST innerLower innerUpper}
    (path : HasSupportedPath before after support rotations) :
    HasSupportedPath (context.plug before) (context.plug after)
      (support + context.word.length) rotations := by
  induction context with
  | hole => simpa [plug, word] using path
  | low left tail ih => simpa [plug, word, Nat.add_assoc] using (ih path).rightContext left
  | high initial right ih => simpa [plug, word, Nat.add_assoc] using (ih path).leftContext right

theorem fold {lower innerLower innerUpper upper : ℕ} {suffix : List Bool}
    (context : Context lower innerLower innerUpper upper)
    {innerFrontier : SupportFrontier innerLower innerUpper} {core : BST innerLower innerUpper}
    (inner : Fold suffix innerFrontier core) :
    Fold (context.word ++ suffix) (context.frontier innerFrontier) (context.plug core) := by
  induction context with
  | hole => exact inner
  | low left tail ih => simpa only [word, frontier, plug, List.cons_append] using Fold.low left (ih inner)
  | high initial right ih => simpa only [word, frontier, plug, List.cons_append] using Fold.high (ih inner) right

end Context

/-- Cut a folded spine after any prescribed number of outer decisions.
The remaining folded tree, including all of its internal keys, stays in
one literal hole of the resulting context. -/
theorem Fold.exists_context {lower upper : ℕ} {initial suffix : List Bool}
    {frontier : SupportFrontier lower upper} {tree : BST lower upper}
    (folded : Fold (initial ++ suffix) frontier tree) :
    ∃ (innerLower innerUpper : ℕ) (context : Context lower innerLower innerUpper upper)
      (innerFrontier : SupportFrontier innerLower innerUpper) (core : BST innerLower innerUpper),
      context.word = initial ∧ context.frontier innerFrontier = frontier ∧
      context.plug core = tree ∧ Fold suffix innerFrontier core := by
  induction initial generalizing lower upper with
  | nil => exact ⟨lower, upper, .hole _ _, frontier, tree, rfl, rfl, rfl, folded⟩
  | cons direction initial ih =>
      cases direction with
      | false =>
          cases folded with
          | low left rest =>
              obtain ⟨innerLower, innerUpper, context, innerFrontier, core, word, same, tree, folded⟩ := ih rest
              exact ⟨innerLower, innerUpper, .low left context, innerFrontier, core,
                by simp [Context.word, word], by simp [Context.frontier, same],
                by simp [Context.plug, tree], folded⟩
      | true =>
          cases folded with
          | high rest right =>
              obtain ⟨innerLower, innerUpper, context, innerFrontier, core, word, same, tree, folded⟩ := ih rest
              exact ⟨innerLower, innerUpper, .high context right, innerFrontier, core,
                by simp [Context.word, word], by simp [Context.frontier, same],
                by simp [Context.plug, tree], folded⟩

end Splay.Accounting.OfflineConnectedSupport.FrontierFolding
