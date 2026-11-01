import Splay.Accounting.OfflineFoldingContext

namespace Splay.Accounting.OfflineConnectedSupport.FrontierFolding

open Splay.Tree

/-- A distinguished root, with the actual selected portions of its children. -/
structure RootSplit (lower root upper : ℕ) where
  left : BST lower root
  right : BST (root + 1) upper
  leftSelected : RootPrefix left
  rightSelected : RootPrefix right

namespace RootSplit

abbrev tree {lower root upper : ℕ} (split : RootSplit lower root upper) : BST lower upper :=
  .node split.left split.right

abbrev selected {lower root upper : ℕ} (split : RootSplit lower root upper) : RootPrefix split.tree :=
  .node split.leftSelected split.rightSelected

def addLow {lower key root upper : ℕ} (left : BST lower key)
    (split : RootSplit (key + 1) root upper) : RootSplit lower root upper where
  left := .node left split.left
  right := split.right
  leftSelected := .node (.none left) split.leftSelected
  rightSelected := split.rightSelected

def addHigh {lower root key upper : ℕ} (split : RootSplit lower root key)
    (right : BST (key + 1) upper) : RootSplit lower root upper where
  left := split.left
  right := .node split.right right
  leftSelected := split.leftSelected
  rightSelected := .node split.rightSelected (.none right)

end RootSplit

namespace Context

def liftSelected : {lower innerLower innerUpper upper : ℕ} →
    (context : Context lower innerLower innerUpper upper) → {core : BST innerLower innerUpper} →
    RootPrefix core → RootPrefix (context.plug core)
  | _, _, _, _, .hole _ _, _, selected => selected
  | _, _, _, _, .low left tail, _, selected => .node (.none left) (tail.liftSelected selected)
  | _, _, _, _, .high initial right, _, selected => .node (initial.liftSelected selected) (.none right)

theorem card_liftSelected {lower innerLower innerUpper upper : ℕ}
    (context : Context lower innerLower innerUpper upper) {core : BST innerLower innerUpper}
    (selected : RootPrefix core) :
    (context.liftSelected selected).card = context.word.length + selected.card := by
  induction context with
  | hole => simp only [liftSelected, word, List.length_nil, Nat.zero_add]
            rfl
  | low left tail ih => simp [liftSelected, word, RootPrefix.card, ih]; omega
  | high initial right ih => simp [liftSelected, word, RootPrefix.card, ih]; omega

/-- Pull the distinguished root through its outer context. Left and right
ancestor subsequences become the two respective spines below that root. -/
def expose {lower innerLower root innerUpper upper : ℕ}
    (context : Context lower innerLower innerUpper upper) (core : RootSplit innerLower root innerUpper) :
    RootSplit lower root upper :=
  match context with
  | .hole _ _ => core
  | .low left tail => (tail.expose core).addLow left
  | .high initial right => (initial.expose core).addHigh right

def exposurePath : {lower innerLower root innerUpper upper : ℕ} →
    (context : Context lower innerLower innerUpper upper) → (core : RootSplit innerLower root innerUpper) →
    SupportedPath (context.liftSelected core.selected) (context.expose core).selected
  | _, _, _, _, _, .hole _ _, core => .nil core.selected
  | _, _, _, _, _, .low left tail, core =>
      let exposed := tail.expose core
      (tail.exposurePath core).rightContext (.none left) |>.append
        (.cons (.root (.left left exposed.left exposed.right))
          (.rootLeft left exposed.left exposed.right (.none left) exposed.leftSelected exposed.rightSelected)
          (.nil _))
  | _, _, _, _, _, .high initial right, core =>
      let exposed := initial.expose core
      (initial.exposurePath core).leftContext (.none right) |>.append
        (.cons (.root (.right exposed.left exposed.right right))
          (.rootRight exposed.left exposed.right right exposed.leftSelected exposed.rightSelected (.none right))
          (.nil _))

set_option backward.isDefEq.respectTransparency false in
theorem exposurePath_length {lower innerLower root innerUpper upper : ℕ}
    (context : Context lower innerLower innerUpper upper) (core : RootSplit innerLower root innerUpper) :
    (context.exposurePath core).length = context.word.length := by
  induction context with
  | hole => rfl
  | low left tail ih =>
      rw [exposurePath, SupportedPath.length_append]
      simp only [SupportedPath.length_rightContext,
        SupportedPath.length, word, List.length_cons, ih]
  | high initial right ih =>
      rw [exposurePath, SupportedPath.length_append]
      simp only [SupportedPath.length_leftContext,
        SupportedPath.length, word, List.length_cons, ih]

theorem exposure_preserves_frontier {lower innerLower root innerUpper upper : ℕ}
    (context : Context lower innerLower innerUpper upper) (core : RootSplit innerLower root innerUpper) :
    (context.expose core).selected.frontier = (context.liftSelected core.selected).frontier :=
  (context.exposurePath core).toExecution.frontier_eq.symm

theorem expose_hasRoot {lower innerLower root innerUpper upper : ℕ}
    (context : Context lower innerLower innerUpper upper) (core : RootSplit innerLower root innerUpper) :
    (context.expose core).tree.HasRoot root := ⟨_, _, rfl⟩

end Context

end Splay.Accounting.OfflineConnectedSupport.FrontierFolding
