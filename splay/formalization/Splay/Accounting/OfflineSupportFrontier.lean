import Splay.Accounting.OfflineConnectedNormalization

namespace Splay.Accounting.OfflineConnectedSupport

/-- The inorder sequence of untouched subtrees. Its interval indices also
record the selected keys separating adjacent subtrees. -/
inductive SupportFrontier : ℕ → ℕ → Type
  | last {lower upper : ℕ} (tree : BST lower upper) : SupportFrontier lower upper
  | next {lower root upper : ℕ} (left : BST lower root)
      (tail : SupportFrontier (root + 1) upper) : SupportFrontier lower upper

namespace SupportFrontier

def card {lower upper : ℕ} : SupportFrontier lower upper → ℕ
  | .last _ => 0
  | .next _ tail => tail.card + 1

/-- Join two frontiers at their intervening selected key. -/
def append {lower root upper : ℕ} (left : SupportFrontier lower root)
    (right : SupportFrontier (root + 1) upper) : SupportFrontier lower upper :=
  match left with
  | .last tree => .next tree right
  | .next tree tail => .next tree (tail.append right)

theorem append_assoc {lower first second upper : ℕ}
    (a : SupportFrontier lower first) (b : SupportFrontier (first + 1) second)
    (c : SupportFrontier (second + 1) upper) :
    (a.append b).append c = a.append (b.append c) := by
  induction a with
  | last tree => rfl
  | next tree tail ih => simp only [append, ih]

@[simp] theorem card_append {lower root upper : ℕ}
    (left : SupportFrontier lower root) (right : SupportFrontier (root + 1) upper) :
    (left.append right).card = left.card + 1 + right.card := by
  induction left with
  | last => simp [append, card, Nat.add_comm]
  | next tree tail ih => simp [append, card, ih]; omega

def tree {lower upper : ℕ} : SupportFrontier lower upper → BST lower upper
  | .last tree => tree
  | .next left tail => .node left tail.tree

def selected {lower upper : ℕ} (frontier : SupportFrontier lower upper) : RootPrefix frontier.tree :=
  match frontier with
  | .last tree => .none tree
  | .next left tail => .node (.none left) tail.selected

end SupportFrontier

namespace RootPrefix

def keys {lower upper : ℕ} {tree : BST lower upper} : RootPrefix tree → List ℕ
  | .none _ => []
  | @node _ root _ _ _ left right => left.keys ++ root :: right.keys

def frontier {lower upper : ℕ} {tree : BST lower upper} :
    RootPrefix tree → SupportFrontier lower upper
  | .none tree => .last tree
  | .node left right => left.frontier.append right.frontier

def leftSpine {lower upper : ℕ} {tree : BST lower upper} : RootPrefix tree → ℕ
  | .none _ => 0
  | .node left _ => left.leftSpine + 1

def rightSpine {lower upper : ℕ} {tree : BST lower upper} : RootPrefix tree → ℕ
  | .none _ => 0
  | .node _ right => right.rightSpine + 1

def IsRightVine {lower upper : ℕ} {tree : BST lower upper} : RootPrefix tree → Prop
  | .none _ => True
  | .node (.none _) right => right.IsRightVine
  | .node (.node _ _) _ => False

@[simp] theorem frontier_card {lower upper : ℕ} {tree : BST lower upper}
    (selected : RootPrefix tree) : selected.frontier.card = selected.card := by
  induction selected with
  | none => rfl
  | node left right ihL ihR => simp [frontier, card, ihL, ihR]

theorem leftSpine_le_card {lower upper : ℕ} {tree : BST lower upper}
    (selected : RootPrefix tree) : selected.leftSpine ≤ selected.card := by
  induction selected with
  | none => rfl
  | node left right ihL ihR => simp only [leftSpine, card]; omega

theorem rightSpine_le_card {lower upper : ℕ} {tree : BST lower upper}
    (selected : RootPrefix tree) : selected.rightSpine ≤ selected.card := by
  induction selected with
  | none => rfl
  | node left right ihL ihR => simp only [rightSpine, card]; omega

/-- The frontier determines a vine including all its unchanged payloads. -/
theorem pack_eq_frontier_of_isRightVine {lower upper : ℕ} {tree : BST lower upper}
    (selected : RootPrefix tree) (vine : selected.IsRightVine) :
    (⟨tree, selected⟩ : Σ t : BST lower upper, RootPrefix t) =
      ⟨selected.frontier.tree, selected.frontier.selected⟩ := by
  induction selected with
  | none => rfl
  | @node lower root upper left right leftPrefix rightPrefix ihL ihR =>
      cases leftPrefix with
      | none =>
          have ih := ihR vine
          have lifted := congrArg
            (fun packed : Σ t : BST (root + 1) upper, RootPrefix t =>
              (⟨Splay.Tree.BST.node left packed.1, RootPrefix.node (.none left) packed.2⟩ :
                Σ t : BST lower upper, RootPrefix t)) ih
          simpa only [frontier, SupportFrontier.append, SupportFrontier.tree,
            SupportFrontier.selected] using lifted
      | node => exact False.elim vine

end RootPrefix

theorem SupportedRotation.keys_eq
    {depth lower upper : ℕ} {before after : BST lower upper}
    {rotation : Splay.Tree.BST.RotationAt depth before after}
    {a : RootPrefix before} {b : RootPrefix after}
    (supported : SupportedRotation rotation a b) : a.keys = b.keys := by
  induction supported with
  | rootRight => simp [RootPrefix.keys, List.append_assoc]
  | rootLeft => simp [RootPrefix.keys, List.append_assoc]
  | leftContext rotation supported right rightPrefix ih => simp [RootPrefix.keys, ih]
  | rightContext left leftPrefix rotation supported ih => simp [RootPrefix.keys, ih]

theorem SupportedRotationExecution.keys_eq
    {length lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after}
    (execution : SupportedRotationExecution length a b) : a.keys = b.keys := by
  induction execution with
  | refl => rfl
  | step rotation supported tail ih => exact supported.keys_eq.trans ih

theorem SupportedRotation.frontier_eq
    {depth lower upper : ℕ} {before after : BST lower upper}
    {rotation : Splay.Tree.BST.RotationAt depth before after}
    {a : RootPrefix before} {b : RootPrefix after}
    (supported : SupportedRotation rotation a b) : a.frontier = b.frontier := by
  induction supported with
  | rootRight => simp [RootPrefix.frontier, SupportFrontier.append_assoc]
  | rootLeft => simp [RootPrefix.frontier, SupportFrontier.append_assoc]
  | leftContext rotation supported right rightPrefix ih => simp [RootPrefix.frontier, ih]
  | rightContext left leftPrefix rotation supported ih => simp [RootPrefix.frontier, ih]

theorem SupportedRotationExecution.frontier_eq
    {length lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after}
    (execution : SupportedRotationExecution length a b) : a.frontier = b.frontier := by
  induction execution with
  | refl => rfl
  | step rotation supported tail ih => exact supported.frontier_eq.trans ih

end Splay.Accounting.OfflineConnectedSupport
