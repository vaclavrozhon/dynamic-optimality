import MultiSplay.AuxiliarySplay
import Splay.Accounting.OfflineHeavyPotential
import Splay.Accounting.OfflineRibPotential

/-!
# Changing a component's ordinal origin

The actual auxiliary keys may be sparse. The indexed splay library uses dense
ordinal keys internally. Adding the same offset to these ordinal keys changes
neither physical tree shape nor cost. `tree_alphabet` proves that changing the
external interpretation of the ordinals cancels this shift exactly.

Only physical trees, frontiers, and substitution payloads are shifted. Virtual
stack templates and their history-dependent digits keep their original indices.
-/

namespace MultiSplay.OrdinalShift

open Splay.Tree (BST)
open Splay.Accounting.OfflineConnectedSupport (SupportFrontier RootPrefix Substitution leafSplit)
open Splay.Accounting.OfflineConnectedSupport.FrontierFolding (Context RootSplit)

def tree (offset : Nat) : {lower upper : Nat} → BST lower upper → BST (offset + lower) (offset + upper)
  | _, _, .empty boundary => .empty (offset + boundary)
  | _, _, .node left right => .node (tree offset left) (tree offset right)

@[simp] theorem tree_size (offset : Nat) {lower upper : Nat} (source : BST lower upper) :
    (tree offset source).size = source.size := by induction source <;> simp_all [tree, BST.size]

@[simp] theorem tree_height (offset : Nat) {lower upper : Nat} (source : BST lower upper) :
    (tree offset source).height = source.height := by induction source <;> simp_all [tree, BST.height]

/-- A pure change of ordinal origin performs no operation on the physical
tree, even when its externally interpreted keys are nonconsecutive. -/
theorem tree_alphabet {α : Type*} (offset : Nat) {lower upper : Nat}
    (source : BST lower upper) (alphabet : Nat → α) :
    Auxiliary.map (fun key => alphabet (key - offset)) (DynamicOptimality.BST.toRaw (tree offset source)) =
      Auxiliary.map alphabet (DynamicOptimality.BST.toRaw source) := by
  induction source <;> simp_all [tree, DynamicOptimality.BST.toRaw, Auxiliary.map]

def frontier (offset : Nat) : {lower upper : Nat} → SupportFrontier lower upper →
    SupportFrontier (offset + lower) (offset + upper)
  | _, _, .last source => .last (tree offset source)
  | _, _, .next source tail => .next (tree offset source) (frontier offset tail)

@[simp] theorem frontier_append (offset : Nat) {lower root upper : Nat}
    (left : SupportFrontier lower root) (right : SupportFrontier (root + 1) upper) :
    frontier offset (left.append right) = (frontier offset left).append (frontier offset right) := by
  induction left <;> simp_all [frontier, SupportFrontier.append]

@[simp] theorem frontier_card (offset : Nat) {lower upper : Nat} (source : SupportFrontier lower upper) :
    (frontier offset source).card = source.card := by
  induction source <;> simp_all [frontier, SupportFrontier.card]

def selected (offset : Nat) : {lower upper : Nat} → {source : BST lower upper} →
    RootPrefix source → RootPrefix (tree offset source)
  | _, _, _, .none source => .none (tree offset source)
  | _, _, _, .node left right => .node (selected offset left) (selected offset right)

@[simp] theorem selected_frontier (offset : Nat) {lower upper : Nat} {source : BST lower upper}
    (portion : RootPrefix source) :
    (selected offset portion).frontier = frontier offset portion.frontier := by
  induction portion <;> simp_all [selected, RootPrefix.frontier, frontier]

@[simp] theorem selected_card (offset : Nat) {lower upper : Nat} {source : BST lower upper}
    (portion : RootPrefix source) : (selected offset portion).card = portion.card := by
  induction portion <;> simp_all [selected, RootPrefix.card]

def substitution (offset : Nat) : {templateLower templateUpper lower upper : Nat} →
    {template : BST templateLower templateUpper} → {actual : BST lower upper} →
    Substitution template actual → Substitution template (tree offset actual)
  | _, _, _, _, _, _, .leaf boundary payload => .leaf boundary (tree offset payload)
  | _, _, _, _, _, _, .node left right => .node (substitution offset left) (substitution offset right)

@[simp] theorem substitution_selected (offset : Nat) {templateLower templateUpper lower upper : Nat}
    {template : BST templateLower templateUpper} {actual : BST lower upper}
    (filling : Substitution template actual) :
    (substitution offset filling).selected = selected offset filling.selected := by
  induction filling <;> simp_all [substitution, Substitution.selected, selected]

def context (offset : Nat) : {lower innerLower innerUpper upper : Nat} →
    Context lower innerLower innerUpper upper →
    Context (offset + lower) (offset + innerLower) (offset + innerUpper) (offset + upper)
  | _, _, _, _, .hole lower upper => .hole (offset + lower) (offset + upper)
  | _, _, _, _, .low left tail => .low (tree offset left) (context offset tail)
  | _, _, _, _, .high initial right => .high (context offset initial) (tree offset right)

@[simp] theorem context_plug (offset : Nat) {lower innerLower innerUpper upper : Nat}
    (surrounding : Context lower innerLower innerUpper upper) (core : BST innerLower innerUpper) :
    (context offset surrounding).plug (tree offset core) = tree offset (surrounding.plug core) := by
  induction surrounding <;> simp_all [context, Context.plug, tree]

theorem context_long (offset : Nat) {lower innerLower innerUpper upper : Nat}
    (surrounding : Context lower innerLower innerUpper upper) (core : BST innerLower innerUpper)
    (long : surrounding.IsLong core) : (context offset surrounding).IsLong (tree offset core) := by
  induction surrounding with
  | hole => trivial
  | low left tail ih => simpa [context, Context.IsLong] using And.intro long.1 (ih core long.2)
  | high initial right ih => simpa [context, Context.IsLong] using And.intro long.1 (ih core long.2)

def rootSplit (offset : Nat) {lower root upper : Nat} (split : RootSplit lower root upper) :
    RootSplit (offset + lower) (offset + root) (offset + upper) where
  left := tree offset split.left
  right := tree offset split.right
  leftSelected := selected offset split.leftSelected
  rightSelected := selected offset split.rightSelected

@[simp] theorem rootSplit_addLow (offset : Nat) {lower pivot root upper : Nat}
    (left : BST lower pivot) (split : RootSplit (pivot + 1) root upper) :
    rootSplit offset (split.addLow left) =
      (rootSplit offset split).addLow (tree offset left) := rfl

@[simp] theorem rootSplit_addHigh (offset : Nat) {lower root pivot upper : Nat}
    (split : RootSplit lower root pivot) (right : BST (pivot + 1) upper) :
    rootSplit offset (split.addHigh right) =
      (rootSplit offset split).addHigh (tree offset right) := rfl

@[simp] theorem rootSplit_expose (offset : Nat) {lower innerLower root innerUpper upper : Nat}
    (surrounding : Context lower innerLower innerUpper upper) (core : RootSplit innerLower root innerUpper) :
    rootSplit offset (surrounding.expose core) = (context offset surrounding).expose (rootSplit offset core) := by
  induction surrounding <;>
    simp_all only [context, Context.expose, rootSplit_addLow, rootSplit_addHigh]

@[simp] theorem tree_leafSplit (offset root : Nat) :
    tree offset (leafSplit root).tree = (leafSplit (offset + root)).tree := rfl

@[simp] theorem rootSplit_leafSplit (offset root : Nat) :
    rootSplit offset (leafSplit root) = leafSplit (offset + root) := rfl

theorem expose_left_frontier (offset : Nat) {lower root upper : Nat}
    (surrounding : Context lower root (root + 1) upper) :
    frontier offset (surrounding.expose (leafSplit root)).leftSelected.frontier =
      ((context offset surrounding).expose (leafSplit (offset + root))).leftSelected.frontier := by
  have same := rootSplit_expose offset surrounding (leafSplit root)
  have sides := congrArg (fun split : RootSplit (offset + lower) (offset + root) (offset + upper) =>
    split.leftSelected.frontier) same
  simpa [rootSplit, selected_frontier] using sides

theorem expose_right_frontier (offset : Nat) {lower root upper : Nat}
    (surrounding : Context lower root (root + 1) upper) :
    frontier offset (surrounding.expose (leafSplit root)).rightSelected.frontier =
      ((context offset surrounding).expose (leafSplit (offset + root))).rightSelected.frontier := by
  have same := rootSplit_expose offset surrounding (leafSplit root)
  have sides := congrArg (fun split : RootSplit (offset + lower) (offset + root) (offset + upper) =>
    split.rightSelected.frontier) same
  simpa [rootSplit, selected_frontier] using sides

end MultiSplay.OrdinalShift
