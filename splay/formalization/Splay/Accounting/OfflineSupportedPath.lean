import Splay.Accounting.OfflineRestrictedSpines

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree.BST

theorem SupportedRotation.symm
    {depth lower upper : ℕ} {before after : BST lower upper}
    {rotation : RotationAt depth before after}
    {a : RootPrefix before} {b : RootPrefix after}
    (supported : SupportedRotation rotation a b) : SupportedRotation rotation.symm b a := by
  induction supported with
  | rootRight => exact .rootLeft _ _ _ _ _ _
  | rootLeft => exact .rootRight _ _ _ _ _ _
  | leftContext rotation supported right rightPrefix ih => exact .leftContext _ ih _ _
  | rightContext left leftPrefix rotation supported ih => exact .rightContext _ _ _ ih

/-- A data-valued supported execution, retaining its particular intermediate
states for the height, rib, rotation-depth, and root-visit certificates. -/
inductive SupportedPath : {lower upper : ℕ} → {before after : BST lower upper} →
    RootPrefix before → RootPrefix after → Type
  | nil {lower upper : ℕ} {tree : BST lower upper} (selected : RootPrefix tree) :
      SupportedPath selected selected
  | cons {depth lower upper : ℕ} {before middle after : BST lower upper}
      {a : RootPrefix before} {b : RootPrefix middle} {c : RootPrefix after}
      (rotation : RotationAt depth before middle)
      (supported : SupportedRotation rotation a b)
      (tail : SupportedPath b c) : SupportedPath a c

namespace SupportedPath

def length {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} : SupportedPath a b → ℕ
  | .nil _ => 0
  | .cons _ _ tail => tail.length + 1

def append {lower upper : ℕ} {before middle after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix middle} {c : RootPrefix after}
    (first : SupportedPath a b) (second : SupportedPath b c) : SupportedPath a c :=
  match first with
  | .nil _ => second
  | .cons rotation supported tail => .cons rotation supported (tail.append second)

def reverse {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b) :
    SupportedPath b a :=
  match path with
  | .nil _ => .nil _
  | .cons rotation supported tail =>
      tail.reverse.append (.cons rotation.symm supported.symm (.nil _))

def leftContext {lower root upper : ℕ} {before after : BST lower root}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b)
    {right : BST (root + 1) upper} (rightSelected : RootPrefix right) :
    SupportedPath (.node a rightSelected) (.node b rightSelected) :=
  match path with
  | .nil _ => .nil _
  | .cons rotation supported tail => .cons (.leftContext rotation _)
      (.leftContext rotation supported _ _) (tail.leftContext rightSelected)

def rightContext {lower root upper : ℕ} {before after : BST (root + 1) upper}
    {a : RootPrefix before} {b : RootPrefix after}
    {left : BST lower root} (leftSelected : RootPrefix left) (path : SupportedPath a b) :
    SupportedPath (.node leftSelected a) (.node leftSelected b) :=
  match path with
  | .nil _ => .nil _
  | .cons rotation supported tail => .cons (.rightContext _ rotation)
      (.rightContext _ _ rotation supported) (tail.rightContext leftSelected)

@[simp] theorem length_leftContext {lower root upper : ℕ} {before after : BST lower root}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b)
    {right : BST (root + 1) upper} (rightSelected : RootPrefix right) :
    (path.leftContext rightSelected).length = path.length := by
  induction path with
  | nil => rfl
  | cons rotation supported tail ih => simp [leftContext, length, ih]

@[simp] theorem length_rightContext {lower root upper : ℕ} {before after : BST (root + 1) upper}
    {a : RootPrefix before} {b : RootPrefix after}
    {left : BST lower root} (leftSelected : RootPrefix left) (path : SupportedPath a b) :
    (path.rightContext leftSelected).length = path.length := by
  generalize equation : path.length = count
  induction count using Nat.strong_induction_on generalizing before after with
  | h count ih =>
      cases path with
      | nil => simpa [rightContext, length] using equation
      | cons rotation supported tail =>
          have rest := ih tail.length (by simp only [length] at equation; omega) tail rfl
          simpa only [rightContext, length, rest] using equation

def ForallTrees {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b)
    (property : BST lower upper → Prop) : Prop :=
  match path with
  | .nil _ => property before
  | .cons _ _ tail => property before ∧ tail.ForallTrees property

def DepthBound {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b)
    (bound : ℕ) : Prop :=
  match path with
  | .nil _ => True
  | @cons depth _ _ _ _ _ _ _ _ _ _ tail => depth ≤ bound ∧ tail.DepthBound bound

def Visits {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b) (key : ℕ) : Prop :=
  match path with
  | .nil _ => before.HasRoot key
  | .cons _ _ tail => before.HasRoot key ∨ tail.Visits key

theorem toExecution {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b) :
    SupportedRotationExecution path.length a b := by
  induction path with
  | nil => exact .refl _
  | cons rotation supported tail ih => exact .step rotation supported ih

@[simp] theorem length_append {lower upper : ℕ} {before middle after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix middle} {c : RootPrefix after}
    (first : SupportedPath a b) (second : SupportedPath b c) :
    (first.append second).length = first.length + second.length := by
  induction first with
  | nil => simp [append, length]
  | cons rotation supported tail ih => simp [append, length, ih, Nat.add_right_comm]

@[simp] theorem length_reverse {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b) :
    path.reverse.length = path.length := by
  induction path with
  | nil => rfl
  | cons rotation supported tail ih => simp [reverse, length, ih]

theorem ForallTrees.initial {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} {path : SupportedPath a b}
    {property : BST lower upper → Prop} (all : path.ForallTrees property) : property before := by
  cases path with
  | nil => exact all
  | cons => exact all.1

theorem ForallTrees.final {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} {path : SupportedPath a b}
    {property : BST lower upper → Prop} (all : path.ForallTrees property) : property after := by
  induction path with
  | nil => exact all
  | cons rotation supported tail ih => exact ih all.2

theorem ForallTrees.imp {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} {path : SupportedPath a b}
    {first second : BST lower upper → Prop} (all : path.ForallTrees first)
    (implies : ∀ tree, first tree → second tree) : path.ForallTrees second := by
  induction path with
  | nil => exact implies _ all
  | cons rotation supported tail ih => exact ⟨implies _ all.1, ih all.2 implies⟩

theorem forall_height_le_of_bound {lower upper height : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b)
    (bound : a.card + a.frontierHeight ≤ height) :
    path.ForallTrees (fun tree => tree.height ≤ height) := by
  induction path with
  | nil selected => exact selected.height_le_card_add_frontierHeight.trans bound
  | @cons depth lower upper before middle after a b c rotation supported tail ih =>
      refine ⟨a.height_le_card_add_frontierHeight.trans bound, ih ?_⟩
      have card := supported.card_eq
      have frontier := supported.frontierHeight_eq
      omega

theorem forall_height_le {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b) :
    path.ForallTrees (fun tree => tree.height ≤ before.height + a.card) := by
  apply path.forall_height_le_of_bound
  have := a.frontierHeight_le_height
  omega

theorem forallTrees_append {lower upper : ℕ} {before middle after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix middle} {c : RootPrefix after}
    (first : SupportedPath a b) (second : SupportedPath b c)
    (property : BST lower upper → Prop) :
    (first.append second).ForallTrees property ↔
      first.ForallTrees property ∧ second.ForallTrees property := by
  induction first with
  | nil => exact ⟨fun all => ⟨all.initial, all⟩, fun all => all.2⟩
  | cons rotation supported tail ih => simp only [append, ForallTrees, ih, and_assoc]

theorem depthBound_append {lower upper : ℕ} {before middle after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix middle} {c : RootPrefix after}
    (first : SupportedPath a b) (second : SupportedPath b c) (bound : ℕ) :
    (first.append second).DepthBound bound ↔
      first.DepthBound bound ∧ second.DepthBound bound := by
  induction first with
  | nil => simp [append, DepthBound]
  | cons rotation supported tail ih => simp only [append, DepthBound, ih, and_assoc]

theorem visits_initial {lower upper key : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b)
    (root : before.HasRoot key) : path.Visits key := by
  cases path with
  | nil => exact root
  | cons => exact .inl root

theorem visits_append {lower upper key : ℕ} {before middle after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix middle} {c : RootPrefix after}
    (first : SupportedPath a b) (second : SupportedPath b c) :
    (first.append second).Visits key ↔ first.Visits key ∨ second.Visits key := by
  induction first with
  | nil =>
      exact ⟨fun visit => .inr visit, fun visit => visit.elim (second.visits_initial) id⟩
  | cons rotation supported tail ih => simp only [append, Visits, ih, or_assoc]

theorem ForallTrees.reverse {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} {path : SupportedPath a b}
    {property : BST lower upper → Prop} (all : path.ForallTrees property) :
    path.reverse.ForallTrees property := by
  induction path with
  | nil => exact all
  | cons rotation supported tail ih =>
      apply (forallTrees_append _ _ _).mpr
      exact ⟨ih all.2, all.2.initial, all.1⟩

theorem DepthBound.reverse {lower upper bound : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} {path : SupportedPath a b}
    (bounded : path.DepthBound bound) : path.reverse.DepthBound bound := by
  induction path with
  | nil => trivial
  | cons rotation supported tail ih =>
      apply (depthBound_append _ _ _).mpr
      exact ⟨ih bounded.2, bounded.1, trivial⟩

end SupportedPath
end Splay.Accounting.OfflineConnectedSupport
