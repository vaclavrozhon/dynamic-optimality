import Splay.Accounting.WholeSplayTemporaryCreationGeometry

namespace Splay.Accounting.WholeSplayTemporarySpineGeometry

open Splay.Rank
open Splay.Tree.BST
open Splay.Lazy.Canonical
open Splay.Accounting.LocalBendGeometry

/-!
Proof-relevant monotone spines accumulated below the promoted key during a
bottom-up splay.

A right spine grows by putting its previous tree below the left edge of a
new root.  Dually, a left spine grows below right edges.  The stored heavy
branch equation is the exact fact supplied by the canonical temporary
boundary minimum.  These two small datatypes isolate the endpoint
``attachment'' phenomenon: every new spine root continues in the same
direction, so only the root of the original base tree can become a new bend.
-/

/--
An explicitly supplied interval minimum determines the canonical heavy
branch of a concrete node.
-/
theorem heavyBranch_eq_of_isIntervalMin
    {n : ℕ} (snapshot : Snapshot n) (node : AtNode n)
    (candidate : External n) (branch : TernaryBranch)
    (minimum :
      IsIntervalMin snapshot.rank
        node.wholeLower node.wholeUpper candidate)
    (contains : branch.Contains node.root candidate.val) :
    node.heavyBranch snapshot = branch := by
  have heavy :
      snapshot.IsHeavyBranch
        node.wholeLower node.wholeUpper node.root branch :=
    ⟨candidate, minimum, contains⟩
  exact
    (snapshot.heavyBranch_unique
      node.wholeLower node.wholeUpper node.whole_nonempty
      node.root heavy).symm

private def rightNode
    {n key root upper : ℕ}
    (inner : BST (key + 1) root)
    (hanging : BST (root + 1) upper)
    (upper_le_n : upper ≤ n) : AtNode n where
  lower := key + 1
  root := root
  upper := upper
  left := inner
  right := hanging
  upper_le_n := upper_le_n

/--
A subtree obtained from one fixed right child by repeatedly adding an
inward-left spine root and an arbitrary light hanging subtree.
-/
inductive RightSpine
    {n key baseUpper : ℕ} (snapshot : Snapshot n)
    (base : BST (key + 1) baseUpper) :
    {upper : ℕ} → BST (key + 1) upper → Type
  | base (base_le_n : baseUpper ≤ n) :
      RightSpine snapshot base base
  | grow {root upper : ℕ} {inner : BST (key + 1) root}
      (innerSpine : RightSpine snapshot base inner)
      (hanging : BST (root + 1) upper)
      (upper_le_n : upper ≤ n)
      (heavy :
        (rightNode inner hanging upper_le_n).heavyBranch snapshot = .left) :
      RightSpine snapshot base (.node inner hanging)

namespace RightSpine

theorem upper_le_n
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) : upper ≤ n :=
  match spine with
  | .base bound => bound
  | .grow _ _ bound _ => bound

theorem base_le_n
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) : baseUpper ≤ n :=
  match spine with
  | .base bound => bound
  | .grow innerSpine _ _ _ => innerSpine.base_le_n

/-- Bends in the light hanging subtrees accumulated along the spine. -/
noncomputable def hangingBends
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) : Finset (Fin n) :=
  match spine with
  | .base _ => ∅
  | .grow innerSpine hanging bound _ =>
      hangingBends innerSpine ∪ bendsFrom snapshot hanging bound none

/--
Entering a right spine through a left heavy edge exposes exactly the fixed
base with the same incoming edge plus the unchanged light hanging subtrees.
-/
theorem bendsFrom_some_left
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) :
    bendsFrom snapshot tree spine.upper_le_n (some .left) =
      bendsFrom snapshot base
          spine.base_le_n (some .left) ∪
        spine.hangingBends := by
  induction spine with
  | base bound =>
      simp [hangingBends]
  | @grow root upper inner innerSpine hanging bound heavy ih =>
      simp only [hangingBends]
      simp only [bendsFrom]
      simp only [rightNode] at heavy
      simp only [heavy]
      simp only [childIncoming]
      simp [bendAt, Turns, ih, Finset.union_assoc]

/--
At the top of a nontrivial right spine there is no incoming heavy edge.
The new root itself is not a bend; its left child receives the spine edge.
-/
theorem bendsFrom_none_grow
    {n key baseUpper root upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {inner : BST (key + 1) root}
    (innerSpine : RightSpine snapshot base inner)
    (hanging : BST (root + 1) upper)
    (bound : upper ≤ n)
    (heavy :
      (rightNode inner hanging bound).heavyBranch snapshot = .left) :
    bendsFrom snapshot (.node inner hanging) bound none =
      bendsFrom snapshot base innerSpine.base_le_n (some .left) ∪
        (innerSpine.hangingBends ∪
          bendsFrom snapshot hanging bound none) := by
  simp only [bendsFrom]
  simp only [rightNode] at heavy
  simp [heavy, childIncoming, bendAt, Turns]
  rw [innerSpine.bendsFrom_some_left]
  ac_rfl

/-- The optional right attachment is the only change caused at the base. -/
theorem base_attachment_card_le_one
    {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper}
    {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) :
    ((bendsFrom snapshot base spine.base_le_n (some .left)) \
      (bendsFrom snapshot base spine.base_le_n none)).card ≤ 1 :=
  bendsFrom_sdiff_le_one snapshot base spine.base_le_n _ _

end RightSpine

private def leftNode
    {n lower root key : ℕ}
    (hanging : BST lower root)
    (inner : BST (root + 1) key)
    (key_le_n : key ≤ n) : AtNode n where
  lower := lower
  root := root
  upper := key
  left := hanging
  right := inner
  upper_le_n := key_le_n

/--
A subtree obtained from one fixed left child by repeatedly adding an
inward-right spine root and an arbitrary light hanging subtree.
-/
inductive LeftSpine
    {n key baseLower : ℕ} (snapshot : Snapshot n)
    (base : BST baseLower key) :
    {lower : ℕ} → BST lower key → Type
  | base (key_le_n : key ≤ n) :
      LeftSpine snapshot base base
  | grow {lower root : ℕ} {inner : BST (root + 1) key}
      (innerSpine : LeftSpine snapshot base inner)
      (hanging : BST lower root)
      (root_le_n : root ≤ n)
      (key_le_n : key ≤ n)
      (heavy :
        (leftNode hanging inner key_le_n).heavyBranch snapshot = .right) :
      LeftSpine snapshot base (.node hanging inner)

namespace LeftSpine

theorem upper_le_n
    {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {tree : BST lower key}
    (spine : LeftSpine snapshot base tree) : key ≤ n :=
  match spine with
  | .base bound => bound
  | .grow _ _ _ bound _ => bound

theorem base_le_n
    {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {tree : BST lower key}
    (spine : LeftSpine snapshot base tree) : key ≤ n :=
  match spine with
  | .base bound => bound
  | .grow innerSpine _ _ _ _ => innerSpine.base_le_n

/-- Bends in the light hanging subtrees accumulated along the left spine. -/
noncomputable def hangingBends
    {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {tree : BST lower key}
    (spine : LeftSpine snapshot base tree) : Finset (Fin n) :=
  match spine with
  | .base _ => ∅
  | .grow innerSpine hanging rootBound _ _ =>
      bendsFrom snapshot hanging rootBound none ∪
        hangingBends innerSpine

/--
Entering a left spine through a right heavy edge exposes exactly the fixed
base with that incoming edge plus all unchanged light hanging subtrees.
-/
theorem bendsFrom_some_right
    {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {tree : BST lower key}
    (spine : LeftSpine snapshot base tree) :
    bendsFrom snapshot tree spine.upper_le_n (some .right) =
      bendsFrom snapshot base spine.base_le_n (some .right) ∪
        spine.hangingBends := by
  induction spine with
  | base bound =>
      simp [hangingBends]
  | @grow lower root inner innerSpine hanging rootBound bound heavy ih =>
      simp only [hangingBends]
      simp only [bendsFrom]
      simp only [leftNode] at heavy
      simp [heavy, childIncoming, bendAt, Turns]
      rw [ih]
      ac_rfl

/--
At the top of a nontrivial left spine there is no incoming heavy edge.
The new root is not a bend and its right child receives the spine edge.
-/
theorem bendsFrom_none_grow
    {n key baseLower lower root : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {inner : BST (root + 1) key}
    (innerSpine : LeftSpine snapshot base inner)
    (hanging : BST lower root)
    (rootBound : root ≤ n)
    (bound : key ≤ n)
    (heavy :
      (leftNode hanging inner bound).heavyBranch snapshot = .right) :
    bendsFrom snapshot (.node hanging inner) bound none =
      bendsFrom snapshot base innerSpine.base_le_n (some .right) ∪
        (bendsFrom snapshot hanging rootBound none ∪
          innerSpine.hangingBends) := by
  simp only [bendsFrom]
  simp only [leftNode] at heavy
  simp [heavy, childIncoming, bendAt, Turns]
  rw [innerSpine.bendsFrom_some_right]
  ac_rfl

/-- The optional left attachment is the only change caused at the base. -/
theorem base_attachment_card_le_one
    {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key}
    {tree : BST lower key}
    (spine : LeftSpine snapshot base tree) :
    ((bendsFrom snapshot base spine.base_le_n (some .right)) \
      (bendsFrom snapshot base spine.base_le_n none)).card ≤ 1 :=
  bendsFrom_sdiff_le_one snapshot base spine.base_le_n _ _

end LeftSpine

end Splay.Accounting.WholeSplayTemporarySpineGeometry
