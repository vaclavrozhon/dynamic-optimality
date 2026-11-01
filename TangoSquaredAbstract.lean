import DynamicOptimality.OnlineBST
import TangoSquared.Paper20261030.OnlineSearchRotationInitialization

/-!
# Tango² in the abstract search-and-rotation BST model

One fixed deterministic mathematical strategy on `2^(h+1)` original keys,
from any initial BST. Each access pays its initial search depth plus one
plus its actual ordinary rotations. Computation is free. The maintained
primary/secondary states are the Tango² construction, with the documented
balanced-tree and accounting repairs; classical choices are fixed per
state and request. No future request is used to select a transition.

This is the power-of-two core theorem. `TangoSquaredAll.lean` supplies the
unrestricted finite-universe endpoint. A bounded local-program implementation
of the stronger paper model is outside these abstract results.
-/

namespace DynamicOptimality.Tango2

open TangoSquared.Paper20261030

abbrev size (h : Nat) := OnlineSearchRotation.keyCount h
abbrev factor (h : Nat) := OnlineSearchRotation.factor h

/-- The same shared online interface is available to splay, Greedy BST
realizations, and classical MultiSplay; no new BST or optimum is defined. -/
noncomputable def strategy (h : Nat) : OnlineBST (size h) where
  State := OnlineSearchRotationInitialization.State h
  tree := OnlineSearchRotationInitialization.State.tree
  tree_word := OnlineSearchRotationInitialization.State.tree_inorder
  advance := OnlineSearchRotationInitialization.next
  accessCost := fun state request =>
    (OnlineSearchRotationInitialization.step state request).cost
  legal := fun state request =>
    (OnlineSearchRotationInitialization.step state request).execution

def initial {h : Nat} (tree : BST 0 (size h)) : (strategy h).State :=
  OnlineSearchRotationInitialization.State.fresh tree

theorem initial_tree {h : Nat} (tree : BST 0 (size h)) :
    (strategy h).tree (initial tree) = tree.toRaw := rfl

theorem run_eq {h : Nat} (state : (strategy h).State) (requests : List (Fin (size h))) :
    (strategy h).run state requests = OnlineSearchRotationInitialization.run state requests := by
  induction requests generalizing state with
  | nil => rfl
  | cons request requests ih =>
    change (let last := (strategy h).run (OnlineSearchRotationInitialization.next state request) requests;
      (last.1, (OnlineSearchRotationInitialization.step state request).cost + last.2)) = _
    rw [ih]
    rfl

noncomputable def cost {h : Nat} (tree : BST 0 (size h)) (requests : List (Fin (size h))) : Nat :=
  ((strategy h).run (initial tree) requests).2

/-- The reported cost belongs to this actual finite execution. -/
theorem execution {h : Nat} (tree : BST 0 (size h)) (requests : List (Fin (size h))) :
    SearchRotation.Execution tree.toRaw (requests.map Fin.val)
      ((strategy h).tree ((strategy h).run (initial tree) requests).1) (cost tree requests) :=
  (strategy h).run_execution (initial tree) requests

/-- Prefixes retain their exact states and exact paid costs. -/
theorem online {h : Nat} (state : (strategy h).State) (first last : List (Fin (size h))) :
    (strategy h).run state (first ++ last) =
      let front := (strategy h).run state first
      let back := (strategy h).run front.1 last
      (back.1, front.2 + back.2) :=
  (strategy h).run_append state first last

/-- Any initial tree; the one-time linear initialization is absorbed. -/
theorem cost_bound {h : Nat} (tree : BST 0 (size h)) (requests : List (Fin (size h))) :
    cost tree requests ≤ 134880000019 * (OPT requests + size h) * factor h := by
  have bound := OnlineSearchRotationInitialization.initialized_bound tree requests
  have positive : 1 ≤ factor h := by unfold factor OnlineSearchRotation.factor; omega
  have reserve : 19 * size h ≤ 19 * (OPT requests + size h) * factor h := by
    calc
      19 * size h ≤ 19 * (OPT requests + size h) := Nat.mul_le_mul_left _ (by omega)
      _ = 19 * (OPT requests + size h) * 1 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ positive
  unfold cost
  rw [run_eq]
  calc
    _ ≤ 19 * size h + 134880000000 * (OPT requests + size h) * factor h := bound
    _ ≤ 19 * (OPT requests + size h) * factor h +
        134880000000 * (OPT requests + size h) * factor h := Nat.add_le_add_right reserve _
    _ = _ := by ring

/-- A single universal constant, uniform over every power-of-two universe,
every initial BST, and every request word. -/
theorem competitive : ∃ C : Nat, 0 < C ∧ ∀ h : Nat,
    ∀ tree : BST 0 (size h), ∀ requests : List (Fin (size h)),
      cost tree requests ≤ C * (OPT requests + size h) * factor h :=
  ⟨134880000019, by decide, fun _ tree requests => cost_bound tree requests⟩

/-- Comparison against every actual execution in the user's own model. -/
theorem competitor_bound {h : Nat} (tree competitor : BST 0 (size h))
    (requests : List (Fin (size h))) {final : RawTree Nat} {paid : Nat}
    (other : SearchRotation.Execution competitor.toRaw (requests.map Fin.val) final paid) :
    cost tree requests ≤ 269760000038 * (paid + size h) * factor h := by
  have optimum := SearchRotation.OPT_le_cost competitor requests other
  calc
    cost tree requests ≤ 134880000019 * (OPT requests + size h) * factor h := cost_bound tree requests
    _ ≤ 134880000019 * (2 * (paid + size h)) * factor h :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    _ = _ := by ring

end DynamicOptimality.Tango2
