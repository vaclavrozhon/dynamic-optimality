import DynamicOptimality.ModelOnline

/-!
# Online postponement of remote rotations

The simulator stores the source strategy's virtual tree and a physical tree,
together with an actual pending rotation sequence from physical to virtual.
For the current request only, it prepends those pending rotations to a
root-serving source trace. Connected-support normalization performs a
rooted connected prefix and leaves a new pending suffix. Its length is a
nonnegative potential, so every finite prefix pays at most twice the
source search-and-rotation cost. No future request enters any choice.

This gives online root-service and rooted-hull strategies, and hence an
adjacent-pointer strategy. All preserve the supplied initial tree and use
exactly its original keys. Their later physical trees may differ from the
source tree; the pending rotation witness is the precise relation between
them.
-/

namespace DynamicOptimality.OnlineModel.Normalization

open ChaCha.MTR
open Splay.Accounting.OfflineConnectedSupport

variable {n : Nat}

/-- An indexed virtual shadow avoids changing the shared raw source interface.
The deferred sequence is real rotations between the two current trees. -/
structure State (source : OnlineBST n) where
  virtual : source.State
  virtualTree : BST 0 n
  virtual_tree : virtualTree.toRaw = source.tree virtual
  physical : BST 0 n
  pending : Nat
  deferred : Splay.Tree.BST.RotationExecution pending physical virtualTree

structure Transition (source : OnlineBST n) (state : State source) (request : Fin n) where
  next : State source
  next_virtual : next.virtual = source.advance state.virtual request
  kept : Nat
  rotations : Splay.Tree.BST.RotationExecution kept state.physical next.physical
  root : next.physical.HasRoot request.val
  hull : HullAccess request.val state.physical.toRaw next.physical.toRaw
  support_bound : hull.cost ≤ kept + 1
  budget : kept + 1 + next.pending ≤ state.pending + 2 * source.accessCost state.virtual request

/-- Normalization examines only the stored state and this single source access.
The newly deferred suffix restores the exact source boundary tree. -/
theorem transition_exists (source : OnlineBST n) (state : State source) (request : Fin n) :
    Nonempty (Transition source state request) := by
  have access : SearchRotation.Access request.val state.virtualTree.toRaw
      (source.tree (source.advance state.virtual request))
      (source.accessCost state.virtual request) := by
    rw [state.virtual_tree]
    exact source.legal state.virtual request
  obtain ⟨served, nextVirtual, depth, count, beforeService, servedRoot,
    afterService, nextVirtualEq, sourceCost⟩ := access.rootService
  obtain ⟨nextPhysical, kept, pending, initialPrefix, finalPrefix,
    supported, positive, root, deferred, counts, supportBound⟩ :=
      RotationExecution.factor_root (state.deferred.append beforeService) servedRoot
  obtain ⟨hull, hullCost⟩ := supported_hull supported positive root
  let next : State source := {
    virtual := source.advance state.virtual request
    virtualTree := nextVirtual
    virtual_tree := nextVirtualEq
    physical := nextPhysical
    pending := pending + (depth + count)
    deferred := deferred.append afterService }
  refine ⟨{
    next := next
    next_virtual := rfl
    kept := kept
    rotations := supported.toRotationExecution
    root := root
    hull := hull
    support_bound := by omega
    budget := ?_ }⟩
  change kept + 1 + (pending + (depth + count)) ≤ _
  omega

/-- This choice is fixed separately for each state and request. -/
noncomputable def transition (source : OnlineBST n) (state : State source) (request : Fin n) :
    Transition source state request :=
  Classical.choice (transition_exists source state request)

def initial (source : OnlineBST n) (state : source.State) (tree : BST 0 n)
    (same : tree.toRaw = source.tree state) : State source where
  virtual := state
  virtualTree := tree
  virtual_tree := same
  physical := tree
  pending := 0
  deferred := .refl

/-- Every legal raw source state has an indexed shadow, so initialization
does not require a user-supplied representation premise. -/
noncomputable def initialFromState (source : OnlineBST n) (state : source.State) : State source :=
  initial source state (indexedTree source state) (indexedTree_toRaw source state)

theorem initialFromState_tree (source : OnlineBST n) (state : source.State) :
    (initialFromState source state).physical.toRaw = source.tree state :=
  indexedTree_toRaw source state

noncomputable def rootStrategy (source : OnlineBST n) : OnlineRootBST n where
  State := State source
  tree state := state.physical
  advance state request := (transition source state request).next
  accessCost state request := (transition source state request).kept + 1
  legal state request := ⟨(transition source state request).kept,
    (transition source state request).rotations, (transition source state request).root, rfl⟩

noncomputable def hullStrategy (source : OnlineBST n) : OnlineHullBST n where
  State := State source
  tree state := state.physical
  advance state request := (transition source state request).next
  accessCost state request := (transition source state request).hull.cost
  legal state request := ⟨(transition source state request).hull, rfl⟩

/-- The adjacent-pointer simulator has the same physical trees as the hull
simulator and uses the checked local hull-to-pointer conversion. -/
noncomputable def pointerStrategy (source : OnlineBST n) : OnlinePointerBST n :=
  (hullStrategy source).hullToPointer

theorem root_run_virtual (source : OnlineBST n) (state : State source)
    (requests : List (Fin n)) :
    ((rootStrategy source).run state requests).1.virtual =
      (source.run state.virtual requests).1 := by
  induction requests generalizing state with
  | nil => rfl
  | cons request requests ih =>
    change ((rootStrategy source).run (transition source state request).next requests).1.virtual = _
    rw [ih, (transition source state request).next_virtual]
    rfl

theorem hull_run_state (source : OnlineBST n) (state : State source)
    (requests : List (Fin n)) :
    ((hullStrategy source).run state requests).1 =
      ((rootStrategy source).run state requests).1 := by
  induction requests generalizing state with
  | nil => rfl
  | cons request requests ih => exact ih _

theorem pointer_run_state (source : OnlineBST n) (state : State source)
    (requests : List (Fin n)) :
    ((pointerStrategy source).run state requests).1 =
      ((rootStrategy source).run state requests).1 :=
  ((hullStrategy source).map_run_state hull_to_pointer state requests).trans
    (hull_run_state source state requests)

/-- The pending length is a potential. It is counted once on each side, even
when an access postpones almost all work or consumes much earlier work. -/
theorem root_run_potential (source : OnlineBST n) (state : State source)
    (requests : List (Fin n)) :
    ((rootStrategy source).run state requests).2 +
        ((rootStrategy source).run state requests).1.pending ≤
      state.pending + 2 * (source.run state.virtual requests).2 := by
  induction requests generalizing state with
  | nil => simp [OnlineModel.run, OnlineBST.run]
  | cons request requests ih =>
    have head := (transition source state request).budget
    have tail := ih (transition source state request).next
    rw [(transition source state request).next_virtual] at tail
    change (transition source state request).kept + 1 +
        ((rootStrategy source).run (transition source state request).next requests).2 +
        ((rootStrategy source).run (transition source state request).next requests).1.pending ≤
      state.pending + 2 *
        (source.accessCost state.virtual request +
          (source.run (source.advance state.virtual request) requests).2)
    omega

theorem hull_run_cost_le_root (source : OnlineBST n) (state : State source)
    (requests : List (Fin n)) :
    ((hullStrategy source).run state requests).2 ≤
      ((rootStrategy source).run state requests).2 := by
  induction requests generalizing state with
  | nil => exact le_rfl
  | cons request requests ih =>
    have head := (transition source state request).support_bound
    have tail := ih (transition source state request).next
    change (transition source state request).hull.cost +
        ((hullStrategy source).run (transition source state request).next requests).2 ≤
      (transition source state request).kept + 1 +
        ((rootStrategy source).run (transition source state request).next requests).2
    omega

/-- The online root-serving simulator starts at the supplied tree, with no
startup cost or additive universe-size term. Every finite prefix satisfies
the same bound. -/
theorem root_cost_le (source : OnlineBST n) (state : source.State) (tree : BST 0 n)
    (same : tree.toRaw = source.tree state) (requests : List (Fin n)) :
    ((rootStrategy source).run (initial source state tree same) requests).2 ≤
      2 * (source.run state requests).2 := by
  have potential := root_run_potential source (initial source state tree same) requests
  simpa only [initial, Nat.zero_add] using
    (Nat.le_add_right _ _).trans potential

theorem hull_cost_le (source : OnlineBST n) (state : source.State) (tree : BST 0 n)
    (same : tree.toRaw = source.tree state) (requests : List (Fin n)) :
    ((hullStrategy source).run (initial source state tree same) requests).2 ≤
      2 * (source.run state requests).2 :=
  (hull_run_cost_le_root source _ requests).trans
    (root_cost_le source state tree same requests)

theorem pointer_cost_le (source : OnlineBST n) (state : source.State) (tree : BST 0 n)
    (same : tree.toRaw = source.tree state) (requests : List (Fin n)) :
    ((pointerStrategy source).run (initial source state tree same) requests).2 ≤
      74 * (source.run state requests).2 := by
  have first := (hullStrategy source).map_run_cost hull_to_pointer
    (initial source state tree same) requests
  have second := hull_cost_le source state tree same requests
  change ((pointerStrategy source).run (initial source state tree same) requests).2 ≤ _ at first
  omega

theorem root_cost_le_from_state (source : OnlineBST n) (state : source.State)
    (requests : List (Fin n)) :
    ((rootStrategy source).run (initialFromState source state) requests).2 ≤
      2 * (source.run state requests).2 :=
  root_cost_le source state _ _ requests

theorem hull_cost_le_from_state (source : OnlineBST n) (state : source.State)
    (requests : List (Fin n)) :
    ((hullStrategy source).run (initialFromState source state) requests).2 ≤
      2 * (source.run state requests).2 :=
  hull_cost_le source state _ _ requests

theorem pointer_cost_le_from_state (source : OnlineBST n) (state : source.State)
    (requests : List (Fin n)) :
    ((pointerStrategy source).run (initialFromState source state) requests).2 ≤
      74 * (source.run state requests).2 :=
  pointer_cost_le source state _ _ requests

theorem root_initial_tree (source : OnlineBST n) (state : source.State) (tree : BST 0 n)
    (same : tree.toRaw = source.tree state) :
    (rootStrategy source).tree (initial source state tree same) = tree := rfl

theorem hull_initial_tree (source : OnlineBST n) (state : source.State) (tree : BST 0 n)
    (same : tree.toRaw = source.tree state) :
    (hullStrategy source).tree (initial source state tree same) = tree := rfl

theorem pointer_initial_tree (source : OnlineBST n) (state : source.State) (tree : BST 0 n)
    (same : tree.toRaw = source.tree state) :
    (pointerStrategy source).tree (initial source state tree same) = tree := rfl

end DynamicOptimality.OnlineModel.Normalization
