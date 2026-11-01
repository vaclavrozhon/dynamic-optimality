import DynamicOptimality.OnlineBST
import DynamicOptimality.SearchRotationEquivalence
import DynamicOptimality.ConnectedPointer

/-!
# Online strategies for the equivalent BST access models

All strategies use the shared indexed BST on exactly the original keys. The
access relation specifies the charged operations; arbitrary internal state
and fixed per-state classical choices are permitted, as in `OnlineBST`.
Pointwise access simulations preserve both boundary trees and every source
state. Delayed rotations, which need a different physical tree, are handled
separately in `ModelOnlineNormalization`.
-/

namespace DynamicOptimality

open TangoSquared.MTR

/-- A BST access relation, including its exact natural-number charge. -/
abbrev ModelAccess (n : Nat) := Fin n → BST 0 n → BST 0 n → Nat → Prop

def searchModelAccess (n : Nat) : ModelAccess n := fun key before after cost =>
  SearchRotation.Access key.val before.toRaw after.toRaw cost

/-- Rotations bring the requested key to the final root; serving it costs one. -/
def rootModelAccess (n : Nat) : ModelAccess n := fun key before after cost =>
  ∃ rotations, Splay.Tree.BST.RotationExecution rotations before after ∧
    after.HasRoot key.val ∧ cost = rotations + 1

def hullModelAccess (n : Nat) : ModelAccess n := fun key before after cost =>
  ∃ access : HullAccess key.val before.toRaw after.toRaw, cost = access.cost

def pointerModelAccess (n : Nat) : ModelAccess n := fun key before after cost =>
  Pointer.Access key.val before.toRaw after.toRaw cost

structure OnlineModel (n : Nat) (Access : ModelAccess n) where
  State : Type
  tree : State → BST 0 n
  advance : State → Fin n → State
  accessCost : State → Fin n → Nat
  legal : ∀ state request, Access request (tree state)
    (tree (advance state request)) (accessCost state request)

abbrev OnlineRootBST (n : Nat) := OnlineModel n (rootModelAccess n)
abbrev OnlineHullBST (n : Nat) := OnlineModel n (hullModelAccess n)
abbrev OnlinePointerBST (n : Nat) := OnlineModel n (pointerModelAccess n)

namespace OnlineModel

variable {n : Nat} {Access Other : ModelAccess n}

def run (strategy : OnlineModel n Access) (state : strategy.State) :
    List (Fin n) → strategy.State × Nat
  | [] => (state, 0)
  | request :: requests =>
    let rest := run strategy (strategy.advance state request) requests
    (rest.1, strategy.accessCost state request + rest.2)

theorem run_append (strategy : OnlineModel n Access) (state : strategy.State)
    (first last : List (Fin n)) :
    strategy.run state (first ++ last) =
      let front := strategy.run state first
      let back := strategy.run front.1 last
      (back.1, front.2 + back.2) := by
  induction first generalizing state with
  | nil => simp [run]
  | cons request first ih => simp only [List.cons_append, run, ih, Nat.add_assoc]

/-- Every selected target access is fixed using only its current source state
and request. This pointwise interface deliberately preserves both trees. -/
def LocalSimulation (Access Other : ModelAccess n) (factor : Nat) : Prop :=
  ∀ key before after cost, Access key before after cost →
    ∃ targetCost, Other key before after targetCost ∧ targetCost ≤ factor * cost

noncomputable def mappedCost (strategy : OnlineModel n Access) {factor : Nat}
    (simulation : LocalSimulation Access Other factor)
    (state : strategy.State) (request : Fin n) : Nat :=
  Classical.choose (simulation request _ _ _ (strategy.legal state request))

theorem mappedCost_spec (strategy : OnlineModel n Access) {factor : Nat}
    (simulation : LocalSimulation Access Other factor)
    (state : strategy.State) (request : Fin n) :
    Other request (strategy.tree state) (strategy.tree (strategy.advance state request))
        (mappedCost strategy simulation state request) ∧
      mappedCost strategy simulation state request ≤ factor * strategy.accessCost state request :=
  Classical.choose_spec (simulation request _ _ _ (strategy.legal state request))

noncomputable def map (strategy : OnlineModel n Access) {factor : Nat}
    (simulation : LocalSimulation Access Other factor) : OnlineModel n Other where
  State := strategy.State
  tree := strategy.tree
  advance := strategy.advance
  accessCost := mappedCost strategy simulation
  legal state request := (mappedCost_spec strategy simulation state request).1

theorem map_run_state (strategy : OnlineModel n Access) {factor : Nat}
    (simulation : LocalSimulation Access Other factor)
    (state : strategy.State) (requests : List (Fin n)) :
    ((strategy.map simulation).run state requests).1 = (strategy.run state requests).1 := by
  induction requests generalizing state with
  | nil => rfl
  | cons request requests ih => exact ih _

theorem map_run_cost (strategy : OnlineModel n Access) {factor : Nat}
    (simulation : LocalSimulation Access Other factor)
    (state : strategy.State) (requests : List (Fin n)) :
    ((strategy.map simulation).run state requests).2 ≤ factor * (strategy.run state requests).2 := by
  induction requests generalizing state with
  | nil => simp [run]
  | cons request requests ih =>
    have head := (mappedCost_spec strategy simulation state request).2
    have tail := ih (strategy.advance state request)
    change mappedCost strategy simulation state request +
        ((strategy.map simulation).run (strategy.advance state request) requests).2 ≤
      factor * (strategy.accessCost state request + (strategy.run (strategy.advance state request) requests).2)
    rw [Nat.mul_add]
    omega

theorem indexed_inorder (tree : BST 0 n) : tree.toRaw.inorder = List.range n := by
  apply List.Pairwise.eq_of_mem_iff tree.toRaw_ordered List.pairwise_lt_range
  intro key
  rw [BST.toRaw_mem, List.mem_range]
  omega

/-- Erase only the interval indices, retaining every actual tree and charge. -/
def toOnlineBST (strategy : OnlineModel n (searchModelAccess n)) : OnlineBST n where
  State := strategy.State
  tree state := (strategy.tree state).toRaw
  tree_word _ := indexed_inorder _
  advance := strategy.advance
  accessCost := strategy.accessCost
  legal := strategy.legal

theorem toOnlineBST_run (strategy : OnlineModel n (searchModelAccess n))
    (state : strategy.State) (requests : List (Fin n)) :
    strategy.toOnlineBST.run state requests = strategy.run state requests := by
  induction requests generalizing state with
  | nil => rfl
  | cons request requests ih =>
    change ((strategy.toOnlineBST.run (strategy.advance state request) requests).1,
      strategy.accessCost state request +
        (strategy.toOnlineBST.run (strategy.advance state request) requests).2) = _
    rw [ih]
    rfl

theorem root_to_search : LocalSimulation (rootModelAccess n) (searchModelAccess n) 2 := by
  intro key before after cost access
  obtain ⟨count, rotations, root, rfl⟩ := access
  obtain ⟨legal, bound⟩ := SearchRotation.access_of_rootService key rotations root
  exact ⟨_, legal, by omega⟩

theorem hull_to_pointer : LocalSimulation (hullModelAccess n) (pointerModelAccess n) 37 := by
  intro key before after cost access
  obtain ⟨hull, rfl⟩ := access
  exact hullAccess_pointer hull before.toRaw_ordered

theorem pointer_to_hull : LocalSimulation (pointerModelAccess n) (hullModelAccess n) 1 := by
  intro key before after cost access
  obtain ⟨hull, bound⟩ := Pointer.Access.toHullAccess access
  exact ⟨hull.cost, ⟨hull, rfl⟩, by simpa using bound⟩

/-- A marked service must spend at least the initial depth in preceding
rotations. The statement permits arbitrary marked requests before this one. -/
theorem marked_depth_le {a b : RawTree Nat} {word : List Nat} {rotations key : Nat}
    (trace : MarkedTrace a word b rotations) {lower upper : Nat}
    (before : BST lower upper) (same : before.toRaw = a) (requested : key ∈ word) :
    before.depth key ≤ rotations := by
  induction trace generalizing before with
  | nil => simp at requested
  | rotate step rest ih =>
    obtain ⟨middle, depth, rotation, sameMiddle⟩ := restricted_lift step before same
    have next := ih middle sameMiddle requested
    have previous := (SearchRotation.rotation_depth_within_one rotation key).2
    omega
  | serve root rest ih =>
    rcases List.mem_cons.mp requested with first | later
    · subst key
      have hasRoot := toRaw_hasRoot before (same ▸ root)
      exact (Splay.Tree.BST.depth_eq_zero_of_hasRoot hasRoot).trans_le (Nat.zero_le _)
    · exact ih before same later

theorem restrictedSteps_to_rotations {a b : RawTree Nat} {count : Nat}
    (steps : Tree.RestrictedSteps count a b) : SearchRotation.Rotations a b count := by
  induction steps with
  | refl => exact .refl _
  | @cons before middle after count head tail ih =>
    have rotation : SearchRotation.Rotation before middle := by
      cases head with
      | rootRight a b c x y => exact .rootRight a b c x y
      | rootLeft a b c x y => exact .rootLeft a b c x y
      | rightRight a b c d x y z => exact .rightContext a x (.rootRight b c d y z)
      | rightLeft a b c d x y z => exact .rightContext a x (.rootLeft b c d y z)
      | leftRight a b c d x y z => exact .leftContext (.rootRight a b c x y) z d
      | leftLeft a b c d x y z => exact .leftContext (.rootLeft a b c x y) z d
    exact .step rotation ih

/-- Exact raw/indexed representation equivalence. The auxiliary rotation
sequence is used only to establish the indexed witness, not charged or
executed by a simulator. -/
theorem indexed_of_inorder (tree : RawTree Nat) (keys : tree.inorder = List.range n) :
    ∃ indexed : BST 0 n, indexed.toRaw = tree := by
  obtain ⟨initial, _, _, _, _⟩ := OPT_attained ([] : List (Fin n))
  have same : initial.toRaw.inorder = tree.inorder := (indexed_inorder initial).trans keys.symm
  obtain ⟨count, _, steps⟩ := Tree.restricted_rotation_linear initial.toRaw tree same
  obtain ⟨indexed, _, erased⟩ := SearchRotation.rotations_lift
    (restrictedSteps_to_rotations steps) initial rfl
  exact ⟨indexed, erased⟩

noncomputable def indexedTree (source : OnlineBST n) (state : source.State) : BST 0 n :=
  Classical.choose (indexed_of_inorder (source.tree state) (source.tree_word state))

theorem indexedTree_toRaw (source : OnlineBST n) (state : source.State) :
    (indexedTree source state).toRaw = source.tree state :=
  Classical.choose_spec (indexed_of_inorder (source.tree state) (source.tree_word state))

theorem hull_to_search : LocalSimulation (hullModelAccess n) (searchModelAccess n) 25 := by
  intro key before after cost access
  obtain ⟨hull, rfl⟩ := access
  obtain ⟨rotations, bound, trace⟩ := hull.marked_trace before.toRaw_ordered
  have depth := marked_depth_le (key := key.val) trace before rfl (by simp)
  have positive := hull.cost_pos
  refine ⟨before.depth key.val + 1 + rotations, ?_, ?_⟩
  · exact ⟨before.depth key.val, rotations,
      SearchRotation.toRaw_searchDepth before (Nat.zero_le _) key.isLt,
      restrictedSteps_to_rotations trace.rotations, rfl⟩
  · omega

theorem LocalSimulation.trans {A B C : ModelAccess n} {a b : Nat}
    (first : LocalSimulation A B a) (second : LocalSimulation B C b) :
    LocalSimulation A C (b * a) := by
  intro key before after cost access
  obtain ⟨middleCost, middle, firstBound⟩ := first key before after cost access
  obtain ⟨targetCost, target, secondBound⟩ := second key before after middleCost middle
  exact ⟨targetCost, target, secondBound.trans (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left b firstBound)⟩

theorem pointer_to_search : LocalSimulation (pointerModelAccess n) (searchModelAccess n) 25 := by
  simpa using pointer_to_hull.trans hull_to_search

noncomputable def hullToPointer (strategy : OnlineHullBST n) : OnlinePointerBST n :=
  strategy.map hull_to_pointer

noncomputable def pointerToHull (strategy : OnlinePointerBST n) : OnlineHullBST n :=
  strategy.map pointer_to_hull

noncomputable def hullToSearch (strategy : OnlineHullBST n) : OnlineBST n :=
  (strategy.map hull_to_search).toOnlineBST

noncomputable def pointerToSearch (strategy : OnlinePointerBST n) : OnlineBST n :=
  (strategy.map pointer_to_search).toOnlineBST

noncomputable def rootToSearch (strategy : OnlineRootBST n) : OnlineBST n :=
  (strategy.map root_to_search).toOnlineBST

theorem root_run_execution (strategy : OnlineRootBST n) (state : strategy.State)
    (requests : List (Fin n)) :
    ∃ rotations, OfflineExecution requests (strategy.tree state)
      (strategy.tree (strategy.run state requests).1) rotations ∧
        (strategy.run state requests).2 = requests.length + rotations := by
  induction requests generalizing state with
  | nil => exact ⟨0, .done _, rfl⟩
  | cons request requests ih =>
    obtain ⟨headCount, head, root, headCost⟩ := strategy.legal state request
    obtain ⟨tailCount, tail, tailCost⟩ := ih (strategy.advance state request)
    refine ⟨headCount + tailCount, .next head root tail, ?_⟩
    simp only [run, List.length_cons]
    omega

theorem hull_run_execution (strategy : OnlineHullBST n) (state : strategy.State)
    (requests : List (Fin n)) :
    AccessExecution (strategy.tree state).toRaw (requests.map Fin.val)
      (strategy.tree (strategy.run state requests).1).toRaw
      (strategy.run state requests).2 := by
  induction requests generalizing state with
  | nil => exact .nil _
  | cons request requests ih =>
    obtain ⟨access, paid⟩ := strategy.legal state request
    simpa only [run, List.map_cons, paid] using AccessExecution.cons access (ih _)

theorem pointer_run_execution (strategy : OnlinePointerBST n) (state : strategy.State)
    (requests : List (Fin n)) :
    Pointer.Execution (strategy.tree state).toRaw (requests.map Fin.val)
      (strategy.tree (strategy.run state requests).1).toRaw
      (strategy.run state requests).2 := by
  induction requests generalizing state with
  | nil => exact .nil _
  | cons request requests ih => exact .cons (strategy.legal state request) (ih _)

theorem hullToSearch_run_cost (strategy : OnlineHullBST n) (state : strategy.State)
    (requests : List (Fin n)) :
    (strategy.hullToSearch.run state requests).2 ≤ 25 * (strategy.run state requests).2 := by
  change ((strategy.map hull_to_search).toOnlineBST.run state requests).2 ≤ _
  rw [toOnlineBST_run]
  exact map_run_cost strategy hull_to_search state requests

theorem pointerToSearch_run_cost (strategy : OnlinePointerBST n) (state : strategy.State)
    (requests : List (Fin n)) :
    (strategy.pointerToSearch.run state requests).2 ≤ 25 * (strategy.run state requests).2 := by
  change ((strategy.map pointer_to_search).toOnlineBST.run state requests).2 ≤ _
  rw [toOnlineBST_run]
  exact map_run_cost strategy pointer_to_search state requests

theorem rootToSearch_run_cost (strategy : OnlineRootBST n) (state : strategy.State)
    (requests : List (Fin n)) :
    (strategy.rootToSearch.run state requests).2 ≤ 2 * (strategy.run state requests).2 := by
  change ((strategy.map root_to_search).toOnlineBST.run state requests).2 ≤ _
  rw [toOnlineBST_run]
  exact map_run_cost strategy root_to_search state requests

end OnlineModel
end DynamicOptimality
