import MultiSplay.GlobalPreferredHistory
import DynamicOptimality.OnlineBST

/-!
# A fixed classical MultiSplay strategy on an indexed reference

Every transition is chosen from proved physical classical executions using
only its current state and request. The choice is mathematical; computation
is free in the shared search-depth-plus-rotations model. This module proves
legality and prefix consistency, while the competitive bound additionally
requires the persistent forest replay and its cheap exact-word comparator.
-/

namespace MultiSplay.Global.Preferred.Online

open DynamicOptimality DynamicOptimality.SearchRotation
open TangoSquared.MTR
open EndpointEncoding ClassicalSwitch

variable {n : Nat}

structure State (reference : BST 0 n) where
  preference : EndpointEncoding.State
  actual : BST 0 n
  represented : Realizes preference reference.toRaw actual.toRaw

/-- The reference tree itself is an actual representation for every initial
preference state, including the empty universe. -/
def initial (reference : BST 0 n) (preference : EndpointEncoding.State) : State reference :=
  ⟨preference,reference,Preferred.initial preference reference.toRaw⟩

structure Transition {reference : BST 0 n} (state : State reference) (request : Fin n) where
  after : BST 0 n
  rotations : Nat
  work : Nat
  classicalRun : Switches state.preference reference.toRaw
    (actualEmissions state.preference (nodeAddress reference request.val))
    state.actual.toRaw after.toRaw rotations work
  represented : Realizes (nodeStep state.preference (nodeAddress reference request.val))
    reference.toRaw after.toRaw
  legal : Access request.val state.actual.toRaw after.toRaw
    (state.actual.depth request.val + 1 + rotations)
  bound : state.actual.depth request.val + 1 + rotations ≤ 2*work+1

 theorem transition_exists {reference : BST 0 n} (state : State reference) (request : Fin n) :
    Nonempty (Transition state request) := by
  obtain ⟨after,count,work,run,next,legal,bound⟩ :=
    request_access reference state.actual request state.preference state.represented
  obtain ⟨indexed,lifted,same⟩ := rotations_lift run.rotations state.actual rfl
  exact ⟨⟨indexed,count,work,same.symm ▸ run,same.symm ▸ next,same.symm ▸ legal,bound⟩⟩

/-- One fixed choice per current state and request. No future word is an input. -/
noncomputable def step {reference : BST 0 n} (state : State reference) (request : Fin n) :
    Transition state request := Classical.choice (transition_exists state request)

noncomputable def advance {reference : BST 0 n} (state : State reference) (request : Fin n) :
    State reference :=
  ⟨nodeStep state.preference (nodeAddress reference request.val),
    (step state request).after,(step state request).represented⟩

def accessCost {reference : BST 0 n} (state : State reference) (request : Fin n)
    (transition : Transition state request) : Nat :=
  state.actual.depth request.val + 1 + transition.rotations

 theorem indexed_inorder (tree : BST 0 n) : tree.toRaw.inorder = List.range n := by
  apply List.Pairwise.eq_of_mem_iff tree.toRaw_ordered List.pairwise_lt_range
  intro key
  rw [BST.toRaw_mem,List.mem_range]
  omega

noncomputable def strategy (reference : BST 0 n) : OnlineBST n where
  State := State reference
  tree state := state.actual.toRaw
  tree_word state := indexed_inorder state.actual
  advance := advance
  accessCost state request := accessCost state request (step state request)
  legal state request := (step state request).legal

noncomputable def runWork {reference : BST 0 n} (state : State reference) : List (Fin n) → Nat
  | [] => 0
  | request::rest => (step state request).work + runWork (advance state request) rest

noncomputable def runRotations {reference : BST 0 n} (state : State reference) : List (Fin n) → Nat
  | [] => 0
  | request::rest => (step state request).rotations + runRotations (advance state request) rest

/-- Chronological original requests, retaining the actual classical switch
schedule inside each request. This certificate connects the online choices
to a persistent forest replay without changing those choices afterward. -/
inductive Requests (reference : BST 0 n) : EndpointEncoding.State → List (Fin n) →
    RawTree Nat → RawTree Nat → Nat → Nat → Prop
  | nil (preference : EndpointEncoding.State) (physical : RawTree Nat) :
      Requests reference preference [] physical physical 0 0
  | cons {preference : EndpointEncoding.State} {request : Fin n} {rest : List (Fin n)}
      {before middle after : RawTree Nat} {firstCount restCount firstWork restWork : Nat}
      (first : Switches preference reference.toRaw
        (actualEmissions preference (nodeAddress reference request.val))
        before middle firstCount firstWork)
      (later : Requests reference (nodeStep preference (nodeAddress reference request.val)) rest
        middle after restCount restWork) :
      Requests reference preference (request::rest) before after
        (firstCount+restCount) (firstWork+restWork)

 theorem run_classical {reference : BST 0 n} (state : State reference) (requests : List (Fin n)) :
    Requests reference state.preference requests state.actual.toRaw
      ((strategy reference).run state requests).1.actual.toRaw
      (runRotations state requests) (runWork state requests) := by
  induction requests generalizing state with
  | nil => exact .nil _ _
  | cons request rest ih => exact .cons (step state request).classicalRun (ih (advance state request))

 theorem run_cost_le {reference : BST 0 n} (state : State reference) (requests : List (Fin n)) :
    ((strategy reference).run state requests).2 ≤ 2 * runWork state requests + requests.length := by
  induction requests generalizing state with
  | nil => simp [OnlineBST.run,runWork]
  | cons request rest ih =>
      have first := (step state request).bound
      have later := ih (advance state request)
      change state.actual.depth request.val + 1 + (step state request).rotations +
        ((strategy reference).run (advance state request) rest).2 ≤
          2 * ((step state request).work + runWork (advance state request) rest) + rest.length + 1
      omega

 theorem execution {reference : BST 0 n} (state : State reference) (requests : List (Fin n)) :
    SearchRotation.Execution state.actual.toRaw (requests.map Fin.val)
      ((strategy reference).run state requests).1.actual.toRaw
      ((strategy reference).run state requests).2 :=
  (strategy reference).run_execution state requests

 theorem online {reference : BST 0 n} (state : State reference) (first rest : List (Fin n)) :
    (strategy reference).run state (first++rest) =
      let front := (strategy reference).run state first
      let back := (strategy reference).run front.1 rest
      (back.1,front.2+back.2) :=
  (strategy reference).run_append state first rest

 theorem initial_tree (reference : BST 0 n) (preference : EndpointEncoding.State) :
    (strategy reference).tree (initial reference preference) = reference.toRaw := rfl

 theorem empty_word {reference : BST 0 n} (state : State reference) :
    (strategy reference).run state [] = (state,0) := rfl

end MultiSplay.Global.Preferred.Online
