import TangoSquared.Paper20261030.GlobalPrimaryOnlineState
import TangoSquared.Paper20261030.SearchRotationMetadata
import DynamicOptimality.PointerRelabel
import DynamicOptimality.SearchRotationEquivalence

set_option autoImplicit false

/-! A deterministic online Tango-squared strategy on the natural keys
`0,...,2^(h+1)-1`. Each request searches its actual initial tree and then
performs ordinary rotations. All other computation and bookkeeping are
free in this model. A single transition is fixed for each maintained
state and current request; it is never selected using a future request
word. Classical choice specifies the strategy, as permitted by the
abstract model; no executable evaluator is asserted.

The maintained states and their successors are exactly those already
used by `OnlineSpecification`. Relabeling their nonnegative integer keys
gives the public natural-key tree without adding any vertices. -/

namespace TangoSquared.Paper20261030.OnlineSearchRotation

open DynamicOptimality

abbrev keyCount (h : Nat) : Nat := 2^(h+1)

def factor (h : Nat) : Nat := Nat.clog 2 (Nat.clog 2 (h+1)+2)+1

def reference (h : Nat) := DepthTree.midpoint 0 h (Nat.zero_le h)

abbrev keyWord (h : Nat) := (Dyadic.canonical (h+1) 0).leaves

theorem keyWord_length (h : Nat) : (keyWord h).length = keyCount h := by
  rw [keyWord,OnlineSpecification.canonical_word,List.length_map,List.length_range]

theorem keyWord_distinct (h : Nat) : (keyWord h).Nodup := Dyadic.canonical_nodup _ _

def requestIndex {h : Nat} (request : Fin (keyCount h)) : Fin (keyWord h).length :=
  ⟨request.val,by rw [keyWord_length]; exact request.isLt⟩

theorem requestIndex_rank {h : Nat} (request : Fin (keyCount h)) :
    OnlineSpecification.rank (requestIndex request) = request := Fin.ext rfl

theorem requestIndex_key {h : Nat} (request : Fin (keyCount h)) :
    OnlineSpecification.key (keyWord h) (requestIndex request) = (request.val : Int) := by
  rw [OnlineSpecification.canonical_key,requestIndex_rank]

/-- Proof-relevant maintained component data is allowed as free internal
state. Its public tree is the actual ordinary BST defined below. -/
structure State (h : Nat) where
  maintained : OnlineSpecification.State (reference h) (keyWord h)

def State.tree {h : Nat} (state : State h) : RawTree Nat :=
  Relabel.tree Int.toNat state.maintained.tree

theorem State.tree_inorder {h : Nat} (state : State h) :
    state.tree.inorder = List.range (keyCount h) := by
  rw [State.tree,Relabel.tree_word,state.maintained.tree_word (keyWord_distinct h),
    keyWord,OnlineSpecification.canonical_word,List.map_map]
  simp only [Function.comp_def,Int.toNat_natCast]
  exact List.map_id _

theorem State.tree_ordered {h : Nat} (state : State h) : MTR.Tree.Ordered state.tree := by
  unfold MTR.Tree.Ordered
  rw [state.tree_inorder]
  exact List.pairwise_lt_range

theorem State.tree_key {h : Nat} (state : State h) (request : Fin (keyCount h)) :
    request.val ∈ state.tree.inorder := by
  rw [state.tree_inorder]
  exact List.mem_range.mpr request.isLt

noncomputable def initial (h : Nat) : State h :=
  ⟨OnlineSpecification.canonicalState (reference h)⟩

noncomputable def sourceStep {h : Nat} (state : State h) (request : Fin (keyCount h)) :=
  OnlineSpecification.step (keyWord_distinct h) state.maintained (requestIndex request)

noncomputable def next {h : Nat} (state : State h) (request : Fin (keyCount h)) : State h :=
  ⟨(sourceStep state request).after⟩

theorem next_memory {h : Nat} (state : State h) (request : Fin (keyCount h)) :
    (next state request).maintained.memory =
      state.maintained.memory.completeAdvance (h+1) (request.val : Int) := by
  simpa only [next,sourceStep,requestIndex_key] using (sourceStep state request).memory

/-- One fixed actual search-and-rotation access to the same canonical
successor as the maintained source transition. -/
structure Transition {h : Nat} (state : State h) (request : Fin (keyCount h)) where
  cost : Nat
  execution : SearchRotation.Access request.val state.tree (next state request).tree cost
  bound : cost ≤ 2*(sourceStep state request).cost

theorem transition_exists {h : Nat} (state : State h) (request : Fin (keyCount h)) :
    Nonempty (Transition state request) := by
  obtain ⟨pointerCost,pointerBound,pointer⟩ := (sourceStep state request).execution.pointer
  have natural := Relabel.access Int.toNat pointer
  have actual : MTR.Pointer.Access request.val state.tree (next state request).tree pointerCost := by
    simpa only [State.tree,next,sourceStep,requestIndex_key,Int.toNat_natCast,OnlineSpecification.State.tree] using natural
  obtain ⟨cost,execution,bound⟩ := SearchRotationBridge.pointer_access state.tree_ordered actual
  exact ⟨⟨cost,execution,bound.trans (Nat.mul_le_mul_left 2 pointerBound)⟩⟩

noncomputable def step {h : Nat} (state : State h) (request : Fin (keyCount h)) : Transition state request :=
  Classical.choice (transition_exists state request)

noncomputable def run {h : Nat} (state : State h) : List (Fin (keyCount h)) → State h × Nat
  | [] => (state,0)
  | request::requests =>
      let last := run (next state request) requests
      (last.1,(step state request).cost+last.2)

theorem run_execution {h : Nat} (state : State h) (requests : List (Fin (keyCount h))) :
    SearchRotation.Execution state.tree (requests.map Fin.val)
      (run state requests).1.tree (run state requests).2 := by
  induction requests generalizing state with
  | nil => exact .nil _
  | cons request requests ih => exact .cons (step state request).execution (ih _)

/-- The public strategy retains the exact existing maintained successor
states. Only the charged operation model and original key type change. -/
theorem run_state {h : Nat} (state : State h) (requests : List (Fin (keyCount h))) :
    (run state requests).1.maintained =
      (OnlineSpecification.run (keyWord_distinct h) state.maintained (requests.map requestIndex)).1 := by
  induction requests generalizing state with
  | nil => rfl
  | cons request requests ih =>
    change (run (next state request) requests).1.maintained =
      (OnlineSpecification.run (keyWord_distinct h) (sourceStep state request).after (requests.map requestIndex)).1
    exact ih (next state request)

theorem run_cost_le_source {h : Nat} (state : State h) (requests : List (Fin (keyCount h))) :
    (run state requests).2 ≤
      2*(OnlineSpecification.run (keyWord_distinct h) state.maintained (requests.map requestIndex)).2 := by
  induction requests generalizing state with
  | nil => exact le_rfl
  | cons request requests ih =>
    have front := (step state request).bound
    have back := ih (next state request)
    change (step state request).cost+(run (next state request) requests).2 ≤
      2*((sourceStep state request).cost+
        (OnlineSpecification.run (keyWord_distinct h) (sourceStep state request).after (requests.map requestIndex)).2)
    change (run (next state request) requests).2 ≤
      2*(OnlineSpecification.run (keyWord_distinct h) (sourceStep state request).after (requests.map requestIndex)).2 at back
    omega

/-- Extending a prefix continues from its already selected actual state
and adds the costs of those same per-request transitions. -/
theorem run_append {h : Nat} (state : State h) (first last : List (Fin (keyCount h))) :
    run state (first++last) =
      let front := run state first
      let back := run front.1 last
      (back.1,front.2+back.2) := by
  induction first generalizing state with
  | nil => simp only [List.nil_append,run,Nat.zero_add]
  | cons request first ih => simp only [List.cons_append,run,ih,Nat.add_assoc]

theorem run_state_append {h : Nat} (state : State h) (first last : List (Fin (keyCount h))) :
    (run state (first++last)).1 = (run (run state first).1 last).1 := by rw [run_append]

theorem run_cost_append {h : Nat} (state : State h) (first last : List (Fin (keyCount h))) :
    (run state (first++last)).2 = (run state first).2 + (run (run state first).1 last).2 := by
  rw [run_append]

theorem canonical_bound (h : Nat) (requests : List (Fin (keyCount h))) :
    (run (initial h) requests).2 ≤
      134880000000*(OPT requests+keyCount h)*factor h := by
  have bound := OnlineSpecification.canonical_OPT_cost h (requests.map requestIndex)
  have ranks : (requests.map requestIndex).map OnlineSpecification.rank = requests := by
    rw [List.map_map]
    simp only [Function.comp_def,requestIndex_rank]
    exact List.map_id _
  rw [ranks] at bound
  have actual := run_cost_le_source (initial h) requests
  change (run (initial h) requests).2 ≤ _ at actual
  change (OnlineSpecification.run (keyWord_distinct h) (initial h).maintained
    (requests.map requestIndex)).2 ≤ 67440000000*(OPT requests+keyCount h)*factor h at bound
  exact actual.trans (by nlinarith)

/-- Comparison with every actual competing execution in the same cost
model. The shared `OPT` is reused; no new optimum is introduced. -/
theorem canonical_competitor_bound (h : Nat) (requests : List (Fin (keyCount h)))
    (competitor : BST 0 (keyCount h)) {final : RawTree Nat} {cost : Nat}
    (execution : SearchRotation.Execution competitor.toRaw (requests.map Fin.val) final cost) :
    (run (initial h) requests).2 ≤ 269760000000*(cost+keyCount h)*factor h := by
  have optimum := SearchRotation.OPT_le_cost competitor requests execution
  calc
    (run (initial h) requests).2 ≤ 134880000000*(OPT requests+keyCount h)*factor h := canonical_bound h requests
    _ ≤ 134880000000*(2*(cost+keyCount h))*factor h :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    _ = _ := by ring

end TangoSquared.Paper20261030.OnlineSearchRotation
