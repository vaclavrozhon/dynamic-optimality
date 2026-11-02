import DynamicOptimality.OnlineBST
import ChaCha.Paper20261030.OnlineSearchRotationInitializationCore

/-!
# Starting an online BST strategy from an arbitrary supplied tree

A fresh state contains the supplied indexed BST. Its first request searches
that tree, performs a fixed linear-cost initialization, and executes the
canonical strategy's first rotations. All subsequent transitions are the
unchanged canonical strategy. The initialization is paid at most once and
no transition depends on future requests.
-/

namespace DynamicOptimality.OnlineBST.Initialization

open DynamicOptimality.SearchRotation

variable {n : Nat}

abbrev State (source : OnlineBST n) := BST 0 n ⊕ source.State

/-- The indexed shared BST stores exactly its interval of keys. -/
theorem indexed_inorder (tree : BST 0 n) : tree.toRaw.inorder = List.range n := by
  apply List.Pairwise.eq_of_mem_iff tree.toRaw_ordered List.pairwise_lt_range
  intro key
  rw [BST.toRaw_mem,List.mem_range]
  omega

/-- The initialization is fixed before the first request is supplied. -/
noncomputable def fixedInitialization (source : OnlineBST n) (canonical : source.State)
    (before : BST 0 n) :
    ChaCha.Paper20261030.OnlineSearchRotationInitialization.Initialization
      before.toRaw (source.tree canonical) :=
  ChaCha.Paper20261030.OnlineSearchRotationInitialization.initialization
    before.toRaw (source.tree canonical)
    ((indexed_inorder before).trans (source.tree_word canonical).symm)

structure FirstTransition (source : OnlineBST n) (canonical : source.State)
    (before : BST 0 n) (request : Fin n) where
  cost : Nat
  canonicalDepth : Nat
  canonicalCount : Nat
  canonicalSearch : ChaCha.MTR.Tree.searchDepth request.val (source.tree canonical) = some canonicalDepth
  canonicalRun : Rotations (source.tree canonical)
    (source.tree (source.advance canonical request)) canonicalCount
  canonicalCost : source.accessCost canonical request = canonicalDepth + 1 + canonicalCount
  exactCost : cost = before.depth request.val + 1 +
    ((fixedInitialization source canonical before).count + canonicalCount)
  legal : Access request.val before.toRaw
    (source.tree (source.advance canonical request)) cost
  bound : cost ≤ 19*n + source.accessCost canonical request

 theorem firstTransition_exists (source : OnlineBST n) (canonical : source.State)
    (before : BST 0 n) (request : Fin n) :
    Nonempty (FirstTransition source canonical before request) := by
  obtain ⟨depth,count,search,run,paid⟩ := source.legal canonical request
  let setup := fixedInitialization source canonical before
  have depthBound := before.depth_le_size request.val
  rw [before.size_eq_upper] at depthBound
  have setupBound := setup.bound
  rw [BST.toRaw_size,before.size_eq_upper] at setupBound
  refine ⟨⟨before.depth request.val + 1 + (setup.count+count),depth,count,
    search,run,paid,rfl,?_,?_⟩⟩
  · exact ⟨before.depth request.val,setup.count+count,
      toRaw_searchDepth before (Nat.zero_le _) request.isLt,setup.rotations.append run,rfl⟩
  · omega

/-- The chosen first transition retains a literal concatenation through the
canonical tree, with exactly its charged rotation count. -/
theorem FirstTransition.transcript {source : OnlineBST n} {canonical : source.State}
    {before : BST 0 n} {request : Fin n}
    (transition : FirstTransition source canonical before request) :
    Rotations before.toRaw (source.tree (source.advance canonical request))
      ((fixedInitialization source canonical before).count+transition.canonicalCount) :=
  (fixedInitialization source canonical before).rotations.append transition.canonicalRun

/-- A supplied algorithmic transcript with the canonical cost has precisely
the retained count, so it can replace the canonical part without changing
any endpoint or charge. -/
theorem FirstTransition.canonicalCount_eq {source : OnlineBST n} {canonical : source.State}
    {before : BST 0 n} {request : Fin n}
    (transition : FirstTransition source canonical before request) {depth count : Nat}
    (search : ChaCha.MTR.Tree.searchDepth request.val (source.tree canonical) = some depth)
    (paid : source.accessCost canonical request = depth+1+count) :
    transition.canonicalCount = count := by
  have same := Option.some.inj (transition.canonicalSearch.symm.trans search)
  have original := transition.canonicalCost
  omega

noncomputable def firstStep (source : OnlineBST n) (canonical : source.State)
    (before : BST 0 n) (request : Fin n) :
    FirstTransition source canonical before request :=
  Classical.choice (firstTransition_exists source canonical before request)

def tree (source : OnlineBST n) : State source → RawTree Nat
  | .inl before => before.toRaw
  | .inr active => source.tree active

def advance (source : OnlineBST n) (canonical : source.State) :
    State source → Fin n → State source
  | .inl _,request => .inr (source.advance canonical request)
  | .inr active,request => .inr (source.advance active request)

noncomputable def accessCost (source : OnlineBST n) (canonical : source.State) :
    State source → Fin n → Nat
  | .inl before,request => (firstStep source canonical before request).cost
  | .inr active,request => source.accessCost active request

noncomputable def strategy (source : OnlineBST n) (canonical : source.State) : OnlineBST n where
  State := State source
  tree := tree source
  tree_word state := by
    cases state with
    | inl before => exact indexed_inorder before
    | inr active => exact source.tree_word active
  advance := advance source canonical
  accessCost := accessCost source canonical
  legal state request := by
    cases state with
    | inl before => exact (firstStep source canonical before request).legal
    | inr active => exact source.legal active request

/-- The fresh physical tree is the supplied BST, before any initialization. -/
theorem initial_tree (source : OnlineBST n) (canonical : source.State) (before : BST 0 n) :
    (strategy source canonical).tree (.inl before) = before.toRaw := rfl

/-- Once active, the wrapper preserves the exact states and costs. -/
theorem run_active (source : OnlineBST n) (canonical active : source.State)
    (requests : List (Fin n)) :
    (strategy source canonical).run (.inr active) requests =
      (.inr (source.run active requests).1,(source.run active requests).2) := by
  induction requests generalizing active with
  | nil => rfl
  | cons request rest ih =>
      simpa only [OnlineBST.run,strategy,advance,accessCost] using
        congrArg (fun result : State source × Nat =>
          (result.1,source.accessCost active request+result.2))
          (ih (source.advance active request))

/-- Initialization contributes a single additive linear allowance. -/
theorem run_cost_le (source : OnlineBST n) (canonical : source.State)
    (before : BST 0 n) (requests : List (Fin n)) :
    ((strategy source canonical).run (.inl before) requests).2 ≤
      19*n+(source.run canonical requests).2 := by
  cases requests with
  | nil => simp [OnlineBST.run]
  | cons request rest =>
      have first := (firstStep source canonical before request).bound
      change (firstStep source canonical before request).cost +
        ((strategy source canonical).run (.inr (source.advance canonical request)) rest).2 ≤ _
      rw [run_active]
      change (firstStep source canonical before request).cost +
        (source.run (source.advance canonical request) rest).2 ≤
          19*n+(source.accessCost canonical request+
            (source.run (source.advance canonical request) rest).2)
      omega

/-- A nonempty run reaches exactly the canonical run's physical tree. -/
theorem run_tree (source : OnlineBST n) (canonical : source.State)
    (before : BST 0 n) (request : Fin n) (rest : List (Fin n)) :
    (strategy source canonical).tree
      ((strategy source canonical).run (.inl before) (request::rest)).1 =
      source.tree (source.run canonical (request::rest)).1 := by
  change (strategy source canonical).tree
    ((strategy source canonical).run (.inr (source.advance canonical request)) rest).1 = _
  rw [run_active]
  rfl

end DynamicOptimality.OnlineBST.Initialization
