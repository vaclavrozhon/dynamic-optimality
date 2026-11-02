import ChaCha.Paper20261030.SplayAuxiliaryOnlineSharedOPT
import ChaCha.Paper20261030.SplayAuxiliaryRelabel
import ChaCha.Paper20261030.OnlineSearchRotation
import DynamicOptimality.OnlineBST

/-! The ordinary-splay Cha-Cha online strategy on its canonical natural
key universe. Relabeling preserves the chosen state transitions and their
exact charges; all mathematical auxiliary state is free bookkeeping. -/

namespace ChaCha.Paper20261030.SplayAuxiliary.Natural

open DynamicOptimality
open OnlineSearchRotation (keyCount factor reference keyWord requestIndex requestIndex_key requestIndex_rank)

abbrev State (h : Nat) := Online.State (reference h) (keyWord h)

def tree {h : Nat} (state : State h) : RawTree Nat := Relabel.tree Int.toNat (Online.tree state)

 theorem tree_word {h : Nat} (state : State h) : (tree state).inorder = List.range (keyCount h) := by
  rw [tree,Relabel.tree_word,Online.tree_word (Dyadic.canonical_ordered _ _),
    OnlineSpecification.canonical_word,List.map_map]
  simp only [Function.comp_def,Int.toNat_natCast]
  exact List.map_id _

noncomputable def initial (h : Nat) : State h := Online.canonicalState (reference h)

noncomputable def sourceStep {h : Nat} (state : State h) (request : Fin (keyCount h)) :=
  Online.step (Dyadic.canonical_ordered _ _) state (requestIndex request)

noncomputable def next {h : Nat} (state : State h) (request : Fin (keyCount h)) : State h :=
  (sourceStep state request).after

 theorem legal {h : Nat} (state : State h) (request : Fin (keyCount h)) :
    SearchRotation.Access request.val (tree state) (tree (next state request)) (sourceStep state request).cost := by
  have keys : ∀ value ∈ (Online.tree state).inorder, 0 ≤ value := by
    intro value member
    rw [Online.tree_word (Dyadic.canonical_ordered _ _)] at member
    exact ((Dyadic.canonical_zero_mem _ _).mp member).1
  have execution := (sourceStep state request).execution
  change SearchRotation.Access (OnlineSpecification.key (keyWord h) (requestIndex request)) _ _ _ at execution
  rw [requestIndex_key] at execution
  have natural := access_toNat (Int.natCast_nonneg request.val) keys execution
  simpa only [Int.toNat_natCast,tree,next] using natural

noncomputable def strategy (h : Nat) : OnlineBST (keyCount h) where
  State := State h
  tree := tree
  tree_word := tree_word
  advance := next
  accessCost := fun state request => (sourceStep state request).cost
  legal := legal

 theorem run_eq {h : Nat} (state : State h) (requests : List (Fin (keyCount h))) :
    (strategy h).run state requests =
      Online.run (Dyadic.canonical_ordered _ _) state (requests.map requestIndex) := by
  induction requests generalizing state with
  | nil => rfl
  | cons request requests ih =>
    change (let last := (strategy h).run (next state request) requests;
      (last.1,(sourceStep state request).cost+last.2)) = _
    rw [ih]
    rfl

 theorem canonical_bound (h : Nat) (requests : List (Fin (keyCount h))) :
    ((strategy h).run (initial h) requests).2 ≤
      60002000*(OPT requests+keyCount h)*factor h := by
  have bound := Online.canonical_OPT_cost h (requests.map requestIndex)
  have ranks : (requests.map requestIndex).map OnlineSpecification.rank = requests := by
    rw [List.map_map]
    simp only [Function.comp_def,requestIndex_rank]
    exact List.map_id _
  rw [ranks] at bound
  rw [run_eq]
  exact bound

/-- The public transition retains the ordinary-splay request certificate. -/
 theorem ordinary {h : Nat} (state : State h) (request : Fin (keyCount h)) :
    RequestExecution (reference h) state.memory (request.val : Int) state.components
      (next state request).components := by
  have instanceSame : (fun a b : Int => LinearOrder.toDecidableEq a b) = Int.instDecidableEq := Subsingleton.elim _ _
  simpa only [next,Online.key,requestIndex_key,instanceSame] using (sourceStep state request).ordinary

 theorem next_memory {h : Nat} (state : State h) (request : Fin (keyCount h)) :
    (next state request).memory = state.memory.completeAdvance (h+1) (request.val : Int) := by
  have instanceSame : (fun a b : Int => LinearOrder.toDecidableEq a b) = Int.instDecidableEq := Subsingleton.elim _ _
  simpa only [next,Online.key,requestIndex_key,instanceSame] using (sourceStep state request).memory

end ChaCha.Paper20261030.SplayAuxiliary.Natural
