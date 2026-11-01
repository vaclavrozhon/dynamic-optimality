import TangoSquared.Paper20261030.OnlineSharedOPT

set_option autoImplicit false

/-! The canonical maintained component state already determines one
actual ordinary key tree. Under free computation, a fixed choice of
the proved next physical transition is an online mathematical strategy:
the choice depends on the current state and request, never on the future
request word. This module fixes the erased pointer transition costs too,
so the execution and cost bounds concern that same prefix-consistent
strategy. It does not assert effective evaluation of classical choice.
-/

namespace TangoSquared.Paper20261030.OnlineSpecification

open ColoredStorage PreferredProjection Secondary SecondaryDecomposition LocalReferences

variable {α : Type*} [DecidableEq α] {h : Nat}

def State.tree {reference : DepthTree 0 h} {keyWord : List α} (state : State reference keyWord) :
    MTR.Tree α := Auxiliary.Metadata.forgetTree state.physical

theorem State.tree_word {reference : DepthTree 0 h} {keyWord : List α}
    (state : State reference keyWord) (distinct : keyWord.Nodup) : state.tree.inorder = keyWord := by
  rw [State.tree,State.physical,GapBST.Storage.forget_encode,GapBST.encode_word]
  exact (state.valid.physical_leaves (completedDepth reference) state.perfect
    (state.word.symm ▸ distinct) state.memory.preference state.components).trans state.word

theorem State.tree_key {reference : DepthTree 0 h} {keyWord : List α}
    (state : State reference keyWord) (distinct : keyWord.Nodup) (request : Fin keyWord.length) :
    key keyWord request ∈ state.tree.inorder := by
  rw [state.tree_word distinct]
  exact List.getElem_mem _

/-- A selected ordinary-tree transition to the very same next maintained
state used by `step`. The witness is chosen once per state and request. -/
structure PointerTransition {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (state : State reference keyWord) (request : Fin keyWord.length) where
  cost : Nat
  execution : MTR.Pointer.Access (key keyWord request) state.tree
    (step distinct state request).after.tree cost
  bound : cost ≤ (step distinct state request).cost

theorem pointer_transition_exists {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (state : State reference keyWord) (request : Fin keyWord.length) :
    Nonempty (PointerTransition distinct state request) := by
  obtain ⟨cost,bound,execution⟩ := (step distinct state request).execution.pointer
  exact ⟨⟨cost,execution,bound⟩⟩

noncomputable def pointerStep {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (state : State reference keyWord) (request : Fin keyWord.length) :
    PointerTransition distinct state request := Classical.choice (pointer_transition_exists distinct state request)

noncomputable def pointerCost {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (state : State reference keyWord) : List (Fin keyWord.length) → Nat
  | [] => 0
  | request::requests => (pointerStep distinct state request).cost +
      pointerCost distinct (step distinct state request).after requests

theorem pointerCost_execution {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (state : State reference keyWord) (requests : List (Fin keyWord.length)) :
    MTR.Pointer.Execution state.tree (requests.map (key keyWord))
      (run distinct state requests).1.tree (pointerCost distinct state requests) := by
  induction requests generalizing state with
  | nil => exact .nil _
  | cons request requests ih => exact .cons (pointerStep distinct state request).execution (ih _)

theorem pointerCost_le_run {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (state : State reference keyWord) (requests : List (Fin keyWord.length)) :
    pointerCost distinct state requests ≤ (run distinct state requests).2 := by
  induction requests generalizing state with
  | nil => exact le_rfl
  | cons request requests ih =>
    exact Nat.add_le_add (pointerStep distinct state request).bound (ih _)

theorem pointerCost_append {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (state : State reference keyWord)
    (first last : List (Fin keyWord.length)) :
    pointerCost distinct state (first++last) = pointerCost distinct state first +
      pointerCost distinct (run distinct state first).1 last := by
  induction first generalizing state with
  | nil => simp only [List.nil_append,pointerCost,run,Nat.zero_add]
  | cons request first ih => simp only [List.cons_append,pointerCost,run,ih,Nat.add_assoc]

theorem canonical_tree_word (reference : DepthTree 0 h) :
    (canonicalState reference).tree.inorder = (List.range (2^(h+1))).map (fun key : Nat => (key : Int)) := by
  rw [(canonicalState reference).tree_word (Dyadic.canonical_nodup _ _),canonical_word]

theorem canonical_pointer_OPT_cost (height : Nat)
    (requests : List (Fin (Dyadic.canonical (height+1) 0).leaves.length)) :
    pointerCost (Dyadic.canonical_nodup _ _) (canonicalState (DepthTree.midpoint 0 height (Nat.zero_le height))) requests ≤
      67440000000*(DynamicOptimality.OPT (requests.map rank)+2^(height+1))*
        (Nat.clog 2 (Nat.clog 2 (height+1)+2)+1) :=
  (pointerCost_le_run _ _ _).trans (canonical_OPT_cost height requests)

end TangoSquared.Paper20261030.OnlineSpecification
