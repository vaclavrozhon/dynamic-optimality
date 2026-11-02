import ChaCha.Paper20261030.GlobalPrimaryOnlineState
import DynamicOptimality.PointerInitialization

set_option autoImplicit false

/-! Initialization of the fixed online strategy from any actual tree on
the same key word. The initialization is chosen independently of all
requests, performed once at the first request, and charged linearly.
An empty prefix leaves the supplied initial tree untouched. -/

namespace ChaCha.Paper20261030.OnlineSpecification

open ColoredStorage PreferredProjection Secondary SecondaryDecomposition LocalReferences

variable {α : Type*} [DecidableEq α] {h : Nat}

structure TreeInitialization {reference : DepthTree 0 h} {keyWord : List α}
    (initial : MTR.Tree α) (state : State reference keyWord) where
  cost : Nat
  trace : MTR.Pointer.Trace (.atRoot initial) [] (.atRoot state.tree) cost
  bound : cost ≤ 18*initial.size

theorem tree_initialization_exists {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (initial : MTR.Tree α) (state : State reference keyWord)
    (word : initial.inorder = keyWord) : Nonempty (TreeInitialization initial state) := by
  obtain ⟨cost,trace,bound⟩ := DynamicOptimality.initialize_pointer initial state.tree
    (word.trans (state.tree_word distinct).symm) []
  exact ⟨⟨cost,trace,bound⟩⟩

noncomputable def treeInitialization {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (initial : MTR.Tree α) (state : State reference keyWord)
    (word : initial.inorder = keyWord) : TreeInitialization initial state :=
  Classical.choice (tree_initialization_exists distinct initial state word)

noncomputable def initializedCost {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (initial : MTR.Tree α) (state : State reference keyWord)
    (word : initial.inorder = keyWord) (requests : List (Fin keyWord.length)) : Nat :=
  if requests = [] then 0 else (treeInitialization distinct initial state word).cost + pointerCost distinct state requests

noncomputable def initializedTree {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (initial : MTR.Tree α) (state : State reference keyWord)
    (requests : List (Fin keyWord.length)) : MTR.Tree α :=
  if requests = [] then initial else (run distinct state requests).1.tree

theorem initialized_execution {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (initial : MTR.Tree α) (state : State reference keyWord)
    (word : initial.inorder = keyWord) (requests : List (Fin keyWord.length)) :
    MTR.Pointer.Execution initial (requests.map (key keyWord))
      (initializedTree distinct initial state requests) (initializedCost distinct initial state word requests) := by
  by_cases empty : requests = []
  · subst requests
    simpa [initializedTree,initializedCost] using MTR.Pointer.Execution.nil initial
  · simp only [initializedTree,initializedCost,if_neg empty]
    exact DynamicOptimality.prepend_pointer_initialization (treeInitialization distinct initial state word).trace
      (pointerCost_execution distinct state requests) (by
        intro mapped
        cases requests with
        | nil => exact empty rfl
        | cons request requests => simp at mapped)

theorem initialized_cost_bound {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (initial : MTR.Tree α) (state : State reference keyWord)
    (word : initial.inorder = keyWord) (requests : List (Fin keyWord.length)) :
    initializedCost distinct initial state word requests ≤ 18*initial.size + (run distinct state requests).2 := by
  by_cases empty : requests = []
  · simp only [initializedCost,if_pos empty]; exact Nat.zero_le _
  · simp only [initializedCost,if_neg empty]
    exact Nat.add_le_add (treeInitialization distinct initial state word).bound (pointerCost_le_run distinct state requests)

theorem initialized_cost_append {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (initial : MTR.Tree α) (state : State reference keyWord)
    (word : initial.inorder = keyWord) (first last : List (Fin keyWord.length)) (started : first ≠ []) :
    initializedCost distinct initial state word (first++last) = initializedCost distinct initial state word first +
      pointerCost distinct (run distinct state first).1 last := by
  have combined : first++last ≠ [] := fun empty => started (List.append_eq_nil_iff.mp empty).1
  simp only [initializedCost,if_neg combined,if_neg started,pointerCost_append,Nat.add_assoc]

theorem initialized_tree_word {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (initial : MTR.Tree α) (state : State reference keyWord)
    (word : initial.inorder = keyWord) (requests : List (Fin keyWord.length)) :
    (initializedTree distinct initial state requests).inorder = keyWord := by
  by_cases empty : requests = []
  · simpa only [initializedTree,if_pos empty] using word
  · simpa only [initializedTree,if_neg empty] using (run distinct state requests).1.tree_word distinct

end ChaCha.Paper20261030.OnlineSpecification
