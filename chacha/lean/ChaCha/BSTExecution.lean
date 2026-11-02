import ChaCha.RestrictedRotations

/-!
# Rooted-hull BST executions

A hull is represented by its ordinary BST skeleton. Its empty child slots hold
the untouched hanging subtrees, in inorder. A legal hull transition rearranges
the skeleton on the same keys and retains all hanging subtrees in their slots.
The charged cost is the number of skeleton nodes, not the universe size.
-/

namespace ChaCha.MTR
namespace Tree

variable {α : Type*}

/-- Fill the inorder gaps of a skeleton, starting at gap index `start`. -/
def graft (skeleton : Tree α) (gaps : Nat → Tree α) (start : Nat := 0) : Tree α :=
  match skeleton with
  | .empty => gaps start
  | .node l x r => .node (graft l gaps start) x (graft r gaps (start + size l + 1))

/-- A shallow skeleton rotation is the same actual shallow rotation after
restoring arbitrary untouched hanging subtrees. -/
theorem RestrictedStep.graft {s t : Tree α} (h : RestrictedStep s t)
    (gaps : Nat → Tree α) (start : Nat) :
    RestrictedStep (graft s gaps start) (graft t gaps start) := by
  cases h <;> simp only [Tree.graft, size]
  all_goals try simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · exact .rootRight _ _ _ _ _
  · exact .rootLeft _ _ _ _ _
  · exact .rightRight _ _ _ _ _ _ _
  · exact .rightLeft _ _ _ _ _ _ _
  · exact .leftRight _ _ _ _ _ _ _
  · exact .leftLeft _ _ _ _ _ _ _

theorem RestrictedSteps.graft {s t : Tree α} {k : Nat} (h : RestrictedSteps k s t)
    (gaps : Nat → Tree α) (start : Nat) :
    RestrictedSteps k (graft s gaps start) (graft t gaps start) := by
  induction h with
  | refl => exact .refl _
  | cons step rest ih => exact .cons (step.graft gaps start) ih

/-- The actual linear rotation bound scales with the touched hull, preserving
all its arbitrary hanging subtrees. -/
theorem graft_simulation_linear (s t : Tree α) (same : inorder s = inorder t)
    (gaps : Nat → Tree α) (start : Nat) :
    ∃ k ≤ 3 * size s + 3 * size t,
      RestrictedSteps k (graft s gaps start) (graft t gaps start) := by
  obtain ⟨k, hk, h⟩ := restricted_rotation_linear s t same
  exact ⟨k, hk, h.graft gaps start⟩

theorem length_inorder (t : Tree α) : (inorder t).length = size t := by
  induction t with
  | empty => rfl
  | node l a r ihl ihr => simp [inorder, size, ihl, ihr]; omega

theorem graft_rootKey (t : Tree α) (gaps : Nat → Tree α) (start : Nat)
    {x : α} (h : rootKey t = some x) : rootKey (graft t gaps start) = some x := by
  cases t with
  | empty => simp [rootKey] at h
  | node l a r => exact h

theorem inorder_sublist_graft (t : Tree α) (gaps : Nat → Tree α) (start : Nat) :
    (inorder t).Sublist (inorder (graft t gaps start)) := by
  induction t generalizing start with
  | empty => exact List.nil_sublist _
  | node l a r ihl ihr =>
    exact ((ihl start).append (List.Sublist.refl [a])).append (ihr _)

variable [LinearOrder α]

theorem ordered_of_graft {t : Tree α} {gaps : Nat → Tree α} {start : Nat}
    (h : Ordered (graft t gaps start)) : Ordered t :=
  List.Pairwise.sublist (inorder_sublist_graft t gaps start) h

/-- Successful search follows from actual BST ordering and membership. -/
theorem searchDepth_exists_of_mem {t : Tree α} {x : α}
    (hord : Ordered t) (hmem : x ∈ inorder t) : ∃ d, searchDepth x t = some d := by
  induction t with
  | empty => simp [inorder] at hmem
  | node l a r ihl ihr =>
    have hl : Ordered l := List.Pairwise.sublist
      ((List.sublist_append_left (inorder l) [a]).trans
        (List.sublist_append_left (inorder l ++ [a]) (inorder r))) hord
    have hr : Ordered r := List.Pairwise.sublist (List.sublist_append_right _ _) hord
    have hleft : ∀ y ∈ inorder l, y < a := by
      have hh := (List.pairwise_append.mp (List.pairwise_append.mp hord).1).2.2
      intro y hy
      exact hh y hy a (by simp)
    have hright : ∀ y ∈ inorder r, a < y := by
      have hh := (List.pairwise_append.mp hord).2.2
      intro y hy
      exact hh a (by simp) y hy
    simp only [inorder, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with (hm | heq) | hm
    · obtain ⟨d, hd⟩ := ihl hl hm
      exact ⟨d + 1, by simp [searchDepth, hleft x hm, hd]⟩
    · subst x
      exact ⟨0, searchDepth_root l r a⟩
    · obtain ⟨d, hd⟩ := ihr hr hm
      exact ⟨d + 1, by simp [searchDepth, not_lt_of_gt (hright x hm), hright x hm, hd]⟩

end Tree

open Tree

/-- One concrete rooted-hull transition serving `x`. -/
structure HullStep {α : Type*} (x : α) (before after : Tree α) where
  source : Tree α
  target : Tree α
  gaps : Nat → Tree α
  source_tree : graft source gaps 0 = before
  target_tree : graft target gaps 0 = after
  same_keys : inorder source = inorder target
  target_root : rootKey target = some x

def HullStep.cost {x : α} {before after : Tree α} (h : HullStep x before after) : Nat :=
  size h.source

theorem HullStep.cost_pos {x : α} {before after : Tree α}
    (h : HullStep x before after) : 0 < h.cost := by
  have hsize : size h.source = size h.target := by
    rw [← length_inorder, h.same_keys, length_inorder]
  have hn : 0 < size h.target := by
    cases ht : h.target with
    | empty => have hr := h.target_root; simp [ht, rootKey] at hr
    | node l a r => simp [size]; omega
  change 0 < size h.source
  omega

theorem HullStep.root_after {x : α} {before after : Tree α}
    (h : HullStep x before after) : rootKey after = some x := by
  rw [← h.target_tree]
  exact graft_rootKey _ _ _ h.target_root

/-- A legal hull transition has a real shallow-rotation simulation charged
only to its own touched nodes. -/
theorem HullStep.shallow_simulation {x : α} {before after : Tree α}
    (h : HullStep x before after) :
    ∃ k ≤ 6 * h.cost, RestrictedSteps k before after := by
  obtain ⟨k, hk, hs⟩ := graft_simulation_linear h.source h.target h.same_keys h.gaps 0
  have hsize : size h.source = size h.target := by
    rw [← length_inorder, h.same_keys, length_inorder]
  refine ⟨k, ?_, ?_⟩
  · unfold HullStep.cost
    omega
  · simpa only [h.source_tree, h.target_tree] using hs

/-- An actual rooted-hull BST execution, with the sum of its hull sizes. -/
inductive HullExecution {α : Type*} : Tree α → List α → Tree α → Nat → Prop
  | nil (t : Tree α) : HullExecution t [] t 0
  | cons {t u v : Tree α} {x : α} {xs : List α} {k : Nat}
      (step : HullStep x t u) (rest : HullExecution u xs v k) :
      HullExecution t (x :: xs) v (step.cost + k)

theorem HullExecution.length_le_cost {t u : Tree α} {xs : List α} {k : Nat}
    (h : HullExecution t xs u k) : xs.length ≤ k := by
  induction h with
  | nil => simp
  | cons step rest ih => have hp := step.cost_pos; simp only [List.length_cons]; omega

/-- A shallow-rotation execution with explicitly marked root accesses.
Rotation steps carry cost one here; root accesses remain in the served word. -/
inductive MarkedTrace {α : Type*} : Tree α → List α → Tree α → Nat → Prop
  | nil (t : Tree α) : MarkedTrace t [] t 0
  | rotate {t u v : Tree α} {xs : List α} {k : Nat}
      (step : RestrictedStep t u) (rest : MarkedTrace u xs v k) :
      MarkedTrace t xs v (k + 1)
  | serve {t v : Tree α} {x : α} {xs : List α} {k : Nat}
      (at_root : rootKey t = some x) (rest : MarkedTrace t xs v k) :
      MarkedTrace t (x :: xs) v k

theorem MarkedTrace.trans {t u v : Tree α} {xs ys : List α} {k l : Nat}
    (h : MarkedTrace t xs u k) (h' : MarkedTrace u ys v l) :
    MarkedTrace t (xs ++ ys) v (k + l) := by
  induction h with
  | nil => simpa using h'
  | rotate step rest ih =>
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      MarkedTrace.rotate step (ih h')
  | serve at_root rest ih => exact .serve at_root (ih h')

theorem Tree.RestrictedSteps.toMarkedTrace {t u : Tree α} {k : Nat}
    (h : RestrictedSteps k t u) : MarkedTrace t [] u k := by
  induction h with
  | refl => exact .nil _
  | cons step rest ih => exact .rotate step ih

theorem MarkedTrace.rotations {t u : Tree α} {xs : List α} {k : Nat}
    (h : MarkedTrace t xs u k) : RestrictedSteps k t u := by
  induction h with
  | nil => exact .refl _
  | rotate step rest ih => exact .cons step ih
  | serve at_root rest ih => exact ih

/-- Restore the initial physical BST by reversing its actual shallow rotations.
This avoids any additional universe-size or touched-union argument. -/
theorem MarkedTrace.close {t u : Tree α} {xs : List α} {k : Nat}
    (h : MarkedTrace t xs u k) : MarkedTrace t xs t (2 * k) := by
  have hh := h.trans h.rotations.symm.toMarkedTrace
  simpa only [List.append_nil, Nat.two_mul] using hh

theorem HullExecution.marked_trace {t u : Tree α} {xs : List α} {cost : Nat}
    (h : HullExecution t xs u cost) :
    ∃ k ≤ 6 * cost, MarkedTrace t xs u k := by
  induction h with
  | nil t => exact ⟨0, by omega, .nil t⟩
  | @cons t u v x xs cost step rest ih =>
    obtain ⟨k, hk, hstep⟩ := step.shallow_simulation
    obtain ⟨l, hl, hrest⟩ := ih
    refine ⟨k + l, by omega, ?_⟩
    exact hstep.toMarkedTrace.trans (.serve step.root_after hrest)

/-- Every rooted-hull BST execution has a closed shallow-rotation execution
serving the same original word, with linear cost and no startup term. -/
theorem HullExecution.closed_marked_trace {t u : Tree α} {xs : List α} {cost : Nat}
    (h : HullExecution t xs u cost) :
    ∃ k ≤ 12 * cost, MarkedTrace t xs t k := by
  obtain ⟨k, hk, ht⟩ := h.marked_trace
  exact ⟨2 * k, by omega, ht.close⟩

/-- The general rooted-hull access model: the requested key belongs to the
touched hull, but the final root is unrestricted. -/
structure HullAccess {α : Type*} (x : α) (before after : Tree α) where
  source : Tree α
  target : Tree α
  gaps : Nat → Tree α
  source_tree : graft source gaps 0 = before
  target_tree : graft target gaps 0 = after
  same_keys : inorder source = inorder target
  requested : x ∈ inorder source

def HullAccess.cost {x : α} {before after : Tree α} (h : HullAccess x before after) : Nat :=
  size h.source

theorem HullAccess.cost_pos {x : α} {before after : Tree α}
    (h : HullAccess x before after) : 0 < h.cost := by
  have hm := h.requested
  have hp : 0 < (inorder h.source).length := List.length_pos_of_mem hm
  simpa only [length_inorder, HullAccess.cost] using hp

variable [LinearOrder α]

/-- An access can be marked between two shallow transformations, with no
restriction on the root of the original after-tree. -/
theorem HullAccess.marked_trace {x : α} {before after : Tree α}
    (h : HullAccess x before after) (hord : Ordered before) :
    ∃ k ≤ 12 * h.cost, MarkedTrace before [x] after k := by
  have hs : Ordered h.source := ordered_of_graft (h.source_tree.symm ▸ hord)
  obtain ⟨d, hd⟩ := searchDepth_exists_of_mem hs h.requested
  let middle := moveToRoot x h.source
  have hinorder : inorder middle = inorder h.source := inorder_moveToRoot x h.source
  obtain ⟨k, hk, hleft⟩ := graft_simulation_linear h.source middle hinorder.symm h.gaps 0
  obtain ⟨l, hl, hright⟩ := graft_simulation_linear middle h.target
    (hinorder.trans h.same_keys) h.gaps 0
  have hroot : rootKey (graft middle h.gaps 0) = some x :=
    graft_rootKey _ _ _ (rootKey_moveToRoot_of_searchDepth x h.source d hd)
  have hsize : size h.source = size h.target := by
    rw [← length_inorder, h.same_keys, length_inorder]
  have hm : size middle = size h.source := by
    rw [← length_inorder, hinorder, length_inorder]
  refine ⟨k + l, ?_, ?_⟩
  · unfold HullAccess.cost
    omega
  · rw [h.source_tree] at hleft
    rw [h.target_tree] at hright
    exact hleft.toMarkedTrace.trans (.serve hroot hright.toMarkedTrace)

theorem HullAccess.ordered_after {x : α} {before after : Tree α}
    (h : HullAccess x before after) (hord : Ordered before) : Ordered after := by
  obtain ⟨_, _, ht⟩ := h.marked_trace hord
  unfold Ordered at *
  rw [← ht.rotations.inorder_eq]
  exact hord

/-- An execution of general rooted-hull accesses, with arbitrary final roots. -/
inductive AccessExecution {α : Type*} : Tree α → List α → Tree α → Nat → Prop
  | nil (t : Tree α) : AccessExecution t [] t 0
  | cons {t u v : Tree α} {x : α} {xs : List α} {k : Nat}
      (step : HullAccess x t u) (rest : AccessExecution u xs v k) :
      AccessExecution t (x :: xs) v (step.cost + k)

omit [LinearOrder α] in
theorem AccessExecution.length_le_cost {t u : Tree α} {xs : List α} {cost : Nat}
    (h : AccessExecution t xs u cost) : xs.length ≤ cost := by
  induction h with
  | nil => simp
  | cons step rest ih =>
    have hp := step.cost_pos
    simp only [List.length_cons]
    omega

theorem AccessExecution.marked_trace {t u : Tree α} {xs : List α} {cost : Nat}
    (h : AccessExecution t xs u cost) (hord : Ordered t) :
    ∃ k ≤ 12 * cost, MarkedTrace t xs u k := by
  induction h with
  | nil t => exact ⟨0, by omega, .nil t⟩
  | @cons t u v x xs cost step rest ih =>
    obtain ⟨k, hk, hstep⟩ := step.marked_trace hord
    obtain ⟨l, hl, hrest⟩ := ih (step.ordered_after hord)
    exact ⟨k + l, by omega, hstep.trans hrest⟩

theorem AccessExecution.closed_marked_trace {t u : Tree α} {xs : List α} {cost : Nat}
    (h : AccessExecution t xs u cost) (hord : Ordered t) :
    ∃ k ≤ 24 * cost, MarkedTrace t xs t k := by
  obtain ⟨k, hk, ht⟩ := h.marked_trace hord
  exact ⟨2 * k, by omega, ht.close⟩

end ChaCha.MTR
