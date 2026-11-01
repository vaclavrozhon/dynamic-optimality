import DynamicOptimality.SearchRotationIndexed

/-!
# Constant-factor equivalence with the shared root-serving optimum

The local conversion searches for the current request, brings it to the
root, serves it, undoes those rotations, and executes the specified final
rotations. Thus its next boundary tree is exactly the specified tree and
it needs no future requests. The converse uses the fact that each rotation
can reduce the requested key's depth by at most one.
-/

namespace DynamicOptimality.SearchRotation

open TangoSquared.MTR

/-- A local root service and return to the prescribed boundary tree.
The two rotation sequences use only this access and its initial tree. -/
theorem Access.rootService {n cost : Nat} {key : Fin n}
    {before : BST 0 n} {after : RawTree Nat}
    (access : Access key.val before.toRaw after cost) :
    ∃ (served next : BST 0 n) (depth count : Nat),
      Splay.Tree.BST.RotationExecution depth before served ∧
      served.HasRoot key.val ∧
      Splay.Tree.BST.RotationExecution (depth + count) served next ∧
      next.toRaw = after ∧ cost = depth + 1 + count := by
  obtain ⟨depth, count, search, trace, costEq⟩ := access
  have depthEq : before.depth key.val = depth := by
    have actual := toRaw_searchDepth before (Nat.zero_le _) key.isLt
    rw [actual] at search
    exact Option.some.inj search
  obtain ⟨next, rotations, nextEq⟩ := rotations_lift trace before rfl
  obtain ⟨served, splay⟩ := Splay.Tree.BST.SplayExecution.exists_splay before
    (Nat.zero_le key.val) key.isLt
  have forward : Splay.Tree.BST.RotationExecution depth before served := by
    simpa [depthEq] using splay.toRotationExecution
  exact ⟨served, next, depth, count, forward, splay.hasRoot_after,
    (rotations_symm forward).append rotations, nextEq, costEq⟩

/-- The conversion to shared root service preserves the initial tree.
Rotations after the last service can be discarded by the shared interface. -/
theorem Execution.toOffline {a b : RawTree Nat} {word : List Nat} {cost : Nat}
    (execution : Execution a word b cost) {n : Nat}
    (tree : BST 0 n) (same : tree.toRaw = a)
    (requests : List (Fin n)) (wordEq : requests.map Fin.val = word) :
    ∃ (last : BST 0 n) (rotations : Nat),
      OfflineExecution requests tree last rotations ∧
      requests.length + rotations ≤ 2 * cost := by
  induction execution generalizing n with
  | nil =>
    have requestsEq : requests = [] := by simpa using wordEq
    subst requests
    exact ⟨tree, 0, .done tree, by simp⟩
  | @cons key word a middle b headCost tailCost head tail ih =>
    cases requests with
    | nil => simp at wordEq
    | cons request requests =>
      obtain ⟨keyEq, restEq⟩ := List.cons.inj wordEq
      have access : Access request.val tree.toRaw middle headCost := by
        simpa only [same, keyEq] using head
      obtain ⟨served, next, depth, count, forward, root, returnToNext, nextEq, costEq⟩ :=
        access.rootService
      obtain ⟨last, rotations, offline, bound⟩ := ih next nextEq requests restEq
      by_cases empty : requests = []
      · subst requests
        refine ⟨served, depth, ?_, ?_⟩
        · simpa using Splay.Accounting.OfflineOptimum.Execution.next forward root (.done served)
        · simp only [List.length_cons, List.length_nil]
          omega
      · have rest := Splay.Accounting.OfflineOptimum.Execution.prependRotations empty
          returnToNext offline
        refine ⟨last, depth + (depth + count + rotations), .next forward root rest, ?_⟩
        simp only [List.length_cons]
        omega

/-- Every search-and-rotation execution pays the existing attained OPT,
up to the universal factor two. No new optimum is defined. -/
theorem OPT_le_cost {n cost : Nat} (initial : BST 0 n)
    {final : RawTree Nat} (requests : List (Fin n))
    (execution : Execution initial.toRaw (requests.map Fin.val) final cost) :
    OPT requests ≤ 2 * cost := by
  obtain ⟨last, rotations, offline, bound⟩ := execution.toOffline initial rfl requests rfl
  exact (OPT_le_execution offline).trans bound

/-- One root-serving access admits a search-and-rotation access with the
same boundary trees and at most twice its rotation count plus one. -/
theorem access_of_rootService {n count : Nat} (key : Fin n)
    {before after : BST 0 n}
    (rotations : Splay.Tree.BST.RotationExecution count before after)
    (root : after.HasRoot key.val) :
    Access key.val before.toRaw after.toRaw (before.depth key.val + 1 + count) ∧
      before.depth key.val + 1 + count ≤ 2 * count + 1 := by
  have initialDepth := rotations_depth_le rotations key.val
  have finalDepth := Splay.Tree.BST.depth_eq_zero_of_hasRoot root
  refine ⟨⟨before.depth key.val, count,
    toRaw_searchDepth before (Nat.zero_le _) key.isLt, rotations_toRaw rotations, rfl⟩, ?_⟩
  omega

/-- Root-serving executions retain both boundary trees under this conversion. -/
theorem ofOffline {n rotations : Nat} {requests : List (Fin n)}
    {initial final : BST 0 n}
    (offline : OfflineExecution requests initial final rotations) :
    ∃ cost, Execution initial.toRaw (requests.map Fin.val) final.toRaw cost ∧
      cost ≤ 2 * (requests.length + rotations) := by
  induction offline with
  | done tree => exact ⟨0, .nil _, by simp⟩
  | @next access accesses before served after prefixRotations tailRotations head root tail ih =>
    obtain ⟨tailCost, tailExecution, tailBound⟩ := ih
    obtain ⟨headExecution, headBound⟩ := access_of_rootService access head root
    refine ⟨before.depth access.val + 1 + prefixRotations + tailCost, ?_, ?_⟩
    · exact .cons headExecution tailExecution
    · simp only [List.length_cons]
      omega

/-- The already attained shared OPT has a search-and-rotation witness
whose cost is at most twice OPT, with a freely chosen initial tree. -/
theorem exists_cost_le_OPT {n : Nat} (requests : List (Fin n)) :
    ∃ (initial final : BST 0 n) (cost : Nat),
      Execution initial.toRaw (requests.map Fin.val) final.toRaw cost ∧
      cost ≤ 2 * OPT requests := by
  obtain ⟨initial, final, rotations, offline, optimum⟩ := OPT_attained requests
  obtain ⟨cost, execution, bound⟩ := ofOffline offline
  exact ⟨initial, final, cost, execution, by omega⟩

end DynamicOptimality.SearchRotation
