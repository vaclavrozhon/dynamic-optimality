import DynamicOptimality.PointerInitialization
import DynamicOptimality.SearchRotationIndexed
import ChaCha.Paper20261030.SearchRotationMetadata

set_option autoImplicit false

/-!
Initialization for the search-path-plus-rotations model. The first request
is searched in the supplied tree before any initialization rotations. A
fixed initialization then reaches the canonical tree, after which the
canonical transition's rotations are performed. All intermediate trees
are actual ordinary BSTs; the initialization is charged only once.
-/

namespace ChaCha.Paper20261030.OnlineSearchRotationInitialization

open DynamicOptimality DynamicOptimality.SearchRotation

/-- A fixed finite sequence of rotations between trees with the same word. -/
structure Initialization (before after : RawTree Nat) where
  count : Nat
  rotations : Rotations before after count
  bound : count ≤ 18 * before.size

theorem initialization_exists (before after : RawTree Nat)
    (word : before.inorder = after.inorder) : Nonempty (Initialization before after) := by
  obtain ⟨cost, trace, bound⟩ := initialize_pointer before after word []
  obtain ⟨count, rotations, countBound⟩ := SearchRotationBridge.pointer_trace_rotations trace
  exact ⟨⟨count, rotations, countBound.trans bound⟩⟩

/-- Chosen independently of all requests; computation is free in this model. -/
noncomputable def initialization (before after : RawTree Nat)
    (word : before.inorder = after.inorder) : Initialization before after :=
  Classical.choice (initialization_exists before after word)

/-- Initial search is paid in `before`, not in the initialized tree.
The canonical first access contributes only its actual rotations here. -/
theorem prepend_initialization {n cost : Nat} (before : BST 0 n)
    {middle after : RawTree Nat} (key : Fin n)
    (initialization : Initialization before.toRaw middle)
    (access : Access key.val middle after cost) :
    ∃ actualCost, Access key.val before.toRaw after actualCost ∧
      actualCost ≤ 19 * n + cost := by
  obtain ⟨depth, count, search, rotations, costEq⟩ := access
  have depthBound := before.depth_le_size key.val
  rw [before.size_eq_upper] at depthBound
  have initializationBound := initialization.bound
  rw [BST.toRaw_size, before.size_eq_upper] at initializationBound
  refine ⟨before.depth key.val + 1 + (initialization.count + count), ?_, ?_⟩
  · exact ⟨before.depth key.val, initialization.count + count,
      toRaw_searchDepth before (Nat.zero_le _) key.isLt,
      initialization.rotations.append rotations, rfl⟩
  · omega

end ChaCha.Paper20261030.OnlineSearchRotationInitialization
