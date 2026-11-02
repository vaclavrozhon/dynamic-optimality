import DynamicOptimality.SearchRotationEquivalence
import DynamicOptimality.SearchRotationProjection

set_option autoImplicit false

/-!
# Virtual extension of an ordered key universe

The original tree is retained as the left subtree of a new root `n` when
the universe grows from `[0,n)` to `[0,N)`. The remaining virtual keys form
a fixed right subtree. Requests still name only original keys. Their
search depths grow by one and their rotations lift inside the left child,
giving a constant-factor comparison with the same shared offline optimum.
-/

namespace DynamicOptimality.UniverseExtension

open ChaCha.MTR SearchRotation

/-- A fixed tree on an arbitrary finite interval. -/
def intervalTree (lower : Nat) : (count : Nat) → BST lower (lower + count)
  | 0 => .empty lower
  | count + 1 => by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Splay.Tree.BST.node (.empty lower) (intervalTree (lower + 1) count))

def interval (lower upper : Nat) (bound : lower ≤ upper) : BST lower upper :=
  Nat.add_sub_of_le bound ▸ intervalTree lower (upper - lower)

/-- No original shape is changed by extending the virtual universe. -/
def extend {n N : Nat} (tree : BST 0 n) (bound : n ≤ N) : BST 0 N :=
  if same : n = N then same ▸ tree
  else .node tree (interval (n + 1) N (by omega))

@[simp] theorem extend_self {n : Nat} (tree : BST 0 n) (bound : n ≤ n) :
    extend tree bound = tree := by simp [extend]

theorem extend_toRaw_of_lt {n N : Nat} (tree : BST 0 n) (bound : n ≤ N)
    (strict : n < N) :
    (extend tree bound).toRaw =
      .node tree.toRaw n (interval (n + 1) N (by omega)).toRaw := by
  simp only [extend, dif_neg (by omega : n ≠ N), BST.toRaw]

/-- Removing virtual keys recovers the exact original physical tree. -/
theorem prune_extend {n N : Nat} (tree : BST 0 n) (bound : n ≤ N) :
    Prefix.prune n (extend tree bound).toRaw = tree.toRaw := by
  have original : Prefix.prune n tree.toRaw = tree.toRaw :=
    Prefix.prune_eq_self n (fun key member => (BST.toRaw_mem tree |>.mp member).2)
  by_cases same : n = N
  · subst N
    simpa only [extend_self] using original
  · rw [extend_toRaw_of_lt tree bound (by omega)]
    simpa only [Prefix.prune, Nat.lt_irrefl, if_false] using original

/-- Adding the same root and right subtree preserves every actual rotation. -/
theorem rotations_left {before after : RawTree Nat} {count : Nat}
    (trace : Rotations before after count) (root : Nat) (right : RawTree Nat) :
    Rotations (.node before root right) (.node after root right) count := by
  induction trace with
  | refl => exact .refl _
  | step head tail ih => exact .step (.leftContext head root right) ih

/-- An original-key search pays exactly one additional vertex. -/
theorem access_left {before after : RawTree Nat} {key root cost : Nat}
    (access : Access key before after cost) (inside : key < root) (right : RawTree Nat) :
    Access key (.node before root right) (.node after root right) (cost + 1) := by
  obtain ⟨depth, count, found, rotations, costEq⟩ := access
  refine ⟨depth + 1, count, ?_, rotations_left rotations root right, by omega⟩
  simp only [Tree.searchDepth, inside, if_true, found, Option.map_some]

/-- The whole extension adds one search unit per original request. -/
theorem execution_left {before after : RawTree Nat} {requests : List Nat} {cost root : Nat}
    (execution : Execution before requests after cost)
    (inside : ∀ key ∈ requests, key < root) (right : RawTree Nat) :
    Execution (.node before root right) requests (.node after root right) (cost + requests.length) := by
  induction execution with
  | nil => exact .nil _
  | @cons key requests before middle after headCost tailCost head tail ih =>
      have first := access_left head (inside key (by simp)) right
      have rest := ih (fun key member => inside key (by simp [member]))
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Execution.cons first rest

theorem castLE_word {n N : Nat} (requests : List (Fin n)) (bound : n ≤ N) :
    (requests.map (Fin.castLE bound)).map Fin.val = requests.map Fin.val := by
  rw [List.map_map]
  rfl

/-- Virtual extra keys change the shared optimum by at most a universal
factor six. This includes the empty universe and empty request word. -/
theorem OPT_castLE_le {n N : Nat} (requests : List (Fin n)) (bound : n ≤ N) :
    OPT (requests.map (Fin.castLE bound)) ≤ 6 * OPT requests := by
  by_cases same : n = N
  · subst N
    have requestsEq : requests.map (Fin.castLE bound) = requests := by
      exact List.map_id' _
    rw [requestsEq]
    omega
  · have strict : n < N := by omega
    obtain ⟨before, after, cost, execution, costBound⟩ := exists_cost_le_OPT requests
    obtain ⟨_, _, rotations, _, optimum⟩ := OPT_attained requests
    have lengthBound : requests.length ≤ OPT requests := by omega
    let right := (interval (n + 1) N (by omega)).toRaw
    have extended := execution_left execution (root := n) (by
      intro key member
      obtain ⟨request, _, rfl⟩ := List.mem_map.mp member
      exact request.isLt) right
    have actual : Execution (extend before bound).toRaw
        ((requests.map (Fin.castLE bound)).map Fin.val)
        (.node after.toRaw n right) (cost + requests.length) := by
      rw [extend_toRaw_of_lt before bound strict, castLE_word]
      simpa only [List.length_map, right] using extended
    have lifted := OPT_le_cost (extend before bound) (requests.map (Fin.castLE bound)) actual
    omega

end DynamicOptimality.UniverseExtension
