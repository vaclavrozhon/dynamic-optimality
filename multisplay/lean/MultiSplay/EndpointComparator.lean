import MultiSplay.CopyComparator
import MultiSplay.EndpointPrimary
import MultiSplay.ReferenceAddresses
import MultiSplay.SwitchEmissions
import TangoSquared.LowerBound

/-!
# The same adaptive endpoint word for counters and competitors

`choices` selects the copy opposite to the current node preference and carries
the updated preference state forward. Its projection is the original request
word. The main bound below concerns the primary node-switch counter (including
the final switch). Its hypotheses specify only the height and ordering of the
reference-node addresses; no cost comparison is assumed.

This does not yet bound the secondary ledger or the physical multi-splay cost.
-/

namespace MultiSplay.EndpointEncoding

open DynamicOptimality (RawTree)
open TangoSquared.Primary (Key)

def choices (address : Nat → Key) (state : State) : List Nat → List (Nat × Bool)
  | [] => []
  | key :: rest =>
      (key, !state (address key)) :: choices address (nodeStep state (address key)) rest

theorem choices_project (address : Nat → Key) (state : State) (keys : List Nat) :
    (choices address state keys).map Prod.fst = keys := by
  induction keys generalizing state <;> simp_all [choices]

theorem choices_word (height : Nat) (address : Nat → Key) (state : State) (keys : List Nat) :
    CopyComparator.requestWord (fun side key => copy height (address key) side)
      (choices address state keys) = encode height state (keys.map address) := by
  induction keys generalizing state <;>
    simp_all [choices, CopyComparator.requestWord, encode, request]

theorem exists_endpoint_competitor {n : Nat} (requests : List (Fin n))
    (height : Nat) (address : Nat → Key) (state : State) :
    ∃ (initial : DynamicOptimality.BST 0 n) (final : RawTree Nat) (cost : Nat),
      TangoSquared.MTR.Pointer.Execution
        (CopyComparator.expand (fun side key => copy height (address key) side) initial.toRaw)
        (encode height state ((requests.map Fin.val).map address))
        (CopyComparator.expand (fun side key => copy height (address key) side) final) cost ∧
      cost ≤ 148 * DynamicOptimality.OPT requests := by
  obtain ⟨initial, final, cost, execution, bound⟩ := DynamicOptimality.exists_pointer_of_OPT requests
  obtain ⟨expandedCost, expandedBound, expanded⟩ := CopyComparator.execution_expand execution
    (fun side key => copy height (address key) side)
    (choices address state (requests.map Fin.val)) (choices_project address state _)
  rw [choices_word] at expanded
  exact ⟨initial, final, expandedCost, expanded, by omega⟩

/-- All costs here are the existing concrete pointer cost and the shared
attained `OPT`. `within` and `between` say that the two copies of each reference
node appear consecutively in the active inorder alphabet. -/
theorem primary_switches_le_OPT {n height : Nat} (requests : List (Fin n))
    (address : Nat → Key) (state : State)
    (inside : ∀ key < n, (address key).length < height)
    (within : ∀ key < n, copy height (address key) false < copy height (address key) true)
    (between : ∀ x < n, ∀ y < n, x < y →
      copy height (address x) true < copy height (address y) false) :
    requests.length + nodeCost height state ((requests.map Fin.val).map address) ≤
      427424 * DynamicOptimality.OPT requests + (2 ^ height - 1) := by
  obtain ⟨initial, final, cost, execution, bound⟩ :=
    exists_endpoint_competitor requests height address state
  have ordered := CopyComparator.expand_ordered
    (fun side key => copy height (address key) side) initial.toRaw initial.toRaw_ordered
    (fun key member => within key (DynamicOptimality.BST.toRaw_mem initial |>.mp member).2)
    (fun x hx y hy less => between x (DynamicOptimality.BST.toRaw_mem initial |>.mp hx).2
      y (DynamicOptimality.BST.toRaw_mem initial |>.mp hy).2 less)
  have leaves : ∀ leaf ∈ TangoSquared.MTR.Tree.inorder
      (CopyComparator.expand (fun side key => copy height (address key) side) initial.toRaw),
      leaf.length = 2 * height := by
    intro leaf member
    rw [CopyComparator.inorder_expand] at member
    obtain ⟨key, inInitial, inPair⟩ := List.mem_flatMap.mp member
    have keyBound := (DynamicOptimality.BST.toRaw_mem initial |>.mp inInitial).2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inPair
    rcases inPair with rfl | rfl <;> exact copy_length (inside key keyBound) _
  have lower := TangoSquared.dynamic_bst_lower_bound execution ordered leaves
  have primary := nodeCost_le_primary height state ((requests.map Fin.val).map address)
  rw [encode_length, List.length_map, List.length_map] at lower
  omega

/-- Primary switch bound for a concrete reference BST and arbitrary initial
preferred directions. The address-height and copy-order properties are proved
from `reference`. For a perfect reference the final allowance is its node count.
This counts the preference protocol, not the physical auxiliary-tree cost. -/
theorem reference_primary_switches_le_OPT {n : Nat} (requests : List (Fin n))
    (reference : DynamicOptimality.BST 0 n) (state : State) :
    requests.length + nodeCost reference.height state
      ((requests.map Fin.val).map (nodeAddress reference)) ≤
      427424 * DynamicOptimality.OPT requests + (2 ^ reference.height - 1) := by
  apply primary_switches_le_OPT
  · intro key inside
    exact nodeAddress_length_lt reference (Nat.zero_le _) inside
  · intro key _
    exact copy_false_lt_true _ _
  · intro x xInside y yInside less
    exact reference_copies_between reference xInside yInside less

/-- The bound applies to the actual bottom-up ancestor order with its final
switch, not only to the analytically increasing emission list. -/
theorem actual_switches_le_OPT {n : Nat} (requests : List (Fin n))
    (reference : DynamicOptimality.BST 0 n) (state : State) :
    requests.length + (actualHistory state
      ((requests.map Fin.val).map (nodeAddress reference))).length ≤
      427424 * DynamicOptimality.OPT requests + (2 ^ reference.height - 1) := by
  rw [actualHistory_length (height := reference.height) state _ ?_]
  · exact reference_primary_switches_le_OPT requests reference state
  · intro address member
    obtain ⟨key, inKeys, rfl⟩ := List.mem_map.mp member
    obtain ⟨request, _, rfl⟩ := List.mem_map.mp inKeys
    exact nodeAddress_length_lt reference (Nat.zero_le _) request.isLt

theorem perfect_reference_actual_switches_le_OPT {n : Nat} (requests : List (Fin n))
    (reference : DynamicOptimality.BST 0 n) (perfect : 2 ^ reference.height = n + 1)
    (state : State) :
    requests.length + (actualHistory state
      ((requests.map Fin.val).map (nodeAddress reference))).length ≤
      427424 * DynamicOptimality.OPT requests + n := by
  simpa only [perfect, Nat.add_sub_cancel] using actual_switches_le_OPT requests reference state

end MultiSplay.EndpointEncoding
