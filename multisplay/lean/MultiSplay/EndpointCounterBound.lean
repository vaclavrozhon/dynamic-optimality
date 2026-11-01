import MultiSplay.SecondaryLeafLedgerBound
import MultiSplay.EndpointComparator

/-!
# The actual multisplay switch counters are bounded by OPT

The original primary state may be arbitrary. Its embedded pivots retain that
state, while connectors and padding start right. The endpoint-copy simulation,
arbitrary-hierarchy dynamic lower bound, chronological ledger embedding, and
linear initialization support are assembled without a Tango upper-bound premise.
This is a counter theorem, not yet a physical multisplay cost theorem.
-/

namespace MultiSplay.EndpointEncoding

open TangoSquared.Primary (Key)
open TangoSquared (DepthTree)

noncomputable def liftState (state : State) (owner : Key) : Bool := by
  classical
  exact if found : ∃ original, core original = owner then state found.choose else true

theorem liftState_matches (state : State) : Matches state (liftState state) := by
  classical
  intro owner
  unfold liftState
  have found : ∃ original, core original = core owner := ⟨owner,rfl⟩
  rw [dif_pos found]
  exact congrArg state (core_injective found.choose_spec)

theorem liftState_right (height : Nat) (state : State) : RightOutside height (liftState state) := by
  classical
  intro owner internal absent
  have missing : ¬∃ original, core original = owner := by
    rintro ⟨original,rfl⟩
    have inside : original.length < height := by rw [core_length] at internal; omega
    exact absent (mem_coreNodes.mpr ⟨original,inside,Or.inl rfl⟩)
  simp only [liftState,dif_neg missing]

theorem actual_counters_le_encoded_lower {height : Nat} (hierarchy : DepthTree 0 height)
    (state : State) (addresses : List Key) (inside : ∀ address ∈ addresses, address.length < height) :
    addresses.length + (actualHistory state addresses).length + Secondary.actualLedger hierarchy (fun _ => true) state addresses ≤
      5*((encode height state addresses).length +
        IntervalLower.secondaryDemands (EndpointHierarchy.doubled hierarchy) (encode height state addresses) +
        TangoSquared.primaryCount (2*height) (encode height state addresses)) + 21*(2^height-1) := by
  have embedding := Secondary.actualLedger_le_encoded hierarchy (fun _ => true) (liftState_matches state) inside
  have ledger := Secondary.encoded_leafLedger_bound (EndpointHierarchy.doubled hierarchy) (liftState_right height state) state inside
  have primary := nodeCost_le_primary height state addresses
  rw [← actualHistory_length state addresses inside] at primary
  rw [encode_length]
  omega

/-- Uniform in the arbitrary interval hierarchy and initial primary state. -/
theorem actual_counters_le_OPT {n height : Nat} (requests : List (Fin n))
    (hierarchy : DepthTree 0 height) (address : Nat → Key) (state : State)
    (inside : ∀ key < n, (address key).length < height)
    (within : ∀ key < n, copy height (address key) false < copy height (address key) true)
    (between : ∀ x < n, ∀ y < n, x < y → copy height (address x) true < copy height (address y) false) :
    requests.length + (actualHistory state ((requests.map Fin.val).map address)).length +
      Secondary.actualLedger hierarchy (fun _ => true) state ((requests.map Fin.val).map address) ≤
        2137120*DynamicOptimality.OPT requests + 21*(2^height-1) := by
  obtain ⟨initial,final,cost,execution,paid⟩ := exists_endpoint_competitor requests height address state
  have ordered := CopyComparator.expand_ordered
    (fun side key => copy height (address key) side) initial.toRaw initial.toRaw_ordered
    (fun key member => within key (DynamicOptimality.BST.toRaw_mem initial |>.mp member).2)
    (fun x hx y hy less => between x (DynamicOptimality.BST.toRaw_mem initial |>.mp hx).2
      y (DynamicOptimality.BST.toRaw_mem initial |>.mp hy).2 less)
  have leaves : ∀ leaf ∈ TangoSquared.MTR.Tree.inorder
      (CopyComparator.expand (fun side key => copy height (address key) side) initial.toRaw), leaf.length = 2*height := by
    intro leaf member
    rw [CopyComparator.inorder_expand] at member
    obtain ⟨key,present,inPair⟩ := List.mem_flatMap.mp member
    have bounded := (DynamicOptimality.BST.toRaw_mem initial |>.mp present).2
    simp only [List.mem_cons,List.not_mem_nil,or_false] at inPair
    rcases inPair with rfl | rfl <;> exact copy_length (inside key bounded) _
  have lower := IntervalLower.dynamic_bst_lower_bound (EndpointHierarchy.doubled hierarchy) execution ordered leaves
  have valid : ∀ key ∈ (requests.map Fin.val).map address, key.length < height := by
    intro key member
    obtain ⟨index,indices,rfl⟩ := List.mem_map.mp member
    obtain ⟨query,_,rfl⟩ := List.mem_map.mp indices
    exact inside query.val query.isLt
  have counters := actual_counters_le_encoded_lower hierarchy state _ valid
  simp only [List.length_map] at counters
  omega

theorem reference_actual_counters_le_OPT {n : Nat} (requests : List (Fin n))
    (reference : DynamicOptimality.BST 0 n) (hierarchy : DepthTree 0 reference.height) (state : State) :
    requests.length + (actualHistory state ((requests.map Fin.val).map (nodeAddress reference))).length +
      Secondary.actualLedger hierarchy (fun _ => true) state ((requests.map Fin.val).map (nodeAddress reference)) ≤
        2137120*DynamicOptimality.OPT requests + 21*(2^reference.height-1) := by
  apply actual_counters_le_OPT
  · intro key inside
    exact nodeAddress_length_lt reference (Nat.zero_le _) inside
  · intro key _
    exact copy_false_lt_true _ _
  · intro x xInside y yInside less
    exact reference_copies_between reference xInside yInside less

/-- For a perfect reference the initialization term is its actual node count. -/
theorem perfect_reference_actual_counters_le_OPT {n : Nat} (requests : List (Fin n))
    (reference : DynamicOptimality.BST 0 n) (perfect : 2^reference.height = n+1)
    (hierarchy : DepthTree 0 reference.height) (state : State) :
    requests.length + (actualHistory state ((requests.map Fin.val).map (nodeAddress reference))).length +
      Secondary.actualLedger hierarchy (fun _ => true) state ((requests.map Fin.val).map (nodeAddress reference)) ≤
        2137120*DynamicOptimality.OPT requests + 21*n := by
  simpa only [perfect,Nat.add_sub_cancel] using reference_actual_counters_le_OPT requests reference hierarchy state

end MultiSplay.EndpointEncoding
