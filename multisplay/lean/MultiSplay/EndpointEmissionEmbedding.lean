import MultiSplay.EndpointHierarchy
import MultiSplay.SecondaryEmissionWords
import Mathlib.Data.List.Sort

/-!
# Chronological embedding of the actual endpoint switches

The increasing multisplay emissions map to a subsequence of the primary
changes of the encoded leaf access. This preserves their order, not only
their cardinality. Projecting onto a doubled owner row therefore preserves
the original secondary writes exactly.
-/

namespace MultiSplay.EndpointEncoding

open ChaCha.Primary (Key branch)

theorem ascendingEmissions_increasing (state : State) (address : Key) :
    (ascendingEmissions state address).Pairwise (fun a b => a.length < b.length) := by
  induction address generalizing state with
  | nil => simp [ascendingEmissions, ancestorEmissions]
  | cons edge rest ih =>
      rw [ascendingEmissions_cons]
      have tail : ((ascendingEmissions (below state edge) rest).map (edge :: ·)).Pairwise
          (fun a b => a.length < b.length) := by
        simpa only [List.pairwise_map, List.length_cons, Nat.add_lt_add_iff_right] using ih (below state edge)
      by_cases same : state [] = edge
      · simpa only [if_pos same, List.nil_append] using tail
      · simp only [if_neg same, List.singleton_append, List.pairwise_cons]
        refine ⟨?_,tail⟩
        intro key member
        obtain ⟨owner,_,rfl⟩ := List.mem_map.mp member
        simp

theorem ancestorEmissions_increasing (state : State) (address : Key) :
    (ancestorEmissions state address).Pairwise (fun a b => a.length < b.length) :=
  (ascendingEmissions_increasing state address).sublist (List.sublist_append_left _ _)

/-- The mandatory endpoint toggle becomes an ordinary even-depth primary
change. All its proper ancestors occur in the same chronological order. -/
theorem emissions_sublist {height : Nat} {nodeState leafState : State}
    (aligned : Matches nodeState leafState) {address : Key} (inside : address.length < height) :
    ((ascendingEmissions nodeState address).map core).Sublist
      (ancestorEmissions leafState (request height nodeState address)) := by
  have subset : (ascendingEmissions nodeState address).map core ⊆
      ancestorEmissions leafState (request height nodeState address) := by
    intro owner member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    have shorter := (ascendingEmissions_prefix originalMember).length_le
    have different : core original ≠ request height nodeState address := by
      intro same
      have length := congrArg List.length same
      simp only [core_length, request, copy_length inside] at length
      omega
    have changed := ascendingEmissions_mem.mp originalMember
    have embedded : core original ∈ ascendingEmissions leafState (request height nodeState address) := by
      apply ascendingEmissions_mem.mpr
      simpa only [nodeWrite, if_neg different, writes_match, aligned original] using changed
    simpa only [ascendingEmissions, List.mem_append, List.mem_singleton, different, or_false] using embedded
  have increasing : ((ascendingEmissions nodeState address).map core).Pairwise
      (fun a b => a.length < b.length) := by
    rw [List.pairwise_map]
    exact (ascendingEmissions_increasing nodeState address).imp (fun {a b} less => by
      simp only [core_length]; omega)
  have distinct := (ascendingEmissions_nodup nodeState address).map core_injective
  obtain ⟨permuted, permutation, subsequence⟩ := List.subperm_of_subset distinct subset
  have equal := permutation.eq_of_pairwise (fun a b _ _ hab hba => False.elim (Nat.lt_asymm hab hba))
    ((ancestorEmissions_increasing leafState (request height nodeState address)).sublist subsequence) increasing
  exact equal ▸ subsequence

theorem core_take (depth : Nat) (address : Key) :
    (core address).take (2*depth) = core (address.take depth) := by
  induction depth generalizing address with
  | zero => simp [core]
  | succ depth ih =>
      cases address with
      | nil => simp [core]
      | cons edge rest =>
          simpa only [Nat.mul_add, Nat.mul_one, List.take_succ_cons, core] using
            congrArg (fun tail => edge :: edge :: tail) (ih rest)

theorem request_take {depth : Nat} {address : Key} (bounded : depth ≤ address.length)
    (height : Nat) (state : State) :
    (request height state address).take (2*depth) = core (address.take depth) := by
  unfold request copy
  rw [List.append_assoc, List.take_append_of_le_length (by simpa only [core_length] using Nat.mul_le_mul_left 2 bounded)]
  exact core_take depth address

end MultiSplay.EndpointEncoding

namespace MultiSplay.EndpointHierarchy

open ChaCha.Primary (Key)
open EndpointEncoding

/-- A retained even-depth emission makes exactly the same owner-row write. -/
theorem project_core (height : Nat) (state : State) (original : Secondary.Row)
    {address emitted : Key} (ancestor : emitted.IsPrefix address) :
    Secondary.project (row height original) (request height state address) (core emitted) =
      Secondary.project original address emitted := by
  have bounds := split_contains height original.1 emitted.length
  have direction := split_direction height original.1 emitted.length
  by_cases inside : original.1.lo ≤ emitted.length ∧ emitted.length ≤ original.1.hi
  · have lower : original.1.lo ≤ address.length := inside.1.trans ancestor.length_le
    have owners : core original.2 = (request height state address).take (2*original.1.lo) ↔
        original.2 = address.take original.1.lo := by
      rw [request_take lower]
      exact core_injective.eq_iff
    have owners' : core original.2 = (request height state address).take (split height original.1).lo ↔
        original.2 = address.take original.1.lo := owners
    simp only [Secondary.project, row, core_length, bounds, if_pos inside, direction, owners']
  · have outside := mt bounds.mp inside
    simp only [Secondary.project, row, core_length, if_neg inside, if_neg outside, ite_self]

theorem projected_core_emissions (height : Nat) (state : State) (address : Key) (original : Secondary.Row) :
    ((ascendingEmissions state address).map core).filterMap
        (Secondary.project (row height original) (request height state address)) =
      (ascendingEmissions state address).filterMap (Secondary.project original address) := by
  rw [List.filterMap_map]
  apply List.filterMap_congr
  intro emitted member
  exact project_core height state original (ascendingEmissions_prefix member)

end MultiSplay.EndpointHierarchy
