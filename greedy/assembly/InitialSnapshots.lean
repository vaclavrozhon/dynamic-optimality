import InitialBlockState
import BlockUpperBase

/-! Starting history, clock and numerical invariants derived from the
constructed actual child lists, together with the initial two-grower
birth journal. The initializer accepts no initial block invariant. -/

namespace GreedyMerge.InitialBlocks

open OrderedBlocks Primitives BlockCoverage
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis

noncomputable def epoch (n : ℕ) : ℕ :=
  1 + Finset.univ.sup (fun item : (External n × Bool) × External n =>
    ticket item.1.1 item.1.2 item.2)

theorem ticket_before_epoch {n : ℕ} (owner record : External n) (side : Bool) :
    ticket owner side record < epoch n := by
  have bound : ticket owner side record ≤
      Finset.univ.sup (fun item : (External n × Bool) × External n =>
        ticket item.1.1 item.1.2 item.2) :=
    Finset.le_sup (f := fun item : (External n × Bool) × External n =>
      ticket item.1.1 item.1.2 item.2) (Finset.mem_univ ((owner, side), record))
  unfold epoch
  omega

theorem state_beforeTime {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ) :
    ActualLinks.BeforeTime (epoch n) (state snapshot tree K) := by
  intro owner side actual member
  rw [state_entries] at member
  obtain ⟨record, _, rfl⟩ := List.mem_map.mp member
  exact ticket_before_epoch owner record side

theorem state_histories {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ) :
    ActualLinks.Histories (state snapshot tree K) := by
  intro owner side
  refine ⟨?_, ?_⟩
  · simp [state]
  · intro grower same
    have ordered := state_history snapshot tree K owner side
    rw [same] at ordered
    exact ordered

theorem state_upper {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ)
    (rank : ℕ → ℕ) : ∀ owner side, UpperBase rank (state snapshot tree K owner side) := by
  intro owner side block member
  simp [state] at member

/-- The computed starting labels coincide with actual parent-rank gaps,
including the bounded fallback at the unique global root. -/
theorem state_label {n : ℕ} (comparator tree : BST 0 n) (K : ℤ) (record : External n) :
    StateLabels.label comparator.externalDepth K (state (Snapshot.ofTree comparator) tree K) record.val =
      rawLabel (Snapshot.ofTree comparator) tree K record := by
  cases parent : canonicalParent (Snapshot.ofTree comparator) tree record with
  | none =>
      have root := (canonicalParent_eq_none_iff (Snapshot.ofTree comparator) tree record).mp parent
      rw [rawLabel, parent]
      simpa only [root] using StateLabels.root_label (Snapshot.ofTree comparator) tree
        comparator.externalDepth K _ (state_sound _ _ _)
  | some owner =>
      obtain ⟨side, actual, member, equal⟩ := state_complete (Snapshot.ofTree comparator) tree K
        record owner parent (by simp)
      have growing : actual ∈ growerEntries (state (Snapshot.ofTree comparator) tree K owner side).grower := member
      have result := StateLabels.label_of_growing (Snapshot.ofTree comparator) tree comparator.externalDepth
        K _ (state_valid _ _ _) (state_sound _ _ _) owner side actual growing
      rw [equal] at result
      rw [rawLabel, parent]
      exact result

/-- Stored creator and entry snapshots are the actual state-defined
labels at the constructed starting state. -/
theorem entry_snapshots {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (owner record : External n) (side : Bool) :
    (entry (Snapshot.ofTree comparator) tree K owner side record).entryLabel =
      StateLabels.label comparator.externalDepth K (state (Snapshot.ofTree comparator) tree K) record.val ∧
    (entry (Snapshot.ofTree comparator) tree K owner side record).creatorLabel =
      StateLabels.label comparator.externalDepth K (state (Snapshot.ofTree comparator) tree K) owner.val :=
  ⟨(state_label comparator tree K record).symm, (state_label comparator tree K owner).symm⟩

def birthIds (n : ℕ) : List ℕ := List.range (2 * (2*n+1))

@[simp] theorem birthIds_length (n : ℕ) : (birthIds n).length = 2 * (2*n+1) := by
  simp [birthIds]

theorem birthIds_distinct (n : ℕ) : (birthIds n).Nodup := List.nodup_range

theorem slot_mem_birthIds {n : ℕ} (owner : External n) (side : Bool) :
    slot owner side ∈ birthIds n := by
  have bound := owner.isLt
  simp only [birthIds, List.mem_range]
  cases side <;> simp only [slot, Bool.toNat_false, Bool.toNat_true] <;> omega

theorem state_id_supported {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ)
    (owner : External n) (side : Bool) (grower : Grower)
    (present : (state snapshot tree K owner side).grower = some grower) :
    grower.id ∈ birthIds n := by
  have equal := Option.some.inj present
  have idEqual := congrArg Grower.id equal
  rw [← idEqual]
  exact slot_mem_birthIds owner side

end GreedyMerge.InitialBlocks

#print axioms GreedyMerge.InitialBlocks.state_beforeTime
#print axioms GreedyMerge.InitialBlocks.state_label
#print axioms GreedyMerge.InitialBlocks.entry_snapshots
#print axioms GreedyMerge.InitialBlocks.state_id_supported
