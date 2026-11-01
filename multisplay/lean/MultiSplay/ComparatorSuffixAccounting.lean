import MultiSplay.ComparatorSuffixRestoration
import TangoSquared.FragmentHierarchy

/-!
# Charging a suffix access only to genuine writes

The induced secondary access has at most one additional flip on its
structural boundary. All other flips are charged to changes of the same
original interval records in `writeGenuine`. Thus neither the starting
depth nor the boundary-spine length appears in the access bound.
-/

namespace MultiSplay.ComparatorSuffix

open TangoSquared
open TangoSquared.PreferredProjection
open TangoSquared.Paper20261030
open Secondary (intervalUpdate decodeDepth)
open SecondaryDecomposition
open ColoredStorage Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition

theorem decoded_flips_le_sum {a b : Nat} (reference : DepthTree a b)
    (bits : DepthSplit → Bool) (request : Nat) :
    (decodeDepth reference bits).accessFlips request ≤
      ∑ split ∈ reference.nodes, edgeChange (bits split) (intervalUpdate request bits split) := by
  induction reference with
  | leaf a => simp [decodeDepth,PrefRouter.accessFlips,DepthTree.nodes]
  | @node a b cut ha hb left right ihl ihr =>
      rw [DepthTree.nodes,Finset.sum_insert,Finset.sum_union (DepthTree.children_disjoint left right)]
      · simp only [decodeDepth,PrefRouter.accessFlips]
        by_cases inLeft : a ≤ request ∧ request ≤ cut
        · rw [if_pos ((Secondary.decodeDepth_mem left bits request).mpr inLeft)]
          have root : intervalUpdate request bits ⟨a,cut,b⟩ = false := by
            simp only [intervalUpdate]
            rw [if_pos (show a ≤ request ∧ request ≤ b by omega)]
            exact decide_eq_false (by omega)
          rw [root]
          omega
        · rw [if_neg (fun member => inLeft ((Secondary.decodeDepth_mem left bits request).mp member))]
          by_cases inRight : cut + 1 ≤ request ∧ request ≤ b
          · rw [if_pos ((Secondary.decodeDepth_mem right bits request).mpr inRight)]
            have root : intervalUpdate request bits ⟨a,cut,b⟩ = true := by
              simp only [intervalUpdate]
              rw [if_pos (show a ≤ request ∧ request ≤ b by omega)]
              exact decide_eq_true (by omega)
            rw [root]
            omega
          · rw [if_neg (fun member => inRight ((Secondary.decodeDepth_mem right bits request).mp member))]
            exact Nat.zero_le _
      · simp only [Finset.mem_union,not_or]
        exact ⟨DepthTree.root_not_left left hb,DepthTree.root_not_right right ha⟩

theorem suffix_nodes_image {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lo : a ≤ start) (hi : start ≤ b) :
    (suffix reference start lo hi).nodes =
      (reference.nodes.filter fun split => start ≤ split.cut).image (clip start) := by
  ext split
  constructor
  · intro member
    obtain ⟨original,present,retained,same⟩ := suffix_node_original reference start lo hi member
    exact Finset.mem_image.mpr ⟨original,Finset.mem_filter.mpr ⟨present,retained⟩,same⟩
  · intro member
    obtain ⟨original,present,rfl⟩ := Finset.mem_image.mp member
    exact original_node_suffix reference start lo hi (Finset.mem_filter.mp present).1
      (Finset.mem_filter.mp present).2

def genuineCost {a b : Nat} (reference : DepthTree a b) (start request : Nat)
    (memory : DepthSplit → Bool) : Nat :=
  ∑ split ∈ reference.nodes, edgeChange (memory split) (writeGenuine start request memory split)

theorem clipped_flip_bound {a b : Nat} (reference : DepthTree a b) (start request : Nat)
    (memory : DepthSplit → Bool) {original : DepthSplit}
    (member : original ∈ reference.nodes) (retained : start ≤ original.cut) :
    edgeChange (preference reference start memory (clip start original))
        (intervalUpdate request (preference reference start memory) (clip start original)) ≤
      edgeChange (memory original) (writeGenuine start request memory original) +
        if original ∈ boundaryChanges reference start request then 1 else 0 := by
  by_cases structural : original.lo < start
  · have old : preference reference start memory (clip start original) = false := by
      simp only [preference,clip_cut,original_of_cut reference member,if_pos structural]
    by_cases changed : intervalUpdate request (preference reference start memory) (clip start original) ≠
        preference reference start memory (clip start original)
    · have present := changed_boundary_mem reference start request memory member retained structural changed
      rw [if_pos present]
      unfold edgeChange
      split_ifs <;> omega
    · rw [not_ne_iff.mp changed,edgeChange_self]
      exact Nat.zero_le _
  · have genuine : start ≤ original.lo := by omega
    rw [clip_genuine start original genuine,preference_genuine reference start memory member genuine]
    have updated : intervalUpdate request (preference reference start memory) original =
        writeGenuine start request memory original := by
      simp only [writeGenuine,if_pos genuine,intervalUpdate,
        preference_genuine reference start memory member genuine]
    rw [updated]
    exact Nat.le_add_right _ _

theorem accessFlips_le_genuine {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lo : a ≤ start) (hi : start ≤ b) (request : Nat)
    (memory : DepthSplit → Bool) :
    (decodeDepth (suffix reference start lo hi) (preference reference start memory)).accessFlips request ≤
      genuineCost reference start request memory + 1 := by
  let retained := reference.nodes.filter fun split => start ≤ split.cut
  let charge := fun split => edgeChange (memory split) (writeGenuine start request memory split) +
    if split ∈ boundaryChanges reference start request then 1 else 0
  have flips := decoded_flips_le_sum (suffix reference start lo hi) (preference reference start memory) request
  rw [suffix_nodes_image,Finset.sum_image] at flips
  · have pointwise : (∑ split ∈ retained,
        edgeChange (preference reference start memory (clip start split))
          (intervalUpdate request (preference reference start memory) (clip start split))) ≤
        ∑ split ∈ retained, charge split := by
      apply Finset.sum_le_sum
      intro split member
      exact clipped_flip_bound reference start request memory (Finset.mem_filter.mp member).1
        (Finset.mem_filter.mp member).2
    have enlarged : (∑ split ∈ retained, charge split) ≤ ∑ split ∈ reference.nodes, charge split :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
    have boundarySum : (∑ split ∈ reference.nodes,
        if split ∈ boundaryChanges reference start request then 1 else 0) =
        (boundaryChanges reference start request).card := by
      rw [← Finset.sum_filter,← Finset.card_eq_sum_ones]
      congr 1
      ext split
      simp only [Finset.mem_filter,boundaryChanges,and_self_left]
    have total : (∑ split ∈ reference.nodes, charge split) =
        genuineCost reference start request memory + (boundaryChanges reference start request).card := by
      simp only [charge,Finset.sum_add_distrib,boundarySum,genuineCost]
    have boundary := boundaryChanges_card reference start request
    rw [total] at enlarged
    exact flips.trans (pointwise.trans (enlarged.trans (Nat.add_le_add_left boundary _)))
  · intro first firstMember second secondMember same
    apply original_cut_unique reference (Finset.mem_filter.mp firstMember).1 (Finset.mem_filter.mp secondMember).1
    simpa only [clip_cut] using congrArg DepthSplit.cut same

/-- The complete source-level transaction has cost proportional to genuine
changes plus a constant; structural histories are never charged as new owners. -/
theorem access_genuine_charged {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lo : a ≤ start) (hi : start ≤ b) (request : Nat)
    (memory : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (source (suffix reference start lo hi) (preference reference start memory)) component) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight
        (source (suffix reference start lo hi)
          (preference reference start (writeGenuine start request memory))) out ∧
      SourcePointer.Rearranges (closed component) (closed out)
        ((genuineCost reference start request memory + 2) * repairBound reference) := by
  obtain ⟨out,outRep,run⟩ := access_restore_charged reference start lo hi request memory component represented
  have flips := accessFlips_le_genuine reference start lo hi request memory
  exact ⟨out,outRep,run.mono (Nat.mul_le_mul_right _ (by omega))⟩

end MultiSplay.ComparatorSuffix
