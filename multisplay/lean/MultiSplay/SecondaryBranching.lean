import MultiSplay.SecondaryVariation
import TangoSquared.FragmentHierarchy

/-!
# Counting secondary intervals changed by reversing ancestor emissions

A split is mixed when at least one emitted depth lies in each child interval.
In any binary interval hierarchy, at most k-1 splits are mixed by k emissions.
The statement allows arbitrary interval splits and does not use balancing.
-/

namespace MultiSplay.Secondary

open TangoSquared (DepthSplit DepthTree)

def inInterval (lower upper : Nat) (depths : List Nat) : List Nat :=
  depths.filter (fun depth => decide (lower ≤ depth ∧ depth ≤ upper))

def MixedSplit (split : DepthSplit) (depths : List Nat) : Prop :=
  (∃ depth ∈ depths, split.lo ≤ depth ∧ depth ≤ split.cut) ∧
  (∃ depth ∈ depths, split.cut < depth ∧ depth ≤ split.hi)

instance (split : DepthSplit) (depths : List Nat) : Decidable (MixedSplit split depths) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem mixed_iff_positive (lower cut upper : Nat) (depths : List Nat) :
    MixedSplit ⟨lower,cut,upper⟩ depths ↔
      0 < (inInterval lower cut depths).length ∧ 0 < (inInterval (cut+1) upper depths).length := by
  simp only [MixedSplit, inInterval, List.length_pos_iff_exists_mem, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a, memberA, loA, hiA⟩, ⟨b, memberB, loB, hiB⟩⟩
    exact ⟨⟨a,memberA,loA,hiA⟩,⟨b,memberB,by omega,hiB⟩⟩
  · rintro ⟨⟨a, memberA, loA, hiA⟩, ⟨b, memberB, loB, hiB⟩⟩
    exact ⟨⟨a,memberA,loA,hiA⟩,⟨b,memberB,by omega,hiB⟩⟩

theorem interval_length_split (lower cut upper : Nat) (left : lower ≤ cut) (right : cut < upper) (depths : List Nat) :
    (inInterval lower upper depths).length =
      (inInterval lower cut depths).length + (inInterval (cut+1) upper depths).length := by
  induction depths with
  | nil => rfl
  | cons head tail ih =>
      by_cases whole : lower ≤ head ∧ head ≤ upper <;>
        by_cases low : lower ≤ head ∧ head ≤ cut <;>
        by_cases high : cut+1 ≤ head ∧ head ≤ upper <;>
        simp_all [inInterval] <;> omega

def branching {lower upper : Nat} (hierarchy : DepthTree lower upper) (depths : List Nat) : Nat :=
  ∑ split ∈ hierarchy.nodes, if MixedSplit split depths then 1 else 0

theorem branching_le {lower upper : Nat} (hierarchy : DepthTree lower upper) (depths : List Nat) :
    branching hierarchy depths ≤ (inInterval lower upper depths).length-1 := by
  induction hierarchy with
  | leaf => simp [branching, DepthTree.nodes]
  | @node lower upper cut left right a b iha ihb =>
      have lengths := interval_length_split lower cut upper left right depths
      have pieces : branching (.node cut left right a b) depths =
          (if MixedSplit ⟨lower,cut,upper⟩ depths then 1 else 0) + branching a depths + branching b depths := by
        rw [branching, DepthTree.nodes, Finset.sum_insert, Finset.sum_union (DepthTree.children_disjoint a b)]
        · simp only [branching]
          omega
        · simp only [Finset.mem_union, not_or]
          exact ⟨DepthTree.root_not_left a right, DepthTree.root_not_right b left⟩
      rw [pieces]
      by_cases mixed : MixedSplit ⟨lower,cut,upper⟩ depths
      · have both := (mixed_iff_positive lower cut upper depths).mp mixed
        rw [if_pos mixed]
        omega
      · have notBoth := mt (mixed_iff_positive lower cut upper depths).mpr mixed
        rw [if_neg mixed]
        omega

theorem branching_le_length {lower upper : Nat} (hierarchy : DepthTree lower upper) (depths : List Nat) :
    branching hierarchy depths ≤ depths.length-1 := by
  have bound := branching_le hierarchy depths
  have length := List.length_filter_le (fun depth => decide (lower ≤ depth ∧ depth ≤ upper)) depths
  change (inInterval lower upper depths).length ≤ depths.length at length
  omega

end MultiSplay.Secondary
