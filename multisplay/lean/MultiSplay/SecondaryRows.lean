import MultiSplay.SecondaryBranching
import MultiSplay.SecondaryRowOrder

/-! # One owner row per secondary interval and query -/

namespace MultiSplay.Secondary

open ChaCha (DepthSplit DepthTree)
open ChaCha.Primary (Key level)

def depthWord (split : DepthSplit) (depths : List Nat) : List Bool :=
  depths.filterMap (fun depth => if split.lo ≤ depth ∧ depth ≤ split.hi then some (decide (split.cut < depth)) else none)

theorem false_mem_depthWord (split : DepthSplit) (valid : split.cut ≤ split.hi) (depths : List Nat) :
    false ∈ depthWord split depths ↔ ∃ depth ∈ depths, split.lo ≤ depth ∧ depth ≤ split.cut := by
  constructor
  · intro member
    obtain ⟨depth, present, letter⟩ := List.mem_filterMap.mp member
    by_cases inside : split.lo ≤ depth ∧ depth ≤ split.hi
    · simp only [if_pos inside, Option.some.injEq] at letter
      have small := of_decide_eq_false letter
      exact ⟨depth,present,inside.1,by omega⟩
    · simp [inside] at letter
  · rintro ⟨depth,present,lo,hi⟩
    exact List.mem_filterMap.mpr ⟨depth,present,by simp [lo,hi.trans valid,show ¬split.cut<depth by omega]⟩

theorem true_mem_depthWord (split : DepthSplit) (valid : split.lo ≤ split.cut) (depths : List Nat) :
    true ∈ depthWord split depths ↔ ∃ depth ∈ depths, split.cut < depth ∧ depth ≤ split.hi := by
  constructor
  · intro member
    obtain ⟨depth, present, letter⟩ := List.mem_filterMap.mp member
    by_cases inside : split.lo ≤ depth ∧ depth ≤ split.hi
    · simp only [if_pos inside, Option.some.injEq] at letter
      exact ⟨depth,present,of_decide_eq_true letter,inside.2⟩
    · simp [inside] at letter
  · rintro ⟨depth,present,lo,hi⟩
    exact List.mem_filterMap.mpr ⟨depth,present,by simp [show split.lo≤depth by omega,hi,lo]⟩

theorem mixed_depthWord (split : DepthSplit) (lo : split.lo ≤ split.cut) (hi : split.cut ≤ split.hi) (depths : List Nat) :
    Mixed (depthWord split depths) ↔ MixedSplit split depths := by
  rw [Mixed, false_mem_depthWord split hi, true_mem_depthWord split lo]
  rfl

abbrev Row := Σ _ : DepthSplit, Key

structure Query where
  address : Key
  ancestors : List Nat

def Query.ancestorWrites (query : Query) (row : Row) : List Bool :=
  if row.2 = query.address.take row.1.lo then depthWord row.1 query.ancestors else []

def Query.finalWrites (query : Query) (row : Row) : List Bool :=
  if row.2 = query.address.take row.1.lo then depthWord row.1 [query.address.length] else []

def rows {lower upper : Nat} (hierarchy : DepthTree lower upper) : Finset Row :=
  hierarchy.nodes.sigma (fun split => level split.lo)

theorem query_owner_bound (query : Query) (split : DepthSplit)
    (lo : split.lo ≤ split.cut) (hi : split.cut ≤ split.hi) :
    (∑ owner ∈ level split.lo, if Mixed (query.ancestorWrites ⟨split,owner⟩) then 1 else 0) ≤
      if MixedSplit split query.ancestors then 1 else 0 := by
  have word := mixed_depthWord split lo hi query.ancestors
  by_cases mixed : MixedSplit split query.ancestors
  · have equal : (∑ owner ∈ level split.lo, if Mixed (query.ancestorWrites ⟨split,owner⟩) then 1 else 0) =
        ∑ owner ∈ level split.lo, if owner = query.address.take split.lo then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro owner member
      by_cases same : owner = query.address.take split.lo
      · simp only [Query.ancestorWrites, if_pos same, word.mpr mixed, if_true]
      · simp [Query.ancestorWrites, same, Mixed]
    rw [equal, if_pos mixed]
    simp only [Finset.sum_ite_eq']
    split <;> omega
  · have absent := mt word.mp mixed
    rw [if_neg mixed]
    apply Nat.le_zero.mpr
    apply Finset.sum_eq_zero
    intro owner member
    by_cases same : owner = query.address.take split.lo
    · simp only [Query.ancestorWrites, if_pos same, if_neg absent]
    · simp [Query.ancestorWrites, same, Mixed]

/-- The owner index creates no multiplicity: a query writes one row at each
secondary interval. Only mixed ancestor blocks can be changed by reversal. -/
theorem query_rows_bound {lower upper : Nat} (hierarchy : DepthTree lower upper) (query : Query) :
    (∑ row ∈ rows hierarchy, if Mixed (query.ancestorWrites row) then 1 else 0) ≤ query.ancestors.length-1 := by
  have intervals : (∑ row ∈ rows hierarchy, if Mixed (query.ancestorWrites row) then 1 else 0) ≤
      branching hierarchy query.ancestors := by
    rw [rows, Finset.sum_sigma]
    apply Finset.sum_le_sum
    intro split member
    have bounds := hierarchy.node_bounds member
    exact query_owner_bound query split bounds.2.1 (by omega)
  exact intervals.trans (branching_le_length hierarchy query.ancestors)

end MultiSplay.Secondary
