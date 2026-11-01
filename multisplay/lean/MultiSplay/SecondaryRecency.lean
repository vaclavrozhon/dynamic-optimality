import MultiSplay.EndpointLedgerSupport
import TangoSquared.NormalizedWords

/-!
# The first changed depth after an owner-local request

`Remembers` says that a primary state still records the last request within
one owner's subtree. Requests outside that subtree preserve this fact. On
the next local request, no changed depth precedes the lowest common ancestor,
and that ancestor changes whenever the two requested leaves are distinct.
-/

namespace MultiSplay.Secondary

open TangoSquared.Primary
open EndpointEncoding

def Remembers (state : State) (owner previous : Key) : Prop :=
  ∀ node side, owner.IsPrefix node → branch node previous = some side → state node = side

theorem remembers_after (state : State) (owner previous : Key) :
    Remembers (leafStep state previous) owner previous := by
  intro node side ancestor written
  simp [leafStep,written]

theorem Remembers.away {state : State} {owner previous leaf : Key}
    (remembered : Remembers state owner previous) (outside : ¬ owner.IsPrefix leaf) :
    Remembers (leafStep state leaf) owner previous := by
  intro node side ancestor written
  have silent : branch node leaf = none := by
    have absent : ¬node.IsPrefix leaf := fun pre => outside (ancestor.trans pre)
    simp [branch,absent]
  simp [leafStep,silent,remembered node side ancestor written]

theorem remembered_no_early_change {state : State} {owner previous leaf emitted : Key}
    (remembered : Remembers state owner previous)
    (ownerPrevious : owner.IsPrefix previous) (ownerLeaf : owner.IsPrefix leaf)
    (lower : owner.length ≤ emitted.length)
    (member : emitted ∈ ascendingEmissions state leaf) :
    lcaDepth previous leaf ≤ emitted.length := by
  by_contra early
  have less : emitted.length < lcaDepth previous leaf := by omega
  have prefixLeaf := ascendingEmissions_prefix member
  have prefixPrevious : emitted.IsPrefix previous := by
    have common : emitted.IsPrefix (leaf.take (lcaDepth previous leaf)) := by
      apply List.prefix_of_prefix_length_le prefixLeaf (List.take_prefix _ _)
      simp only [List.length_take,Nat.min_eq_left (lcaDepth_le_right previous leaf)]
      omega
    exact common.trans (take_lca_prefix_left previous leaf)
  have ancestor : owner.IsPrefix emitted := List.prefix_of_prefix_length_le ownerLeaf prefixLeaf lower
  have lengthPrevious : emitted.length < previous.length := less.trans_le (lcaDepth_le_left previous leaf)
  have lengthLeaf : emitted.length < leaf.length := less.trans_le (lcaDepth_le_right previous leaf)
  let side := previous[emitted.length]
  have written : branch emitted previous = some side := by
    simp [branch,prefixPrevious,List.getElem?_eq_getElem lengthPrevious,side]
  have same : branch emitted leaf = some side := by
    rw [branch,if_pos prefixLeaf,← getElem?_eq_of_lt_lca less]
    exact List.getElem?_eq_getElem lengthPrevious
  have old := remembered emitted side ancestor written
  have different : emitted ≠ leaf := fun eqn => by subst emitted; omega
  have changed := ascendingEmissions_mem.mp member
  simp [nodeWrite,different,changes,same,old] at changed

theorem remembered_lca_changes {state : State} {owner previous leaf : Key}
    (remembered : Remembers state owner previous)
    (ownerPrevious : owner.IsPrefix previous) (ownerLeaf : owner.IsPrefix leaf)
    (properPrevious : lcaDepth previous leaf < previous.length)
    (properLeaf : lcaDepth previous leaf < leaf.length) :
    leaf.take (lcaDepth previous leaf) ∈ ancestorEmissions state leaf := by
  obtain ⟨left,right,different,before,after⟩ :=
    TangoSquared.NormalizedWords.branches_at_proper_lca properPrevious properLeaf
  have old := remembered _ left (prefix_take_lca ownerPrevious ownerLeaf) before
  have notLeaf : leaf.take (lcaDepth previous leaf) ≠ leaf := by
    intro same
    have lengths := congrArg List.length same
    simp only [List.length_take,Nat.min_eq_left (lcaDepth_le_right previous leaf)] at lengths
    omega
  have member : leaf.take (lcaDepth previous leaf) ∈ ascendingEmissions state leaf := by
    apply ascendingEmissions_mem.mpr
    simp [nodeWrite,notLeaf,changes,after,old,different]
  simpa only [ascendingEmissions,List.mem_append,List.mem_singleton,notLeaf,or_false] using member

def rowDepths (row : Row) (state : State) (leaf : Key) : List Nat :=
  if row.2 = leaf.take row.1.lo then
    ((ascendingEmissions state leaf).map List.length).filter
      (fun depth => decide (row.1.lo ≤ depth ∧ depth ≤ row.1.hi))
  else []

theorem rowDepths_increasing (row : Row) (state : State) (leaf : Key) :
    (rowDepths row state leaf).Pairwise (· < ·) := by
  unfold rowDepths
  split
  · exact (List.pairwise_map.mpr (ascendingEmissions_increasing state leaf)).filter _
  · simp

theorem project_eq_depths (row : Row) (state : State) (leaf : Key) :
    (ascendingEmissions state leaf).filterMap (project row leaf) =
      (rowDepths row state leaf).map (fun depth => decide (row.1.cut < depth)) := by
  by_cases owner : row.2 = leaf.take row.1.lo
  · simp only [rowDepths,if_pos owner,project,owner,if_true]
    generalize ascendingEmissions state leaf = emissions
    induction emissions with
    | nil => rfl
    | cons emitted rest ih =>
        by_cases inside : row.1.lo ≤ emitted.length ∧ emitted.length ≤ row.1.hi <;>
          simp [inside,ih]
  · simp [project,rowDepths,owner]

theorem rowDepths_head {row : Row} {state : State} {previous leaf : Key}
    (remembered : Remembers state row.2 previous)
    (length : row.2.length = row.1.lo)
    (ownerPrevious : row.2.IsPrefix previous) (ownerLeaf : row.2.IsPrefix leaf)
    (equalLength : previous.length = leaf.length) (nonterminal : row.1.hi < leaf.length) :
    (rowDepths row state leaf).head? =
      if lcaDepth previous leaf ≤ row.1.hi then some (lcaDepth previous leaf) else none := by
  have owner : row.2 = leaf.take row.1.lo := by
    simpa only [length] using List.prefix_iff_eq_take.mp ownerLeaf
  have lower : row.1.lo ≤ lcaDepth previous leaf := by
    have bound := (prefix_take_lca ownerPrevious ownerLeaf).length_le
    simp only [length,List.length_take,Nat.min_eq_left (lcaDepth_le_right previous leaf)] at bound
    exact bound
  have minimum : ∀ depth ∈ rowDepths row state leaf, lcaDepth previous leaf ≤ depth := by
    intro depth member
    simp only [rowDepths,if_pos owner,List.mem_filter,List.mem_map,decide_eq_true_eq] at member
    obtain ⟨⟨emitted,emission,rfl⟩,bounds⟩ := member
    exact remembered_no_early_change remembered ownerPrevious ownerLeaf (by omega) emission
  by_cases inside : lcaDepth previous leaf ≤ row.1.hi
  · have emitted := remembered_lca_changes remembered ownerPrevious ownerLeaf (by omega) (by omega)
    have member : lcaDepth previous leaf ∈ rowDepths row state leaf := by
      simp only [rowDepths,if_pos owner,List.mem_filter,List.mem_map,decide_eq_true_eq]
      exact ⟨⟨leaf.take (lcaDepth previous leaf),List.mem_append_left [leaf] emitted,
        by simp [List.length_take,Nat.min_eq_left (lcaDepth_le_right previous leaf)]⟩,lower,inside⟩
    rw [if_pos inside]
    have sorted := rowDepths_increasing row state leaf
    cases depths : rowDepths row state leaf with
    | nil => simp [depths] at member
    | cons first rest =>
        simp only [depths,List.mem_cons] at member
        have bound := minimum first (by simp [depths])
        rcases member with rfl | later
        · rfl
        · rw [depths,List.pairwise_cons] at sorted
          have strict := sorted.1 _ later
          omega
  · have empty : rowDepths row state leaf = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro depth member
      have bound := minimum depth member
      simp only [rowDepths,if_pos owner,List.mem_filter,decide_eq_true_eq] at member
      omega
    simp [empty,inside]

end MultiSplay.Secondary
