import MultiSplay.SecondaryHeadHistory

/-!
# The global reset budget

A mixed row block corresponds to a branching interval of the query's emitted
depth set. The completion emission contributes one extra depth, so the number
of mixed rows is at most the number of actual primary changes.
-/

namespace MultiSplay.EndpointEncoding

open TangoSquared.Primary (Key branch owners mem_owners)

theorem ancestorEmissions_toFinset {height : Nat} (state : State) {leaf : Key}
    (length : leaf.length = height) :
    (ancestorEmissions state leaf).toFinset = leafSwitches height state leaf := by
  ext owner
  simp only [List.mem_toFinset,leafSwitches,Finset.mem_filter,mem_owners]
  constructor
  · intro member
    have sorted := ascendingEmissions_increasing state leaf
    rw [ascendingEmissions,List.pairwise_append] at sorted
    have less := sorted.2.2 owner member leaf (by simp)
    exact ⟨by omega,ancestorEmissions_changes member⟩
  · rintro ⟨inside,changed⟩
    have different : owner ≠ leaf := fun same => by subst owner; omega
    have member : owner ∈ ascendingEmissions state leaf := by
      apply ascendingEmissions_mem.mpr
      simpa only [nodeWrite,if_neg different] using changed
    simpa only [ascendingEmissions,List.mem_append,List.mem_singleton,different,or_false] using member

theorem ancestorEmissions_count {height : Nat} (state : State) {leaf : Key} (length : leaf.length = height) :
    (ancestorEmissions state leaf).length = (leafSwitches height state leaf).card := by
  have distinct : (ancestorEmissions state leaf).Nodup :=
    (ascendingEmissions_nodup state leaf).sublist (List.sublist_append_left _ _)
  rw [← ancestorEmissions_toFinset state length,List.toFinset_card_of_nodup distinct]

end MultiSplay.EndpointEncoding

namespace MultiSplay.Secondary

open TangoSquared (DepthTree)
open TangoSquared.Primary (Key)
open EndpointEncoding

theorem query_writes_eq_project (state : State) (leaf : Key) (row : Row) :
    (⟨leaf,(ascendingEmissions state leaf).map List.length⟩ : Query).ancestorWrites row =
      (ascendingEmissions state leaf).filterMap (project row leaf) := by
  by_cases owner : row.2 = leaf.take row.1.lo <;>
    simp [Query.ancestorWrites,depthWord,project,owner,List.filterMap_map]

theorem query_reset_budget {lower upper height : Nat} (hierarchy : DepthTree lower upper)
    (state : State) {leaf : Key} (length : leaf.length = height) :
    (∑ row ∈ rows hierarchy,
      if Mixed ((ascendingEmissions state leaf).filterMap (project row leaf)) then 1 else 0) ≤
        (leafSwitches height state leaf).card := by
  have bound := query_rows_bound hierarchy ⟨leaf,(ascendingEmissions state leaf).map List.length⟩
  simp only [query_writes_eq_project] at bound
  have count : ((ascendingEmissions state leaf).map List.length).length - 1 =
      (leafSwitches height state leaf).card := by
    simp only [List.length_map,ascendingEmissions,List.length_append,List.length_singleton,
      Nat.add_sub_cancel,ancestorEmissions_count state length]
  rw [count] at bound
  exact bound

/-- Resets of all persistent owner rows are paid jointly by primary flips. -/
theorem reset_history_budget {lower upper height : Nat} (hierarchy : DepthTree lower upper)
    (state : State) (leaves : List Key) (heights : ∀ leaf ∈ leaves, leaf.length = height) :
    (∑ row ∈ rows hierarchy, rowResets row state leaves) ≤ leafCost height state leaves := by
  induction leaves generalizing state with
  | nil => simp [rowResets,leafBlocks,leafCost]
  | cons leaf rest ih =>
      have first := query_reset_budget hierarchy state (heights leaf (by simp))
      have later := ih (leafStep state leaf) (fun key member => heights key (List.mem_cons_of_mem _ member))
      simp only [rowResets,leafBlocks,List.map_cons,List.sum_cons,Finset.sum_add_distrib,leafCost]
      change _ + (∑ row ∈ rows hierarchy, rowResets row (leafStep state leaf) rest) ≤ _
      omega

end MultiSplay.Secondary
