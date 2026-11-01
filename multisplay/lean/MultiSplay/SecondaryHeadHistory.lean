import MultiSplay.SecondaryHeadAccounting
import MultiSplay.IntervalGadgets

/-!
# Actual row heads and the lower-bound demand word

After the first owner-local request, the first write of each nonempty query
block is exactly the coarse/fine transition of the last two local requests.
No independently supplied head history or charging assumption is used.
-/

namespace MultiSplay.Secondary

open TangoSquared (Gadget transitionLabel transitionWord transitionsFrom changesFrom)
open TangoSquared.Primary
open EndpointEncoding

def rowGadget (row : Row) : Gadget := ⟨row.1,row.2⟩

def leafBlocks (row : Row) (state : State) : List Key → List (List Bool)
  | [] => []
  | leaf::rest => ((ascendingEmissions state leaf).filterMap (project row leaf)) ::
      leafBlocks row (leafStep state leaf) rest

theorem leafBlocks_flatten (row : Row) (state : State) (leaves : List Key) :
    (leafBlocks row state leaves).flatten = leafRow row state leaves := by
  induction leaves generalizing state with
  | nil => rfl
  | cons leaf rest ih => simp only [leafBlocks,List.flatten_cons,leafRow,ih]

theorem leafBlocks_increasing (row : Row) (state : State) (leaves : List Key) :
    ∀ block ∈ leafBlocks row state leaves, block.Pairwise (· ≤ ·) := by
  induction leaves generalizing state with
  | nil => simp [leafBlocks]
  | cons leaf rest ih =>
      intro block member
      rcases List.mem_cons.mp member with rfl | later
      · rw [project_eq_depths]
        exact rowDepths_writes_increasing row state leaf
      · exact ih _ _ later

def headHistory (row : Row) (state : State) (leaves : List Key) : List Bool :=
  (leafBlocks row state leaves).filterMap List.head?

theorem headHistory_cons (row : Row) (state : State) (leaf : Key) (rest : List Key) :
    headHistory row state (leaf::rest) =
      ((ascendingEmissions state leaf).filterMap (project row leaf)).head?.toList ++
        headHistory row (leafStep state leaf) rest := by
  simp only [headHistory,leafBlocks]
  cases first : ((ascendingEmissions state leaf).filterMap (project row leaf)).head? <;>
    simp only [List.filterMap_cons,first,Option.toList_none,Option.toList_some,List.nil_append,List.singleton_append]

theorem outside_row_empty {row : Row} {leaf : Key} (outside : ¬row.2.IsPrefix leaf) (state : State) :
    (ascendingEmissions state leaf).filterMap (project row leaf) = [] := by
  have different : row.2 ≠ leaf.take row.1.lo := fun same => outside (same ▸ List.take_prefix _ _)
  simp [project,different]

theorem transitionLabel_lca {row : Row} {previous leaf : Key} (cut : row.1.cut ≤ row.1.hi)
    (equalLength : previous.length = leaf.length) (nonterminal : row.1.hi < leaf.length) :
    transitionLabel (rowGadget row).coarse (rowGadget row).fine previous leaf =
      if lcaDepth previous leaf ≤ row.1.hi then some (decide (row.1.cut < lcaDepth previous leaf)) else none := by
  have coarse := take_eq_iff (x := previous) (y := leaf) (d := row.1.cut+1) (by omega) (by omega)
  have fine := take_eq_iff (x := previous) (y := leaf) (d := row.1.hi+1) (by omega) (by omega)
  simp only [transitionLabel,rowGadget,Gadget.coarse,Gadget.fine,coarse,fine]
  by_cases beforeCut : lcaDepth previous leaf ≤ row.1.cut
  · simp [show ¬row.1.cut+1 ≤ lcaDepth previous leaf by omega,
      show lcaDepth previous leaf ≤ row.1.hi by omega,show ¬row.1.cut < lcaDepth previous leaf by omega]
  · by_cases inside : lcaDepth previous leaf ≤ row.1.hi
    · simp [show row.1.cut+1 ≤ lcaDepth previous leaf by omega,
        show ¬row.1.hi+1 ≤ lcaDepth previous leaf by omega,inside,
        show row.1.cut < lcaDepth previous leaf by omega]
    · simp [show row.1.cut+1 ≤ lcaDepth previous leaf by omega,
        show row.1.hi+1 ≤ lcaDepth previous leaf by omega,inside]

theorem block_head_transition {row : Row} {state : State} {previous leaf : Key}
    (remembered : Remembers state row.2 previous) (length : row.2.length = row.1.lo)
    (ownerPrevious : row.2.IsPrefix previous) (ownerLeaf : row.2.IsPrefix leaf)
    (cut : row.1.cut ≤ row.1.hi) (equalLength : previous.length = leaf.length)
    (nonterminal : row.1.hi < leaf.length) :
    ((ascendingEmissions state leaf).filterMap (project row leaf)).head? =
      transitionLabel (rowGadget row).coarse (rowGadget row).fine previous leaf := by
  rw [project_eq_depths,List.head?_map,rowDepths_head remembered length ownerPrevious ownerLeaf equalLength nonterminal,
    transitionLabel_lca cut equalLength nonterminal]
  split <;> rfl

theorem headHistory_remembered {height : Nat} {row : Row} {state : State} {previous : Key}
    (remembered : Remembers state row.2 previous) (length : row.2.length = row.1.lo)
    (ownerPrevious : row.2.IsPrefix previous) (cut : row.1.cut ≤ row.1.hi)
    (nonterminal : row.1.hi < height) (previousHeight : previous.length = height)
    (leaves : List Key) (heights : ∀ leaf ∈ leaves, leaf.length = height) :
    headHistory row state leaves = transitionsFrom (rowGadget row).coarse (rowGadget row).fine previous (ownerWord row.2 leaves) := by
  induction leaves generalizing state previous with
  | nil => rfl
  | cons leaf rest ih =>
      have here := heights leaf (by simp)
      have later := fun key member => heights key (List.mem_cons_of_mem _ member)
      rw [headHistory_cons]
      by_cases inside : row.2.IsPrefix leaf
      · rw [block_head_transition remembered length ownerPrevious inside cut (by omega) (by omega)]
        rw [ih (remembers_after state row.2 leaf) inside here later]
        simp only [ownerWord,List.filter_cons,decide_eq_true inside,if_true,transitionsFrom]
      · rw [outside_row_empty inside state]
        simp only [List.head?_nil,Option.toList_none,List.nil_append]
        rw [ih (remembered.away inside) ownerPrevious previousHeight later]
        simp only [ownerWord,List.filter_cons,decide_eq_false inside,Bool.false_eq_true,if_false]

theorem headHistory_first {height : Nat} {row : Row} (state : State)
    (length : row.2.length = row.1.lo) (cut : row.1.cut ≤ row.1.hi) (nonterminal : row.1.hi < height)
    (leaves : List Key) (heights : ∀ leaf ∈ leaves, leaf.length = height) :
    ∃ first : Option Bool, headHistory row state leaves = first.toList ++
      transitionWord (rowGadget row).coarse (rowGadget row).fine (ownerWord row.2 leaves) := by
  induction leaves generalizing state with
  | nil => exact ⟨none,rfl⟩
  | cons leaf rest ih =>
      have here := heights leaf (by simp)
      have later := fun key member => heights key (List.mem_cons_of_mem _ member)
      by_cases inside : row.2.IsPrefix leaf
      · refine ⟨((ascendingEmissions state leaf).filterMap (project row leaf)).head?,?_⟩
        rw [headHistory_cons,headHistory_remembered (remembers_after state row.2 leaf) length inside cut nonterminal here rest later]
        simp only [ownerWord,List.filter_cons,decide_eq_true inside,if_true,transitionWord]
      · obtain ⟨first,tail⟩ := ih (leafStep state leaf) later
        refine ⟨first,?_⟩
        rw [headHistory_cons,outside_row_empty inside state]
        simp only [List.head?_nil,Option.toList_none,List.nil_append,tail,
          ownerWord,List.filter_cons,decide_eq_false inside,Bool.false_eq_true,if_false]

def rowResets (row : Row) (state : State) (leaves : List Key) : Nat :=
  ((leafBlocks row state leaves).map (fun block => if Mixed block then 1 else 0)).sum

/-- The full nonterminal row estimate, on the actual initialized leaf history. -/
theorem leafRow_demand_bound {height : Nat} {row : Row} (state : State) (initial : Bool)
    (length : row.2.length = row.1.lo) (cut : row.1.cut ≤ row.1.hi) (nonterminal : row.1.hi < height)
    (leaves : List Key) (heights : ∀ leaf ∈ leaves, leaf.length = height) :
    changesFrom initial (leafRow row state leaves) ≤
      2*(rowGadget row).count leaves + 2*rowResets row state leaves + 3 := by
  have blocks := write_blocks_head_bound initial (leafBlocks row state leaves) (leafBlocks_increasing row state leaves)
  obtain ⟨first,heads⟩ := headHistory_first state length cut nonterminal leaves heights
  have bound := TangoSquared.FlipAccounting.exceptional_head_bound initial first
    (transitionWord (rowGadget row).coarse (rowGadget row).fine (ownerWord row.2 leaves))
  rw [leafBlocks_flatten] at blocks
  change changesFrom initial (leafRow row state leaves) ≤ changesFrom initial (headHistory row state leaves) +
    2*rowResets row state leaves at blocks
  rw [heads] at blocks
  change changesFrom initial (first.toList ++ _) ≤ 2*(rowGadget row).count leaves + 3 at bound
  omega

end MultiSplay.Secondary
