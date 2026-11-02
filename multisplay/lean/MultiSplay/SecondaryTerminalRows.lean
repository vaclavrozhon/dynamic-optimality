import MultiSplay.SecondaryResetBudget

/-!
# Terminal rows and the support-sensitive initialized bound

Every visited terminal row receives the completion's final right write. From
right initialization its flips are paid entirely by mixed blocks. A row that
never receives a left write needs no first-head allowance.
-/

namespace MultiSplay.Secondary

open ChaCha (changesFrom edgeChange)
open ChaCha.Primary (Key)
open EndpointEncoding

theorem no_left_changes {word : List Bool} (absent : false ∉ word) : changesFrom true word = 0 := by
  induction word with
  | nil => rfl
  | cons bit rest ih =>
      cases bit
      · simp at absent
      · simp only [ChaCha.changesFrom_cons,ChaCha.edgeChange_self,Nat.zero_add]
        exact ih (fun member => absent (List.mem_cons_of_mem _ member))

theorem increasing_word_cost_le_two (initial : Bool) {word : List Bool} (sorted : word.Pairwise (· ≤ ·)) :
    changesFrom initial word ≤ 2 := by
  cases word with
  | nil => simp
  | cons bit rest =>
      obtain ⟨head,tail⟩ := List.pairwise_cons.mp sorted
      have bound := increasing_changes_le bit rest tail head
      cases bit <;> cases initial <;> simp_all [changesFrom,edgeChange] <;> omega

theorem terminal_block_bound {word : List Bool} (sorted : word.Pairwise (· ≤ ·)) (right : true ∈ word) :
    changesFrom true word ≤ 2*(if Mixed word then 1 else 0) := by
  by_cases mixed : Mixed word
  · simpa only [if_pos mixed] using increasing_word_cost_le_two true sorted
  · have absent : false ∉ word := fun left => mixed ⟨left,right⟩
    simp [if_neg mixed,no_left_changes absent]

theorem completion_project {row : Row} {leaf : Key}
    (owner : row.2 = leaf.take row.1.lo) (lower : row.1.lo ≤ row.1.cut)
    (cut : row.1.cut < leaf.length) (terminal : row.1.hi = leaf.length) :
    project row leaf leaf = some true := by
  simp [project,owner,terminal,cut,show row.1.lo ≤ leaf.length by omega]

theorem terminal_row_bound {height : Nat} {row : Row}
    (lower : row.1.lo ≤ row.1.cut) (cut : row.1.cut < height) (terminal : row.1.hi = height)
    (state : State) (leaves : List Key) (heights : ∀ leaf ∈ leaves, leaf.length = height) :
    changesFrom true (leafRow row state leaves) ≤ 2*rowResets row state leaves := by
  induction leaves generalizing state with
  | nil => simp [leafRow,rowResets,leafBlocks]
  | cons leaf rest ih =>
      have here := heights leaf (by simp)
      have later := ih (leafStep state leaf) (fun key member => heights key (List.mem_cons_of_mem _ member))
      by_cases owner : row.2 = leaf.take row.1.lo
      · have ending : (ascendingEmissions state leaf).filterMap (project row leaf) =
            (ancestorEmissions state leaf).filterMap (project row leaf) ++ [true] := by
          simp only [ascendingEmissions,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
            completion_project owner lower (by omega) (by omega)]
        have sorted : ((ascendingEmissions state leaf).filterMap (project row leaf)).Pairwise (· ≤ ·) := by
          rw [project_eq_depths]
          exact rowDepths_writes_increasing row state leaf
        have first := terminal_block_bound sorted (by rw [ending]; simp)
        have last : ((ascendingEmissions state leaf).filterMap (project row leaf)).getLastD true = true := by
          rw [ending]
          simp
        simp only [leafRow,changesFrom_append,last,rowResets,leafBlocks,List.map_cons,List.sum_cons]
        change _ + _ ≤ 2*((if Mixed _ then 1 else 0)+rowResets row (leafStep state leaf) rest)
        omega
      · have empty : (ascendingEmissions state leaf).filterMap (project row leaf) = [] := by
          simp [project,owner]
        simpa only [leafRow,empty,List.nil_append,rowResets,leafBlocks,List.map_cons,List.sum_cons,
          Mixed,List.not_mem_nil, false_and,if_false,Nat.zero_add] using later

/-- The additive initialization term is restricted to rows that receive a
left write. Terminal rows contribute no demand term or initialization term. -/
theorem initialized_row_bound {height : Nat} {row : Row}
    (length : row.2.length = row.1.lo) (lower : row.1.lo ≤ row.1.cut)
    (cut : row.1.cut < row.1.hi) (bounded : row.1.hi ≤ height)
    (state : State) (leaves : List Key) (heights : ∀ leaf ∈ leaves, leaf.length = height) :
    changesFrom true (leafRow row state leaves) ≤
      2*(if row.1.hi < height then (rowGadget row).count leaves else 0) +
      2*rowResets row state leaves + 3*(if false ∈ leafRow row state leaves then 1 else 0) := by
  by_cases left : false ∈ leafRow row state leaves
  · by_cases nonterminal : row.1.hi < height
    · simpa only [if_pos nonterminal,if_pos left] using
        leafRow_demand_bound state true length (by omega) nonterminal leaves heights
    · have terminal : row.1.hi = height := by omega
      have bound := terminal_row_bound lower (by omega) terminal state leaves heights
      simp only [if_neg nonterminal,if_pos left,Nat.mul_zero,Nat.zero_add]
      omega
  · rw [no_left_changes left]
    exact Nat.zero_le _

end MultiSplay.Secondary
