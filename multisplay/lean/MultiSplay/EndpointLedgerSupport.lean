import MultiSplay.EndpointCoreCounting

/-!
# Initial primary changes and left-writing secondary rows

The support bounds apply to the actual adaptive encoded history. They charge
only core vertices and core-owned rows, rather than the full perfect reference.
-/

namespace MultiSplay.EndpointEncoding

open TangoSquared (changesFrom alternations primaryCount)
open TangoSquared.Primary (Key branch owners)

theorem leafCost_eq_sum (height : Nat) (state : State) (leaves : List Key) :
    leafCost height state leaves = ∑ owner ∈ owners height,
      changesFrom (state owner) (leaves.filterMap (branch owner)) := by
  induction leaves generalizing state with
  | nil => simp [leafCost]
  | cons leaf rest ih =>
      rw [leafCost,ih,leafSwitches,Finset.card_filter,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro owner member
      simp only [List.filterMap_cons]
      cases write : branch owner leaf with
      | none => simp [write,changes,leafStep]
      | some side =>
          by_cases same : state owner = side <;>
            simp [write,changes,leafStep,changesFrom,TangoSquared.edgeChange,same]

theorem encoded_outside_changes_zero {height : Nat} {leafState : State}
    (right : RightOutside height leafState) (nodeState : State) {addresses : List Key}
    (inside : ∀ address ∈ addresses, address.length < height) {owner : Key}
    (outside : owner ∉ coreNodes height) (internal : owner.length < 2*height) :
    changesFrom (leafState owner) ((encode height nodeState addresses).filterMap (branch owner)) = 0 := by
  induction addresses generalizing nodeState leafState with
  | nil => rfl
  | cons address rest ih =>
      have here := inside address (by simp)
      have old := right owner internal outside
      have next := right.leafStep here (!nodeState address)
      have later := ih next (nodeStep nodeState address)
        (fun key member => inside key (List.mem_cons_of_mem _ member))
      have noLeft : branch owner (request height nodeState address) ≠ some false :=
        fun left => outside (false_branch_core here (!nodeState address) left)
      change changesFrom ((branch owner (request height nodeState address)).getD (leafState owner))
        ((encode height (nodeStep nodeState address) rest).filterMap (branch owner)) = 0 at later
      simp only [encode,List.filterMap_cons]
      cases write : branch owner (request height nodeState address) with
      | none => simpa only [write,Option.getD_none] using later
      | some side =>
          cases side
          · exact False.elim (noLeft write)
          · simpa only [write,Option.getD_some,changesFrom,TangoSquared.edgeChange,old,
              if_true,Nat.zero_add] using later

theorem encoded_leafCost_le_primary {height : Nat} {leafState : State}
    (right : RightOutside height leafState) (nodeState : State) {addresses : List Key}
    (inside : ∀ address ∈ addresses, address.length < height) :
    leafCost (2*height) leafState (encode height nodeState addresses) ≤
      primaryCount (2*height) (encode height nodeState addresses) + 3*(2^height-1) := by
  have rows : ∀ owner ∈ owners (2*height),
      changesFrom (leafState owner) ((encode height nodeState addresses).filterMap (branch owner)) ≤
        alternations ((encode height nodeState addresses).filterMap (branch owner)) +
          if owner ∈ coreNodes height then 1 else 0 := by
    intro owner member
    by_cases present : owner ∈ coreNodes height
    · simpa only [if_pos present] using TangoSquared.FlipAccounting.changesFrom_le_alternations_add_one
        (leafState owner) ((encode height nodeState addresses).filterMap (branch owner))
    · rw [encoded_outside_changes_zero right nodeState inside present ((TangoSquared.Primary.mem_owners _ _).mp member),if_neg present]
      omega
  have sums := Finset.sum_le_sum rows
  rw [Finset.sum_add_distrib,← leafCost_eq_sum,Finset.sum_boole] at sums
  have initBound : ((owners (2*height)).filter (fun owner => owner ∈ coreNodes height)).card ≤ 3*(2^height-1) := by
    have subset : (owners (2*height)).filter (fun owner => owner ∈ coreNodes height) ⊆ coreNodes height :=
      fun owner member => (Finset.mem_filter.mp member).2
    exact (Finset.card_le_card subset).trans (coreNodes_card height)
  exact sums.trans (Nat.add_le_add_left initBound _)

end MultiSplay.EndpointEncoding

namespace MultiSplay.Secondary

open TangoSquared (DepthTree)
open TangoSquared.Primary (Key)
open EndpointEncoding

theorem project_false {row : Row} {leaf emitted : Key}
    (letter : project row leaf emitted = some false) :
    row.2 = leaf.take row.1.lo ∧ row.1.lo ≤ emitted.length ∧ emitted.length ≤ row.1.cut := by
  unfold project at letter
  split at letter
  next owner =>
    split at letter
    next interval =>
      have direction : ¬row.1.cut < emitted.length := by simpa using letter
      exact ⟨owner,interval.1,by omega⟩
    next absent => cases letter
  next absent => cases letter

theorem encoded_left_owner_core {height : Nat} {row : Row} (cut : row.1.cut < 2*height)
    {leafState : State} (right : RightOutside height leafState) (nodeState : State) {addresses : List Key}
    (inside : ∀ address ∈ addresses, address.length < height)
    (left : false ∈ leafRow row leafState (encode height nodeState addresses)) : row.2 ∈ coreNodes height := by
  induction addresses generalizing nodeState leafState with
  | nil => simp [encode,leafRow] at left
  | cons address rest ih =>
      have here := inside address (by simp)
      simp only [encode,leafRow,List.mem_append] at left
      rcases left with now | later
      · obtain ⟨emitted,member,letter⟩ := List.mem_filterMap.mp now
        obtain ⟨owner,lower,upper⟩ := project_false letter
        have pre := ascendingEmissions_prefix member
        simp only [ascendingEmissions,List.mem_append,List.mem_singleton] at member
        rcases member with ancestor | rfl
        · have coreMember := ancestorEmissions_core right here (!nodeState address) ancestor
          apply coreNodes_prefix_closed coreMember
          apply List.prefix_of_prefix_length_le (owner ▸ List.take_prefix _ _) pre
          rw [owner,List.length_take]
          omega
        · have length := copy_length here (!nodeState address)
          change (request height nodeState address).length = 2*height at length
          omega
      · exact ih (right.leafStep here (!nodeState address)) (nodeStep nodeState address)
          (fun key member => inside key (List.mem_cons_of_mem _ member)) later

/-- Only linearly many initialized secondary rows ever receive a left write. -/
theorem encoded_left_rows_card {height : Nat} (hierarchy : DepthTree 0 (2*height))
    {leafState : State} (right : RightOutside height leafState) (nodeState : State) {addresses : List Key}
    (inside : ∀ address ∈ addresses, address.length < height) :
    ((rows hierarchy).filter (fun row => false ∈ leafRow row leafState (encode height nodeState addresses))).card ≤
      4*(2^height-1) := by
  have subset : (rows hierarchy).filter (fun row => false ∈ leafRow row leafState (encode height nodeState addresses)) ⊆
      coreRows height hierarchy := by
    intro row member
    obtain ⟨valid,left⟩ := Finset.mem_filter.mp member
    have splitMember := (Finset.mem_sigma.mp valid).1
    have bounds := hierarchy.node_bounds splitMember
    exact Finset.mem_filter.mpr ⟨valid,encoded_left_owner_core (by omega) right nodeState inside left⟩
  exact (Finset.card_le_card subset).trans (coreRows_card hierarchy le_rfl)

end MultiSplay.Secondary
