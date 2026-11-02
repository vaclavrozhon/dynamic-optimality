import MultiSplay.SecondaryRecency

/-!
# Removing the reset suffixes of increasing write blocks

Within one query, a row receives only left writes followed by right writes.
Replacing each nonempty block by its first letter costs at most two flips
per mixed block, including the boundary with the following query.
-/

namespace MultiSplay.Secondary

open ChaCha (changesFrom edgeChange)

theorem increasing_changes_le (initial : Bool) (word : List Bool)
    (sorted : word.Pairwise (· ≤ ·)) (lower : ∀ bit ∈ word, initial ≤ bit) :
    changesFrom initial word ≤ if initial then 0 else 1 := by
  induction word generalizing initial with
  | nil => simp
  | cons bit rest ih =>
      obtain ⟨head,tail⟩ := List.pairwise_cons.mp sorted
      have bound := ih bit tail head
      have start := lower bit (by simp)
      cases initial with
      | false =>
          cases bit with
          | false => simpa [changesFrom,edgeChange] using bound
          | true => simpa [changesFrom,edgeChange] using bound
      | true =>
          cases bit with
          | false => exact False.elim ((by decide : ¬((true : Bool) ≤ false)) start)
          | true => simpa [changesFrom,edgeChange] using bound

theorem constant_prefix_changes (bit : Bool) (word tail : List Bool)
    (constant : ∀ value ∈ word, value = bit) :
    changesFrom bit (word++tail) = changesFrom bit tail := by
  induction word with
  | nil => rfl
  | cons value rest ih =>
      have same := constant value (by simp)
      subst value
      simpa only [List.cons_append,ChaCha.changesFrom_cons,ChaCha.edgeChange_self,Nat.zero_add] using
        ih (fun value member => constant value (List.mem_cons_of_mem _ member))

theorem remove_block_tail (initial : Bool) (word tail : List Bool)
    (sorted : word.Pairwise (· ≤ ·)) :
    changesFrom initial (word++tail) ≤
      changesFrom initial (word.head?.toList++tail) + 2*(if Mixed word then 1 else 0) := by
  cases word with
  | nil => simp [Mixed]
  | cons bit rest =>
      by_cases mixed : Mixed (bit::rest)
      · obtain ⟨head,increasing⟩ := List.pairwise_cons.mp sorted
        have inside := increasing_changes_le bit rest increasing head
        have boundary := ChaCha.FlipAccounting.changesFrom_initial_le (rest.getLastD bit) bit tail
        simp only [List.cons_append,ChaCha.changesFrom_cons,List.head?_cons,Option.toList_some,
          List.singleton_append,List.nil_append,if_pos mixed]
        rw [changesFrom_append]
        cases bit <;> simp only [Bool.false_eq_true,if_false,if_true] at inside <;> omega
      · have constant : ∀ value ∈ rest, value = bit := by
          intro value member
          cases bit <;> cases value <;> simp_all [Mixed]
        simp only [List.cons_append,ChaCha.changesFrom_cons,List.head?_cons,Option.toList_some,
          List.singleton_append,List.nil_append,if_neg mixed,Nat.mul_zero,Nat.add_zero]
        rw [constant_prefix_changes bit rest tail constant]

theorem write_blocks_head_bound (initial : Bool) (blocks : List (List Bool))
    (sorted : ∀ block ∈ blocks, block.Pairwise (· ≤ ·)) :
    changesFrom initial blocks.flatten ≤
      changesFrom initial (blocks.filterMap List.head?) +
        2*(blocks.map (fun block => if Mixed block then 1 else 0)).sum := by
  induction blocks generalizing initial with
  | nil => simp
  | cons block rest ih =>
      have tailSorted := fun block member => sorted block (List.mem_cons_of_mem _ member)
      have first := remove_block_tail initial block rest.flatten (sorted block (by simp))
      cases block with
      | nil => simpa [Mixed] using ih initial tailSorted
      | cons bit suffix =>
          have later := ih bit tailSorted
          simp only [List.flatten_cons,List.filterMap_cons,List.head?_cons,List.map_cons,List.sum_cons]
          simp only [List.head?_cons,Option.toList_some,List.singleton_append,ChaCha.changesFrom_cons] at first
          simp only [ChaCha.changesFrom_cons]
          omega

theorem rowDepths_writes_increasing (row : Row) (state : EndpointEncoding.State) (leaf : ChaCha.Primary.Key) :
    ((rowDepths row state leaf).map (fun depth => decide (row.1.cut < depth))).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  apply (rowDepths_increasing row state leaf).imp
  intro a b increasing
  by_cases left : row.1.cut < a <;> by_cases right : row.1.cut < b <;> simp [left,right] <;> omega

end MultiSplay.Secondary
