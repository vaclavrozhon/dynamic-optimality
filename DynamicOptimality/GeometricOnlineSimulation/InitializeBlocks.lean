import DynamicOptimality.GeometricOnlineSimulation.Blocks

/-!
# Initializing dyadic blocks on exactly the supplied keys

Binary expansion of the number of external gaps gives strictly decreasing
block levels. Each block is a perfect BST on its consecutive portion of
the supplied inorder word. No sentinel or duplicate key is introduced.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR ChaCha.MTR.Pointer

variable {α : Type*}

theorem Dyadic.decomposition (size : Nat) :
    ∃ levels, levels.Pairwise (· > ·) ∧ weight levels = size := by
  induction size using Nat.strong_induction_on with
  | h size ih =>
      by_cases zero : size = 0
      · subst size
        exact ⟨[], by simp, rfl⟩
      · let top := Nat.log 2 size
        have positive := Nat.two_pow_pos top
        have lower : 2 ^ top ≤ size := Nat.pow_log_le_self 2 zero
        have upper : size < 2 ^ top * 2 := by
          simpa only [top, pow_succ] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) size
        obtain ⟨rest, descending, remainder⟩ := ih (size - 2 ^ top) (by omega)
        refine ⟨top :: rest, List.pairwise_cons.mpr ⟨?_, descending⟩, ?_⟩
        · intro level member
          have bound := Dyadic.member_weight member
          rw [remainder] at bound
          by_contra contrary
          have powers : 2 ^ top ≤ 2 ^ level := Nat.pow_le_pow_right (by decide) (by omega)
          omega
        · simp only [Dyadic.weight_cons, remainder]
          omega

private theorem word_at (word : List α) (index : Nat) (inside : index < word.length) :
    word.take index ++ [word[index]] ++ word.drop (index + 1) = word := by
  have first : word.take index ++ [word[index]] = word.take (index + 1) := by
    simpa only [List.concat_eq_append] using List.take_concat_get inside
  rw [first]
  exact List.take_append_drop _ _

theorem Perfect.exists_word (level : Nat) (word : List α)
    (length : word.length = 2 ^ level - 1) :
    ∃ tree : RawTree α, Perfect level tree ∧ tree.inorder = word := by
  induction level generalizing word with
  | zero =>
      have empty : word = [] := by simpa using length
      subst word
      exact ⟨.empty, .empty, rfl⟩
  | succ level ih =>
      have positive := Nat.two_pow_pos level
      have size : word.length = 2 ^ level * 2 - 1 := by simpa only [pow_succ] using length
      have inside : 2 ^ level - 1 < word.length := by omega
      obtain ⟨left, leftPerfect, leftWord⟩ := ih (word.take (2 ^ level - 1)) (by
        simp only [List.length_take]
        omega)
      obtain ⟨right, rightPerfect, rightWord⟩ := ih (word.drop (2 ^ level - 1 + 1)) (by
        simp only [List.length_drop]
        omega)
      refine ⟨.node left word[2 ^ level - 1] right, .node _ leftPerfect rightPerfect, ?_⟩
      rw [Tree.inorder, leftWord, rightWord]
      exact word_at word (2 ^ level - 1) inside

theorem Fragment.exists_levels (levels : List Nat) (nonempty : levels ≠ [])
    (word : List α) (length : word.length + 1 = Dyadic.weight levels) :
    ∃ fragment : Fragment α, fragment.levels = levels ∧ fragment.marked.erase.inorder = word := by
  induction levels generalizing word with
  | nil => exact (nonempty rfl).elim
  | cons level rest ih =>
      have positive := Nat.two_pow_pos level
      cases rest with
      | nil =>
          have size : word.length = 2 ^ level - 1 := by
            simp only [Dyadic.weight_cons, Dyadic.weight_nil] at length
            omega
          obtain ⟨tree, perfect, inorder⟩ := Perfect.exists_word level word size
          exact ⟨.block level tree perfect, rfl, inorder⟩
      | cons next rest =>
          have restPositive : 0 < Dyadic.weight (next :: rest) := by
            have := Nat.two_pow_pos next
            simp only [Dyadic.weight_cons]
            omega
          have inside : 2 ^ level - 1 < word.length := by
            rw [Dyadic.weight_cons] at length
            omega
          obtain ⟨first, perfect, firstWord⟩ := Perfect.exists_word level
            (word.take (2 ^ level - 1)) (by simp only [List.length_take]; omega)
          obtain ⟨last, levelsLast, wordLast⟩ := ih (by simp) (word.drop (2 ^ level - 1 + 1)) (by
            simp only [List.length_drop]
            rw [Dyadic.weight_cons] at length
            omega)
          refine ⟨.node (.block level first perfect) word[2 ^ level - 1] last, ?_, ?_⟩
          · simp only [Fragment.levels, levelsLast, List.singleton_append]
          · simp only [Fragment.marked, MarkedTree.erase, Tree.inorder, firstWord, wordLast]
            exact word_at word (2 ^ level - 1) inside

/-- Every finite word has a valid initial block forest, with linear stored
credit and exactly its own original inorder word. -/
theorem Fragment.initial (word : List α) :
    ∃ fragment : Fragment α,
      fragment.marked.erase.inorder = word ∧
      Dyadic.Mountain fragment.levels ∧ Dyadic.credit fragment.levels ≤ word.length := by
  obtain ⟨levels, descending, weight⟩ := Dyadic.decomposition (word.length + 1)
  have nonempty : levels ≠ [] := by intro empty; simp [empty] at weight
  obtain ⟨fragment, levelsEq, wordEq⟩ := Fragment.exists_levels levels nonempty word weight.symm
  refine ⟨fragment, wordEq, ?_, ?_⟩
  · rw [levelsEq]
    exact Dyadic.Mountain.of_decreasing descending
  · have accounting := fragment.credit_eq
    have size : fragment.marked.erase.size = word.length := by
      rw [← Tree.length_inorder, wordEq]
    omega

end DynamicOptimality.GeometricOnlineSimulation
