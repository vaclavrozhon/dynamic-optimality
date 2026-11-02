import DynamicOptimality.ColoredWalks.EmbeddingOrder
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-! # Choosing at most two endpoints per color

The selected list consists of every color minimum and maximum, in the
original key order. Each of the two endpoint sets injects into the colors;
this proves the uniform `2*k` bound without enumerating the key universe.
-/

namespace DynamicOptimality.ColoredWalks

variable {α : Type*} [LinearOrder α]

theorem exists_extreme_selection {k : Nat} (color : α → Fin k) (keys : List α)
    (ordered : keys.Pairwise (· < ·)) :
    ∃ selected : List α, selected.Sublist keys ∧ selected.length ≤ 2*k ∧
      (keys ≠ [] → selected ≠ []) ∧
      (∀ key, Extreme color keys key → key ∈ selected) := by
  classical
  let low : Finset α := keys.toFinset.filter
    (fun key => ∀ other ∈ keys, color other = color key → key ≤ other)
  let high : Finset α := keys.toFinset.filter
    (fun key => ∀ other ∈ keys, color other = color key → other ≤ key)
  have lowBound : low.card ≤ k := by
    calc
      low.card ≤ (Finset.univ : Finset (Fin k)).card :=
        Finset.card_le_card_of_injOn color (fun _ _ => Finset.mem_univ _) (by
          intro x hx y hy same
          have first := (Finset.mem_filter.mp hx).2
          have second := (Finset.mem_filter.mp hy).2
          exact le_antisymm
            (first y (List.mem_toFinset.mp (Finset.mem_filter.mp hy).1) same.symm)
            (second x (List.mem_toFinset.mp (Finset.mem_filter.mp hx).1) same))
      _ = k := Finset.card_fin k
  have highBound : high.card ≤ k := by
    calc
      high.card ≤ (Finset.univ : Finset (Fin k)).card :=
        Finset.card_le_card_of_injOn color (fun _ _ => Finset.mem_univ _) (by
          intro x hx y hy same
          have first := (Finset.mem_filter.mp hx).2
          have second := (Finset.mem_filter.mp hy).2
          exact le_antisymm
            (second x (List.mem_toFinset.mp (Finset.mem_filter.mp hx).1) same)
            (first y (List.mem_toFinset.mp (Finset.mem_filter.mp hy).1) same.symm))
      _ = k := Finset.card_fin k
  let selected := keys.filter (fun key => decide (Extreme color keys key))
  have covers : ∀ key, Extreme color keys key → key ∈ selected := by
    intro key extreme
    exact List.mem_filter.mpr ⟨extreme.1,decide_eq_true extreme⟩
  have selectedSet : selected.toFinset = low ∪ high := by
    ext key
    simp only [selected,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,
      Finset.mem_union,low,high,Finset.mem_filter,Extreme]
    tauto
  have nodup : keys.Nodup := ordered.imp (fun less => ne_of_lt less)
  have size : selected.length ≤ 2*k := by
    have unionBound := (Finset.card_union_le low high).trans (Nat.add_le_add lowBound highBound)
    rw [← selectedSet,List.toFinset_card_of_nodup (nodup.filter _)] at unionBound
    dsimp only [selected]
    omega
  have someExtreme : keys ≠ [] → ∃ key, Extreme color keys key := by
    intro nonempty
    cases keys with
    | nil => exact (nonempty rfl).elim
    | cons first rest =>
      refine ⟨first,List.mem_cons_self,Or.inl ?_⟩
      intro other member same
      rcases List.mem_cons.mp member with rfl | later
      · exact le_rfl
      · exact ((List.pairwise_cons.mp ordered).1 other later).le
  refine ⟨selected,List.filter_sublist,size,?_,covers⟩
  intro nonempty empty
  obtain ⟨key,extreme⟩ := someExtreme nonempty
  have present := covers key extreme
  simpa only [empty,List.not_mem_nil] using present

end DynamicOptimality.ColoredWalks
