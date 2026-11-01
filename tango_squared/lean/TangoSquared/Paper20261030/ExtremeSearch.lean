import TangoSquared.Paper20261030.ComponentBoundary
import TangoSquared.Paper20261030.ComponentMarkers

/-!
# Extreme records of an ordered auxiliary

The endpoint search follows one fixed child direction. Its result is
the first or last record of the exact inorder word. Exposing that record
therefore leaves an empty core on the corresponding side, as required
by the physical meld operation.
-/

namespace TangoSquared.Paper20261030.Auxiliary.Metadata

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl

variable {κ : Type*} {β : κ → Type*}

def extreme (right : Bool) : Impl κ β → Option (Sigma β)
  | .leaf => none
  | .inner _ key value l r =>
      if right then some ((extreme right r).getD ⟨key,value⟩)
      else some ((extreme right l).getD ⟨key,value⟩)

theorem extreme_last (t : Impl κ β) : extreme true t = t.toListModel.getLast? := by
  induction t with
  | leaf => rfl
  | inner cached key value l r ihl ihr =>
    simp only [extreme,if_true,ihr,toListModel_inner,List.getLast?_append,List.getLast?_cons]
    cases r.toListModel.getLast? <;> rfl

theorem extreme_first (t : Impl κ β) : extreme false t = t.toListModel.head? := by
  induction t with
  | leaf => rfl
  | inner cached key value l r ihl ihr =>
    simp only [extreme,Bool.false_eq_true,if_false,ihl,toListModel_inner,List.head?_append,List.head?_cons]
    cases l.toListModel.head? <;> rfl

theorem extreme_none (right : Bool) (t : Impl κ β) : extreme right t = none ↔ t = .leaf := by
  cases t <;> cases right <;> simp [extreme]

theorem extreme_mem (right : Bool) (t : Impl κ β) {e : Sigma β}
    (he : extreme right t = some e) : e ∈ t.toListModel := by
  cases right
  · rw [extreme_first] at he
    exact List.mem_of_head? he
  · rw [extreme_last] at he
    exact List.mem_of_getLast? he

theorem extreme_found [Ord κ] [TransOrd κ] [LawfulEqOrd κ] [BEq κ] [LawfulBEq κ]
    (right : Bool) (t : Impl κ β)
    (ho : t.Ordered) {e : Sigma β} (he : extreme right t = some e) : searchResult e.1 t = true := by
  rw [searchResult_eq_contains,contains_eq_containsKey ho]
  exact Std.Internal.List.containsKey_of_mem (extreme_mem right t he)

theorem maximum_key {γ : Nat → Type*} (t : Impl Nat γ) (ho : t.Ordered) {e : Sigma γ}
    (he : extreme true t = some e) {other : Sigma γ} (hm : other ∈ t.toListModel) : other.1 ≤ e.1 := by
  rw [extreme_last] at he
  obtain ⟨before,hword⟩ := List.getLast?_eq_some_iff.mp he
  change t.toListModel.Pairwise _ at ho
  rw [hword] at ho hm
  rcases List.mem_append.mp hm with hm | hm
  · exact (Nat.compare_eq_lt.mp ((List.pairwise_append.mp ho).2.2 other hm e (by simp))).le
  · cases List.mem_singleton.mp hm
    exact le_rfl

theorem minimum_key {γ : Nat → Type*} (t : Impl Nat γ) (ho : t.Ordered) {e : Sigma γ}
    (he : extreme false t = some e) {other : Sigma γ} (hm : other ∈ t.toListModel) : e.1 ≤ other.1 := by
  rw [extreme_first] at he
  obtain ⟨after,hword⟩ := List.head?_eq_some_iff.mp he
  change t.toListModel.Pairwise _ at ho
  rw [hword] at ho hm
  rcases List.mem_cons.mp hm with heq | hm
  · cases heq
    exact le_rfl
  · exact (Nat.compare_eq_lt.mp ((List.pairwise_cons.mp ho).1 other hm)).le

theorem maximum_split_empty {γ : Nat → Type*} (t : Impl Nat γ) (ht : t.Balanced)
    (ho : t.Ordered) {e : Sigma γ} (he : extreme true t = some e) :
    (splitAt e.1 t ht (extreme_found true t ho he)).right = .leaf := by
  let found := extreme_found true t ho he
  have hempty : (splitAt e.1 t ht found).right.toListModel = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro other hm
    have hlt := Auxiliary.split_right_key e.1 t ht found ho hm
    have hle := maximum_key t ho he (Auxiliary.split_right_mem e.1 t ht found hm)
    omega
  cases hs : (splitAt e.1 t ht found).right with
  | leaf => rfl
  | inner cached key value l r => simp [hs,toListModel] at hempty

theorem minimum_split_empty {γ : Nat → Type*} (t : Impl Nat γ) (ht : t.Balanced)
    (ho : t.Ordered) {e : Sigma γ} (he : extreme false t = some e) :
    (splitAt e.1 t ht (extreme_found false t ho he)).left = .leaf := by
  let found := extreme_found false t ho he
  have hempty : (splitAt e.1 t ht found).left.toListModel = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro other hm
    have hlt := Auxiliary.split_left_key e.1 t ht found ho hm
    have hmem : other ∈ t.toListModel := by
      rw [← Auxiliary.splitAt_toList e.1 t ht found]
      simp only [Auxiliary.SplitResult.impl,bin,toListModel_inner,List.mem_append,List.mem_cons]
      exact Or.inl hm
    have hle := minimum_key t ho he hmem
    omega
  cases hs : (splitAt e.1 t ht found).left with
  | leaf => rfl
  | inner cached key value l r => simp [hs,toListModel] at hempty

end TangoSquared.Paper20261030.Auxiliary.Metadata
