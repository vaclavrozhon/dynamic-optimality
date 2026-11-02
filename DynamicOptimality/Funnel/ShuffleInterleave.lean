import DynamicOptimality.Funnel.Interleave

/-! # The occurrence-embedding and inductive shuffle definitions agree -/

namespace DynamicOptimality.Funnel

variable {α : Type*} [LinearOrder α]

private def removeZero {m n : Nat} (embedding : Fin m ↪o Fin (n+1))
    (positive : ∀ i, embedding i ≠ 0) : Fin m ↪o Fin n :=
  OrderEmbedding.ofStrictMono (fun i => (embedding i).pred (positive i)) (by
    intro i j strict
    exact Fin.pred_lt_pred_iff.mpr (embedding.strictMono strict))

private def remove_left {X Y W : List α} {x : α} (shuffle : Shuffle (x :: X) Y (x :: W))
    (first : shuffle.left 0 = 0) : Shuffle X Y W := by
  let tailLeft : Fin X.length ↪o Fin (x :: W).length := (Fin.succOrderEmb _).trans shuffle.left
  have leftPositive : ∀ i, tailLeft i ≠ 0 := by
    intro i equal
    have less := shuffle.left.strictMono (Fin.succ_pos i)
    change shuffle.left 0 < tailLeft i at less
    rw [equal,first] at less
    exact lt_irrefl _ less
  have rightPositive : ∀ i, shuffle.right i ≠ 0 := by
    intro i equal
    exact (Finset.disjoint_left.mp shuffle.disjoint)
      (Finset.mem_image.mpr ⟨0,Finset.mem_univ _,first⟩)
      (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,equal⟩)
  let left := removeZero tailLeft leftPositive
  let right := removeZero shuffle.right rightPositive
  have leftEq : ∀ i, (left i).succ = shuffle.left i.succ := fun i => Fin.succ_pred (tailLeft i) (leftPositive i)
  have rightEq : ∀ i, (right i).succ = shuffle.right i := fun i => Fin.succ_pred (shuffle.right i) (rightPositive i)
  refine { left := left,right := right,left_keys := ?_,right_keys := ?_,disjoint := ?_,cover := ?_ }
  · intro i
    have keys := shuffle.left_keys i.succ
    rw [← leftEq] at keys
    simpa only [List.get_eq_getElem,Fin.val_succ,List.getElem_cons_succ] using keys
  · intro i
    have keys := shuffle.right_keys i
    rw [← rightEq] at keys
    simpa only [List.get_eq_getElem,Fin.val_succ,List.getElem_cons_succ] using keys
  · apply Finset.disjoint_left.mpr
    intro p fromLeft fromRight
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp fromLeft
    obtain ⟨j,_,equal⟩ := Finset.mem_image.mp fromRight
    have old : shuffle.right j = shuffle.left i.succ := by
      rw [← rightEq,← leftEq,equal]
    exact (Finset.disjoint_left.mp shuffle.disjoint)
      (Finset.mem_image.mpr ⟨i.succ,Finset.mem_univ _,old.symm⟩)
      (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
  · apply Finset.ext
    intro p
    simp only [Finset.mem_union,Finset.mem_univ,iff_true]
    have covered : p.succ ∈ Finset.univ.image shuffle.left ∪ Finset.univ.image shuffle.right := by
      rw [shuffle.cover]
      exact Finset.mem_univ _
    rcases Finset.mem_union.mp covered with fromLeft | fromRight
    · obtain ⟨i,_,equal⟩ := Finset.mem_image.mp fromLeft
      cases i using Fin.cases with
      | zero => exact (Fin.succ_ne_zero p (equal.symm.trans first)).elim
      | succ i =>
        exact Or.inl (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,
          Fin.succ_injective _ ((leftEq i).trans equal)⟩)
    · obtain ⟨i,_,equal⟩ := Finset.mem_image.mp fromRight
      exact Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,
        Fin.succ_injective _ ((rightEq i).trans equal)⟩)

private theorem from_left_head {X Y W : List α} {x : α} (shuffle : Shuffle X Y (x :: W))
    (head : (0 : Fin (x :: W).length) ∈ Finset.univ.image shuffle.left) :
    ∃ tail, X = x :: tail ∧ Nonempty (Shuffle tail Y W) := by
  obtain ⟨i,_,first⟩ := Finset.mem_image.mp head
  cases X with
  | nil => exact i.elim0
  | cons a X =>
    cases i using Fin.cases with
    | zero =>
      have same : x = a := by simpa only [first,List.get_eq_getElem,Fin.val_zero,List.getElem_cons_zero] using shuffle.left_keys 0
      subst a
      exact ⟨X,rfl,⟨remove_left shuffle first⟩⟩
    | succ i =>
      have less := shuffle.left.strictMono (Fin.succ_pos i)
      rw [first] at less
      exact (Fin.not_lt_zero _ less).elim

theorem Shuffle.interleave {X Y W : List α} (shuffle : Shuffle X Y W) : Interleave X Y W := by
  induction W generalizing X Y with
  | nil =>
    have length := shuffle.length
    have leftEmpty : X = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_nil] at length; omega)
    have rightEmpty : Y = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_nil] at length; omega)
    subst X
    subst Y
    exact .nil
  | cons x W ih =>
    have head : (0 : Fin (x :: W).length) ∈ Finset.univ.image shuffle.left ∪
        Finset.univ.image shuffle.right := by rw [shuffle.cover]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp head with fromLeft | fromRight
    · obtain ⟨tail,rfl,⟨rest⟩⟩ := from_left_head shuffle fromLeft
      exact .left x (ih rest)
    · obtain ⟨tail,rfl,⟨rest⟩⟩ := from_left_head shuffle.symm fromRight
      exact .right x (ih rest.symm)

theorem interleave_iff_shuffle {X Y W : List α} : Interleave X Y W ↔ Nonempty (Shuffle X Y W) :=
  ⟨Interleave.exists_shuffle,fun ⟨shuffle⟩ => shuffle.interleave⟩

end DynamicOptimality.Funnel
