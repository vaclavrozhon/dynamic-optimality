import Splay.Lazy.Model

/-! # Stable growing-block identifiers under concatenation and mapping -/

namespace MultiSplay.UniqueBlockPlacement

variable {α β : Type*}

theorem transfer {I J : Type*} {P : I → Prop} {Q : J → Prop}
    (unique : ∃! i, P i) (embed : I → J)
    (forward : ∀ i, P i → Q (embed i))
    (backward : ∀ j, Q j → ∃ i, P i ∧ embed i = j) : ∃! j, Q j := by
  obtain ⟨i, pi, only⟩ := unique
  refine ⟨embed i, forward i pi, ?_⟩
  intro j qj
  obtain ⟨other, po, eq⟩ := backward j qj
  simpa only [only other po] using eq.symm

theorem map (values : List α) (f : α → β) (P : α → Prop) (Q : β → Prop)
    (same : ∀ x, Q (f x) ↔ P x)
    (unique : ∃! i : Fin values.length, P (values.get i)) :
    ∃! i : Fin (values.map f).length, Q ((values.map f).get i) := by
  apply transfer unique (fun i => ⟨i.val, by simpa using i.isLt⟩)
  · intro i property
    simpa only [List.get_eq_getElem, List.getElem_map, same] using property
  · intro j property
    refine ⟨⟨j.val, by simpa using j.isLt⟩, ?_, rfl⟩
    simpa only [List.get_eq_getElem, List.getElem_map, same] using property

theorem append_left (left right : List α) (P : α → Prop)
    (unique : ∃! i : Fin left.length, P (left.get i))
    (outside : ∀ x ∈ right, ¬ P x) :
    ∃! i : Fin (left ++ right).length, P ((left ++ right).get i) := by
  apply transfer unique (fun i => ⟨i.val, by simp only [List.length_append]; omega⟩)
  · intro i property
    simpa only [List.get_eq_getElem, List.getElem_append_left i.isLt] using property
  · intro j property
    have inside : j.val < left.length := by
      by_contra notInside
      have hi : j.val - left.length < right.length := by have := j.isLt; simp only [List.length_append] at this; omega
      have eq : (left ++ right).get j = right.get ⟨j.val - left.length, hi⟩ := by
        simp only [List.get_eq_getElem, List.getElem_append_right (by omega : left.length ≤ j.val)]
      exact outside _ (List.get_mem right _) (eq ▸ property)
    refine ⟨⟨j.val, inside⟩, ?_, rfl⟩
    simpa only [List.get_eq_getElem, List.getElem_append_left inside] using property

theorem append_right (left right : List α) (P : α → Prop)
    (unique : ∃! i : Fin right.length, P (right.get i))
    (outside : ∀ x ∈ left, ¬ P x) :
    ∃! i : Fin (left ++ right).length, P ((left ++ right).get i) := by
  apply transfer unique (fun i => ⟨left.length + i.val, by simp only [List.length_append]; omega⟩)
  · intro i property
    simpa only [List.get_eq_getElem, List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] using property
  · intro j property
    have outsideLeft : left.length ≤ j.val := by
      by_contra notOutside
      have inside : j.val < left.length := by omega
      have eq : (left ++ right).get j = left.get ⟨j.val, inside⟩ := by
        simp only [List.get_eq_getElem, List.getElem_append_left inside]
      exact outside _ (List.get_mem left _) (eq ▸ property)
    have hi : j.val - left.length < right.length := by have := j.isLt; simp only [List.length_append] at this; omega
    refine ⟨⟨j.val - left.length, hi⟩, ?_, ?_⟩
    · simpa only [List.get_eq_getElem, List.getElem_append_right outsideLeft] using property
    · apply Fin.ext
      dsimp
      omega

end MultiSplay.UniqueBlockPlacement
