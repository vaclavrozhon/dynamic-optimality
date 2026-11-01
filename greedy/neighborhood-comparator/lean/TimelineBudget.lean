import AdministrationTimeline
import PhaseTimeline

namespace GreedyForest.Timeline

variable {Record Block : Type*}

noncomputable def paidAppendSplit (first second : List (Update Record Block))
    (p : Paid (first++second)) : Sum (Paid first) (Paid second) := by
  classical
  by_cases hfirst : p.val.val < first.length
  · refine Sum.inl ⟨⟨p.val.val,hfirst⟩,?_⟩
    have hp := p.property
    simpa only [List.get_eq_getElem,List.getElem_append_left hfirst] using hp
  · have hsecond : p.val.val-first.length < second.length := by
      have h := p.val.isLt
      simp only [List.length_append] at h
      omega
    refine Sum.inr ⟨⟨p.val.val-first.length,hsecond⟩,?_⟩
    have hp := p.property
    simpa only [List.get_eq_getElem,List.getElem_append_right (Nat.le_of_not_gt hfirst)] using hp

theorem paidAppendSplit_injective (first second : List (Update Record Block)) :
    Function.Injective (paidAppendSplit first second) := by
  classical
  intro a b hab
  apply Subtype.ext
  apply Fin.ext
  by_cases ha : a.val.val < first.length <;> by_cases hb : b.val.val < first.length
  · simp only [paidAppendSplit,dif_pos ha,dif_pos hb,Sum.inl.injEq] at hab
    exact congrArg (fun p => p.val.val) hab
  · simp only [paidAppendSplit,dif_pos ha,dif_neg hb] at hab
    contradiction
  · simp only [paidAppendSplit,dif_neg ha,dif_pos hb] at hab
    contradiction
  · simp only [paidAppendSplit,dif_neg ha,dif_neg hb,Sum.inr.injEq] at hab
    have h := congrArg (fun p => p.val.val) hab
    dsimp only at h
    omega

/-- Concatenation counts only actual paid occurrences. Empty identifier
ranges and phase links contribute no extra slots. -/
theorem paid_append_card (first second : List (Update Record Block)) :
    Nat.card (Paid (first++second)) ≤ Nat.card (Paid first)+Nat.card (Paid second) := by
  classical
  letI : Fintype (Paid first) := by unfold Paid; infer_instance
  letI : Fintype (Paid second) := by unfold Paid; infer_instance
  have h := Nat.card_le_card_of_injective (paidAppendSplit first second)
    (paidAppendSplit_injective first second)
  simpa [Nat.card_sum] using h

theorem phase_paid_card_zero (rank block : ℕ → ℕ) (initial : ℕ → ℤ)
    (events : List (ℕ × ℕ)) :
    Nat.card (Paid (events.map (GreedyForest.Phase.timelineUpdate rank block initial))) = 0 := by
  classical
  letI : IsEmpty (Paid (events.map (GreedyForest.Phase.timelineUpdate rank block initial))) :=
    ⟨fun p => by
      have h := p.property
      simp [List.get_eq_getElem,GreedyForest.Phase.timelineUpdate] at h⟩
  exact Nat.card_of_isEmpty

end GreedyForest.Timeline

#print axioms GreedyForest.Timeline.paid_append_card
#print axioms GreedyForest.Timeline.phase_paid_card_zero
