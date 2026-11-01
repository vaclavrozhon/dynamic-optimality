import TangoSquared.CyclicGapAccounting
import TangoSquared.GapChronology

/-! Indexed outgoing gaps preserve each selected source occurrence. -/
namespace TangoSquared.IndexedGaps

open CyclicRuns GapChunks CyclicGapAccounting GapChronology

variable {α C : Type*} [LinearOrder α] [LinearOrder C]

private theorem gapsFrom_getElem (coarse : α → C) (cell : C)
    (previous : Chunk (Block α)) (cs : List (Chunk (Block α)))
    (i : Nat) (hi : i < cs.length) :
    (gapsFrom coarse cell previous cs)[i]'(by simpa using hi) =
      outgoingGap coarse cell ((previous :: cs)[i]'(by simp only [List.length_cons]; omega)) cs[i].source := by
  induction cs generalizing previous i with
  | nil => simp at hi
  | cons c cs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [gapsFrom, List.getElem_cons_succ] using ih c i (by simpa using hi)

private theorem getLastD_eq_lastIndex {β : Type*} (b : β) (bs : List β) :
    (b :: bs).getLastD b = (b :: bs)[bs.length] := by
  induction bs generalizing b with
  | nil => rfl
  | cons c cs ih =>
    simpa only [List.getLastD_cons, List.length_cons, List.getElem_cons_succ] using ih c

/-- The successor is taken in the doubled actual chunk list, so the final gap
wraps to the first source without identifying source occurrences. -/
theorem outgoingGaps_getElem (coarse : α → C) (cell : C)
    (cs : List (Chunk (Block α))) (i : Fin cs.length) :
    (outgoingGaps coarse cell cs)[i.val]'(by simp) =
      outgoingGap coarse cell cs[i] ((cs ++ cs)[nextIndex cs i]).source := by
  cases cs with
  | nil => exact Fin.elim0 i
  | cons c cs =>
    by_cases hi : i.val < cs.length
    · simp only [outgoingGaps]
      rw [List.getElem_append_left (by simpa using hi),
        gapsFrom_getElem coarse cell c cs i.val hi]
      have hn : i.val + 1 < (c :: cs).length := by simp; omega
      simp only [Fin.getElem_fin, nextIndex, List.getElem_append_left hn, List.getElem_cons_succ]
    · have he : i.val = cs.length := by have := i.isLt; simp only [List.length_cons] at this; omega
      have hleft : ¬ i.val < (gapsFrom coarse cell c cs).length := by simpa using hi
      simp only [outgoingGaps]
      rw [List.getElem_append_right (Nat.le_of_not_gt hleft)]
      simp only [gapsFrom_length, he, Nat.sub_self, List.getElem_cons_zero]
      rw [getLastD_eq_lastIndex]
      simp only [Fin.getElem_fin, nextIndex, he]
      rw [List.getElem_append_right (show (c :: cs).length ≤ cs.length + 1 by simp)]
      simp only [List.length_cons, Nat.sub_self, List.getElem_cons_zero]


/-- The list of gaps is literally the finite enumeration used for payment records. -/
theorem outgoingGaps_eq_ofFn (coarse : α → C) (cell : C)
    (cs : List (Chunk (Block α))) :
    outgoingGaps coarse cell cs = List.ofFn (fun i : Fin cs.length =>
      outgoingGap coarse cell cs[i] ((cs ++ cs)[nextIndex cs i]).source) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simpa only [List.getElem_ofFn, Fin.getElem_fin] using
      outgoingGaps_getElem coarse cell cs ⟨i, by simpa using hi⟩

end TangoSquared.IndexedGaps
