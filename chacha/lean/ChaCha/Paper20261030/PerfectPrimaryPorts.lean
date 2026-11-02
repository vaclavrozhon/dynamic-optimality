import ChaCha.Paper20261030.CanonicalPhysicalHeaders

/-! Heights of actual exit subtrees in the perfect primary reference. -/

namespace ChaCha.Paper20261030.PrimaryWings

open PreferredProjection

variable {α : Type*} [DecidableEq α]

theorem perfect_port_length {height depth : Nat} {primary : PrefRouter α} {exit : Exit α}
    (perfect : primary.Perfect height) (present : portAt 0 (exits primary) depth = some exit) :
    (exits exit.subtree).length = height-(depth+1) := by
  simp only [portAt,Nat.zero_le,if_true,Nat.sub_zero] at present
  induction height generalizing primary depth with
  | zero =>
    cases primary with
    | leaf key => simp [exits] at present
    | fork => exact False.elim perfect
  | succ height ih =>
    cases primary with
    | leaf key => exact False.elim perfect
    | fork bit left right =>
      cases bit <;> cases depth with
      | zero =>
        simp only [exits,List.getElem?_cons_zero,Option.some.injEq] at present
        subst exit
        first
        | simpa using perfect_exits_length perfect.2
        | simpa using perfect_exits_length perfect.1
      | succ depth =>
        simp only [exits,List.getElem?_cons_succ] at present
        first
        | simpa only [Nat.succ_sub_succ_eq_sub] using ih perfect.1 present
        | simpa only [Nat.succ_sub_succ_eq_sub] using ih perfect.2 present

end ChaCha.Paper20261030.PrimaryWings
