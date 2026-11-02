import ChaCha.Paper20261030.PrimaryComponentStarts

/-!
# Genuine records of dormant paths have different primary owners

At any depth at least the dormant path's start, its endpoint and the
active endpoint have different ancestor addresses. This separates the
persistent memory cells touched by a source access from the genuine
memory of every other stored component.
-/

namespace ChaCha.PreferredProjection.PrefRouter

variable {α : Type*} [DecidableEq α]

theorem componentStart_zero_iff {primary : PrefRouter α} {key : α} (member : key ∈ primary.leaves) :
    primary.componentStart key = 0 ↔ key = primary.terminal := by
  cases primary with
  | leaf value => simpa [componentStart,terminal,leaves] using member
  | fork bit left right =>
    by_cases endpoint : key = (fork bit left right).terminal
    · simp [componentStart,endpoint]
    · simp only [componentStart,if_neg endpoint]
      split_ifs <;> simp [endpoint]

theorem componentStart_le_height {primary : PrefRouter α} {height : Nat}
    (perfect : primary.Perfect height) (key : α) : primary.componentStart key ≤ height := by
  induction height generalizing primary with
  | zero => cases primary <;> simp_all [Perfect,componentStart]
  | succ height ih =>
    cases primary with
    | leaf value => exact False.elim perfect
    | fork bit left right =>
      have hl := ih perfect.1
      have hr := ih perfect.2
      simp only [componentStart]
      split_ifs <;> omega

theorem componentStart_owner_ne {primary : PrefRouter α} {key : α} (distinct : primary.leaves.Nodup)
    (member : key ∈ primary.leaves) (other : key ≠ primary.terminal) {depth : Nat}
    (below : primary.componentStart key ≤ depth) :
    (primary.searchPath key).take depth ≠ (primary.searchPath primary.terminal).take depth := by
  induction primary generalizing depth with
  | leaf value => simp only [leaves,List.mem_singleton] at member; exact False.elim (other member)
  | fork bit left right ihl ihr =>
    obtain ⟨dl,dr,disjoint⟩ := List.nodup_append.mp distinct
    have positive : 0 < (fork bit left right).componentStart key :=
      Nat.pos_of_ne_zero (fun zero => other ((componentStart_zero_iff member).mp zero))
    cases depth with
    | zero => omega
    | succ depth =>
      by_cases inLeft : key ∈ left.leaves
      · cases bit
        · have childOther : key ≠ left.terminal := other
          have childBelow : left.componentStart key ≤ depth := by
            simpa only [componentStart,if_neg other,if_pos inLeft,Nat.add_le_add_iff_right] using below
          simpa only [terminal,Bool.false_eq_true,if_false,searchPath,if_pos inLeft,
            if_pos left.terminal_mem,List.take_succ_cons,ne_eq,List.cons.injEq,true_and] using
              ihl dl inLeft childOther childBelow
        · have outside : right.terminal ∉ left.leaves := fun h => disjoint _ h _ right.terminal_mem rfl
          simp [terminal,searchPath,inLeft,outside,right.terminal_mem,List.take_succ_cons]
      · have inRight : key ∈ right.leaves := (List.mem_append.mp member).resolve_left inLeft
        cases bit
        · simp [terminal,searchPath,inLeft,inRight,left.terminal_mem,List.take_succ_cons]
        · have childOther : key ≠ right.terminal := other
          have childBelow : right.componentStart key ≤ depth := by
            simpa only [componentStart,if_neg other,if_neg inLeft,Nat.add_le_add_iff_right] using below
          have outside : right.terminal ∉ left.leaves := fun h => disjoint _ h _ right.terminal_mem rfl
          simpa only [terminal,if_true,searchPath,if_neg inLeft,if_pos inRight,if_neg outside,
            if_pos right.terminal_mem,List.take_succ_cons,ne_eq,List.cons.injEq,true_and] using
              ihr dr inRight childOther childBelow

end ChaCha.PreferredProjection.PrefRouter
