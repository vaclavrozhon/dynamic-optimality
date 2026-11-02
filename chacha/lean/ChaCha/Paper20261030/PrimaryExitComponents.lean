import ChaCha.Paper20261030.PrimaryComponentOwners
import ChaCha.Paper20261030.PerfectPrimaryPorts

/-!
# Global starts of the components inside an actual primary exit

An exit at depth `d` is rooted at depth `d+1`. Every preferred component
inside it therefore has its local start shifted by exactly `d+1`.
Distinct original keys exclude the active endpoint from the exit subtree.
-/

namespace ChaCha.Paper20261030.PrimaryWings

open PreferredProjection

variable {α : Type*} [DecidableEq α]

theorem port_componentStart {primary : PrefRouter α} {exit : Exit α} {depth : Nat}
    (distinct : primary.leaves.Nodup) (present : portAt 0 (exits primary) depth = some exit)
    {key : α} (member : key ∈ exit.subtree.leaves) :
    primary.componentStart key = depth+1+exit.subtree.componentStart key := by
  simp only [portAt,Nat.zero_le,if_true,Nat.sub_zero] at present
  induction primary generalizing depth with
  | leaf value => simp [exits] at present
  | fork bit left right ihl ihr =>
    obtain ⟨dl,dr,disjoint⟩ := List.nodup_append.mp distinct
    cases bit <;> cases depth
    case false.zero =>
      simp only [exits,List.getElem?_cons_zero,Option.some.injEq] at present
      subst exit
      have outside : key ∉ left.leaves := fun h => disjoint _ h _ member rfl
      have other : key ≠ left.terminal := fun h => outside (h ▸ left.terminal_mem)
      simp [PrefRouter.componentStart,PrefRouter.terminal,other,outside,Nat.add_comm]
    case true.zero =>
      simp only [exits,List.getElem?_cons_zero,Option.some.injEq] at present
      subst exit
      have other : key ≠ right.terminal := fun h => disjoint _ member _ right.terminal_mem h
      simp [PrefRouter.componentStart,PrefRouter.terminal,other,member,Nat.add_comm]
    case false.succ depth =>
      simp only [exits,List.getElem?_cons_succ] at present
      have inside : key ∈ left.leaves := exit_leaves_subset (List.mem_of_getElem? present) key member
      have start := ihl dl present
      have other : key ≠ left.terminal := by
        intro same
        rw [same,PrefRouter.componentStart_terminal] at start
        omega
      simp only [PrefRouter.componentStart,PrefRouter.terminal,Bool.false_eq_true,if_false,
        if_neg other,if_pos inside,start]
      omega
    case true.succ depth =>
      simp only [exits,List.getElem?_cons_succ] at present
      have inside : key ∈ right.leaves := exit_leaves_subset (List.mem_of_getElem? present) key member
      have outside : key ∉ left.leaves := fun h => disjoint _ h _ inside rfl
      have start := ihr dr present
      have other : key ≠ right.terminal := by
        intro same
        rw [same,PrefRouter.componentStart_terminal] at start
        omega
      simp only [PrefRouter.componentStart,PrefRouter.terminal,if_true,
        if_neg other,if_neg outside,start]
      omega

theorem port_endpoint_start {primary : PrefRouter α} {exit : Exit α} {depth : Nat}
    (distinct : primary.leaves.Nodup) (present : portAt 0 (exits primary) depth = some exit) :
    primary.componentStart exit.subtree.terminal = depth+1 := by
  simpa only [PrefRouter.componentStart_terminal,Nat.add_zero] using
    port_componentStart distinct present exit.subtree.terminal_mem

theorem exit_leaves_nodup {primary : PrefRouter α} {exit : Exit α}
    (distinct : primary.leaves.Nodup) (member : exit ∈ exits primary) : exit.subtree.leaves.Nodup := by
  induction primary with
  | leaf key => simp [exits] at member
  | fork bit left right ihl ihr =>
    obtain ⟨dl,dr,_⟩ := List.nodup_append.mp distinct
    cases bit <;> simp only [exits,List.mem_cons] at member
    · rcases member with rfl | member
      · exact dr
      · exact ihl dl member
    · rcases member with rfl | member
      · exact dl
      · exact ihr dr member

theorem perfect_port {height depth : Nat} {primary : PrefRouter α} {exit : Exit α}
    (perfect : primary.Perfect height) (present : portAt 0 (exits primary) depth = some exit) :
    depth < height ∧ exit.subtree.Perfect (height-(depth+1)) := by
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
        first | exact ⟨Nat.zero_lt_succ _,perfect.2⟩ | exact ⟨Nat.zero_lt_succ _,perfect.1⟩
      | succ depth =>
        simp only [exits,List.getElem?_cons_succ] at present
        first
        | exact ⟨Nat.succ_lt_succ (ih perfect.1 present).1,by simpa using (ih perfect.1 present).2⟩
        | exact ⟨Nat.succ_lt_succ (ih perfect.2 present).1,by simpa using (ih perfect.2 present).2⟩

/-- Actual component roots, obtained by repeatedly taking a nonpreferred
exit of the current preferred path. The index is the global root depth. -/
inductive ComponentRoot (whole : PrefRouter α) : Nat → PrefRouter α → Prop
  | root : ComponentRoot whole 0 whole
  | child {start depth : Nat} {parent : PrefRouter α} {exit : Exit α}
      (rooted : ComponentRoot whole start parent)
      (present : portAt 0 (exits parent) depth = some exit) :
      ComponentRoot whole (start+(depth+1)) exit.subtree

theorem ComponentRoot.leaves_subset {whole subtree : PrefRouter α} {start : Nat}
    (rooted : ComponentRoot whole start subtree) :
    ∀ key ∈ subtree.leaves, key ∈ whole.leaves := by
  induction rooted with
  | root => exact fun _ h => h
  | child rooted present ih =>
    simp only [portAt,Nat.zero_le,if_true,Nat.sub_zero] at present
    exact fun key h => ih key (exit_leaves_subset (List.mem_of_getElem? present) key h)

theorem ComponentRoot.nodup {whole subtree : PrefRouter α} {start : Nat}
    (rooted : ComponentRoot whole start subtree) (distinct : whole.leaves.Nodup) :
    subtree.leaves.Nodup := by
  induction rooted with
  | root => exact distinct
  | child rooted present ih =>
    simp only [portAt,Nat.zero_le,if_true,Nat.sub_zero] at present
    exact exit_leaves_nodup ih (List.mem_of_getElem? present)

theorem ComponentRoot.componentStart {whole subtree : PrefRouter α} {start : Nat}
    (rooted : ComponentRoot whole start subtree) (distinct : whole.leaves.Nodup) :
    ∀ key ∈ subtree.leaves, whole.componentStart key = start+subtree.componentStart key := by
  induction rooted with
  | root => exact fun _ _ => (Nat.zero_add _).symm
  | child rooted present ih =>
    intro key member
    have inParent := exit_leaves_subset
      (List.mem_of_getElem? (by simpa [portAt] using present)) key member
    rw [ih key inParent,port_componentStart (rooted.nodup distinct) present member]
    omega

theorem ComponentRoot.endpoint_start {whole subtree : PrefRouter α} {start : Nat}
    (rooted : ComponentRoot whole start subtree) (distinct : whole.leaves.Nodup) :
    whole.componentStart subtree.terminal = start := by
  simpa only [PrefRouter.componentStart_terminal,Nat.add_zero] using
    rooted.componentStart distinct subtree.terminal subtree.terminal_mem

theorem ComponentRoot.perfect {whole subtree : PrefRouter α} {start height : Nat}
    (rooted : ComponentRoot whole start subtree) (perfect : whole.Perfect height) :
    start ≤ height ∧ subtree.Perfect (height-start) := by
  induction rooted with
  | root => exact ⟨Nat.zero_le _,perfect⟩
  | child rooted present ih =>
    obtain ⟨bound,childPerfect⟩ := perfect_port ih.2 present
    exact ⟨by omega,by simpa only [Nat.sub_add_eq] using childPerfect⟩

end ChaCha.Paper20261030.PrimaryWings
