import ChaCha.Paper20261030.PrimaryExitComponents
import ChaCha.Paper20261030.PackedPortAgreement

set_option autoImplicit false

/-! The two endpoints involved in a head exchange are the only components
whose rooted primary subtrees change. Every other component retains its
exact subtree and global starting depth. The proof follows the common
prefix and the two tails of the actual primary exit decomposition. -/

namespace ChaCha.Paper20261030.PrimaryWings

open PreferredProjection

variable {α : Type*} [DecidableEq α]

theorem ComponentRoot.trans {whole parent subtree : PrefRouter α} {start inner : Nat}
    (outside : ComponentRoot whole start parent) (inside : ComponentRoot parent inner subtree) :
    ComponentRoot whole (start+inner) subtree := by
  induction inside with
  | root => simpa only [Nat.add_zero] using outside
  | child rooted present ih =>
    simpa only [Nat.add_assoc] using ComponentRoot.child ih present

theorem ComponentRoot.first_exit {whole subtree : PrefRouter α} {start : Nat}
    (rooted : ComponentRoot whole start subtree) :
    (start = 0 ∧ subtree = whole) ∨
      ∃ depth exit inner, portAt 0 (exits whole) depth = some exit ∧
        ComponentRoot exit.subtree inner subtree ∧ start = depth+1+inner := by
  induction rooted with
  | root => exact Or.inl ⟨rfl,rfl⟩
  | @child start depth parent exit rooted present ih =>
    rcases ih with ⟨rfl,rfl⟩ | ⟨first,branch,inner,found,inside,offset⟩
    · exact Or.inr ⟨depth,exit,0,present,.root,by omega⟩
    · exact Or.inr ⟨first,branch,inner+(depth+1),found,.child inside present,by omega⟩

theorem portAt_shift (start depth : Nat) (ports : List (Exit α)) :
    portAt start ports (start+depth) = portAt 0 ports depth := by
  simp only [portAt,Nat.le_add_right,if_true,Nat.add_sub_cancel_left,Nat.zero_le,Nat.sub_zero]

theorem ComponentRoot.reassociate {before after old incoming subtree : PrefRouter α}
    (common : List (Exit α)) (side : Bool)
    (beforeWord : exits before = common ++ ⟨side,incoming⟩ :: exits old)
    (afterWord : exits after = common ++ ⟨!side,old⟩ :: exits incoming)
    {start : Nat} (rooted : ComponentRoot before start subtree)
    (notRoot : subtree.terminal ≠ before.terminal) (notIncoming : subtree.terminal ≠ incoming.terminal) :
    ComponentRoot after start subtree := by
  rcases rooted.first_exit with ⟨rfl,rfl⟩ | ⟨depth,exit,inner,found,inside,offset⟩
  · exact False.elim (notRoot rfl)
  · by_cases isPrefix : depth < common.length
    · have afterFound : portAt 0 (exits after) depth = some exit := by
        rw [beforeWord,portAt_prefix common _ depth isPrefix] at found
        rw [afterWord,portAt_prefix common _ depth isPrefix]
        exact found
      have child : ComponentRoot after (depth+1) exit.subtree := by
        simpa only [Nat.zero_add] using ComponentRoot.child (.root : ComponentRoot after 0 after) afterFound
      rw [offset]
      exact child.trans inside
    · by_cases boundary : depth = common.length
      · subst depth
        rw [beforeWord,PrimaryWings.portAt_boundary] at found
        cases Option.some.inj found
        rcases inside.first_exit with ⟨rfl,equal⟩ | ⟨localDepth,branch,rest,localFound,within,localOffset⟩
        · exact False.elim (notIncoming (congrArg PrefRouter.terminal equal))
        · have afterFound : portAt 0 (exits after) (common.length+1+localDepth) = some branch := by
            rw [afterWord,portAt_tail common _ _ _ (by omega)]
            rw [portAt_shift]
            exact localFound
          have child : ComponentRoot after (common.length+1+localDepth+1) branch.subtree := by
            simpa only [Nat.zero_add] using
              ComponentRoot.child (.root : ComponentRoot after 0 after) afterFound
          have combined := child.trans within
          convert combined using 1 <;> omega
      · have afterOld : ComponentRoot after (common.length+1) old := by
          have boundary : portAt 0 (exits after) common.length = some ⟨!side,old⟩ := by
            rw [afterWord,PrimaryWings.portAt_boundary]
          simpa only [Nat.zero_add] using
            ComponentRoot.child (.root : ComponentRoot after 0 after) boundary
        have tailFound : portAt 0 (exits old) (depth-(common.length+1)) = some exit := by
          rw [beforeWord,portAt_tail common _ _ _ (by omega)] at found
          simpa only [portAt,show common.length+1 ≤ depth by omega,if_true,Nat.zero_le,Nat.sub_zero] using found
        have oldChild : ComponentRoot old (depth-(common.length+1)+1) exit.subtree := by
          simpa only [Nat.zero_add] using
            ComponentRoot.child (.root : ComponentRoot old 0 old) tailFound
        have combined := afterOld.trans (oldChild.trans inside)
        convert combined using 1 <;> omega

theorem ComponentRoot.head_other {x : α} {d start : Nat} {before after subtree : PrefRouter α}
    (step : PrefRouter.HeadStep x d before after) (rooted : ComponentRoot before start subtree)
    (oldOther : subtree.terminal ≠ before.terminal) (newOther : subtree.terminal ≠ after.terminal) :
    ComponentRoot after start subtree := by
  obtain ⟨common,old,incoming,side,_,_,newEnd,beforeWord,afterWord⟩ := head_exit_decomposition step
  exact rooted.reassociate common side beforeWord afterWord oldOther (by rwa [← newEnd])

theorem ComponentRoot.head_other_iff {x : α} {d start : Nat} {before after subtree : PrefRouter α}
    (step : PrefRouter.HeadStep x d before after)
    (oldOther : subtree.terminal ≠ before.terminal) (newOther : subtree.terminal ≠ after.terminal) :
    ComponentRoot after start subtree ↔ ComponentRoot before start subtree := by
  constructor
  · intro rooted
    obtain ⟨common,old,incoming,side,_,oldEnd,_,beforeWord,afterWord⟩ := head_exit_decomposition step
    have backWord : exits before = common ++ ⟨!(!side),incoming⟩ :: exits old := by simpa using beforeWord
    exact rooted.reassociate common (!side) afterWord backWord newOther (by rwa [← oldEnd])
  · exact fun rooted => rooted.head_other step oldOther newOther

theorem ComponentRoot.eq_root_of_start_zero {whole subtree : PrefRouter α}
    (rooted : ComponentRoot whole 0 subtree) : subtree = whole := by
  rcases rooted.first_exit with ⟨_,same⟩ | ⟨depth,exit,inner,_,_,offset⟩
  · exact same
  · omega

theorem ComponentRoot.eq_root_of_terminal {whole subtree : PrefRouter α} {start : Nat}
    (rooted : ComponentRoot whole start subtree) (distinct : whole.leaves.Nodup)
    (endpoint : subtree.terminal = whole.terminal) : start = 0 ∧ subtree = whole := by
  have atStart := rooted.endpoint_start distinct
  rw [endpoint,PrefRouter.componentStart_terminal] at atStart
  cases atStart
  exact ⟨rfl,rooted.eq_root_of_start_zero⟩

theorem ComponentRoot.excludes_active {whole subtree : PrefRouter α} {start : Nat}
    (rooted : ComponentRoot whole start subtree) (distinct : whole.leaves.Nodup)
    (other : subtree.terminal ≠ whole.terminal) : whole.terminal ∉ subtree.leaves := by
  intro member
  have starts := rooted.componentStart distinct whole.terminal member
  rw [PrefRouter.componentStart_terminal] at starts
  have zero : start = 0 := by omega
  subst start
  exact other (congrArg PrefRouter.terminal rooted.eq_root_of_start_zero)

theorem ComponentRoot.leaves_length_le {whole subtree : PrefRouter α} {start : Nat}
    (rooted : ComponentRoot whole start subtree) : subtree.leaves.length ≤ whole.leaves.length := by
  induction rooted with
  | root => exact le_rfl
  | child rooted present ih =>
    exact (exit_smaller (List.mem_of_getElem? (by simpa [portAt] using present))).le.trans ih

theorem ComponentRoot.proper_leaves_lt {whole subtree : PrefRouter α} {start : Nat}
    (rooted : ComponentRoot whole start subtree) (other : subtree.terminal ≠ whole.terminal) :
    subtree.leaves.length < whole.leaves.length := by
  rcases rooted.first_exit with ⟨_,rfl⟩ | ⟨depth,exit,inner,present,inside,_⟩
  · exact False.elim (other rfl)
  · exact inside.leaves_length_le.trans_lt
      (exit_smaller (List.mem_of_getElem? (by simpa [portAt] using present)))

theorem exits_shared_key_unique {whole : PrefRouter α} (distinct : whole.leaves.Nodup)
    {first second : Exit α} (firstMem : first ∈ exits whole) (secondMem : second ∈ exits whole)
    {key : α} (inFirst : key ∈ first.subtree.leaves) (inSecond : key ∈ second.subtree.leaves) :
    first = second := by
  induction whole with
  | leaf value => simp [exits] at firstMem
  | fork bit left right ihl ihr =>
    obtain ⟨leftUnique,rightUnique,separate⟩ := List.nodup_append.mp distinct
    cases bit
    · simp only [exits,List.mem_cons] at firstMem secondMem
      rcases firstMem with rfl | firstMem
      · rcases secondMem with rfl | secondMem
        · rfl
        · exact False.elim (separate _ (exit_leaves_subset secondMem key inSecond) _ inFirst rfl)
      · rcases secondMem with rfl | secondMem
        · exact False.elim (separate _ (exit_leaves_subset firstMem key inFirst) _ inSecond rfl)
        · exact ihl leftUnique firstMem secondMem
    · simp only [exits,List.mem_cons] at firstMem secondMem
      rcases firstMem with rfl | firstMem
      · rcases secondMem with rfl | secondMem
        · rfl
        · exact False.elim (separate _ inFirst _ (exit_leaves_subset secondMem key inSecond) rfl)
      · rcases secondMem with rfl | secondMem
        · exact False.elim (separate _ inSecond _ (exit_leaves_subset firstMem key inFirst) rfl)
        · exact ihr rightUnique firstMem secondMem

/-- A finite endpoint identifies exactly one component and starting depth. -/
theorem ComponentRoot.endpoint_unique {whole first second : PrefRouter α} {start finish : Nat}
    (left : ComponentRoot whole start first) (right : ComponentRoot whole finish second)
    (distinct : whole.leaves.Nodup) (same : first.terminal = second.terminal) :
    start = finish ∧ first = second := by
  have starts : start = finish := by
    rw [← left.endpoint_start distinct,← right.endpoint_start distinct,same]
  refine ⟨starts,?_⟩
  rcases left.first_exit with ⟨_,rfl⟩ | ⟨firstDepth,firstExit,firstInner,firstFound,firstRoot,_⟩
  · exact (right.eq_root_of_terminal distinct same.symm).2.symm
  · rcases right.first_exit with ⟨_,rfl⟩ | ⟨secondDepth,secondExit,secondInner,secondFound,secondRoot,_⟩
    · exact (left.eq_root_of_terminal distinct same).2
    · have firstMem : firstExit ∈ exits whole := List.mem_of_getElem? (by simpa [portAt] using firstFound)
      have secondMem : secondExit ∈ exits whole := List.mem_of_getElem? (by simpa [portAt] using secondFound)
      have equalExit := exits_shared_key_unique distinct firstMem secondMem
        (firstRoot.leaves_subset first.terminal first.terminal_mem)
        (secondRoot.leaves_subset first.terminal (same ▸ second.terminal_mem))
      cases equalExit
      exact (firstRoot.endpoint_unique secondRoot (exit_leaves_nodup distinct firstMem) same).2
termination_by whole.leaves.length
decreasing_by exact exit_smaller (by assumption)

end ChaCha.Paper20261030.PrimaryWings
