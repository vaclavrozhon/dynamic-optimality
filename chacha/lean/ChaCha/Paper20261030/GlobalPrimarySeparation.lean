import ChaCha.Paper20261030.GlobalPrimaryRoots

set_option autoImplicit false

/-! Primary component subtrees form a nested family: two such subtrees
are comparable by containment or have disjoint original-key leaves.
The final corollary separates every other component from a specified
immediate exit by proper containment or disjointness. -/

namespace ChaCha.Paper20261030.PrimaryWings

open PreferredProjection

variable {α : Type*} [DecidableEq α]

theorem ComponentRoot.nested_or_disjoint {whole first second : PrefRouter α} {start finish : Nat}
    (left : ComponentRoot whole start first) (right : ComponentRoot whole finish second)
    (distinct : whole.leaves.Nodup) :
    (∃ inner, ComponentRoot first inner second ∧ finish = start+inner) ∨
    (∃ inner, ComponentRoot second inner first ∧ start = finish+inner) ∨
    (∀ key, key ∈ first.leaves → key ∈ second.leaves → False) := by
  classical
  by_cases shared : ∃ key, key ∈ first.leaves ∧ key ∈ second.leaves
  · obtain ⟨key,inFirst,inSecond⟩ := shared
    rcases left.first_exit with ⟨startEq,firstEq⟩ | ⟨firstDepth,firstExit,firstInner,firstFound,firstRoot,firstOffset⟩
    · subst start
      subst first
      exact Or.inl ⟨finish,right,by omega⟩
    · rcases right.first_exit with ⟨finishEq,secondEq⟩ | ⟨secondDepth,secondExit,secondInner,secondFound,secondRoot,secondOffset⟩
      · subst finish
        subst second
        exact Or.inr (Or.inl ⟨start,left,by omega⟩)
      · have firstMem : firstExit ∈ exits whole := List.mem_of_getElem? (by simpa [portAt] using firstFound)
        have secondMem : secondExit ∈ exits whole := List.mem_of_getElem? (by simpa [portAt] using secondFound)
        have exitEq := exits_shared_key_unique distinct firstMem secondMem
          (firstRoot.leaves_subset key inFirst) (secondRoot.leaves_subset key inSecond)
        cases exitEq
        have depthEq : firstDepth = secondDepth := by
          have firstChild : ComponentRoot whole (firstDepth+1) firstExit.subtree := by
            simpa only [Nat.zero_add] using ComponentRoot.child (.root : ComponentRoot whole 0 whole) firstFound
          have secondChild : ComponentRoot whole (secondDepth+1) firstExit.subtree := by
            simpa only [Nat.zero_add] using ComponentRoot.child (.root : ComponentRoot whole 0 whole) secondFound
          have eq := (firstChild.endpoint_unique secondChild distinct rfl).1
          omega
        rcases firstRoot.nested_or_disjoint secondRoot (exit_leaves_nodup distinct firstMem) with
          ⟨inner,rooted,offset⟩ | ⟨inner,rooted,offset⟩ | separate
        · exact Or.inl ⟨inner,rooted,by omega⟩
        · exact Or.inr (Or.inl ⟨inner,rooted,by omega⟩)
        · exact False.elim (separate key inFirst inSecond)
  · exact Or.inr (Or.inr (fun key inFirst inSecond => shared ⟨key,inFirst,inSecond⟩))
termination_by whole.leaves.length
decreasing_by exact exit_smaller (by assumption)

/-- A component distinct from the active root and a specified immediate
exit is a proper subtree of that exit, or is disjoint from it. -/
theorem ComponentRoot.separated_from_exit {whole subtree : PrefRouter α} {start depth : Nat}
    (rooted : ComponentRoot whole start subtree) (distinct : whole.leaves.Nodup)
    (exit : Exit α) (present : portAt 0 (exits whole) depth = some exit)
    (notActive : subtree.terminal ≠ whole.terminal)
    (notExit : subtree.terminal ≠ exit.subtree.terminal) :
    subtree.leaves.length < exit.subtree.leaves.length ∨
      (∀ key, key ∈ subtree.leaves → key ∈ exit.subtree.leaves → False) := by
  classical
  by_cases shared : ∃ key, key ∈ subtree.leaves ∧ key ∈ exit.subtree.leaves
  · obtain ⟨key,inSubtree,inExit⟩ := shared
    rcases rooted.first_exit with ⟨_,same⟩ | ⟨firstDepth,firstExit,inner,firstFound,inside,_⟩
    · exact False.elim (notActive (congrArg PrefRouter.terminal same))
    · have firstMem : firstExit ∈ exits whole := List.mem_of_getElem? (by simpa [portAt] using firstFound)
      have exitMem : exit ∈ exits whole := List.mem_of_getElem? (by simpa [portAt] using present)
      have same := exits_shared_key_unique distinct firstMem exitMem
        (inside.leaves_subset key inSubtree) inExit
      subst firstExit
      exact Or.inl (inside.proper_leaves_lt notExit)
  · exact Or.inr (fun key inSubtree inExit => shared ⟨key,inSubtree,inExit⟩)

end ChaCha.Paper20261030.PrimaryWings
