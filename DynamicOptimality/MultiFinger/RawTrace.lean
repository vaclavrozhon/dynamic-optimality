import DynamicOptimality.SearchRotationDepth

/-! # Grouping free-standing rotations into actual search accesses

The multifinger simulator performs rotations while moving its virtual
fingers and serves a request only when its key is at the physical root.
This trace records those actual operations. The conversion charges the
search in the tree before each group of rotations. Rotations after the
last request can be omitted, including for an empty request word.
-/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR SearchRotation

variable {α : Type*} [LinearOrder α]

theorem rotations_preserve_order {before after : RawTree α} {count : Nat}
    (actual : Rotations before after count) (ordered : before.Ordered) : after.Ordered := by
  induction actual with
  | refl => exact ordered
  | step first _ ih => exact ih (RawDepth.rotation_ordered ordered first)

theorem prepend_search_rotations {before middle after : RawTree α}
    {word : List α} {rotations cost : Nat} (nonempty : word ≠ [])
    (actual : Rotations before middle rotations) (ordered : before.Ordered)
    (run : SearchRotation.Execution middle word after cost) :
    ∃ total, SearchRotation.Execution before word after total ∧ total ≤ cost+2*rotations := by
  cases run with
  | nil => exact (nonempty rfl).elim
  | @cons key rest middle next after headCost tailCost head tail =>
    obtain ⟨depth,count,found,moves,rfl⟩ := head
    obtain ⟨initial,search,depthBound⟩ := RawDepth.rotations_initial_depth actual ordered key found
    refine ⟨(initial+1+(rotations+count))+tailCost,?_,?_⟩
    · exact .cons ⟨initial,rotations+count,search,actual.append moves,rfl⟩ tail
    · omega

inductive RawTrace : RawTree α → List α → RawTree α → Nat → Prop
  | done (tree : RawTree α) : RawTrace tree [] tree 0
  | rotate {before middle after : RawTree α} {word : List α} {rotations cost : Nat}
      (actual : Rotations before middle rotations) (rest : RawTrace middle word after cost) :
      RawTrace before word after (rotations+cost)
  | serve {before after : RawTree α} {word : List α} {cost : Nat}
      (key : α) (found : before.rootKey = some key) (rest : RawTrace before word after cost) :
      RawTrace before (key::word) after (cost+1)

/-- One conversion covers empty words and unused trailing movements. -/
theorem RawTrace.to_search {before after : RawTree α} {word : List α} {cost : Nat}
    (trace : RawTrace before word after cost) (ordered : before.Ordered) :
    ∃ final total, SearchRotation.Execution before word final total ∧ total ≤ 2*cost := by
  induction trace with
  | done tree => exact ⟨tree,0,.nil tree,by simp⟩
  | @rotate before middle after word rotations cost actual rest ih =>
    by_cases empty : word = []
    · subst word
      exact ⟨before,0,.nil before,by omega⟩
    · obtain ⟨final,total,run,paid⟩ := ih (rotations_preserve_order actual ordered)
      obtain ⟨converted,search,charge⟩ := prepend_search_rotations empty actual ordered run
      exact ⟨final,converted,search,by omega⟩
  | @serve before after word cost key found rest ih =>
    obtain ⟨final,total,run,paid⟩ := ih ordered
    have depth : Tree.searchDepth key before = some 0 := by
      cases before with
      | empty => cases found
      | node left pivot right =>
        have same : pivot = key := Option.some.inj found
        subst pivot
        simp [Tree.searchDepth]
    refine ⟨final,1+total,.cons ⟨0,0,depth,.refl before,rfl⟩ run,?_⟩
    omega

end DynamicOptimality.MultiFinger
