import MultiSplay.ClassicalSwitchMarked

/-! # The exact ordered attachment exchange of a classical switch -/

namespace MultiSplay.ClassicalSwitch

open DynamicOptimality (RawTree)
open TangoSquared.MTR.Tree (inorder size)
open TangoSquared.Primary (Key)
open EndpointEncoding

variable {α : Type*}

/-- The ordered context above a switched node is the same on both sides.
Only the local preferred-path decomposition at that node changes. -/
theorem Path.holes_switch_interval {state : State} {reference focus : RawTree α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine focus) :
    ∃ front back,
      preferredHoles state reference = front ++ prefixHoles address
        (preferredHoles (restrict state address) focus) ++ back ∧
      preferredHoles (toggle state address) reference = front ++ prefixHoles address
        (preferredHoles (toggle (restrict state address) []) focus) ++ back ∧
      front.length = spine.lowerKeys.length := by
  induction path with
  | here state reference => exact ⟨[],[],by simp [restrict],by simp [restrict],rfl⟩
  | @left state left right focus key address spine agrees rest ih =>
      obtain ⟨front,back,before,after,length⟩ := ih
      refine ⟨prefixHoles [false] front, prefixHoles [false] back ++ [([true],right)],?_,?_,?_⟩
      · simp [preferredHoles, agrees, before, prefixHoles_append, prefixHoles_comp,
          restrict, List.append_assoc]
      · have root : toggle state (false::address) [] = false := by simp [toggle, agrees]
        simp [preferredHoles, root, below_toggle_cons, after, prefixHoles_append, prefixHoles_comp,
          restrict, List.append_assoc]
      · simp [length, Spine.lowerKeys_append, Spine.lowerKeys]
  | @right state left right focus key address spine agrees rest ih =>
      obtain ⟨front,back,before,after,length⟩ := ih
      refine ⟨([false],left)::prefixHoles [true] front, prefixHoles [true] back,?_,?_,?_⟩
      · simp [preferredHoles, agrees, before, prefixHoles_append, prefixHoles_comp,
          restrict, List.append_assoc]
      · have root : toggle state (true::address) [] = true := by simp [toggle, agrees]
        simp [preferredHoles, root, below_toggle_cons, after, prefixHoles_append, prefixHoles_comp,
          restrict, List.append_assoc]
      · simp [length, Spine.lowerKeys_append, Spine.lowerKeys]

def childHoles (state : State) (address : Key) (side : Bool) (child : RawTree α) :
    List (Key × RawTree α) :=
  prefixHoles (address ++ [side]) (preferredHoles (restrict state (address ++ [side])) child)

theorem restrict_child (state : State) (address : Key) (side : Bool) :
    restrict state (address ++ [side]) = below (restrict state address) side := by
  rw [restrict_append]
  rfl

theorem childHoles_length (state : State) (address : Key) (side : Bool) (child : RawTree α) :
    (childHoles state address side child).length =
      size (preferred (restrict state (address ++ [side])) child) + 1 := by
  simp [childHoles, preferredHoles_length]

/-- The two surviving child hole words are used literally, including their
reference addresses. No permutation or reset of their subtrees is allowed. -/
theorem Path.holes_switch {state : State} {reference left right : RawTree α} {pivot : α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine (.node left pivot right)) :
    ∃ front back,
      preferredHoles state reference = front ++
        (if state address then [(address ++ [false],left)] ++ childHoles state address true right
         else childHoles state address false left ++ [(address ++ [true],right)]) ++ back ∧
      preferredHoles (toggle state address) reference = front ++
        (if state address then childHoles state address false left ++ [(address ++ [true],right)]
         else [(address ++ [false],left)] ++ childHoles state address true right) ++ back ∧
      front.length = spine.lower.lowerKeys.length := by
  obtain ⟨front,back,before,after,length⟩ := path.holes_switch_interval
  have side : restrict state address [] = state address := by simp [restrict_eq]
  refine ⟨front,back,?_,?_,by simpa using length⟩
  · rw [before]
    cases direction : state address <;>
      simp [preferredHoles, side, direction, prefixHoles_append, prefixHoles_comp,
        childHoles, restrict_child, prefixHoles, List.map_append, List.append_assoc]
  · rw [after]
    cases direction : state address <;>
      simp [preferredHoles, toggle, side, direction, below_toggle_empty, prefixHoles_append, prefixHoles_comp,
        childHoles, restrict_child, prefixHoles, List.map_append, List.append_assoc]

/-- A toggle at a proper ancestor does not change the preference state inside
either child component. -/
theorem restrict_toggle_child (state : State) (address : Key) (side : Bool) :
    restrict (toggle state address) (address ++ [side]) = restrict state (address ++ [side]) := by
  rw [restrict_append, restrict_toggle, restrict_append]
  exact below_toggle_empty (restrict state address) side

end MultiSplay.ClassicalSwitch
