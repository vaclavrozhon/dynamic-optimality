import MultiSplay.ClassicalSwitchReference
import MultiSplay.ForestUniqueness

/-!
# The canonical preferred-path partition of the actual reference keys

The root component is `preferred`. Every off-path child contributes its own
root component, followed by the remaining components below both children.
An empty off-path child is retained as an empty component, so leaf switches
have the same two-component exchange as other switches without dummy keys.
-/

namespace MultiSplay.ClassicalSwitch

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder size)
open ChaCha.Primary (Key)
open EndpointEncoding

variable {α : Type*}

def otherComponents : State → RawTree α → List (RawTree α)
  | _, .empty => []
  | state, .node left _ right =>
      (if state [] then preferred (below state false) left else preferred (below state true) right) ::
        (otherComponents (below state false) left ++ otherComponents (below state true) right)

def forest (state : State) (reference : RawTree α) : List (RawTree α) :=
  preferred state reference :: otherComponents state reference

theorem below_toggle_other (state : State) (edge other : Bool) (address : Key)
    (different : other ≠ edge) : below (toggle state (edge::address)) other = below state other := by
  funext owner
  simp [below, toggle, different]

private theorem move_first {before after : List α} {selected : α} (run : before.Perm (selected::after))
    (front back : List α) : (front ++ before ++ back).Perm (selected :: (front ++ after ++ back)) := by
  have moved := (run.append_right back).append_left front
  have moved' : (front ++ before ++ back).Perm (front ++ selected :: (after ++ back)) := by
    simpa only [List.append_assoc, List.cons_append] using moved
  exact moved'.trans
    (by simpa only [List.append_assoc] using (List.perm_middle :
      (front ++ selected :: (after ++ back)).Perm (selected :: (front ++ (after ++ back)))))

/-- Inside the selected preferred component, all other components have a
common unchanged remainder. Only the incoming and old tails exchange roles. -/
theorem Path.partition {state : State} {reference focus : RawTree α} {address : Key} {spine : Spine α}
    (path : Path state reference address spine focus) (nonempty : focus ≠ .empty) :
    ∃ remainder,
      (otherComponents state reference).Perm
        (tail (restrict state address) (!(state address)) focus :: remainder) ∧
      (otherComponents (toggle state address) reference).Perm
        (tail (restrict state address) (state address) focus :: remainder) := by
  induction path with
  | here state reference =>
      cases reference with
      | empty => exact False.elim (nonempty rfl)
      | node left key right =>
          refine ⟨otherComponents (EndpointEncoding.below state false) left ++ otherComponents (EndpointEncoding.below state true) right,?_,?_⟩
          · cases side : state [] <;> simp [otherComponents, restrict, tail, side]
          · cases side : state [] <;>
              simp [otherComponents, restrict, tail, side, toggle, below_toggle_empty]
  | @left state left right focus key address spine agrees rest ih =>
      obtain ⟨remainder,before,after⟩ := ih nonempty
      refine ⟨preferred (EndpointEncoding.below state true) right :: (remainder ++ otherComponents (EndpointEncoding.below state true) right),?_,?_⟩
      · simpa [otherComponents, agrees, restrict, EndpointEncoding.below, List.cons_append] using
          move_first before [preferred (EndpointEncoding.below state true) right] (otherComponents (EndpointEncoding.below state true) right)
      · have different := below_toggle_other state false true address (by decide)
        have root : toggle state (false::address) [] = false := by simp [toggle, agrees]
        simpa [otherComponents, root, below_toggle_cons, different, restrict, EndpointEncoding.below, List.cons_append] using
          move_first after [preferred (EndpointEncoding.below state true) right] (otherComponents (EndpointEncoding.below state true) right)
  | @right state left right focus key address spine agrees rest ih =>
      obtain ⟨remainder,before,after⟩ := ih nonempty
      refine ⟨preferred (EndpointEncoding.below state false) left :: (otherComponents (EndpointEncoding.below state false) left ++ remainder),?_,?_⟩
      · simpa [otherComponents, agrees, restrict, EndpointEncoding.below, List.cons_append] using
          move_first before (preferred (EndpointEncoding.below state false) left :: otherComponents (EndpointEncoding.below state false) left) []
      · have different := below_toggle_other state true false address (by decide)
        have root : toggle state (true::address) [] = true := by simp [toggle, agrees]
        simpa [otherComponents, root, below_toggle_cons, different, restrict, EndpointEncoding.below, List.cons_append] using
          move_first after (preferred (EndpointEncoding.below state false) left :: otherComponents (EndpointEncoding.below state false) left) []

theorem forest_keys (state : State) (reference : RawTree α) :
    ((forest state reference).flatMap inorder).Perm (inorder reference) := by
  induction reference generalizing state with
  | empty => simp [forest, preferred, otherComponents, inorder]
  | node left key right ihl ihr =>
      have hl := ihl (below state false)
      have hr := ihr (below state true)
      simp only [forest, List.flatMap_cons] at hl hr
      cases side : state [] with
      | false =>
          let a := inorder (preferred (below state false) left)
          let b := (otherComponents (below state false) left).flatMap inorder
          let c := inorder (preferred (below state true) right)
          let d := (otherComponents (below state true) right).flatMap inorder
          have middle : (a ++ [key] ++ c ++ b ++ d).Perm (a ++ b ++ [key] ++ c ++ d) := by
            have swap := (List.perm_append_comm : (([key] ++ c) ++ b).Perm (b ++ ([key] ++ c)))
            simpa only [List.append_assoc] using (swap.append_right d).append_left a
          have result := ((hl.append (List.Perm.refl [key])).append hr)
          simpa [forest, preferred, otherComponents, side, inorder, List.flatMap_append,
            List.append_assoc, a,b,c,d] using middle.trans
              (by simpa [a,b,c,d,List.append_assoc] using result)
      | true =>
          let a := inorder (preferred (below state false) left)
          let b := (otherComponents (below state false) left).flatMap inorder
          let c := inorder (preferred (below state true) right)
          let d := (otherComponents (below state true) right).flatMap inorder
          have middle : ([key] ++ c ++ a ++ b ++ d).Perm (a ++ b ++ [key] ++ c ++ d) := by
            have swap := (List.perm_append_comm : (([key] ++ c) ++ (a ++ b)).Perm ((a ++ b) ++ ([key] ++ c)))
            simpa only [List.append_assoc] using swap.append_right d
          have result := ((hl.append (List.Perm.refl [key])).append hr)
          simpa [forest, preferred, otherComponents, side, inorder, List.flatMap_append,
            List.append_assoc, a,b,c,d] using middle.trans
              (by simpa [a,b,c,d,List.append_assoc] using result)

theorem forest_unique (state : State) {reference : RawTree α} (unique : (inorder reference).Nodup) :
    CommonForest.UniqueKeys (forest state reference) :=
  (forest_keys state reference).nodup_iff.mpr unique

end MultiSplay.ClassicalSwitch
