import MultiSplay.ClassicalSwitchSelected

/-! # The two affected components of an arbitrary classical switch -/

namespace MultiSplay.ClassicalSwitch

open DynamicOptimality (RawTree)
open ChaCha.Primary (Key)
open EndpointEncoding

variable {α : Type*}

def sourceComponent (state : State) (reference : RawTree α) (address : Key) : RawTree α :=
  preferred (restrict state (address.take (startDepth state address)))
    (referenceAt reference (address.take (startDepth state address)))

def targetComponent (state : State) (reference : RawTree α) (address : Key) : RawTree α :=
  preferred (toggle (restrict state (address.take (startDepth state address)))
    (address.drop (startDepth state address)))
    (referenceAt reference (address.take (startDepth state address)))

def oldComponent (state : State) (reference : RawTree α) (address : Key) : RawTree α :=
  tail (restrict state address) (state address) (referenceAt reference address)

def incomingComponent (state : State) (reference : RawTree α) (address : Key) : RawTree α :=
  tail (restrict state address) (!(state address)) (referenceAt reference address)

theorem sourceComponent_root (state : State) (reference : RawTree α) (address : Key)
    (root : startDepth state address = 0) : sourceComponent state reference address = preferred state reference := by
  simp [sourceComponent, root, restrict, referenceAt]

theorem targetComponent_root (state : State) (reference : RawTree α) (address : Key)
    (root : startDepth state address = 0) : targetComponent state reference address = preferred (toggle state address) reference := by
  simp [targetComponent, root, restrict, referenceAt]

theorem root_partition (state : State) (reference : RawTree α) (address : Key)
    (root : startDepth state address = 0) (real : referenceAt reference address ≠ .empty) :
    ∃ remainder,
      (otherComponents state reference).Perm (incomingComponent state reference address :: remainder) ∧
      (otherComponents (toggle state address) reference).Perm (oldComponent state reference address :: remainder) := by
  simpa only [oldComponent, incomingComponent] using
    (path_at state reference address ((startDepth_zero _ _).mp root) real).partition real

theorem startDepth_cons_nonzero (state : State) (edge : Bool) (address : Key)
    (nonzero : startDepth state (edge::address) ≠ 0) :
    startDepth state (edge::address) = startDepth (below state edge) address + 1 := by
  rw [startDepth]
  split
  · rename_i condition
    exact False.elim (nonzero (by rw [startDepth, if_pos condition]))
  · rfl

theorem sourceComponent_cons (state : State) (edge : Bool) (address : Key)
    (left right : RawTree α) (pivot : α) (nonzero : startDepth state (edge::address) ≠ 0) :
    sourceComponent state (.node left pivot right) (edge::address) =
      sourceComponent (below state edge) (if edge then right else left) address := by
  simp [sourceComponent, startDepth_cons_nonzero state edge address nonzero, restrict, referenceAt]

theorem targetComponent_cons (state : State) (edge : Bool) (address : Key)
    (left right : RawTree α) (pivot : α) (nonzero : startDepth state (edge::address) ≠ 0) :
    targetComponent state (.node left pivot right) (edge::address) =
      targetComponent (below state edge) (if edge then right else left) address := by
  simp [targetComponent, startDepth_cons_nonzero state edge address nonzero, restrict, referenceAt]

theorem oldComponent_cons (state : State) (edge : Bool) (address : Key)
    (left right : RawTree α) (pivot : α) :
    oldComponent state (.node left pivot right) (edge::address) =
      oldComponent (below state edge) (if edge then right else left) address := rfl

theorem incomingComponent_cons (state : State) (edge : Bool) (address : Key)
    (left right : RawTree α) (pivot : α) :
    incomingComponent state (.node left pivot right) (edge::address) =
      incomingComponent (below state edge) (if edge then right else left) address := rfl

private theorem move_pair {before remainder : List α} {first second : α}
    (run : before.Perm (first::second::remainder)) (front back : List α) :
    (front ++ before ++ back).Perm (first::second::(front ++ remainder ++ back)) := by
  have context := (run.append_right back).append_left front
  have swap := (List.perm_append_comm : (front ++ [first,second]).Perm ([first,second] ++ front))
  have finish := swap.append_right (remainder ++ back)
  apply (show (front ++ before ++ back).Perm (front ++ first::second::(remainder ++ back)) by
    simpa [List.append_assoc] using context).trans
  simpa [List.append_assoc] using finish

private theorem add_root {state : State} {reference : RawTree α} {address : Key}
    (same : preferred (toggle state address) reference = preferred state reference)
    {remainder : List (RawTree α)}
    (before : (otherComponents state reference).Perm
      (sourceComponent state reference address :: incomingComponent state reference address :: remainder))
    (after : (otherComponents (toggle state address) reference).Perm
      (targetComponent state reference address :: oldComponent state reference address :: remainder)) :
    (forest state reference).Perm (sourceComponent state reference address ::
      incomingComponent state reference address :: preferred state reference :: remainder) ∧
    (forest (toggle state address) reference).Perm (targetComponent state reference address ::
      oldComponent state reference address :: preferred state reference :: remainder) := by
  constructor
  · simpa [forest] using move_pair before [preferred state reference] []
  · simpa [forest, same] using move_pair after [preferred state reference] []

/-- For a switch outside the root preferred path, its root component stays
literally unchanged. Its two affected components have one common remainder. -/
theorem nonroot_partition (state : State) (reference : RawTree α) (address : Key)
    (nonzero : startDepth state address ≠ 0) (real : referenceAt reference address ≠ .empty) :
    preferred (toggle state address) reference = preferred state reference ∧
    ∃ remainder,
      (otherComponents state reference).Perm
        (sourceComponent state reference address :: incomingComponent state reference address :: remainder) ∧
      (otherComponents (toggle state address) reference).Perm
        (targetComponent state reference address :: oldComponent state reference address :: remainder) := by
  induction address generalizing state reference with
  | nil => simp [startDepth] at nonzero
  | cons edge address ih =>
      cases reference with
      | empty => exact False.elim (real rfl)
      | node left pivot right =>
          have childReal : referenceAt (if edge then right else left) address ≠ .empty := real
          have recursiveFrame : ∃ remainder,
              (forest (below state edge) (if edge then right else left)).Perm
                (sourceComponent (below state edge) (if edge then right else left) address ::
                 incomingComponent (below state edge) (if edge then right else left) address :: remainder) ∧
              (forest (toggle (below state edge) address) (if edge then right else left)).Perm
                (targetComponent (below state edge) (if edge then right else left) address ::
                 oldComponent (below state edge) (if edge then right else left) address :: remainder) := by
            by_cases root : startDepth (below state edge) address = 0
            · obtain ⟨remainder,before,after⟩ := root_partition (below state edge) _ address root childReal
              refine ⟨remainder,?_,?_⟩
              · simpa [forest, sourceComponent_root _ _ _ root] using
                  List.Perm.cons (preferred (below state edge) (if edge then right else left)) before
              · simpa [forest, targetComponent_root _ _ _ root] using
                  List.Perm.cons (preferred (toggle (below state edge) address) (if edge then right else left)) after
            · obtain ⟨same,remainder,before,after⟩ := ih (below state edge) _ root childReal
              exact ⟨preferred (below state edge) (if edge then right else left)::remainder,
                add_root same before after⟩
          cases edge with
          | false =>
              have sibling := below_toggle_other state false true address (by decide)
              have root : toggle state (false::address) [] = state [] := by simp [toggle]
              cases side : state [] with
              | false =>
                  have childNonzero : startDepth (below state false) address ≠ 0 := by
                    intro zero
                    simp [startDepth, zero, side] at nonzero
                  obtain ⟨same,remainder,before,after⟩ := ih (below state false) left childNonzero childReal
                  refine ⟨?_,preferred (below state true) right :: (remainder ++ otherComponents (below state true) right),?_,?_⟩
                  · simp [preferred, root, side, below_toggle_cons, same]
                  · simpa [otherComponents, side, sourceComponent_cons _ _ _ _ _ _ nonzero,
                      incomingComponent_cons, List.cons_append] using
                      move_pair before [preferred (below state true) right] (otherComponents (below state true) right)
                  · simpa [otherComponents, root, side, below_toggle_cons, sibling,
                      targetComponent_cons _ _ _ _ _ _ nonzero, oldComponent_cons, List.cons_append] using
                      move_pair after [preferred (below state true) right] (otherComponents (below state true) right)
              | true =>
                  obtain ⟨remainder,before,after⟩ := recursiveFrame
                  refine ⟨?_,remainder ++ otherComponents (below state true) right,?_,?_⟩
                  · simp [preferred, root, side, sibling]
                  · simpa [otherComponents, forest, side, sourceComponent_cons _ _ _ _ _ _ nonzero,
                      incomingComponent_cons, List.cons_append] using
                      move_pair before [] (otherComponents (below state true) right)
                  · simpa [otherComponents, forest, root, side, below_toggle_cons, sibling,
                      targetComponent_cons _ _ _ _ _ _ nonzero, oldComponent_cons, List.cons_append] using
                      move_pair after [] (otherComponents (below state true) right)
          | true =>
              have sibling := below_toggle_other state true false address (by decide)
              have root : toggle state (true::address) [] = state [] := by simp [toggle]
              cases side : state [] with
              | true =>
                  have childNonzero : startDepth (below state true) address ≠ 0 := by
                    intro zero
                    simp [startDepth, zero, side] at nonzero
                  obtain ⟨same,remainder,before,after⟩ := ih (below state true) right childNonzero childReal
                  refine ⟨?_,preferred (below state false) left :: (otherComponents (below state false) left ++ remainder),?_,?_⟩
                  · simp [preferred, root, side, below_toggle_cons, same]
                  · simpa [otherComponents, side, sourceComponent_cons _ _ _ _ _ _ nonzero,
                      incomingComponent_cons, List.cons_append] using
                      move_pair before (preferred (below state false) left :: otherComponents (below state false) left) []
                  · simpa [otherComponents, root, side, below_toggle_cons, sibling,
                      targetComponent_cons _ _ _ _ _ _ nonzero, oldComponent_cons, List.cons_append] using
                      move_pair after (preferred (below state false) left :: otherComponents (below state false) left) []
              | false =>
                  obtain ⟨remainder,before,after⟩ := recursiveFrame
                  have shuffleBefore := List.Perm.cons (preferred (below state true) right)
                    (List.perm_append_comm (l₁ := otherComponents (below state false) left)
                      (l₂ := otherComponents (below state true) right))
                  have shuffleAfter := List.Perm.cons (preferred (toggle (below state true) address) right)
                    (List.perm_append_comm (l₁ := otherComponents (below state false) left)
                      (l₂ := otherComponents (toggle (below state true) address) right))
                  refine ⟨?_,remainder ++ otherComponents (below state false) left,?_,?_⟩
                  · simp [preferred, root, side, sibling]
                  · have combined := shuffleBefore.trans (by
                      simpa [forest, List.cons_append] using
                        move_pair before [] (otherComponents (below state false) left))
                    simpa [otherComponents, side, sourceComponent_cons _ _ _ _ _ _ nonzero,
                      incomingComponent_cons] using combined
                  · have combined := shuffleAfter.trans (by
                      simpa [forest, List.cons_append] using
                        move_pair after [] (otherComponents (below state false) left))
                    simpa [otherComponents, root, side, below_toggle_cons, sibling,
                      targetComponent_cons _ _ _ _ _ _ nonzero, oldComponent_cons] using combined

/-- The full canonical forest changes exactly these two component domains;
every other component, including every deeper preferred-path history, has the
same actual canonical subtree on both sides. -/
theorem selected_partition (state : State) (reference : RawTree α) (address : Key)
    (real : referenceAt reference address ≠ .empty) :
    ∃ remainder,
      (forest state reference).Perm
        (sourceComponent state reference address :: incomingComponent state reference address :: remainder) ∧
      (forest (toggle state address) reference).Perm
        (targetComponent state reference address :: oldComponent state reference address :: remainder) := by
  by_cases root : startDepth state address = 0
  · obtain ⟨remainder,before,after⟩ := root_partition state reference address root real
    refine ⟨remainder,?_,?_⟩
    · simpa [forest, sourceComponent_root _ _ _ root] using List.Perm.cons (preferred state reference) before
    · simpa [forest, targetComponent_root _ _ _ root] using List.Perm.cons (preferred (toggle state address) reference) after
  · obtain ⟨same,remainder,before,after⟩ := nonroot_partition state reference address root real
    exact ⟨preferred state reference :: remainder,add_root same before after⟩

end MultiSplay.ClassicalSwitch
