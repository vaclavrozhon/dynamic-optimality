import MultiSplay.GlobalPreferredRootExecution
import MultiSplay.GlobalPreferredReplacement
import MultiSplay.ClassicalSwitchAccountingHoles
import MultiSplay.ClassicalSwitchAccountingLocalization

/-!
# Actual classical switches in arbitrary preferred components

The certificate descends through actual opaque subtrees until it reaches the
selected preferred component. There it records the prescribed pivot and guard
splays, the ordered hole exchange, and its exact ordinary rotations. Thus the
recursive descent changes no auxiliary tree above the selected component.
-/

namespace MultiSplay.Global.Preferred

open DynamicOptimality DynamicOptimality.SearchRotation
open TangoSquared.MTR
open Pointer (MarkedTree)
open TangoSquared.Primary (Key)
open EndpointEncoding ClassicalSwitch CommonForest

variable {α : Type*}

/-- A physical classical switch, retaining its actual containing contexts and
its literal pure-component event word. `work` also includes the analytical
split and join charges; `rotations` counts only actual BST rotations. -/
inductive Switch : State → RawTree α → Key → RawTree α → RawTree α → Nat → Nat → Prop
  | root {state : State} {reference left right : RawTree α} {pivot : α}
      {address : Key} {spine : Spine α} {before main old foreign : MarkedTree α}
      {rotations : Nat}
      (path : Path state reference address spine (.node left pivot right))
      (represented : Component state reference before)
      (foreignRep : Component (restrict state (address ++ [!(state address)]))
        (if state address then left else right) foreign)
      (mainRep : Component (toggle state address) reference main)
      (oldRep : Component (restrict state (address ++ [state address]))
        (if state address then right else left) old)
      (attached : foreign.erase = before.gapArray (incomingGapIndex (state address) spine.lower
        (tail (restrict state address) (state address) (.node left pivot right))))
      (execution : ClassicalSwitch.Execution pivot foreign.skeleton (state address)
        spine.lower spine.upper before.skeleton main.skeleton old.skeleton rotations)
      (partition : Repartition (state address) spine.lower before foreign main old)
      (actual : Rotations before.erase main.erase rotations)
      (trace : SplayTrace [before.skeleton,foreign.skeleton] (eventWord reference state address)
        [main.skeleton,old.skeleton]
        (rotations + 2 + 2*spine.lower.count + 2*spine.upper.count)) :
      Switch state reference address before.erase main.erase rotations
        (rotations + 2 + 2*spine.lower.count + 2*spine.upper.count)
  | inside {state : State} {reference : RawTree α} {entry : Key × RawTree α}
      {suffix : Key} {before : MarkedTree α} {replacement : RawTree α}
      {rotations work index : Nat} (context : MarkedTree.Context α)
      (represented : Component state reference before)
      (found : (preferredHoles state reference)[index]? = some entry)
      (shape : before = context.plug (.hole (before.gapArray index)))
      (position : context.holesBefore.length = index)
      (child : Switch (restrict state entry.1) entry.2 suffix
        (before.gapArray index) replacement rotations work) :
      Switch state reference (entry.1 ++ suffix) before.erase
        (context.plug (.hole replacement)).erase rotations work

 theorem Switch.rotations {state : State} {reference before after : RawTree α}
    {address : Key} {count work : Nat}
    (run : Switch state reference address before after count work) :
    Rotations before after count := by
  induction run with
  | root path represented foreignRep mainRep oldRep attached execution partition actual trace => exact actual
  | inside context represented found shape position child ih =>
      rw [shape]
      exact context_rotations context ih

 theorem Switch.rotations_le_work {state : State} {reference before after : RawTree α}
    {address : Key} {count work : Nat}
    (run : Switch state reference address before after count work) : count ≤ work := by
  induction run with
  | root => omega
  | inside _ _ _ _ _ _ ih => exact ih

/-- Subtree domains retain the unique original keys. -/
theorem referenceAt_inorder_sublist (reference : RawTree α) (address : Key) :
    (referenceAt reference address).inorder.Sublist reference.inorder := by
  induction address generalizing reference with
  | nil => exact .refl _
  | cons edge rest ih =>
      cases reference with
      | empty => simp [referenceAt, Tree.inorder]
      | node left key right =>
          cases edge with
          | false =>
              exact (ih left).trans (by simp only [Tree.inorder]; exact
                (List.sublist_append_left _ _).trans (List.sublist_append_left _ _))
          | true =>
              exact (ih right).trans (by simp only [Tree.inorder]; exact
                List.sublist_append_right _ _)

/-- Every real reference owner has an actual classical physical switch from
every represented current tree. The result recursively represents exactly
the toggled preference state. No future request is involved. -/
theorem switch_exists (state : State) (reference physical : RawTree α) (address : Key)
    (unique : reference.inorder.Nodup) (real : referenceAt reference address ≠ .empty)
    (represented : Realizes state reference physical) :
    ∃ after rotations work,
      Switch state reference address physical after rotations work ∧
      Realizes (toggle state address) reference after := by
  classical
  obtain ⟨before, erase, component⟩ := represented.expose
  by_cases follows : RootPreferred state address
  · have path := path_at state reference address follows real
    cases focus : referenceAt reference address with
    | empty => exact False.elim (real focus)
    | node left pivot right =>
        rw [focus] at path
        obtain ⟨main,old,foreign,rotations,next,foreignRep,oldRep,attached,actual,execution,trace,root,hole,partition⟩ :=
          root_execution path unique component
        refine ⟨main.erase,rotations,rotations + 2 +
          2*(referenceSpine reference address).lower.count +
          2*(referenceSpine reference address).upper.count,?_,next.realizes⟩
        rw [← erase]
        exact .root path component foreignRep next oldRep attached execution partition actual trace
  · obtain ⟨entry,member,suffix,addressEq,samePreferred,sameHoles,childState,otherStates⟩ :=
      localize_outside state reference address follows
    obtain ⟨index,found⟩ := List.getElem?_of_mem member
    have subtree := preferredHoles_referenceAt state reference member
    have childReal : referenceAt entry.2 suffix ≠ .empty := by
      rw [← subtree, ← referenceAt_append, ← addressEq]
      exact real
    have childUnique : entry.2.inorder.Nodup := by
      rw [← subtree]
      exact unique.sublist (referenceAt_inorder_sublist reference entry.1)
    have child := component.2 index entry found
    obtain ⟨replacement,rotations,work,run,next⟩ :=
      switch_exists (restrict state entry.1) entry.2 (before.gapArray index) suffix
        childUnique childReal child
    obtain ⟨after,context,shape,position,afterShape,nextComponent,actual⟩ :=
      component.replace_hole_context samePreferred sameHoles
        (preferredHoles_nodup state reference) index entry found replacement
        (by simpa only [childState] using next) run.rotations otherStates
    refine ⟨after.erase,rotations,work,?_,nextComponent.realizes⟩
    rw [← erase, afterShape, addressEq]
    exact .inside context component found shape position run
termination_by reference.size
decreasing_by
  apply preferredHoles_size_lt state _ member
  intro absent
  apply real
  rw [absent, referenceAt_empty]

end MultiSplay.Global.Preferred
