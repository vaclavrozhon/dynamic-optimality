import MultiSplay.GlobalPreferredInventoryRoot
import MultiSplay.GlobalPreferredInventoryFocus
import MultiSplay.GlobalPreferredInventorySlots

/-!
# The persistent forest of an actual physical switch

The selected pair is extracted from the actual recursively attached component
inventory. Recursion beneath an opaque subtree retains every surrounding
component literally. Consequently its pure splay trace can be replayed in one
persistent forest, with the same word and the same work.
-/

namespace MultiSplay.Global.Preferred

open DynamicOptimality (RawTree)
open TangoSquared.MTR
open Pointer (MarkedTree)
open TangoSquared.Primary (Key)
open EndpointEncoding ClassicalSwitch CommonForest

variable {α : Type*}

theorem Switch.core_pair {state : State} {reference before after : RawTree α}
    {address : Key} {count work : Nat}
    (run : Switch state reference address before after count work)
    (unique : reference.inorder.Nodup)
    (real : referenceAt reference address ≠ .empty)
    {trees : List (RawTree α)} (inventory : Core state reference before trees) :
    ∃ next source incoming target parked remainder,
      Core (toggle state address) reference after next ∧
      source ≠ .empty ∧
      trees.Perm (rootPart source ++ rootPart incoming ++ remainder) ∧
      next.Perm (rootPart target ++ rootPart parked ++ remainder) ∧
      SplayTrace [source,incoming] (eventWord reference state address) [target,parked] work := by
  induction run generalizing trees with
  | @root state reference left right pivot address spine before main old foreign rotations
      path represented foreignRep mainRep oldRep attached execution partition actual trace =>
      obtain ⟨next,remainder,nextCore,first,last⟩ := repartition_inventory path unique
        represented foreignRep mainRep oldRep partition inventory
      refine ⟨next,before.skeleton,foreign.skeleton,main.skeleton,old.skeleton,remainder,
        nextCore,?_,first,last,trace⟩
      intro absent
      have keys := represented.1
      rw [absent] at keys
      cases reference with
      | empty => exact real (referenceAt_empty address)
      | node left pivot right =>
          cases side : state [] <;> simp [preferred,side,Tree.inorder] at keys
  | @inside state reference entry suffix before replacement count work index context
      represented found shape position child ih =>
      have member := List.mem_of_getElem? found
      have childReal : referenceAt entry.2 suffix ≠ .empty := by
        rw [← preferredHoles_referenceAt state reference member, ← referenceAt_append]
        exact real
      have childUnique : entry.2.inorder.Nodup := by
        rw [← preferredHoles_referenceAt state reference member]
        exact unique.sublist (referenceAt_inorder_sublist reference entry.1)
      obtain ⟨descendants,treeShape,children⟩ := inventory.expose unique represented
      obtain ⟨front,selected,back,descShape,selectedCore,replace⟩ :=
        children.focus (preferredHoles_nodup state reference) index entry found
      obtain ⟨next,source,incoming,target,parked,remainder,nextCore,nonempty,first,last,trace⟩ :=
        ih childUnique childReal selectedCore
      obtain ⟨samePreferred,sameHoles⟩ := preferredHoles_toggle_frame state reference member suffix
      have newChildren := replace (toggle state (entry.1 ++ suffix)) replacement next
        (by simpa only [restrict_toggle_append] using nextCore) (by
          intro other present different
          apply restrict_toggle_of_not_prefix
          intro ancestor
          exact different (preferredHoles_prefix_unique state reference present member ancestor
            (List.prefix_append _ _)))
      have afterHoles : (context.plug (.hole replacement)).holes = before.holes.set index replacement := by
        calc
          _ = (context.plug (.hole (before.gapArray index))).holes.set
              context.holesBefore.length replacement :=
            context_hole_list context (before.gapArray index) replacement
          _ = _ := by rw [← shape,position]
      have afterSkeleton : (context.plug (.hole replacement)).skeleton = before.skeleton := by
        rw [shape]
        exact context_hole_skeleton context replacement (before.gapArray index)
      have assembled : Core (toggle state (entry.1 ++ suffix)) reference
          (context.plug (.hole replacement)).erase
          (rootPart before.skeleton ++ (front ++ next ++ back)) := by
        have built := Core.of_branches
          (actual := context.plug (.hole replacement))
          (show (context.plug (.hole replacement)).skeleton.inorder =
              (preferred (toggle state (entry.1 ++ suffix)) reference).inorder by
            rw [afterSkeleton,samePreferred]; exact represented.1)
          (show Branches (toggle state (entry.1 ++ suffix))
              (preferredHoles (toggle state (entry.1 ++ suffix)) reference)
              (context.plug (.hole replacement)).holes (front ++ next ++ back) by
            rw [sameHoles,afterHoles]; exact newChildren)
        simpa only [afterSkeleton] using built
      obtain ⟨rest,beforeOrder,afterOrder⟩ :=
        pair_context (front := rootPart before.skeleton ++ front) (back := back) first last
      refine ⟨_,source,incoming,target,parked,rest,assembled,nonempty,?_,?_,?_⟩
      · rw [treeShape,descShape]
        simpa only [List.append_assoc] using beforeOrder
      · simpa only [List.append_assoc] using afterOrder
      · rw [eventWord_hole state reference member suffix real]
        exact trace

/-- One actual switch updates its selected pair in the same persistent
forest. Empty incoming or parked components occupy existing analytical
slots; the fixed slot count is maintained without initializing any tree. -/
theorem Switch.inventory [DecidableEq α]
    {state : State} {reference before after : RawTree α}
    {address : Key} {count work : Nat}
    (run : Switch state reference address before after count work)
    (unique : reference.inorder.Nodup)
    (real : referenceAt reference address ≠ .empty)
    {trees : List (RawTree α)} (inventory : Inventory state reference before trees) :
    ∃ next, Inventory (toggle state address) reference after next ∧
      SplayTrace trees (eventWord reference state address) next work := by
  obtain ⟨core,represented,same,length,mass⟩ := inventory
  obtain ⟨next,source,incoming,target,parked,remainder,nextCore,nonempty,first,last,trace⟩ :=
    run.core_pair unique real represented
  exact inventory_pair ⟨core,represented,same,length,mass⟩ nextCore same first last nonempty
    trace (Accounting.eventWord_balanced reference state address)

end MultiSplay.Global.Preferred
