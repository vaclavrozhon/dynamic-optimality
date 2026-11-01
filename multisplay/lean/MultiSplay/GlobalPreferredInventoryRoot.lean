import MultiSplay.GlobalPreferredInventoryCore
import MultiSplay.GlobalPreferredExecution

/-!
# A classical root switch preserves one persistent component inventory

The ordered physical hole exchange supplies the same untouched descendant
components before and after the switch. Only the selected and incoming
auxiliary roots are replaced by the main and parked roots. Empty root parts
contribute no nonempty component; the completed forest supplies their slots.
-/

namespace MultiSplay.Global.Preferred

open DynamicOptimality (RawTree)
open TangoSquared.MTR
open Pointer (MarkedTree)
open TangoSquared.Primary (Key)
open EndpointEncoding ClassicalSwitch

variable {α : Type*}

private theorem move_block (first block rest : List α) :
    (first ++ block ++ rest).Perm (block ++ first ++ rest) :=
  (List.perm_append_comm).append_right rest

private theorem size_of_word {a b : RawTree α} (same : a.inorder = b.inorder) : a.size = b.size := by
  simpa only [Tree.length_inorder] using congrArg List.length same

/-- All four local markings arise in the retained physical certificate.
Their untouched component inventory is literally the same list up to
reordering; no auxiliary tree is initialized at this switch. -/
theorem repartition_inventory {state : State} {reference left right : RawTree α} {pivot : α}
    {address : Key} {spine : Spine α}
    (path : Path state reference address spine (.node left pivot right))
    (unique : reference.inorder.Nodup)
    {before foreign main old : MarkedTree α} {trees : List (RawTree α)}
    (represented : Component state reference before)
    (foreignRep : Component (restrict state (address ++ [!(state address)]))
      (if state address then left else right) foreign)
    (mainRep : Component (toggle state address) reference main)
    (oldRep : Component (restrict state (address ++ [state address]))
      (if state address then right else left) old)
    (partition : Repartition (state address) spine.lower before foreign main old)
    (inventory : Core state reference before.erase trees) :
    ∃ next remainder : List (RawTree α),
      Core (toggle state address) reference main.erase next ∧
      trees.Perm (rootPart before.skeleton ++ rootPart foreign.skeleton ++ remainder) ∧
      next.Perm (rootPart main.skeleton ++ rootPart old.skeleton ++ remainder) := by
  obtain ⟨descendants,treeShape,children⟩ := inventory.expose unique represented
  obtain ⟨front,back,beforeHoles,afterHoles,frontLength⟩ := path.holes_switch
  obtain ⟨actualFront,actualBack,actualLength,beforeActual,afterActual⟩ := partition
  have aligned : front.length = actualFront.length := frontLength.trans actualLength.symm
  have focusUnique : (TangoSquared.MTR.Tree.node left pivot right).inorder.Nodup := by
    rw [← path.referenceAt]
    exact unique.sublist (referenceAt_inorder_sublist reference address)
  rw [beforeHoles,beforeActual] at children
  cases direction : state address with
  | false =>
      simp only [direction,Bool.false_eq_true,↓reduceIte,Bool.not_false] at children afterHoles afterActual foreignRep oldRep
      have oldLength : (childHoles state address false left).length = old.holes.length := by
        rw [childHoles_length,MarkedTree.holes_length,size_of_word oldRep.1]
      obtain ⟨frontTrees,restTrees,descShape,frontChildren,restChildren⟩ :=
        Branches.split (first := front) (rest := childHoles state address false left ++
          [(address ++ [true],right)] ++ back)
          (firstPhysical := actualFront) (restPhysical := old.holes ++ [foreign.erase] ++ actualBack)
          (by simpa only [List.append_assoc] using children) aligned
      obtain ⟨oldTrees,incomingBackTrees,restShape,oldChildren,incomingBackChildren⟩ :=
        Branches.split (first := childHoles state address false left)
          (rest := (address ++ [true],right)::back)
          (firstPhysical := old.holes) (restPhysical := foreign.erase::actualBack)
          (by simpa only [List.append_assoc,List.singleton_append] using restChildren) oldLength
      cases incomingBackChildren with
      | @cons _ _ _ _ _ incomingTrees backTrees incomingCore backChildren =>
          obtain ⟨foreignTrees,foreignShape,foreignChildren⟩ :=
            incomingCore.expose (Auxiliary.nodup_node focusUnique).2.1 foreignRep
          have parkedCore := Core.of_branches oldRep.1 (oldChildren.unprefix (address ++ [false]))
          have middle : Branches state
              ((address ++ [false],left)::childHoles state address true right)
              (old.erase::foreign.holes)
              ((rootPart old.skeleton ++ oldTrees) ++ foreignTrees) :=
            .cons parkedCore (foreignChildren.prefix (address ++ [true]))
          have assembled : Branches state (preferredHoles (toggle state address) reference) main.holes
              (frontTrees ++ ((rootPart old.skeleton ++ oldTrees) ++ foreignTrees) ++ backTrees) := by
            rw [afterHoles,afterActual]
            simpa only [List.singleton_append,List.append_assoc] using
              frontChildren.append (middle.append backChildren)
          have nextChildren := assembled.state_congr fun entry member =>
            path.after_hole_restrict_toggle (by simp) member
          let remainder := frontTrees ++ oldTrees ++ foreignTrees ++ backTrees
          refine ⟨_,remainder,Core.of_branches mainRep.1 nextChildren,?_,?_⟩
          · rw [treeShape,descShape,restShape,foreignShape]
            simpa only [remainder,List.append_assoc] using
              (move_block (frontTrees ++ oldTrees) (rootPart foreign.skeleton)
                (foreignTrees ++ backTrees)).append_left (rootPart before.skeleton)
          · simpa only [remainder,List.append_assoc] using
              (move_block frontTrees (rootPart old.skeleton)
                (oldTrees ++ foreignTrees ++ backTrees)).append_left (rootPart main.skeleton)
  | true =>
      simp only [direction,↓reduceIte,Bool.not_true] at children afterHoles afterActual foreignRep oldRep
      have oldLength : (childHoles state address true right).length = old.holes.length := by
        rw [childHoles_length,MarkedTree.holes_length,size_of_word oldRep.1]
      obtain ⟨frontTrees,restTrees,descShape,frontChildren,restChildren⟩ :=
        Branches.split (first := front)
          (rest := (address ++ [false],left)::(childHoles state address true right ++ back))
          (firstPhysical := actualFront) (restPhysical := foreign.erase::(old.holes ++ actualBack))
          (by simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using children) aligned
      cases restChildren with
      | @cons _ _ _ _ _ incomingTrees oldBackTrees incomingCore oldBackChildren =>
          obtain ⟨oldTrees,backTrees,oldBackShape,oldChildren,backChildren⟩ :=
            Branches.split oldBackChildren oldLength
          obtain ⟨foreignTrees,foreignShape,foreignChildren⟩ :=
            incomingCore.expose (Auxiliary.nodup_node focusUnique).1 foreignRep
          have parkedCore := Core.of_branches oldRep.1 (oldChildren.unprefix (address ++ [true]))
          have parkedBranch : Branches state [(address ++ [true],right)] [old.erase]
              (rootPart old.skeleton ++ oldTrees) := by
            simpa only [List.append_nil] using (Branches.cons parkedCore (Branches.nil state))
          have middle : Branches state
              (childHoles state address false left ++ [(address ++ [true],right)])
              (foreign.holes ++ [old.erase])
              (foreignTrees ++ (rootPart old.skeleton ++ oldTrees)) :=
            (foreignChildren.prefix (address ++ [false])).append parkedBranch
          have assembled : Branches state (preferredHoles (toggle state address) reference) main.holes
              (frontTrees ++ (foreignTrees ++ (rootPart old.skeleton ++ oldTrees)) ++ backTrees) := by
            rw [afterHoles,afterActual]
            simpa only [List.append_assoc,List.append_nil] using
              frontChildren.append (middle.append backChildren)
          have nextChildren := assembled.state_congr fun entry member =>
            path.after_hole_restrict_toggle (by simp) member
          let remainder := frontTrees ++ foreignTrees ++ oldTrees ++ backTrees
          refine ⟨_,remainder,Core.of_branches mainRep.1 nextChildren,?_,?_⟩
          · rw [treeShape,descShape,foreignShape,oldBackShape]
            simpa only [remainder,List.append_assoc] using
              (move_block frontTrees (rootPart foreign.skeleton)
                (foreignTrees ++ oldTrees ++ backTrees)).append_left (rootPart before.skeleton)
          · simpa only [remainder,List.append_assoc] using
              (move_block (frontTrees ++ foreignTrees) (rootPart old.skeleton)
                (oldTrees ++ backTrees)).append_left (rootPart main.skeleton)

end MultiSplay.Global.Preferred
