import MultiSplay.GlobalPreferredRoot

/-! # Total classical switching in the actual root component -/

namespace MultiSplay.Global.Preferred

open DynamicOptimality DynamicOptimality.SearchRotation
open TangoSquared.MTR
open Pointer (MarkedTree)
open TangoSquared.Primary (Key)
open EndpointEncoding ClassicalSwitch CommonForest

variable {α : Type*}

/-- Every real owner on the root preferred path admits the prescribed
classical switch. Both the next physical representation and the exact
pure-component splay transcript are produced from the current state. -/
theorem root_execution {state : State} {reference left right : RawTree α} {pivot : α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine (.node left pivot right))
    (unique : reference.inorder.Nodup) {before : MarkedTree α}
    (represented : Component state reference before) :
    ∃ main old foreign : MarkedTree α, ∃ rotations : Nat,
      Component (toggle state address) reference main ∧
      Component (restrict state (address ++ [!(state address)]))
        (if state address then left else right) foreign ∧
      Component (restrict state (address ++ [state address]))
        (if state address then right else left) old ∧
      foreign.erase = before.gapArray (incomingGapIndex (state address) spine.lower
        (tail (restrict state address) (state address) (.node left pivot right))) ∧
      Rotations before.erase main.erase rotations ∧
      ClassicalSwitch.Execution pivot foreign.skeleton (state address) spine.lower spine.upper
        before.skeleton main.skeleton old.skeleton rotations ∧
      SplayTrace [before.skeleton,foreign.skeleton] (eventWord reference state address)
        [main.skeleton,old.skeleton]
        (rotations + 2 + 2*spine.lower.count + 2*spine.upper.count) ∧
      main.skeleton.rootKey = some pivot ∧ old.erase ∈ main.holes ∧
      Repartition (state address) spine.lower before foreign main old := by
  obtain ⟨foreign, foreignRep, attached⟩ := represented.incoming path
  have foreignKeys : foreign.skeleton.inorder =
      (tail (restrict state address) (!(state address)) (.node left pivot right)).inorder := by
    have keys := foreignRep.1
    cases side : state address <;> simpa [side, tail, restrict_child] using keys
  have sourceUnique : before.skeleton.inorder.Nodup := by
    rw [represented.1]
    exact unique.sublist (preferred_sublist state reference)
  obtain ⟨after, parkedTree, rotations, run, trace, afterKeys, oldKeys⟩ :=
    path.eventWord_execution before.skeleton foreign.skeleton represented.1 foreignKeys sourceUnique
  have oldSize : parkedTree.size =
      (tail (restrict state address) (state address) (.node left pivot right)).size := by
    simpa only [Tree.length_inorder] using congrArg List.length oldKeys
  obtain ⟨main, old, mainSkeleton, oldSkeleton, actual, hole, partition⟩ :=
    execution_repartition run before foreign rfl rfl
      (by simpa only [incomingGapIndex, oldSize] using attached)
  have ⟨nextRep, oldRep⟩ :=
    repartition_components path represented foreignRep
      (by simpa only [mainSkeleton] using afterKeys)
      (by simpa only [oldSkeleton] using oldKeys) partition
  exact ⟨main, old, foreign, rotations, nextRep, foreignRep, oldRep, attached, actual,
    by simpa only [mainSkeleton, oldSkeleton] using run,
    by simpa only [mainSkeleton, oldSkeleton] using trace,
    mainSkeleton.symm ▸ run.root, hole, partition⟩

end MultiSplay.Global.Preferred
