import MultiSplay.ComparatorGuardPreparation
import MultiSplay.ComparatorPointerProgram
import ChaCha.Paper20261030.AuxiliaryPointer

/-!
# Actual guard walks and their shared rooted frontier

Walking two external-gap paths is an ordinary root-returning pointer
execution, including when a gap is empty. Tracking that execution gives
one rooted hull containing all neighboring guards and preserves every
unvisited physical subtree literally. The same tracker can pull the
guards back through an earlier preparation trace.
-/

namespace MultiSplay.ComparatorGuard

open DynamicOptimality (RawTree)
open ChaCha.MTR
open ChaCha.MTR.Tree (inorder size)
open Pointer (MarkedTree Cursor Trace Step Frame)

variable {α : Type*}

/-- The served keys of an actual pointer execution belong to a shared
before/after hull. The bound counts actual exposed keys, not payload size. -/
theorem trace_hull {before after : RawTree α} {visited : List α} {cost : Nat}
    (execution : Trace (Cursor.atRoot before) visited (Cursor.atRoot after) cost) :
    ∃ source target : MarkedTree α,
      source.erase = before ∧ target.erase = after ∧
      source.holes = target.holes ∧ source.skeleton.inorder = target.skeleton.inorder ∧
      source.skeleton.size ≤ cost + 1 ∧
      ∀ key ∈ visited, key ∈ source.skeleton.inorder := by
  cases before with
  | empty =>
      have unchanged : Cursor.atRoot after = Cursor.atRoot (.empty : RawTree α) := by
        cases execution with
        | nil => rfl
        | step move rest => cases move
        | serve atKey rest => simp [Cursor.atRoot,Tree.rootKey] at atKey
      have empty : after = .empty := congrArg Cursor.focus unchanged
      have noVisits := execution.empty_root_word
      refine ⟨.hole .empty,.hole .empty,rfl,empty.symm,rfl,rfl,?_,?_⟩
      · simp [MarkedTree.skeleton,Tree.size]
      · simp [noVisits]
  | node left key right =>
      let initial : Pointer.SeenCursor α := ⟨.hole left,key,.hole right,[]⟩
      let marked : MarkedTree α := .node (.hole left) key (.hole right)
      obtain ⟨last,source,lastCursor,sourceTree,sameHoles,sameKeys,_,small,served⟩ :=
        execution.tracked initial rfl marked rfl rfl
      refine ⟨source,last.tree,sourceTree,?_,sameHoles,sameKeys,?_,served⟩
      · rw [last.erase_tree,lastCursor]
        rfl
      · have rootSize : marked.skeleton.size = 1 := rfl
        rw [rootSize] at small
        omega

/-- Reconfiguration of a tracked hull keeps its actual ordered frontier. -/
theorem marked_program {source target : MarkedTree α}
    (holes : source.holes = target.holes)
    (keys : source.skeleton.inorder = target.skeleton.inorder) :
    ∃ cost ≤ 12 * source.skeleton.size,
      CommonForest.Program [source.erase] [] [target.erase] cost := by
  have arrays : source.gapArray = target.gapArray := by
    funext index
    simp only [MarkedTree.gapArray,holes]
  obtain ⟨count,countBound,rotations⟩ := Tree.graft_simulation_linear
    source.skeleton target.skeleton keys source.gapArray 0
  obtain ⟨cost,bound,program⟩ := CommonForest.restrictedSteps_program rotations
  have sameSize : source.skeleton.size = target.skeleton.size := by
    simpa only [Tree.length_inorder] using congrArg List.length keys
  refine ⟨cost,by omega,?_⟩
  rw [source.graft_gapArray] at program
  rw [arrays,target.graft_gapArray] at program
  exact program

/-- A null external gap needs no fictitious cursor visit. Every real key
on its route is served and the pointer returns to its original root. -/
theorem GapRoute.roundTrip {tree : RawTree α} {index : Nat} {keys : List α}
    (route : GapRoute tree index keys) (ancestors : List (Frame α)) :
    ∃ cost ≤ 3 * keys.length,
      Trace ⟨tree,ancestors⟩ keys ⟨tree,ancestors⟩ cost := by
  induction route generalizing ancestors with
  | empty => exact ⟨0,by simp,.nil _⟩
  | @left left right root index keys child ih =>
      cases left with
      | empty =>
          cases child
          exact ⟨1,by simp,.serve rfl (.nil _)⟩
      | node a key b =>
          obtain ⟨cost,bound,run⟩ := ih (.left root right :: ancestors)
          have back : Trace ⟨.node a key b,.left root right :: ancestors⟩ []
              ⟨.node (.node a key b) root right,ancestors⟩ 1 :=
            .step (.upLeft _ _ _ _) (.nil _)
          have joined := ChaCha.Paper20261030.Auxiliary.trace_append run back
          refine ⟨cost+3,by simp only [List.length_cons]; omega,?_⟩
          simpa only [List.append_nil,Nat.add_assoc] using
            Trace.serve (x := root) rfl (Trace.step (.left a b right key root ancestors) joined)
  | @right left right root index keys child ih =>
      cases right with
      | empty =>
          cases child
          exact ⟨1,by simp,.serve rfl (.nil _)⟩
      | node a key b =>
          obtain ⟨cost,bound,run⟩ := ih (.right left root :: ancestors)
          have back : Trace ⟨.node a key b,.right left root :: ancestors⟩ []
              ⟨.node left root (.node a key b),ancestors⟩ 1 :=
            .step (.upRight _ _ _ _) (.nil _)
          have joined := ChaCha.Paper20261030.Auxiliary.trace_append run back
          refine ⟨cost+3,by simp only [List.length_cons]; omega,?_⟩
          simpa only [List.append_nil,Nat.add_assoc] using
            Trace.serve (x := root) rfl (Trace.step (.right left a b root key ancestors) joined)

/-- Both paths are explored inside the same actual component. Their
neighbor keys therefore occur in one bounded, literal rooted hull. -/
theorem two_gap_hull {tree : RawTree α} {first second : Nat}
    {firstKeys secondKeys : List α}
    (firstRoute : GapRoute tree first firstKeys)
    (secondRoute : GapRoute tree second secondKeys) :
    ∃ hull : MarkedTree α, hull.erase = tree ∧
      hull.skeleton.size ≤ 3 * (firstKeys.length + secondKeys.length) + 1 ∧
      (∀ key ∈ firstKeys, key ∈ hull.skeleton.inorder) ∧
      (∀ key ∈ secondKeys, key ∈ hull.skeleton.inorder) := by
  obtain ⟨firstCost,firstBound,firstRun⟩ := firstRoute.roundTrip []
  obtain ⟨secondCost,secondBound,secondRun⟩ := secondRoute.roundTrip []
  have run := ChaCha.Paper20261030.Auxiliary.trace_append firstRun secondRun
  obtain ⟨source,target,sourceTree,_,_,_,small,served⟩ := trace_hull run
  refine ⟨source,sourceTree,by omega,?_,?_⟩
  · intro key member
    exact served key (List.mem_append_left _ member)
  · intro key member
    exact served key (List.mem_append_right _ member)

end MultiSplay.ComparatorGuard
