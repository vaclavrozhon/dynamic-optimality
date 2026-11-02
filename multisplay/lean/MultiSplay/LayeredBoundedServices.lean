import MultiSplay.LayeredBoundedJoin

/-!
# Common root checkpoints for the combined normalizer

A split exposes the requested pivot through both representations. A service
uses the same exposure, serves the common root, and rejoins the exact returned
histories. No structural event is added to the prescribed common word.
-/

namespace MultiSplay.Layered.Bounded

open Splay.Tree (BST)
open Splay.Accounting.OfflineConnectedSupport (heavyHeight)
open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder)
open ChaCha.Paper20261030.Auxiliary (Rearranges)
open CommonForest (RootAccess)

variable {α : Type*}

theorem split_trace {capacity : Nat} (state : State capacity α)
    {left right : RawTree α} {key : α} (root : state.source = .node left key right) :
    ∃ a b : State capacity α, ∃ cost : Nat,
      a.source = left ∧ b.source = right ∧
      Trace capacity [state.actual] [.split (inorder left) key (inorder right)] [a.actual, b.actual] cost ∧
      cost + 18 * (a.potential + b.potential) ≤ 18 * state.potential + 44620705 := by
  obtain ⟨a, b, work, leftEq, rightEq, path, bound⟩ := split_exists state root
  refine ⟨a, b, 18 * work + 1, leftEq, rightEq, ?_, by omega⟩
  have prepare := CommonForest.Trace.single (CommonForest.Step.prepare (access := Access capacity) path)
  have split := CommonForest.Trace.single (CommonForest.Step.split
    (access := Access capacity) (prepare := Preparation capacity) ⟨RootAccess.root a.actual key b.actual, path.geometry.2⟩)
  simpa [a.inorder_eq, b.inorder_eq, leftEq, rightEq] using prepare.append split

theorem service_trace {capacity : Nat} (state : State capacity α)
    {left right : RawTree α} {key : α} (root : state.source = .node left key right) :
    ∃ result : State capacity α, ∃ cost : Nat,
      result.source = state.source ∧
      Trace capacity [state.actual] [.search (inorder state.source) key] [result.actual] cost ∧
      cost + 18 * result.potential ≤ 18 * state.potential + 89241409 := by
  rcases state with ⟨⟨lower, upper, source, heavyTree, actual, heavyRep, side, ribRep, fits⟩, alphabet⟩
  cases source with
  | empty => simp [State.source, DynamicOptimality.BST.toRaw, Auxiliary.map] at root
  | node l r =>
      simp only [State.source, DynamicOptimality.BST.toRaw, Auxiliary.map,
        ChaCha.MTR.Tree.node.injEq] at root
      obtain ⟨hs⟩ := Heavy.exists_split heavyRep
      have heavyFits : heavyTree.size ≤ capacity := (Rib.same_interval_size (.node l r) heavyTree) ▸ fits
      have hi := heavyRep.height_le_capacity fits
      have he := heavy_node_height hs.leftRep hs.rightRep fits
      have hw := hs.work_le
      have heh : (BST.node hs.actualLeft hs.actualRight).height ≤ heavyHeight capacity := by
        dsimp [heavyHeight]; omega
      obtain ⟨exposed, exposedRep, firstWork, firstCount, firstRun, firstCountBound, firstBound⟩ :=
        simulate hs.path (by dsimp [heavyHeight]; omega) ribRep heavyFits
      obtain ⟨rs⟩ := Rib.exists_split exposedRep
      obtain ⟨hj⟩ := Heavy.exists_join hs.leftRep hs.rightRep fits
      have exposedFits : (BST.node hs.actualLeft hs.actualRight).size ≤ capacity :=
        (Rib.same_interval_size (.node l r) (.node hs.actualLeft hs.actualRight)) ▸ fits
      obtain ⟨rejoined, rejoinedRep, joinWork, joinPath, joinWorkBound, joinBound⟩ :=
        Splay.Accounting.OfflineConnectedSupport.RibRepresentation.exists_join side rs.leftRep rs.rightRep exposedFits
      have hf := hj.representation.height_le_capacity fits
      have hjw := hj.work_le
      obtain ⟨final, finalRep, lastWork, lastCount, lastRun, lastCountBound, lastBound⟩ :=
        simulate hj.path (by dsimp [heavyHeight]; omega) rejoinedRep exposedFits
      have ribInitialHeight := (exposedRep.height_le exposedFits).trans (Nat.mul_le_mul_right _ heh)
      have ribExposedHeight := rib_node_height rs.leftRep rs.rightRep exposedFits heh
      have ribFinalHeight := (rejoinedRep.height_le exposedFits).trans (Nat.mul_le_mul_right _ heh)
      have rsw := rs.work_le
      let result : State capacity α := ⟨⟨lower, upper, .node l r, hj.actual, final,
        hj.representation, side, finalRep, fits⟩, alphabet⟩
      let exposedL := Auxiliary.map alphabet (DynamicOptimality.BST.toRaw rs.actualLeft)
      let exposedR := Auxiliary.map alphabet (DynamicOptimality.BST.toRaw rs.actualRight)
      have ribSplitPath := prepare alphabet rs.path (by omega) ribExposedHeight (by omega)
        exposedRep.geometry.1 (rib_node_geometry rs.leftRep rs.rightRep)
      have ribJoinPath := prepare alphabet joinPath ribExposedHeight (by omega) (by omega)
        (rib_node_geometry rs.leftRep rs.rightRep) rejoinedRep.geometry.1
      have firstPath : Preparation capacity (Auxiliary.map alphabet (DynamicOptimality.BST.toRaw actual))
          (.node exposedL key exposedR) (18 * firstWork + 18 * rs.work) := by
        simpa only [exposedL, exposedR, DynamicOptimality.BST.toRaw, Auxiliary.map, root.2.1] using
          (BoundedMacros.Preparation.segment alphabet firstRun (show 3 * firstCount ≤ 18 * firstWork by omega)).trans ribSplitPath
      have lastPath : Preparation capacity (.node exposedL key exposedR) result.actual (18 * joinWork + 18 * lastWork) := by
        simpa only [exposedL, exposedR, result, State.actual,
          DynamicOptimality.BST.toRaw, Auxiliary.map, root.2.1] using
          ribJoinPath.trans (BoundedMacros.Preparation.segment alphabet lastRun (show 3 * lastCount ≤ 18 * lastWork by omega))
      have keys : inorder (.node exposedL key exposedR) =
          inorder (Auxiliary.map alphabet (DynamicOptimality.BST.toRaw (.node l r))) := by
        simpa only [DynamicOptimality.BST.toRaw, Auxiliary.map, root.2.1] using
          Alphabet.indexed_inorder_eq (.node rs.actualLeft rs.actualRight) (.node l r) alphabet
      refine ⟨result, (18 * firstWork + 18 * rs.work) + (1 + (18 * joinWork + 18 * lastWork)), rfl, ?_, ?_⟩
      · have first := CommonForest.Trace.single (CommonForest.Step.prepare (access := Access capacity) firstPath)
        have middle := CommonForest.Trace.single (CommonForest.Step.search
          (access := Access capacity) (prepare := Preparation capacity) ⟨RootAccess.root exposedL key exposedR, firstPath.geometry.2⟩)
        have last := CommonForest.Trace.single (CommonForest.Step.prepare (access := Access capacity) lastPath)
        simpa only [List.nil_append, List.append_nil, keys, State.actual, State.source] using
          first.append (middle.append last)
      · have hsBound := hs.amortized
        have rsBound := rs.amortized
        have hjBound := hj.amortized
        change (18 * firstWork + 18 * rs.work) + (1 + (18 * joinWork + 18 * lastWork)) +
          18 * (21552 * hj.representation.potential + finalRep.potential) ≤
          18 * (21552 * heavyRep.potential + ribRep.potential) + 89241409
        omega

end MultiSplay.Layered.Bounded
