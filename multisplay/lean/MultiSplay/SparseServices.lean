import MultiSplay.SparseHeavy
import MultiSplay.SparseRib
import MultiSplay.ForestProgram

/-!
# Root services and common splits without history resets

The root service exposes the comparison pivot, serves it in place, and rejoins
its returned child histories. The split deletes that same exposed pivot. Each
trace has the prescribed common event word and a constant amortized allowance.
-/

namespace MultiSplay.SparseHeavy

open DynamicOptimality (RawTree)
open Splay.Tree (BST)
open TangoSquared.MTR.Tree (inorder)
open TangoSquared.Paper20261030.Auxiliary (Rearranges)
open CommonForest (RootAccess)

variable {α : Type*}

abbrev PhysicalTrace := @CommonForest.Trace α RootAccess Rearranges

theorem split_trace {capacity : Nat} (state : State capacity α)
    {left right : RawTree α} {key : α} (root : state.source = .node left key right) :
    ∃ a b : State capacity α, ∃ cost : Nat,
      a.source = left ∧ b.source = right ∧
      PhysicalTrace [state.actual] [.split (inorder left) key (inorder right)] [a.actual, b.actual] cost ∧
      cost + 18 * (a.potential + b.potential) ≤ 18 * state.potential + 2071 := by
  obtain ⟨a, b, work, leftEq, rightEq, path, bound, sizeEq⟩ := split_exists state root
  refine ⟨a, b, 18 * work + 1, leftEq, rightEq, ?_, by omega⟩
  have prepare := CommonForest.Trace.single (CommonForest.Step.prepare (access := RootAccess) path)
  have split := CommonForest.Trace.single (CommonForest.Step.split
    (prepare := Rearranges) (RootAccess.root a.actual key b.actual))
  simpa [a.inorder_eq, b.inorder_eq, leftEq, rightEq] using prepare.append split

theorem service_trace {capacity : Nat} (state : State capacity α)
    {left right : RawTree α} {key : α} (root : state.source = .node left key right) :
    ∃ result : State capacity α, ∃ cost : Nat,
      result.source = state.source ∧
      PhysicalTrace [state.actual] [.search (inorder state.source) key] [result.actual] cost ∧
      cost + 18 * result.potential ≤ 18 * state.potential + 4141 := by
  rcases state with ⟨⟨lower, upper, source, actual, representation, fits⟩, alphabet⟩
  cases source with
  | empty => simp [State.source, DynamicOptimality.BST.toRaw, Auxiliary.map] at root
  | node l r =>
      simp only [State.source, DynamicOptimality.BST.toRaw, Auxiliary.map,
        TangoSquared.MTR.Tree.node.injEq] at root
      obtain ⟨split⟩ := Heavy.exists_split representation
      obtain ⟨joined⟩ := Heavy.exists_join split.leftRep split.rightRep fits
      let target := joined.actual
      let finalRep := joined.representation
      let joinWork := joined.work
      have joinPath := joined.path
      have joinBound := joined.amortized
      let result : State capacity α := ⟨.ofRepresentation finalRep fits, alphabet⟩
      let exposedL := Auxiliary.map alphabet (DynamicOptimality.BST.toRaw split.actualLeft)
      let exposedR := Auxiliary.map alphabet (DynamicOptimality.BST.toRaw split.actualRight)
      have firstPath : Rearranges (Auxiliary.map alphabet (DynamicOptimality.BST.toRaw actual))
          (.node exposedL key exposedR) (18 * split.work) := by
        simpa [DynamicOptimality.BST.toRaw, Auxiliary.map, root.2.1] using
          Alphabet.rearranges alphabet (supported_rearranges split.path)
      have lastPath : Rearranges (.node exposedL key exposedR) result.actual (18 * joinWork) := by
        simpa [result, State.actual, Heavy.Component.ofRepresentation, exposedL, exposedR,
          DynamicOptimality.BST.toRaw, Auxiliary.map, root.2.1] using
          Alphabet.rearranges alphabet (supported_rearranges joinPath)
      have keys : inorder (.node exposedL key exposedR) =
          inorder (Auxiliary.map alphabet (DynamicOptimality.BST.toRaw (.node l r))) := by
        simpa only [DynamicOptimality.BST.toRaw, Auxiliary.map, root.2.1] using
          Alphabet.indexed_inorder_eq (.node split.actualLeft split.actualRight) (.node l r) alphabet
      refine ⟨result, 18 * split.work + (1 + 18 * joinWork), rfl, ?_, ?_⟩
      · have first := CommonForest.Trace.single (CommonForest.Step.prepare (access := RootAccess) firstPath)
        have middle := CommonForest.Trace.single (CommonForest.Step.search
          (prepare := Rearranges) (RootAccess.root exposedL key exposedR))
        have last := CommonForest.Trace.single (CommonForest.Step.prepare (access := RootAccess) lastPath)
        simpa only [List.nil_append, List.append_nil, keys, State.actual, State.source] using
          first.append (middle.append last)
      · have splitBound := split.amortized
        change 18 * split.work + (1 + 18 * joinWork) + 18 * finalRep.potential ≤
          18 * representation.potential + 4141
        dsimp [finalRep, joinWork]
        omega

end MultiSplay.SparseHeavy

namespace MultiSplay.SparseRib

open DynamicOptimality (RawTree)
open Splay.Tree (BST)
open TangoSquared.MTR.Tree (inorder)
open TangoSquared.Paper20261030.Auxiliary (Rearranges)
open CommonForest (RootAccess)

variable {α : Type*}

abbrev PhysicalTrace := @CommonForest.Trace α RootAccess Rearranges

theorem split_trace {capacity : Nat} (state : State capacity α)
    {left right : RawTree α} {key : α} (root : state.source = .node left key right) :
    ∃ a b : State capacity α, ∃ cost : Nat,
      a.source = left ∧ b.source = right ∧
      PhysicalTrace [state.actual] [.split (inorder left) key (inorder right)] [a.actual, b.actual] cost ∧
      cost + 18 * (a.potential + b.potential) ≤ 18 * state.potential + 8065 := by
  obtain ⟨a, b, work, leftEq, rightEq, path, bound, sizeEq⟩ := split_exists state root
  refine ⟨a, b, 18 * work + 1, leftEq, rightEq, ?_, by omega⟩
  have prepare := CommonForest.Trace.single (CommonForest.Step.prepare (access := RootAccess) path)
  have split := CommonForest.Trace.single (CommonForest.Step.split
    (prepare := Rearranges) (RootAccess.root a.actual key b.actual))
  simpa [a.inorder_eq, b.inorder_eq, leftEq, rightEq] using prepare.append split

theorem service_trace {capacity : Nat} (state : State capacity α)
    {left right : RawTree α} {key : α} (root : state.source = .node left key right) :
    ∃ result : State capacity α, ∃ cost : Nat,
      result.source = state.source ∧
      PhysicalTrace [state.actual] [.search (inorder state.source) key] [result.actual] cost ∧
      cost + 18 * result.potential ≤ 18 * state.potential + 16129 := by
  rcases state with ⟨⟨lower, upper, side, source, actual, representation, fits⟩, alphabet⟩
  cases source with
  | empty => simp [State.source, DynamicOptimality.BST.toRaw, Auxiliary.map] at root
  | node l r =>
      simp only [State.source, DynamicOptimality.BST.toRaw, Auxiliary.map,
        TangoSquared.MTR.Tree.node.injEq] at root
      obtain ⟨split⟩ := Rib.exists_split representation
      obtain ⟨target, finalRep, joinWork, joinPath, joinWorkBound, joinBound⟩ :=
        Splay.Accounting.OfflineConnectedSupport.RibRepresentation.exists_join side
          split.leftRep split.rightRep fits
      let result : State capacity α := ⟨.ofRepresentation finalRep fits, alphabet⟩
      let exposedL := Auxiliary.map alphabet (DynamicOptimality.BST.toRaw split.actualLeft)
      let exposedR := Auxiliary.map alphabet (DynamicOptimality.BST.toRaw split.actualRight)
      have firstPath : Rearranges (Auxiliary.map alphabet (DynamicOptimality.BST.toRaw actual))
          (.node exposedL key exposedR) (18 * split.work) := by
        simpa [DynamicOptimality.BST.toRaw, Auxiliary.map, root.2.1] using
          Alphabet.rearranges alphabet (supported_rearranges split.path)
      have lastPath : Rearranges (.node exposedL key exposedR) result.actual (18 * joinWork) := by
        simpa [result, State.actual, Rib.Component.ofRepresentation, exposedL, exposedR,
          DynamicOptimality.BST.toRaw, Auxiliary.map, root.2.1] using
          Alphabet.rearranges alphabet (supported_rearranges joinPath)
      have keys : inorder (.node exposedL key exposedR) =
          inorder (Auxiliary.map alphabet (DynamicOptimality.BST.toRaw (.node l r))) := by
        simpa only [DynamicOptimality.BST.toRaw, Auxiliary.map, root.2.1] using
          Alphabet.indexed_inorder_eq (.node split.actualLeft split.actualRight) (.node l r) alphabet
      refine ⟨result, 18 * split.work + (1 + 18 * joinWork), rfl, ?_, ?_⟩
      · have first := CommonForest.Trace.single (CommonForest.Step.prepare (access := RootAccess) firstPath)
        have middle := CommonForest.Trace.single (CommonForest.Step.search
          (prepare := Rearranges) (RootAccess.root exposedL key exposedR))
        have last := CommonForest.Trace.single (CommonForest.Step.prepare (access := RootAccess) lastPath)
        simpa only [List.nil_append, List.append_nil, keys, State.actual, State.source] using
          first.append (middle.append last)
      · have splitBound := split.amortized
        change 18 * split.work + (1 + 18 * joinWork) + 18 * finalRep.potential ≤
          18 * representation.potential + 16129
        omega

end MultiSplay.SparseRib
