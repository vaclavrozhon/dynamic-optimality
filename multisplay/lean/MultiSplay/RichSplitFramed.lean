import MultiSplay.RichSplitPlacement
import MultiSplay.RichRestrictionFrame
import MultiSplay.InterfaceSplitHistory

/-!
# Continuing either split component in the same global interface history

The two new roots are unassigned, and every unselected record is a proved
passive frame. Hence any subsequent local splay realization can be replayed
in the actual global history without restarting its block accounting.
-/

namespace MultiSplay.RichSplit

open Splay.Tree (BST)
open Splay.Rank (Snapshot)
open Splay.Lazy (State Block Element)
open Splay.Lazy.Canonical

variable {l r : Nat} {params : Splay.Interface.Parameters}

theorem retired_records {n : Nat} (source : State n) (boundary : InterfaceForest.SplitBoundary source.toInterface) :
    ∀ id : Fin source.blocks.length, ∃ block,
      boundary.final.block? id.val = some block ∧ block.creator = (source.blocks.get id).creator ∧
      (block.mode = .growing → (source.blocks.get id).mode = .growing) ∧
      block.elements.Sublist (source.blocks.get id).elements := by
  intro id
  exact ⟨boundary.record id.val (source.blocks.get id).toInterface,
    boundary.final_lookup _ _ (RichSplitBoundary.interface_lookup source id),
    boundary.record_creator _ _, boundary.record_growing _ _, boundary.record_elements _ _⟩

theorem left_separated (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr))
    (boundary : InterfaceForest.SplitBoundary source.toInterface)
    (leftEq : boundary.left = JoinIntervals.leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl))
    (rightEq : boundary.right = JoinIntervals.rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr))
    (leftCreator : boundary.growingLeftBlock.creator = JoinRanks.pivot l r)
    (rightCreator : boundary.growingRightBlock.creator = JoinRanks.pivot l r) :
    (leftPlacement left right sl sr source represented boundary leftEq rightEq leftCreator rightCreator).Separated := by
  apply RichRestriction.separated source _ (leftEmbedding left right sl sr source represented) represented.stable boundary.final
    (by simpa [State.toInterface] using boundary.final_blocks_length) (retired_records source boundary)
  · change JoinIntervals.leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl) ∉ boundary.final.allElements
    rw [← leftEq]
    exact (boundary.roots_unassigned represented.valid.1).1
  · rfl
  · intro i; rfl

theorem right_separated (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr))
    (boundary : InterfaceForest.SplitBoundary source.toInterface)
    (leftEq : boundary.left = JoinIntervals.leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl))
    (rightEq : boundary.right = JoinIntervals.rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr))
    (leftCreator : boundary.growingLeftBlock.creator = JoinRanks.pivot l r)
    (rightCreator : boundary.growingRightBlock.creator = JoinRanks.pivot l r) :
    (rightPlacement left right sl sr source represented boundary leftEq rightEq leftCreator rightCreator).Separated := by
  apply RichRestriction.separated source _ (rightEmbedding left right sl sr source represented) represented.stable boundary.final
    (by simpa [State.toInterface] using boundary.final_blocks_length) (retired_records source boundary)
  · change JoinIntervals.rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr) ∉ boundary.final.allElements
    rw [← rightEq]
    exact (boundary.roots_unassigned represented.valid.1).2
  · rfl
  · intro i; rfl

/-- Both outputs have a constructed passive frame inside the exact final state
of the same global trace. Each can immediately run any local interface history. -/
theorem exists_framed_split (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)) :
    ∃ boundary : InterfaceForest.SplitBoundary source.toInterface,
      Splay.Interface.Trace params source.toInterface boundary.word boundary.final ∧
      (leftState left right sl sr source represented).Represents params (Snapshot.ofTree left).withTruePriority sl ∧
      (rightState left right sl sr source represented).Represents params (Snapshot.ofTree right).withTruePriority sr ∧
      Nonempty (InterfaceFramedTrace.Framed params (leftState left right sl sr source represented).toInterface boundary.final) ∧
      Nonempty (InterfaceFramedTrace.Framed params (rightState left right sl sr source represented).toInterface boundary.final) ∧
      boundary.word.length ≤ 8 ∧ Splay.Interface.totalInserts boundary.word = 0 ∧
      Splay.Interface.totalIncreases boundary.word = 0 ∧ Splay.Interface.totalActivity boundary.word = 0 := by
  obtain ⟨boundary, leftEq, rightEq, leftCreator, rightCreator⟩ := RichSplitBoundary.exists_boundary left right sl sr source represented
  have execution := boundary.trace represented.valid.1
  have valid := InterfaceForest.trace_final_valid execution
  exact ⟨boundary, execution,
    left_represents left right sl sr source represented, right_represents left right sl sr source represented,
    ⟨(leftPlacement left right sl sr source represented boundary leftEq rightEq leftCreator rightCreator).framed
      (left_separated left right sl sr source represented boundary leftEq rightEq leftCreator rightCreator) valid⟩,
    ⟨(rightPlacement left right sl sr source represented boundary leftEq rightEq leftCreator rightCreator).framed
      (right_separated left right sl sr source represented boundary leftEq rightEq leftCreator rightCreator) valid⟩,
    boundary.word_length, boundary.inserts, boundary.increases, boundary.activity⟩

end MultiSplay.RichSplit
