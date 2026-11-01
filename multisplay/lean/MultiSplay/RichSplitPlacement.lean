import MultiSplay.RichSplit
import MultiSplay.InterfacePlacement

/-! # Exact placement of both split histories in the resulting global state -/

namespace MultiSplay.RichSplit

open Splay.Tree (BST)
open Splay.Rank (Snapshot)
open Splay.Lazy (State Block Element)
open Splay.Lazy.Canonical

variable {l r : Nat} {params : Splay.Interface.Parameters}

noncomputable def leftPlacement (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr))
    (boundary : InterfaceForest.SplitBoundary source.toInterface)
    (leftEq : boundary.left = JoinIntervals.leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl))
    (rightEq : boundary.right = JoinIntervals.rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr))
    (leftCreator : boundary.growingLeftBlock.creator = JoinRanks.pivot l r)
    (rightCreator : boundary.growingRightBlock.creator = JoinRanks.pivot l r) :
    InterfacePlacement.Placement (leftState left right sl sr source represented).toInterface boundary.final where
  element := JoinIntervals.leftEmbedding l r
  element_injective := RankEmbedding.external_injective _ _
  id := fun id => (RichRestriction.origin source _ (leftEmbedding left right sl sr source represented)
    ⟨id.val, by simpa [State.toInterface, leftState, rightState] using id.isLt⟩).val
  id_injective := by
    intro i j eq
    have same := RichRestriction.origin_injective source _ (leftEmbedding left right sl sr source represented) (Fin.ext eq)
    exact Fin.ext (congrArg (fun k : Fin (leftState left right sl sr source represented).blocks.length => k.val) same)
  lookup := by
    intro id
    let localId : Fin (leftState left right sl sr source represented).blocks.length := ⟨id.val, by simpa [State.toInterface, leftState, rightState] using id.isLt⟩
    let oldId := RichRestriction.origin source _ (leftEmbedding left right sl sr source represented) localId
    have inside := RichRestriction.origin_inside source _ (leftEmbedding left right sl sr source represented) localId
    have outside : (source.blocks.get oldId).owner ≠ JoinRanks.pivot l r := by
      obtain ⟨x, eq⟩ := inside
      exact fun same => JoinIntervals.left_ne_pivot l r x (eq.trans same)
    refine ⟨(source.blocks.get oldId).toInterface,
      retained_lookup left right sl sr source represented boundary leftEq rightEq leftCreator rightCreator oldId outside, ?_⟩
    have retained := RichRestriction.observable_retained source _ (leftEmbedding left right sl sr source represented) represented.stable localId
    simpa only [State.toInterface, List.get_eq_getElem, List.getElem_map, leftState, rightState, leftEmbedding, rightEmbedding, localId, oldId] using retained
  value := by
    intro x
    by_cases root : x = canonicalRoot (Snapshot.ofTree left).withTruePriority sl
    · subst x
      rw [← leftEq, boundary.final_left_value]
      simp [leftState, RichRestriction.state, State.toInterface, canonicalHeapView]
    · rw [boundary.final_other_value]
      · simp only [leftState, RichRestriction.state, State.toInterface, canonicalHeapView, root, if_false, leftEmbedding]
      · rw [leftEq]
        exact fun same => root ((RankEmbedding.external_injective _ _) same)
      · rw [rightEq]
        exact JoinIntervals.disjoint l r _ _

noncomputable def rightPlacement (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr))
    (boundary : InterfaceForest.SplitBoundary source.toInterface)
    (leftEq : boundary.left = JoinIntervals.leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl))
    (rightEq : boundary.right = JoinIntervals.rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr))
    (leftCreator : boundary.growingLeftBlock.creator = JoinRanks.pivot l r)
    (rightCreator : boundary.growingRightBlock.creator = JoinRanks.pivot l r) :
    InterfacePlacement.Placement (rightState left right sl sr source represented).toInterface boundary.final where
  element := JoinIntervals.rightEmbedding l r
  element_injective := RankEmbedding.external_injective _ _
  id := fun id => (RichRestriction.origin source _ (rightEmbedding left right sl sr source represented)
    ⟨id.val, by simpa [State.toInterface, leftState, rightState] using id.isLt⟩).val
  id_injective := by
    intro i j eq
    have same := RichRestriction.origin_injective source _ (rightEmbedding left right sl sr source represented) (Fin.ext eq)
    exact Fin.ext (congrArg (fun k : Fin (rightState left right sl sr source represented).blocks.length => k.val) same)
  lookup := by
    intro id
    let localId : Fin (rightState left right sl sr source represented).blocks.length := ⟨id.val, by simpa [State.toInterface, leftState, rightState] using id.isLt⟩
    let oldId := RichRestriction.origin source _ (rightEmbedding left right sl sr source represented) localId
    have inside := RichRestriction.origin_inside source _ (rightEmbedding left right sl sr source represented) localId
    have outside : (source.blocks.get oldId).owner ≠ JoinRanks.pivot l r := by
      obtain ⟨x, eq⟩ := inside
      exact fun same => JoinIntervals.right_ne_pivot l r x (eq.trans same)
    refine ⟨(source.blocks.get oldId).toInterface,
      retained_lookup left right sl sr source represented boundary leftEq rightEq leftCreator rightCreator oldId outside, ?_⟩
    have retained := RichRestriction.observable_retained source _ (rightEmbedding left right sl sr source represented) represented.stable localId
    simpa only [State.toInterface, List.get_eq_getElem, List.getElem_map, leftState, rightState, leftEmbedding, rightEmbedding, localId, oldId] using retained
  value := by
    intro x
    by_cases root : x = canonicalRoot (Snapshot.ofTree right).withTruePriority sr
    · subst x
      rw [← rightEq, boundary.final_right_value]
      simp [rightState, RichRestriction.state, State.toInterface, canonicalHeapView]
    · rw [boundary.final_other_value]
      · simp only [rightState, RichRestriction.state, State.toInterface, canonicalHeapView, root, if_false, rightEmbedding]
      · rw [leftEq]
        exact (JoinIntervals.disjoint l r _ _).symm
      · rw [rightEq]
        exact fun same => root ((RankEmbedding.external_injective _ _) same)

/-- A constructed common split, with both reusable rich representations and
placements in the same persistent strict-interface execution. -/
theorem exists_split (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)) :
    ∃ boundary : InterfaceForest.SplitBoundary source.toInterface,
      Splay.Interface.Trace params source.toInterface boundary.word boundary.final ∧
      (leftState left right sl sr source represented).Represents params (Snapshot.ofTree left).withTruePriority sl ∧
      (rightState left right sl sr source represented).Represents params (Snapshot.ofTree right).withTruePriority sr ∧
      Nonempty (InterfacePlacement.Placement (leftState left right sl sr source represented).toInterface boundary.final) ∧
      Nonempty (InterfacePlacement.Placement (rightState left right sl sr source represented).toInterface boundary.final) ∧
      boundary.word.length ≤ 8 ∧ Splay.Interface.totalInserts boundary.word = 0 ∧
      Splay.Interface.totalIncreases boundary.word = 0 ∧ Splay.Interface.totalActivity boundary.word = 0 := by
  obtain ⟨boundary, leftEq, rightEq, leftCreator, rightCreator⟩ := RichSplitBoundary.exists_boundary left right sl sr source represented
  exact ⟨boundary, boundary.trace represented.valid.1,
    left_represents left right sl sr source represented, right_represents left right sl sr source represented,
    ⟨leftPlacement left right sl sr source represented boundary leftEq rightEq leftCreator rightCreator⟩,
    ⟨rightPlacement left right sl sr source represented boundary leftEq rightEq leftCreator rightCreator⟩,
    boundary.word_length, boundary.inserts, boundary.increases, boundary.activity⟩

end MultiSplay.RichSplit
