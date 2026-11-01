import MultiSplay.RichSplitPacking

/-! # Exact shared-history representation after a common split -/

namespace MultiSplay.RichRestriction

open Splay.Lazy (State Block Element HeapView)

variable {n m : Nat} {params : Splay.Interface.Parameters}

theorem observable_selected_retired (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (stable : source.Stable params) (pivot : Element m) (outside : ∀ x, embedding.element x ≠ pivot) :
    ((state source small embedding).toInterface.blocks.map (InterfaceEmbedding.block embedding.element)).map InterfaceHistory.observable =
      ((source.blocks.filter (fun block => decide (block.owner ∈ Set.range embedding.element))).map
        (RichSplit.retiredRecord pivot)).map InterfaceHistory.observable := by
  classical
  rw [observable_selected source small embedding stable]
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro block member
  obtain ⟨x, same⟩ := of_decide_eq_true (List.mem_filter.mp member).2
  have notPivot : block.owner ≠ pivot := fun eq => outside x (same.trans eq)
  simp only [RichSplit.retiredRecord, notPivot, if_false]

end MultiSplay.RichRestriction

namespace MultiSplay.RichSplit

open Splay.Tree (BST)
open Splay.Rank (Snapshot)
open Splay.Lazy (State Block Element)
open Splay.Lazy.Canonical

variable {l r : Nat} {params : Splay.Interface.Parameters}

theorem packing_equivalent (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr))
    (boundary : InterfaceForest.SplitBoundary source.toInterface)
    (leftEq : boundary.left = JoinIntervals.leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl))
    (rightEq : boundary.right = JoinIntervals.rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr))
    (leftCreator : boundary.growingLeftBlock.creator = JoinRanks.pivot l r)
    (rightCreator : boundary.growingRightBlock.creator = JoinRanks.pivot l r) :
    InterfacePermutation.Equivalent
      (InterfacePacking.pack (archive source (JoinRanks.pivot l r))
        [leftComponent left right sl sr source represented, rightComponent left right sl sr source represented])
      boundary.final := by
  constructor
  · have leftBlocks := RichRestriction.observable_selected_retired source _
      (leftEmbedding left right sl sr source represented) represented.stable (JoinRanks.pivot l r) (JoinIntervals.left_ne_pivot l r)
    have rightBlocks := RichRestriction.observable_selected_retired source _
      (rightEmbedding left right sl sr source represented) represented.stable (JoinRanks.pivot l r) (JoinIntervals.right_ne_pivot l r)
    change (((leftState left right sl sr source represented).toInterface.blocks.map (InterfaceEmbedding.block (JoinIntervals.leftEmbedding l r))).map InterfaceHistory.observable) = _ at leftBlocks
    change (((rightState left right sl sr source represented).toInterface.blocks.map (InterfaceEmbedding.block (JoinIntervals.rightEmbedding l r))).map InterfaceHistory.observable) = _ at rightBlocks
    simp only [InterfacePacking.pack, InterfacePrefix.state, List.map_append, leftComponent, rightComponent]
    rw [leftBlocks, rightBlocks, final_blocks left right sl sr source represented boundary leftEq rightEq leftCreator rightCreator]
    convert (owner_partition (l := l) (r := r) source).map
      (fun block => InterfaceHistory.observable (retiredRecord (JoinRanks.pivot l r) block)) using 1 <;>
      simp [archive, leftEmbedding, rightEmbedding, List.map_map, List.append_assoc, Function.comp_def]
  · funext x
    change (InterfacePrefix.state (JoinIntervals.leftEmbedding l r)
      (InterfacePrefix.state (JoinIntervals.rightEmbedding l r) (archive source (JoinRanks.pivot l r))
        (rightState left right sl sr source represented).toInterface)
      (leftState left right sl sr source represented).toInterface).value x = boundary.final.value x
    rcases JoinIntervals.cases_element l r x with ⟨x, rfl⟩ | rfl | ⟨x, rfl⟩
    · rw [InterfacePrefix.value_image _ (RankEmbedding.external_injective _ _)]
      exact ((leftPlacement left right sl sr source represented boundary leftEq rightEq leftCreator rightCreator).value x).symm
    · rw [InterfacePrefix.value_outside _ _ _ _ (by rintro ⟨x, same⟩; exact JoinIntervals.left_ne_pivot l r x same),
        InterfacePrefix.value_outside _ _ _ _ (by rintro ⟨x, same⟩; exact JoinIntervals.right_ne_pivot l r x same)]
      have root : source.view.root = JoinRanks.pivot l r := by
        rw [represented.view_eq]
        change canonicalRoot _ _ = _
        rw [(JoinPriority.structure_eq (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree sl sr)).1]
        exact JoinIntervals.root_eq left right sl sr
      have neutral := represented.valuesRealizeGaps.1
      rw [root] at neutral
      rw [boundary.final_other_value]
      · exact neutral.symm
      · rw [leftEq]
        exact (JoinIntervals.left_ne_pivot l r _).symm
      · rw [rightEq]
        exact (JoinIntervals.right_ne_pivot l r _).symm
    · rw [InterfacePrefix.value_outside _ _ _ _ (by rintro ⟨y, same⟩; exact JoinIntervals.disjoint l r y x same),
        InterfacePrefix.value_image _ (RankEmbedding.external_injective _ _)]
      exact ((rightPlacement left right sl sr source represented boundary leftEq rightEq leftCreator rightCreator).value x).symm

/-- The actual final history is exactly the two restricted histories plus the
passive retired archive, up to harmless proof-local naming of records. -/
theorem exists_packed_split (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)) :
    ∃ boundary : InterfaceForest.SplitBoundary source.toInterface,
      Splay.Interface.Trace params source.toInterface boundary.word boundary.final ∧
      InterfacePermutation.Equivalent
        (InterfacePacking.pack (archive source (JoinRanks.pivot l r))
          [leftComponent left right sl sr source represented, rightComponent left right sl sr source represented])
        boundary.final ∧ boundary.word.length ≤ 8 := by
  obtain ⟨boundary, leftEq, rightEq, leftCreator, rightCreator⟩ := RichSplitBoundary.exists_boundary left right sl sr source represented
  exact ⟨boundary, boundary.trace represented.valid.1,
    packing_equivalent left right sl sr source represented boundary leftEq rightEq leftCreator rightCreator, boundary.word_length⟩

end MultiSplay.RichSplit
