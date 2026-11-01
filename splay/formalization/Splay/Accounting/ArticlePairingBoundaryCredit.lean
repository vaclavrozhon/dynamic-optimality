import Splay.Accounting.ArticleBoundaryPairCount
import Splay.Accounting.ArticleBoundaryPhaseCredit
import Splay.Accounting.BoundaryChargeCover
import Splay.Accounting.ArticlePairingStageCounts

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

namespace ArticlePairingStage

variable {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
  {before : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
  (stage : ArticlePairingStage params snapshot before key kinds initial)

def boundaryMatching : List (Interface.Pairing n) :=
  stage.boundary.firstAllocation.matching ++ stage.boundary.secondAllocation.matching

noncomputable def preparedSmall (element : Interface.Element n) : Bool := by
  classical
  exact decide (∃ (id : Interface.BlockId) (source : Lazy.Block n),
    stage.preparation.final.blocks[id]? = some source ∧ source.mode = .shrinking ∧
      element ∈ source.elements ∧ source.elements.length ≤ 12)

theorem boundaryMatching_length : stage.boundaryMatching.length = 2 * stage.boundaryCount := by
  have first := stage.boundary.firstAllocation.agreement.length_eq
  have second := stage.boundary.secondAllocation.agreement.length_eq
  simp only [boundaryMatching, List.length_append, boundaryCount]
  omega

theorem boundary_source {pairing : Interface.Pairing n} (member : pairing ∈ stage.boundaryMatching) :
    ∃ (id : Interface.BlockId) (source : Lazy.Block n),
      stage.preparation.final.blocks[id]? = some source ∧ source.mode = .shrinking ∧
        pairing.loser ∈ source.elements ∧ source.owner = valuePos key := by
  have distinct := stage.allBatches.filtered_groups_nodup (zigZigDoubleGroupIndices_nodup kinds 0)
    (fun row => decide (row ∉ stage.preparation.internalRows stage.allBatches
      (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero))
  have parent : canonicalParent snapshot before pairing.loser = some (valuePos key) := by
    rcases List.mem_append.mp member with member | member
    · exact (stage.boundary.firstAllocation.agreement.root_parents distinct key.isLt stage.rankZero member).2
    · exact (stage.boundary.secondAllocation.agreement.root_parents distinct key.isLt stage.rankZero member).2
  obtain ⟨id, source, found, shrinking, inside⟩ := stage.preparation.rootChild_shrinking parent
  have placed := (stage.preparation.represents.valid.2 source (List.mem_of_getElem? found)).parent_eq inside
  rw [stage.preparation.represents.view_parent_eq, parent] at placed
  exact ⟨id, source, found, shrinking, inside, (Option.some.inj placed).symm⟩

theorem workItem_spec
    {item : ArticleAdmissibleSourceWorkItem key.val snapshot before params stage.preparation.final}
    (member : item ∈ stage.preparation.admissibleWorklist stage.allBatches
      (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero) :
    item.source.owner = valuePos key ∧ item.sourceId ≠ stage.preparation.leftId ∧
      item.sourceId ≠ stage.preparation.rightId ∧
      stage.preparation.SourceAdmissible stage.allBatches
        ⟨item.sourceId, (List.getElem?_eq_some_iff.mp item.sourceFound).1⟩ := by
  obtain ⟨index, _, equal⟩ := List.mem_map.mp member
  subst item
  have chosen := (stage.preparation.admissibleItem stage.allBatches
    (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero index).property
  have selected := (stage.preparation.mem_admissibleIndices stage.allBatches index.val).mp index.property
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [chosen.2.1]
    exact selected.1
  · rw [chosen.1]
    exact selected.2.2.1
  · rw [chosen.1]
    exact selected.2.2.2.1
  · have indexEq : (⟨_, (List.getElem?_eq_some_iff.mp
        (stage.preparation.admissibleItem stage.allBatches
          (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero index).val.sourceFound).1⟩ :
        Fin stage.preparation.final.blocks.length) = index.val := Fin.ext chosen.1
    rw [indexEq]
    exact selected

theorem boundary_small_or_workItem
    {after : BST 0 n} {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (exempt : 2 ≤ params.exemptPasses) (fraction : 8 * params.matchingNumerator ≤ params.matchingDenominator)
    (unbroken : PassedBlocksUnbroken snapshot before stage.preparation.final)
    {pairing : Interface.Pairing n} (member : pairing ∈ stage.boundaryMatching) :
    stage.preparedSmall pairing.loser = true ∨
      ∃ item ∈ stage.preparation.admissibleWorklist stage.allBatches
        (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero,
        pairing.loser ∈ item.source.elements := by
  classical
  obtain ⟨id, source, found, shrinking, inside, owner⟩ := stage.boundary_source member
  by_cases small : source.elements.length ≤ 12
  · left
    exact decide_eq_true ⟨id, source, found, shrinking, inside, small⟩
  have notLeft : id ≠ stage.preparation.leftId := by
    intro equal
    rw [equal, stage.preparation.leftFound] at found
    have sourceEq := Option.some.inj found
    simp [← sourceEq, stage.preparation.leftElements] at small
  have notRight : id ≠ stage.preparation.rightId := by
    intro equal
    rw [equal, stage.preparation.rightFound] at found
    have sourceEq := Option.some.inj found
    simp [← sourceEq, stage.preparation.rightElements] at small
  have admissible := stage.preparation.large_source_admissible transcript stage.rankZero stage.allBatches
    exempt fraction unbroken found owner shrinking notLeft notRight (by omega)
  obtain ⟨item, itemMember, _, sourceEq, _⟩ := stage.preparation.admissibleWorklist_complete stage.allBatches
    (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero _ admissible
  have locatedEq : (stage.preparation.locatedSource
      ⟨id, (List.getElem?_eq_some_iff.mp found).1⟩).block = source :=
    (List.getElem?_eq_some_iff.mp found).2
  exact Or.inr ⟨item, itemMember, by rw [sourceEq, locatedEq]; exact inside⟩

theorem smallCredit {cutoff : ℕ} :
    Interface.boundaryCredit cutoff stage.final.toInterface +
      (stage.boundaryMatching.filter fun pairing => stage.preparedSmall pairing.loser).length ≤
        Interface.boundaryCredit cutoff stage.internal.chain.final.toInterface := by
  classical
  apply stage.boundary.smallCredit stage.preparedSmall
  intro pairing member selected
  obtain ⟨oldId, old, oldFound, _, oldMember, oldSmall⟩ := of_decide_eq_true selected
  have nextExists : ∃ (id : Interface.BlockId) (source : Lazy.Block n),
      stage.internal.chain.final.blocks[id]? = some source ∧ source.mode = .shrinking ∧
        pairing.loser ∈ source.elements := by
    rcases List.mem_append.mp member with member | member
    · exact stage.boundary.first.sources pairing member
    · exact stage.preparation.boundaryPair_shrinking stage.allBatches
        (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero stage.internal
        stage.boundary.secondAllocation.agreement member
  obtain ⟨nextId, next, nextFound, shrinking, nextMember⟩ := nextExists
  have sublist := stage.internal.shrinkingRefines.elements_sublist_of_common_element
    stage.preparation.represents.valid oldFound oldMember nextFound shrinking nextMember
  exact ⟨nextId, next, nextFound, shrinking, nextMember, sublist.length_le.trans oldSmall⟩

end ArticlePairingStage
end Splay.Accounting
