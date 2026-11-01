import Splay.Accounting.ArticlePreparedPairingFraction
import Splay.Accounting.ArticlePairingRowPartition
import Splay.Accounting.ArticleTemporaryUnbroken

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

/-- Every prepared source of size at least twelve is selected: a new source
uses its two exempt passes; an older one uses its proved unbroken geometry. -/
theorem ArticleRequestPreparation.large_source_admissible {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n} {before after : BST 0 n} {key : Fin n} {initial : Lazy.State n}
    {kinds : List SplayStepKind} {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (preparation : ArticleRequestPreparation params snapshot before key initial)
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (rankZero : snapshot.rank (valuePos key) = 0)
    (allBatches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key.val
      (zigZigDoubleGroupIndices kinds 0))
    (exempt : 2 ≤ params.exemptPasses) (fraction : 8 * params.matchingNumerator ≤ params.matchingDenominator)
    (unbroken : PassedBlocksUnbroken snapshot before preparation.final)
    {id : Interface.BlockId} {source : Block n}
    (found : preparation.final.blocks[id]? = some source) (owner : source.owner = valuePos key)
    (shrinking : source.mode = .shrinking) (notLeft : id ≠ preparation.leftId) (notRight : id ≠ preparation.rightId)
    (large : 12 ≤ source.elements.length) :
    preparation.SourceAdmissible allBatches ⟨id, (List.getElem?_eq_some_iff.mp found).1⟩ := by
  have blockEq : (preparation.locatedSource ⟨id, (List.getElem?_eq_some_iff.mp found).1⟩).block = source :=
    (List.getElem?_eq_some_iff.mp found).2
  dsimp only [ArticleRequestPreparation.SourceAdmissible]
  rw [blockEq]
  refine ⟨owner, shrinking, notLeft, notRight, ?_⟩
  by_cases zero : source.passCount = 0
  · exact Or.inl (by omega)
  · right
    have sizeBound := preparation.unbroken_source_fraction transcript rankZero allBatches found owner notLeft notRight
      (unbroken source (List.mem_of_getElem? found) zero)
    have eight : source.elements.length ≤ 8 * (ArticleSourcePairings.filtered source.elements allBatches).rows.length := by omega
    calc
      params.matchingNumerator * source.elements.length ≤
          params.matchingNumerator * (8 * (ArticleSourcePairings.filtered source.elements allBatches).rows.length) :=
        Nat.mul_le_mul_left _ eight
      _ = (8 * params.matchingNumerator) * (ArticleSourcePairings.filtered source.elements allBatches).rows.length := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ fraction

/-- A boundary row cannot be wholly contained in any selected source: the
implemented worklist already assigns that exact row to an internal macro. -/
theorem ArticleRequestPreparation.boundaryRow_not_contained_of_admissible {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n} {before : BST 0 n} {key : Fin n} {initial : Lazy.State n}
    (preparation : ArticleRequestPreparation params snapshot before key initial) {groups : List ℕ}
    (allBatches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key.val groups)
    (distinct : groups.Nodup) (rankZero : snapshot.rank (valuePos key) = 0)
    (index : Fin preparation.final.blocks.length) (admissible : preparation.SourceAdmissible allBatches index)
    {row : ℕ × (List (External n) × List (External n))}
    (member : row ∈ (preparation.boundaryBatches allBatches distinct rankZero).rows) :
    ¬ ∀ element ∈ row.2.1 ++ row.2.2, element ∈ (preparation.locatedSource index).block.elements := by
  intro contained
  have boundary := (preparation.mem_boundaryBatches allBatches distinct rankZero row).mp member
  obtain ⟨item, itemMember, _, _, rows⟩ := preparation.admissibleWorklist_complete allBatches distinct rankZero index admissible
  apply boundary.2
  exact List.mem_flatMap.mpr ⟨item, itemMember, by
    rw [rows]
    exact List.mem_filter.mpr ⟨boundary.1, decide_eq_true contained⟩⟩

end Splay.Accounting
