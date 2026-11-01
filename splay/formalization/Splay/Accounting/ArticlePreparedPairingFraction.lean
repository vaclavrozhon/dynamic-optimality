import Splay.Accounting.ArticlePreparedWorklist

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

/-- The actual filter retains at least every complete group certified by
the geometric fraction proof. The endpoint choices need not be identified
with a separately chosen realization. -/
theorem ArticleInternalPairingFractionCertificate.filtered_length_bound
    {n : ℕ} {snapshot : Snapshot n} {before : BST 0 n} {key : Fin n}
    {kinds : List SplayStepKind} {elements : List (Element n)}
    (certificate : ArticleInternalPairingFractionCertificate kinds elements
      (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key.val 0))
    (allBatches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key.val
      (zigZigDoubleGroupIndices kinds 0)) :
    elements.length ≤ 4 * (ArticleSourcePairings.filtered elements allBatches).rows.length + 6 := by
  have subset : certificate.fraction.groups ⊆
      (ArticleSourcePairings.filtered elements allBatches).rows.map Prod.fst := by
    intro group groupMember
    have allMember := mem_zigZigDoubleGroupIndices_zero_of_doubleStepFlags_eq_true
      (certificate.fraction.internal_zigZig group groupMember)
    obtain ⟨row, rowMember, rowGroup⟩ := List.mem_map.mp (allBatches.groups_perm.mem_iff.mpr allMember)
    refine List.mem_map.mpr ⟨row, List.mem_filter.mpr ⟨rowMember, ?_⟩, rowGroup⟩
    apply decide_eq_true
    intro element inside
    obtain ⟨extra, winner, firstLoser, secondLoser, candidates, firstEq, secondEq, chunkEq,
      _, _, _, _, candidatePerm, _, _⟩ := allBatches.aligned row rowMember
    have candidateMember : element ∈ candidates := by
      apply candidatePerm.mem_iff.mpr
      rw [firstEq, secondEq] at inside
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at inside ⊢
      tauto
    apply certificate.mem_of_mem_groupChunk groupMember
    rw [← rowGroup, chunkEq]
    exact List.mem_cons_of_mem _ candidateMember
  have groupsBound : certificate.fraction.groups.length ≤
      ((ArticleSourcePairings.filtered elements allBatches).rows.map Prod.fst).length := by
    calc
      _ = certificate.fraction.groups.toFinset.card := (List.toFinset_card_of_nodup certificate.fraction.groups_nodup).symm
      _ ≤ ((ArticleSourcePairings.filtered elements allBatches).rows.map Prod.fst).toFinset.card :=
        Finset.card_le_card (fun group member => List.mem_toFinset.mpr (subset (List.mem_toFinset.mp member)))
      _ ≤ _ := List.toFinset_card_le _
  have bound := certificate.fraction.length_bound
  simp only [List.length_map] at groupsBound
  simp only [List.length_reverse] at bound
  omega

/-- Quantitative fraction estimate for each actual prepared unbroken
source, with its implemented row filter rather than an existential batch. -/
theorem ArticleRequestPreparation.unbroken_source_fraction {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n} {before after : BST 0 n} {key : Fin n} {initial : Lazy.State n}
    {kinds : List SplayStepKind} {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (preparation : ArticleRequestPreparation params snapshot before key initial)
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (rankZero : snapshot.rank (valuePos key) = 0)
    (allBatches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key.val
      (zigZigDoubleGroupIndices kinds 0))
    {id : Interface.BlockId} {source : Block n}
    (found : preparation.final.blocks[id]? = some source) (owner : source.owner = valuePos key)
    (notLeft : id ≠ preparation.leftId) (notRight : id ≠ preparation.rightId)
    (unbroken : canonicalBlockCrossSideUnbroken snapshot before source) :
    source.elements.length ≤ 4 * (ArticleSourcePairings.filtered source.elements allBatches).rows.length + 6 := by
  obtain ⟨removed, erased, fresh⟩ := exists_articleIsolatedBoundariesWitness snapshot before key rankZero
    preparation.represents preparation.leftFound preparation.leftElements
    preparation.rightFound preparation.rightElements found owner notLeft notRight
  have segment := (preparation.represents.valid.2 source (List.mem_of_getElem? found)).isSegment
    |>.foldl_erase_ambient_of_fresh fresh
  rw [← erased] at segment
  obtain ⟨certificate⟩ := article_internalPairingFractionCertificate snapshot transcript key.isLt rankZero source owner unbroken segment
  exact certificate.filtered_length_bound allBatches

end Splay.Accounting
