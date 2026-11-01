import Splay.Accounting.ArticlePairingPassRealizer
import Splay.Lazy.ValueTrace

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST
open ArticleBatchDestinationAllocation

private theorem totalInserts_append
    {n : ℕ} (first second : List (Interface.Operation n)) :
    Interface.totalInserts (first ++ second) =
      Interface.totalInserts first + Interface.totalInserts second := by
  simp [Interface.totalInserts]

private theorem totalIncreases_append
    {n : ℕ} (first second : List (Interface.Operation n)) :
    Interface.totalIncreases (first ++ second) =
      Interface.totalIncreases first + Interface.totalIncreases second := by
  simp [Interface.totalIncreases]

/-- Contracted value required after the loser is attached below the winner. -/
def articlePairingLoserTarget {n : ℕ} (view : Lazy.HeapView n)
    (pairing : Interface.Pairing n) : ℕ :=
  Analysis.contractedGap
    (view.rank pairing.loser - view.rank pairing.winner)

/-- The numeric target is exactly the contracted point gap in the zero-gap
growing destination after reparenting. -/
theorem BatchReparentedView.paired_transientContractedGap_eq_target
    {n : ℕ} {beforeView : Lazy.HeapView n}
    {matching : List (Interface.Pairing n)}
    (after : BatchReparentedView beforeView matching)
    {pairing : Interface.Pairing n} (pairingMember : pairing ∈ matching)
    (rankOrder : beforeView.rank pairing.winner <
      beforeView.rank pairing.loser) :
    Analysis.transientContractedGap
        (after.view.rawGap pairing.loser) 0 =
      articlePairingLoserTarget beforeView pairing := by
  unfold articlePairingLoserTarget Analysis.transientContractedGap
    Analysis.transientPointGap
  rw [after.paired_rawGap pairingMember]
  rw [show (0 : ℤ) = 0 by rfl, sub_zero]
  congr 1
  apply Int.ofNat_inj.mp
  rw [Int.toNat_of_nonneg (by omega), Nat.cast_sub rankOrder.le]

/-- Restore every paired loser, in matching order, to its new contracted gap. -/
def restoreArticlePairingLosers {n : ℕ} (view : Lazy.HeapView n) :
    Lazy.State n → List (Interface.Pairing n) → Lazy.State n
  | state, [] => state
  | state, pairing :: matching =>
      restoreArticlePairingLosers view
        (state.adjustValue pairing.loser
          (articlePairingLoserTarget view pairing)) matching

/-- Visible value-change events emitted by loser restoration. -/
def restoreArticlePairingLoserEvents {n : ℕ} (view : Lazy.HeapView n) :
    Lazy.State n → List (Interface.Pairing n) → List (Lazy.Event n)
  | _, [] => []
  | state, pairing :: matching =>
      state.adjustValueEvents pairing.loser
          (articlePairingLoserTarget view pairing) ++
        restoreArticlePairingLoserEvents view
          (state.adjustValue pairing.loser
            (articlePairingLoserTarget view pairing)) matching

@[simp]
theorem restoreArticlePairingLosers_blocks {n : ℕ}
    (view : Lazy.HeapView n) (state : Lazy.State n)
    (matching : List (Interface.Pairing n)) :
    (restoreArticlePairingLosers view state matching).blocks = state.blocks := by
  induction matching generalizing state with
  | nil => rfl
  | cons pairing matching ih =>
      rw [restoreArticlePairingLosers, ih]
      exact State.adjustValue_blocks state pairing.loser _

@[simp]
theorem restoreArticlePairingLosers_view {n : ℕ}
    (view : Lazy.HeapView n) (state : Lazy.State n)
    (matching : List (Interface.Pairing n)) :
    (restoreArticlePairingLosers view state matching).view = state.view := by
  induction matching generalizing state with
  | nil => rfl
  | cons pairing matching ih =>
      rw [restoreArticlePairingLosers, ih]
      exact State.adjustValue_view state pairing.loser _

@[simp]
theorem restoreArticlePairingLosers_append {n : ℕ}
    (view : Lazy.HeapView n) (state : Lazy.State n)
    (first second : List (Interface.Pairing n)) :
    restoreArticlePairingLosers view state (first ++ second) =
      restoreArticlePairingLosers view
        (restoreArticlePairingLosers view state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons pairing first ih =>
      simp only [List.cons_append, restoreArticlePairingLosers]
      exact ih (state := state.adjustValue pairing.loser
        (articlePairingLoserTarget view pairing))

/-- Loser restoration depends on the supplied heap view only through ranks. -/
theorem restoreArticlePairingLosers_eq_of_rank_eq {n : ℕ}
    {firstView secondView : Lazy.HeapView n}
    (rankEq : firstView.rank = secondView.rank)
    (state : Lazy.State n) (matching : List (Interface.Pairing n)) :
    restoreArticlePairingLosers firstView state matching =
      restoreArticlePairingLosers secondView state matching := by
  induction matching generalizing state with
  | nil => rfl
  | cons pairing matching ih =>
      have targetEq : articlePairingLoserTarget firstView pairing =
          articlePairingLoserTarget secondView pairing := by
        simp [articlePairingLoserTarget, rankEq]
      simp only [restoreArticlePairingLosers]
      rw [targetEq]
      exact ih (state := state.adjustValue pairing.loser
        (articlePairingLoserTarget secondView pairing))

/-- Pointwise-equal input values remain equal after the same loser targets
are restored; block and heap-view fields are irrelevant to this statement. -/
theorem restoreArticlePairingLosers_value_congr {n : ℕ}
    (view : Lazy.HeapView n) {first second : Lazy.State n}
    (valueEq : first.value = second.value)
    (matching : List (Interface.Pairing n)) :
    (restoreArticlePairingLosers view first matching).value =
      (restoreArticlePairingLosers view second matching).value := by
  induction matching generalizing first second with
  | nil => exact valueEq
  | cons pairing matching ih =>
      apply ih
      funext element
      by_cases equal : element = pairing.loser
      · subst element
        simp [articlePairingLoserTarget, Analysis.contractedGap]
      · rw [State.adjustValue_value_of_ne first equal,
          State.adjustValue_value_of_ne second equal]
        exact congrFun valueEq element

/-- Positive bounded loser targets give a legal rich restoration trace. -/
theorem restoreArticlePairingLosers_trace
    {n : ℕ} {params : Interface.Parameters}
    (view : Lazy.HeapView n) (state : Lazy.State n)
    (matching : List (Interface.Pairing n))
    (valid : state.Valid params)
    (positive : ∀ pairing ∈ matching,
      1 ≤ articlePairingLoserTarget view pairing)
    (bounded : ∀ pairing ∈ matching,
      articlePairingLoserTarget view pairing ≤ params.valueBound) :
    Trace params state
      (restoreArticlePairingLoserEvents view state matching)
      (restoreArticlePairingLosers view state matching) := by
  induction matching generalizing state with
  | nil =>
      exact Trace.nil valid
  | cons pairing matching ih =>
      have headPositive := positive pairing (by simp)
      have headBounded := bounded pairing (by simp)
      have headTrace := state.adjustValue_trace pairing.loser
        (articlePairingLoserTarget view pairing) valid headPositive headBounded
      have tailTrace := ih (state := state.adjustValue pairing.loser
          (articlePairingLoserTarget view pairing)) headTrace.final_valid
        (by
          intro candidate candidateMember
          exact positive candidate (by simp [candidateMember]))
        (by
          intro candidate candidateMember
          exact bounded candidate (by simp [candidateMember]))
      simpa [restoreArticlePairingLoserEvents,
        restoreArticlePairingLosers] using headTrace.append tailTrace

/-- Restoring losers never inserts an element. -/
theorem totalInserts_restoreArticlePairingLoserEvents_eq_zero
    {n : ℕ} (view : Lazy.HeapView n) (state : Lazy.State n)
    (matching : List (Interface.Pairing n)) :
    Interface.totalInserts
        (eraseOperations
          (restoreArticlePairingLoserEvents view state matching)) = 0 := by
  induction matching generalizing state with
  | nil => simp [restoreArticlePairingLoserEvents, eraseOperations,
      Interface.totalInserts]
  | cons pairing matching ih =>
      rw [restoreArticlePairingLoserEvents, eraseOperations_append,
        totalInserts_append,
        State.totalInserts_adjustValueEvents, ih]

/-- Earlier restorations do not alter a later distinct loser. -/
theorem restoreArticlePairingLosers_value_of_not_mem_losers
    {n : ℕ} (view : Lazy.HeapView n) (state : Lazy.State n)
    (matching : List (Interface.Pairing n))
    {element : Interface.Element n}
    (notMember : element ∉ Interface.pairingLosers matching) :
    (restoreArticlePairingLosers view state matching).value element =
      state.value element := by
  induction matching generalizing state with
  | nil => rfl
  | cons pairing matching ih =>
      have parts : element ≠ pairing.loser ∧
          element ∉ Interface.pairingLosers matching := by
        simpa [Interface.pairingLosers] using notMember
      rw [restoreArticlePairingLosers,
        ih (state := state.adjustValue pairing.loser
          (articlePairingLoserTarget view pairing)) parts.2]
      exact State.adjustValue_value_of_ne state parts.1 _

/-- With distinct losers, every restored loser has exactly its own target. -/
theorem restoreArticlePairingLosers_value_loser
    {n : ℕ} (view : Lazy.HeapView n) (state : Lazy.State n)
    {matching : List (Interface.Pairing n)}
    (losersNodup : (Interface.pairingLosers matching).Nodup)
    {pairing : Interface.Pairing n} (pairingMember : pairing ∈ matching)
    (positive : 1 ≤ articlePairingLoserTarget view pairing) :
    (restoreArticlePairingLosers view state matching).value pairing.loser =
      articlePairingLoserTarget view pairing := by
  induction matching generalizing state with
  | nil => simp at pairingMember
  | cons head matching ih =>
      have nodupParts : head.loser ∉ Interface.pairingLosers matching ∧
          (Interface.pairingLosers matching).Nodup := by
        simpa [Interface.pairingLosers] using losersNodup
      rcases List.mem_cons.mp pairingMember with rfl | tailMember
      · rw [restoreArticlePairingLosers,
          restoreArticlePairingLosers_value_of_not_mem_losers]
        · exact State.adjustValue_value_self state _ _ positive
        · exact nodupParts.1
      · exact ih (state := state.adjustValue head.loser
          (articlePairingLoserTarget view head)) nodupParts.2
          tailMember

/-- If every target is no larger than its original loser value and losers are
distinct, the restoration suffix contains decreases only. -/
theorem totalIncreases_restoreArticlePairingLoserEvents_eq_zero
    {n : ℕ} (view : Lazy.HeapView n) (state : Lazy.State n)
    {matching : List (Interface.Pairing n)}
    (losersNodup : (Interface.pairingLosers matching).Nodup)
    (targetLe : ∀ pairing ∈ matching,
      articlePairingLoserTarget view pairing ≤ state.value pairing.loser) :
    Interface.totalIncreases
        (eraseOperations
          (restoreArticlePairingLoserEvents view state matching)) = 0 := by
  induction matching generalizing state with
  | nil => simp [restoreArticlePairingLoserEvents, eraseOperations,
      Interface.totalIncreases]
  | cons pairing matching ih =>
      have nodupParts : pairing.loser ∉ Interface.pairingLosers matching ∧
          (Interface.pairingLosers matching).Nodup := by
        simpa [Interface.pairingLosers] using losersNodup
      have headLe := targetLe pairing (by simp)
      have tailLe : ∀ candidate ∈ matching,
          articlePairingLoserTarget view candidate ≤
            (state.adjustValue pairing.loser
              (articlePairingLoserTarget view pairing)).value
                candidate.loser := by
        intro candidate candidateMember
        have different : candidate.loser ≠ pairing.loser := by
          intro equal
          apply nodupParts.1
          exact List.mem_map.mpr ⟨candidate, candidateMember, equal⟩
        rw [State.adjustValue_value_of_ne state different]
        exact targetLe candidate (by simp [candidateMember])
      rw [restoreArticlePairingLoserEvents, eraseOperations_append,
        totalIncreases_append]
      have headZero : Interface.totalIncreases
          (eraseOperations
            (state.adjustValueEvents pairing.loser
              (articlePairingLoserTarget view pairing))) = 0 := by
        simp [State.eraseOperations_adjustValueEvents, headLe,
          Interface.totalIncreases, Interface.Operation.increaseCount]
      rw [headZero, ih (state := state.adjustValue pairing.loser
        (articlePairingLoserTarget view pairing)) nodupParts.2 tailLe]

/-- Semantic endpoint of one article pairing batch.  If the pass uses the
unchanged source interval gap and all pre-existing values have been restored,
then restoring the paired losers establishes exact contracted-gap values in
the source remainder, every growing destination, and every untouched block. -/
theorem ArticleBatchDestinationAllocation.valuesRealizeGaps_after_loserRestoration
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ} {phase : PairingPhase}
    {batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups}
    {params : Interface.Parameters} {state base : Lazy.State n}
    (allocation : ArticleBatchDestinationAllocation phase batches state)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (geometric : GeometricMatchingValid state sourceId source
      allocation.matching)
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    (after : BatchReparentedView state.view allocation.matching)
    (baseBlocks : base.blocks = Lazy.Block.passBlocks state.blocks sourceId
      source allocation.matching source.intervalGap)
    (baseView : base.view = after.view)
    (baseValue : base.value = state.value)
    (rankOrder : ∀ pairing ∈ allocation.matching,
      state.view.rank pairing.winner < state.view.rank pairing.loser) :
    (restoreArticlePairingLosers state.view base allocation.matching)
      |>.ValuesRealizeGaps := by
  classical
  let final := restoreArticlePairingLosers state.view base allocation.matching
  have finalBlocks : final.blocks =
      Lazy.Block.passBlocks state.blocks sourceId source allocation.matching
        source.intervalGap := by
    simp [final, baseBlocks]
  have finalView : final.view = after.view := by
    simp [final, baseView]
  have sourceMember : source ∈ state.blocks :=
    List.mem_of_getElem? sourceFound
  have sourceNodup : source.elements.Nodup := by
    have sourceInterfaceFound : state.toInterface.block? sourceId =
        some source.toInterface := by
      unfold Interface.State.block? Lazy.State.toInterface
      simpa using congrArg (Option.map Lazy.Block.toInterface) sourceFound
    have interfaceNodup :=
      valid.toInterface.block_elements_nodup sourceInterfaceFound
    change source.elements.Nodup at interfaceNodup
    exact interfaceNodup
  have losersNodup :
      (Interface.pairingLosers allocation.matching).Nodup :=
    Interface.pairingLosers_nodup geometric.2.1
  have positive : ∀ pairing ∈ allocation.matching,
      1 ≤ articlePairingLoserTarget state.view pairing := by
    intro pairing pairingMember
    simp [articlePairingLoserTarget, Analysis.contractedGap]
  have notLoser_of_mem_nonSource :
      ∀ {blockId : Interface.BlockId} {block : Lazy.Block n},
        state.blocks[blockId]? = some block → blockId ≠ sourceId →
          ∀ {element}, element ∈ block.elements →
            element ∉ Interface.pairingLosers allocation.matching := by
    intro blockId block blockFound blockNeSource element elementMember
      loserMember
    obtain ⟨pairing, pairingMember, loserEq⟩ :=
      List.mem_map.mp (by
        simpa only [Interface.pairingLosers] using loserMember)
    have loserSource :=
      BatchReparentedView.loser_mem_source geometric pairingMember
    have idsEq := valid.blockId_eq_of_element_mem blockFound elementMember
      sourceFound (by simpa [loserEq] using loserSource)
    exact blockNeSource idsEq
  change final.ValuesRealizeGaps
  constructor
  · rw [finalView, after.root_eq]
    rw [restoreArticlePairingLosers_value_of_not_mem_losers]
    · rw [baseValue]
      exact values.1
    · intro rootLoser
      obtain ⟨pairing, pairingMember, loserEq⟩ :=
        List.mem_map.mp (by
          simpa only [Interface.pairingLosers] using rootLoser)
      apply valid.root_not_mem
      exact State.mem_allElements_iff.mpr
        ⟨source, sourceMember, by
          simpa [loserEq] using
            BatchReparentedView.loser_mem_source geometric pairingMember⟩
  · intro block blockMember element elementMember
    have passBlockMember : block ∈
        Lazy.Block.passBlocks state.blocks sourceId source
          allocation.matching source.intervalGap := by
      rw [← finalBlocks]
      exact blockMember
    obtain ⟨blockId, blockFound⟩ :=
      List.mem_iff_getElem?.mp passBlockMember
    by_cases blockIsSource : blockId = sourceId
    · subst blockId
      have expectedFound := Lazy.Block.passBlocks_source_getElem?
        state.blocks sourceId source allocation.matching source.intervalGap
        sourceFound (by
          intro pairing pairingMember
          exact (geometric.2.2.2 pairing pairingMember).2.1)
      have blockEq : block = source.afterPassSource allocation.matching
          source.intervalGap :=
        Option.some.inj (blockFound.symm.trans expectedFound)
      subst block
      have remainderMember : element ∈
          Interface.removeLosers source.elements allocation.matching := by
        simpa [Lazy.Block.afterPassSource] using elementMember
      have remainderFacts : element ∈ source.elements ∧
          element ∉ Interface.pairingLosers allocation.matching := by
        rw [Interface.removeLosers_eq_foldl,
          List.mem_foldl_erase_iff sourceNodup] at remainderMember
        exact remainderMember
      rw [restoreArticlePairingLosers_value_of_not_mem_losers
        state.view base allocation.matching remainderFacts.2, baseValue]
      have original := values.2 source sourceMember element remainderFacts.1
      change state.value element = Analysis.transientContractedGap
        (final.view.rawGap element) source.intervalGap
      rw [finalView, after.unpaired_rawGap]
      · simpa [finalView, Lazy.Block.afterPassSource] using original
      · intro pairing pairingMember equal
        apply remainderFacts.2
        exact List.mem_map.mpr ⟨pairing, pairingMember, equal.symm⟩
    · by_cases selected : ∃ pairing ∈ allocation.matching,
          pairing.destination = blockId
      · obtain ⟨pairing, pairingMember, destinationEq⟩ := selected
        obtain ⟨destination, destinationFound, destinationGrowing,
            _destinationOwner, _destinationSide⟩ :=
          allocation.richDestinations pairing pairingMember
        have destinationFoundAtId : state.blocks[blockId]? =
            some destination := by
          simpa only [destinationEq] using destinationFound
        have expectedFound := Lazy.Block.passBlocks_destination_getElem?
          state.blocks sourceId source allocation.matching source.intervalGap
          allocation.destinationsNodup pairing pairingMember destination
          destinationFound
          (destinationEq.trans_ne blockIsSource)
        have blockEq : block = destination.inserted pairing.loser :=
          Option.some.inj (blockFound.symm.trans (by
            simpa only [destinationEq] using expectedFound))
        subst block
        have destinationMember : destination ∈ state.blocks :=
          List.mem_of_getElem? destinationFound
        have destinationGap : destination.intervalGap = 0 :=
          (valid.2 destination destinationMember).growing_intervalGap_eq_zero
            destinationGrowing
        simp only [Lazy.Block.inserted] at elementMember
        rcases List.mem_cons.mp elementMember with rfl | oldMember
        · rw [restoreArticlePairingLosers_value_loser state.view base
            losersNodup pairingMember (positive pairing pairingMember)]
          change articlePairingLoserTarget state.view pairing =
            Analysis.transientContractedGap
              (final.view.rawGap pairing.loser) destination.intervalGap
          rw [finalView, destinationGap]
          exact
            (_root_.Splay.Accounting.BatchReparentedView.paired_transientContractedGap_eq_target
              after pairingMember (rankOrder pairing pairingMember)).symm
        · have notLoser := notLoser_of_mem_nonSource destinationFound
            (destinationEq.trans_ne blockIsSource) oldMember
          rw [restoreArticlePairingLosers_value_of_not_mem_losers
            state.view base allocation.matching notLoser, baseValue]
          have original := values.2 destination destinationMember element
            oldMember
          change state.value element = Analysis.transientContractedGap
            (final.view.rawGap element) destination.intervalGap
          rw [finalView, after.unpaired_rawGap]
          · simpa [finalView, Lazy.Block.inserted] using original
          · intro candidate candidateMember equal
            apply notLoser
            exact List.mem_map.mpr
              ⟨candidate, candidateMember, equal.symm⟩
      · have passLt := (List.getElem?_eq_some_iff.mp blockFound).1
        have stateLt : blockId < state.blocks.length := by
          simpa using passLt
        let oldBlock := state.blocks[blockId]'stateLt
        have oldFound : state.blocks[blockId]? = some oldBlock := by
          apply List.getElem?_eq_some_iff.mpr
          exact ⟨stateLt, rfl⟩
        have unchanged := Lazy.Block.passBlocks_getElem?_of_ne state.blocks
          sourceId blockId source allocation.matching source.intervalGap
          blockIsSource (by
            intro pairing pairingMember equal
            exact selected ⟨pairing, pairingMember, equal⟩)
        have blockEq : block = oldBlock :=
          Option.some.inj (blockFound.symm.trans (unchanged.trans oldFound))
        subst block
        have oldMember : oldBlock ∈ state.blocks :=
          List.mem_of_getElem? oldFound
        have notLoser := notLoser_of_mem_nonSource oldFound blockIsSource
          elementMember
        rw [restoreArticlePairingLosers_value_of_not_mem_losers
          state.view base allocation.matching notLoser, baseValue]
        have original := values.2 oldBlock oldMember element elementMember
        change state.value element = Analysis.transientContractedGap
          (final.view.rawGap element) oldBlock.intervalGap
        rw [finalView, after.unpaired_rawGap]
        · simpa [finalView] using original
        · intro pairing pairingMember equal
          apply notLoser
          exact List.mem_map.mpr ⟨pairing, pairingMember, equal.symm⟩

/-- Every retained endpoint pair has a loser target no larger than its value
in the original represented source state.  This applies uniformly to the
first and second article phases; the second phase does not need to be
reconstructed from the intermediate state for this numerical fact. -/
theorem ArticleSourcePairings.loserTarget_le_of_agreement
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ}
    {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches)
    {phase : PairingPhase} {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement phase batches matching)
    {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    (rankEq : state.view.rank = snapshot.rank) :
    ∀ pairing ∈ matching,
      articlePairingLoserTarget state.view pairing ≤
        state.value pairing.loser := by
  intro pairing pairingMember
  obtain ⟨row, rowMember, selectedEq⟩ :=
    agreement.exists_row_of_mem pairingMember
  obtain ⟨winner, firstLoser, secondLoser, candidates, firstEq,
      secondEq, firstAdjacent, secondAdjacent, losersNe, candidatePerm,
      candidateChunk, candidateSegment, firstInBlock, secondInBlock,
      winnerInside, firstInside, secondInside⟩ :=
    plan.row_inside rowMember
  have sourceMember : source ∈ state.blocks :=
    List.mem_of_getElem? sourceFound
  cases phase with
  | first =>
      simp only [articleRowSelection] at selectedEq
      have pairEq : [winner, firstLoser] =
          [pairing.winner, pairing.loser] :=
        firstEq.symm.trans selectedEq
      have endpoints : winner = pairing.winner ∧
          firstLoser = pairing.loser := by simpa using pairEq
      have rankOrder : state.view.rank pairing.winner <
          state.view.rank pairing.loser := by
        rw [rankEq]
        exact agreement.rank_lt pairingMember
      exact (internalPairingLoserTarget_le valid values sourceMember
        (by simpa [sourceElements, endpoints.1] using winnerInside)
        (by simpa [sourceElements, endpoints.2] using firstInside)
        rankOrder).1
  | second =>
      simp only [articleRowSelection] at selectedEq
      have pairEq : [winner, secondLoser] =
          [pairing.winner, pairing.loser] :=
        secondEq.symm.trans selectedEq
      have endpoints : winner = pairing.winner ∧
          secondLoser = pairing.loser := by simpa using pairEq
      have rankOrder : state.view.rank pairing.winner <
          state.view.rank pairing.loser := by
        rw [rankEq]
        exact agreement.rank_lt pairingMember
      exact (internalPairingLoserTarget_le valid values sourceMember
        (by simpa [sourceElements, endpoints.1] using winnerInside)
        (by simpa [sourceElements, endpoints.2] using secondInside)
        rankOrder).1

theorem ArticleInternalPairingFractionCertificate.loserTarget_le_of_agreement
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {phase : PairingPhase} {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement phase batches matching)
    {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    (rankEq : state.view.rank = snapshot.rank) :
    ∀ pairing ∈ matching,
      articlePairingLoserTarget state.view pairing ≤
        state.value pairing.loser := by
  exact (certificate.sourcePairings batches).loserTarget_le_of_agreement agreement sourceFound sourceElements valid values rankEq

/-- A first-phase loser and a second-phase loser are always distinct, even
when they come from different retained rows.  Equal rows use the local
two-loser fact; distinct rows use disjoint four-child chunks. -/
theorem ArticleSourcePairings.firstSecondLosers_ne
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ}
    {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches)
    {firstMatching secondMatching : List (Interface.Pairing n)}
    (firstAgreement :
      ArticleBatchEndpointAgreement .first batches firstMatching)
    (secondAgreement :
      ArticleBatchEndpointAgreement .second batches secondMatching) :
    ∀ firstPairing ∈ firstMatching, ∀ secondPairing ∈ secondMatching,
      firstPairing.loser ≠ secondPairing.loser := by
  have groupMapNodup : (batches.rows.map Prod.fst).Nodup :=
    batches.groups_perm.nodup_iff.mpr plan.groups_nodup
  intro firstPairing firstMember secondPairing secondMember
  obtain ⟨firstRow, firstRowMember, firstSelected⟩ :=
    firstAgreement.exists_row_of_mem firstMember
  obtain ⟨secondRow, secondRowMember, secondSelected⟩ :=
    secondAgreement.exists_row_of_mem secondMember
  obtain ⟨firstWinner, firstLoser, firstSecondLoser, firstCandidates,
      firstEq, firstSecondEq, firstAdjacent, firstSecondAdjacent,
      firstLosersNe, firstCandidatePerm, firstCandidateChunk,
      firstCandidateSegment, firstInBlock, firstSecondInBlock,
      firstWinnerInside, firstLoserInside, firstSecondLoserInside⟩ :=
    plan.row_inside firstRowMember
  obtain ⟨secondWinner, secondFirstLoser, secondLoser, secondCandidates,
      secondFirstEq, secondEq, secondFirstAdjacent, secondAdjacent,
      secondLosersNe, secondCandidatePerm, secondCandidateChunk,
      secondCandidateSegment, secondFirstInBlock, secondInBlock,
      secondWinnerInside, secondFirstLoserInside, secondLoserInside⟩ :=
    plan.row_inside secondRowMember
  simp only [articleRowSelection] at firstSelected secondSelected
  have firstPairEq : [firstWinner, firstLoser] =
      [firstPairing.winner, firstPairing.loser] :=
    firstEq.symm.trans firstSelected
  have firstEndpoints : firstWinner = firstPairing.winner ∧
      firstLoser = firstPairing.loser := by simpa using firstPairEq
  have secondPairEq : [secondWinner, secondLoser] =
      [secondPairing.winner, secondPairing.loser] :=
    secondEq.symm.trans secondSelected
  have secondEndpoints : secondWinner = secondPairing.winner ∧
      secondLoser = secondPairing.loser := by simpa using secondPairEq
  intro loserEq
  have endpointEq : firstLoser = secondLoser := by
    rw [firstEndpoints.2, secondEndpoints.2]
    exact loserEq
  by_cases sameGroup : firstRow.1 = secondRow.1
  · have rowsEq : firstRow = secondRow :=
      List.inj_on_of_nodup_map groupMapNodup
        firstRowMember secondRowMember sameGroup
    subst secondRow
    have localSecondEq : [firstWinner, firstSecondLoser] =
        [secondWinner, secondLoser] :=
      firstSecondEq.symm.trans secondEq
    have localLosers : firstSecondLoser = secondLoser := by
      exact (by simpa using localSecondEq :
        firstWinner = secondWinner ∧ firstSecondLoser = secondLoser).2
    apply firstLosersNe
    exact endpointEq.trans localLosers.symm
  · have firstLoserCandidate : firstLoser ∈ firstCandidates :=
      firstCandidatePerm.mem_iff.mpr (by simp)
    have secondLoserCandidate : secondLoser ∈ secondCandidates :=
      secondCandidatePerm.mem_iff.mpr (by simp)
    exact groupChunks_disjoint_of_nodup
      (rootHeavyPathChildrenBottomUp_nodup snapshot before)
      sameGroup
      (firstCandidateChunk.mem firstLoserCandidate)
      (by
        rw [endpointEq]
        exact secondCandidateChunk.mem secondLoserCandidate)

theorem ArticleInternalPairingFractionCertificate.firstSecondLosers_ne
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {firstMatching secondMatching : List (Interface.Pairing n)}
    (firstAgreement :
      ArticleBatchEndpointAgreement .first batches firstMatching)
    (secondAgreement :
      ArticleBatchEndpointAgreement .second batches secondMatching) :
    ∀ firstPairing ∈ firstMatching, ∀ secondPairing ∈ secondMatching,
      firstPairing.loser ≠ secondPairing.loser := by
  exact (certificate.sourcePairings batches).firstSecondLosers_ne firstAgreement secondAgreement

/-- The loser list of the two retained phase matchings is duplicate-free. -/
theorem ArticleSourcePairings.twoPhaseLosers_nodup
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ}
    {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches)
    {firstMatching secondMatching : List (Interface.Pairing n)}
    (firstAgreement :
      ArticleBatchEndpointAgreement .first batches firstMatching)
    (secondAgreement :
      ArticleBatchEndpointAgreement .second batches secondMatching) :
    (Interface.pairingLosers (firstMatching ++ secondMatching)).Nodup := by
  have firstEndpointsNodup :
      (firstMatching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]).Nodup := by
    rw [firstAgreement.matchingEndpoints_eq_rows]
    simpa [articleRowSelection] using batches.firstEndpoints_nodup
  have secondEndpointsNodup :
      (secondMatching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]).Nodup := by
    rw [secondAgreement.matchingEndpoints_eq_rows]
    simpa [articleRowSelection] using batches.secondEndpoints_nodup
  have firstNodup := Interface.pairingLosers_nodup firstEndpointsNodup
  have secondNodup := Interface.pairingLosers_nodup secondEndpointsNodup
  rw [Interface.pairingLosers, List.map_append]
  apply List.nodup_append.mpr
  refine ⟨firstNodup, secondNodup, ?_⟩
  intro firstLoser firstLoserMember secondLoser secondLoserMember equal
  obtain ⟨firstPairing, firstMember, firstEq⟩ :=
    List.mem_map.mp firstLoserMember
  obtain ⟨secondPairing, secondMember, secondEq⟩ :=
    List.mem_map.mp secondLoserMember
  apply plan.firstSecondLosers_ne firstAgreement
    secondAgreement firstPairing firstMember secondPairing secondMember
  exact firstEq.trans (equal.trans secondEq.symm)

theorem ArticleInternalPairingFractionCertificate.twoPhaseLosers_nodup
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {firstMatching secondMatching : List (Interface.Pairing n)}
    (firstAgreement :
      ArticleBatchEndpointAgreement .first batches firstMatching)
    (secondAgreement :
      ArticleBatchEndpointAgreement .second batches secondMatching) :
    (Interface.pairingLosers (firstMatching ++ secondMatching)).Nodup := by
  exact (certificate.sourcePairings batches).twoPhaseLosers_nodup firstAgreement secondAgreement

/-- One article pass followed by its loser decreases is a legal rich trace,
and the restoration suffix contributes no productive operation. -/
theorem ArticleBatchDestinationAllocation.richPassTrace_with_loserRestoration
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ} {phase : PairingPhase}
    {batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups}
    {params : Interface.Parameters} {state : Lazy.State n}
    (allocation : ArticleBatchDestinationAllocation phase batches state)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (geometric : GeometricMatchingValid state sourceId source
      allocation.matching)
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    (growingTopmost : state.GrowingTopmost)
    (rankEq : state.view.rank = snapshot.rank)
    (largeEnough :
      source.passCount < params.exemptPasses ∨
        params.matchingNumerator * source.elements.length ≤
          params.matchingDenominator * allocation.matching.length)
    (after : BatchReparentedView state.view allocation.matching)
    (topmost : BatchTopmostGeometry after) :
    ∃ sourceIntervalGap,
      let winners := articleGoodWinners state allocation.matching
      let prepared := decreaseEach state winners
      let passed := prepared.passAtView after.view sourceId source
        allocation.matching sourceIntervalGap
      let restored := increaseEach passed winners
      let final := restoreArticlePairingLosers state.view restored
        allocation.matching
      Trace params state
          (articlePairingPassEvents state sourceId allocation.matching ++
            restoreArticlePairingLoserEvents state.view restored
              allocation.matching)
          final ∧
        Interface.totalInserts
            (eraseOperations
              (restoreArticlePairingLoserEvents state.view restored
                allocation.matching)) = 0 ∧
        Interface.totalIncreases
            (eraseOperations
              (restoreArticlePairingLoserEvents state.view restored
                allocation.matching)) = 0 ∧
        (∀ pairing ∈ allocation.matching,
          final.value pairing.loser =
            articlePairingLoserTarget state.view pairing) ∧
        final.ValuesRealizeGaps := by
  obtain ⟨sourceIntervalGap, sourceGapEq, passTrace, restoredValue⟩ :=
    allocation.richPassTrace_of_topmostReparentedView sourceFound geometric
      valid values growingTopmost rankEq largeEnough after topmost
  let winners := articleGoodWinners state allocation.matching
  let prepared := decreaseEach state winners
  let passed := prepared.passAtView after.view sourceId source
    allocation.matching sourceIntervalGap
  let restored := increaseEach passed winners
  have targets : ∀ pairing ∈ allocation.matching,
      articlePairingLoserTarget state.view pairing ≤
        state.value pairing.loser := by
    intro pairing pairingMember
    have endpoints := (geometric.2.2.2 pairing pairingMember).1
    have rankOrder : state.view.rank pairing.winner <
        state.view.rank pairing.loser := by
      rw [rankEq]
      exact allocation.agreement.rank_lt pairingMember
    exact (internalPairingLoserTarget_le valid values
      (List.mem_of_getElem? sourceFound) endpoints.first_mem
      endpoints.second_mem rankOrder).1
  have positive : ∀ pairing ∈ allocation.matching,
      1 ≤ articlePairingLoserTarget state.view pairing := by
    intro pairing pairingMember
    simp [articlePairingLoserTarget, Analysis.contractedGap]
  have bounded : ∀ pairing ∈ allocation.matching,
      articlePairingLoserTarget state.view pairing ≤ params.valueBound := by
    intro pairing pairingMember
    exact (targets pairing pairingMember).trans
      (valid.toInterface.2.1 pairing.loser).2
  have restorationTrace := restoreArticlePairingLosers_trace state.view
    restored allocation.matching passTrace.final_valid positive bounded
  have losersNodup :
      (Interface.pairingLosers allocation.matching).Nodup := by
    exact Interface.pairingLosers_nodup geometric.2.1
  have restoredTargetLe : ∀ pairing ∈ allocation.matching,
      articlePairingLoserTarget state.view pairing ≤
        restored.value pairing.loser := by
    intro pairing pairingMember
    rw [restoredValue]
    exact targets pairing pairingMember
  have finalValues :
      (restoreArticlePairingLosers state.view restored allocation.matching)
        |>.ValuesRealizeGaps := by
    apply allocation.valuesRealizeGaps_after_loserRestoration sourceFound
      geometric valid values after
    · calc
        restored.blocks = passed.blocks := by simp [restored]
        _ = Lazy.Block.passBlocks prepared.blocks sourceId source
            allocation.matching sourceIntervalGap := rfl
        _ = Lazy.Block.passBlocks prepared.blocks sourceId source
            allocation.matching source.intervalGap := by rw [sourceGapEq]
        _ = Lazy.Block.passBlocks state.blocks sourceId source
            allocation.matching source.intervalGap := by
              rw [show prepared.blocks = state.blocks by
                simp [prepared, winners]]
    · simp [restored, passed, prepared, winners]
    · exact restoredValue
    · intro pairing pairingMember
      rw [rankEq]
      exact allocation.agreement.rank_lt pairingMember
  refine ⟨sourceIntervalGap, ?_,
    totalInserts_restoreArticlePairingLoserEvents_eq_zero
      state.view restored allocation.matching,
    totalIncreases_restoreArticlePairingLoserEvents_eq_zero state.view restored
      losersNodup restoredTargetLe, ?_, finalValues⟩
  · simpa [articlePairingPassEvents, List.append_assoc] using
      passTrace.append restorationTrace
  · intro pairing pairingMember
    exact restoreArticlePairingLosers_value_loser state.view restored
      losersNodup pairingMember (positive pairing pairingMember)

/-- Article-facing two-phase macro including the contracted-gap decreases of
all first- and second-phase losers.  The two `Pass` operations retain their
actual matchings and persistent destination identifiers; the final suffix is
proved to contain neither inserts nor increases. -/
def ArticleRetainedPairingBatches.RestoredTwoPhaseRichPassTrace
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ}
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key groups)
    (params : Interface.Parameters) (state : Lazy.State n)
    (sourceId : Interface.BlockId) (source : Lazy.Block n)
    (firstAllocation :
      ArticleBatchDestinationAllocation .first batches state) : Prop :=
  ∃ afterFirst : BatchReparentedView state.view firstAllocation.matching,
    ∃ firstIntervalGap : ℤ,
      firstIntervalGap = source.intervalGap ∧
      let firstWinners :=
        articleGoodWinners state firstAllocation.matching
      let firstPrepared := decreaseEach state firstWinners
      let firstPassed := firstPrepared.passAtView afterFirst.view sourceId
        source firstAllocation.matching firstIntervalGap
      let middle := increaseEach firstPassed firstWinners
      middle.Valid params ∧ middle.value = state.value ∧
      ∃ secondAllocation :
          ArticleBatchDestinationAllocation .second batches middle,
        ∃ afterSecond :
            BatchReparentedView middle.view secondAllocation.matching,
          ∃ secondIntervalGap : ℤ,
            secondIntervalGap = source.intervalGap ∧
            let secondSource := source.afterPassSource
              firstAllocation.matching firstIntervalGap
            let secondWinners :=
              articleGoodWinners middle secondAllocation.matching
            let secondPrepared := decreaseEach middle secondWinners
            let secondPassed := secondPrepared.passAtView afterSecond.view
              sourceId secondSource secondAllocation.matching secondIntervalGap
            let passFinal := increaseEach secondPassed secondWinners
            let matching :=
              firstAllocation.matching ++ secondAllocation.matching
            let final := restoreArticlePairingLosers state.view passFinal matching
            let restorationEvents :=
              restoreArticlePairingLoserEvents state.view passFinal matching
            Trace params state
                (articlePairingPassEvents state sourceId
                    firstAllocation.matching ++
                  articlePairingPassEvents middle sourceId
                    secondAllocation.matching ++ restorationEvents)
                final ∧
              Interface.totalInserts
                  (eraseOperations restorationEvents) = 0 ∧
              Interface.totalIncreases
                  (eraseOperations restorationEvents) = 0 ∧
              final.view = afterSecond.view ∧
              (∀ pairing ∈ matching,
                final.value pairing.loser =
                  articlePairingLoserTarget state.view pairing) ∧
              final.ValuesRealizeGaps ∧
              final.Stable params

/- The original fraction-certificate API remains definitionally equal. -/
def ArticleInternalPairingFractionCertificate.RestoredTwoPhaseRichPassTrace
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    (params : Interface.Parameters) (state : Lazy.State n)
    (sourceId : Interface.BlockId) (source : Lazy.Block n)
    (firstAllocation :
      ArticleBatchDestinationAllocation .first batches state) : Prop :=
  ∃ afterFirst : BatchReparentedView state.view firstAllocation.matching,
    ∃ firstIntervalGap : ℤ,
      firstIntervalGap = source.intervalGap ∧
      let firstWinners :=
        articleGoodWinners state firstAllocation.matching
      let firstPrepared := decreaseEach state firstWinners
      let firstPassed := firstPrepared.passAtView afterFirst.view sourceId
        source firstAllocation.matching firstIntervalGap
      let middle := increaseEach firstPassed firstWinners
      middle.Valid params ∧ middle.value = state.value ∧
      ∃ secondAllocation :
          ArticleBatchDestinationAllocation .second batches middle,
        ∃ afterSecond :
            BatchReparentedView middle.view secondAllocation.matching,
          ∃ secondIntervalGap : ℤ,
            secondIntervalGap = source.intervalGap ∧
            let secondSource := source.afterPassSource
              firstAllocation.matching firstIntervalGap
            let secondWinners :=
              articleGoodWinners middle secondAllocation.matching
            let secondPrepared := decreaseEach middle secondWinners
            let secondPassed := secondPrepared.passAtView afterSecond.view
              sourceId secondSource secondAllocation.matching secondIntervalGap
            let passFinal := increaseEach secondPassed secondWinners
            let matching :=
              firstAllocation.matching ++ secondAllocation.matching
            let final := restoreArticlePairingLosers state.view passFinal matching
            let restorationEvents :=
              restoreArticlePairingLoserEvents state.view passFinal matching
            Trace params state
                (articlePairingPassEvents state sourceId
                    firstAllocation.matching ++
                  articlePairingPassEvents middle sourceId
                    secondAllocation.matching ++ restorationEvents)
                final ∧
              Interface.totalInserts
                  (eraseOperations restorationEvents) = 0 ∧
              Interface.totalIncreases
                  (eraseOperations restorationEvents) = 0 ∧
              final.view = afterSecond.view ∧
              (∀ pairing ∈ matching,
                final.value pairing.loser =
                  articlePairingLoserTarget state.view pairing) ∧
              final.ValuesRealizeGaps ∧
              final.Stable params

/-- The already checked two-phase `Pass` trace extends canonically by the
article's loser decreases. -/
theorem ArticleSourcePairings.with_loserRestoration_of_invariants
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ}
    {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches)
    {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    {firstAllocation :
      ArticleBatchDestinationAllocation .first batches state}
    (twoPhase : batches.TwoPhaseRichPassTrace params state
      sourceId source firstAllocation)
    (valid : state.Valid params)
    (values : state.ValuesRealizeGaps)
    (rankEq : state.view.rank = snapshot.rank)
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (sourceShrinking : source.mode = .shrinking) :
    batches.RestoredTwoPhaseRichPassTrace params state
      sourceId source firstAllocation := by
  unfold ArticleRetainedPairingBatches.TwoPhaseRichPassTrace at twoPhase
  obtain ⟨afterFirst, firstIntervalGap, firstIntervalGapEq, middleValid,
      middleValueEq, secondAllocation, afterSecond, secondIntervalGap,
      secondIntervalGapEq, passTrace, passComplete, passOneGrowing,
      passGrowingTopmost, passOrdered, passValueEq⟩ := twoPhase
  unfold ArticleRetainedPairingBatches.RestoredTwoPhaseRichPassTrace
  refine ⟨afterFirst, firstIntervalGap, firstIntervalGapEq, middleValid,
    middleValueEq, secondAllocation, afterSecond, secondIntervalGap,
    secondIntervalGapEq, ?_⟩
  dsimp only
  let firstWinners := articleGoodWinners state firstAllocation.matching
  let firstPrepared := decreaseEach state firstWinners
  let firstPassed := firstPrepared.passAtView afterFirst.view sourceId source
    firstAllocation.matching firstIntervalGap
  let middle := increaseEach firstPassed firstWinners
  let secondSource := source.afterPassSource firstAllocation.matching
    firstIntervalGap
  let secondWinners := articleGoodWinners middle secondAllocation.matching
  let secondPrepared := decreaseEach middle secondWinners
  let secondPassed := secondPrepared.passAtView afterSecond.view sourceId
    secondSource secondAllocation.matching secondIntervalGap
  let passFinal := increaseEach secondPassed secondWinners
  let matching := firstAllocation.matching ++ secondAllocation.matching
  let final := restoreArticlePairingLosers state.view passFinal matching
  let restorationEvents :=
    restoreArticlePairingLoserEvents state.view passFinal matching
  have targetLeState : ∀ pairing ∈ matching,
      articlePairingLoserTarget state.view pairing ≤
        state.value pairing.loser := by
    intro pairing pairingMember
    rcases List.mem_append.mp pairingMember with firstMember | secondMember
    · exact plan.loserTarget_le_of_agreement
        firstAllocation.agreement sourceFound sourceElements
        valid values rankEq pairing firstMember
    · exact plan.loserTarget_le_of_agreement
        secondAllocation.agreement sourceFound sourceElements
        valid values rankEq pairing secondMember
  have targetLeFinal : ∀ pairing ∈ matching,
      articlePairingLoserTarget state.view pairing ≤
        passFinal.value pairing.loser := by
    intro pairing pairingMember
    rw [passValueEq]
    exact targetLeState pairing pairingMember
  have positive : ∀ pairing ∈ matching,
      1 ≤ articlePairingLoserTarget state.view pairing := by
    intro pairing pairingMember
    simp [articlePairingLoserTarget, Analysis.contractedGap]
  have bounded : ∀ pairing ∈ matching,
      articlePairingLoserTarget state.view pairing ≤ params.valueBound := by
    intro pairing pairingMember
    exact (targetLeState pairing pairingMember).trans
      (valid.toInterface.2.1 pairing.loser).2
  have losersNodup : (Interface.pairingLosers matching).Nodup := by
    exact plan.twoPhaseLosers_nodup
      firstAllocation.agreement secondAllocation.agreement
  have restorationTrace : Trace params passFinal restorationEvents final := by
    exact restoreArticlePairingLosers_trace state.view passFinal matching
      passTrace.final_valid positive bounded
  have sourceInterfaceFound : state.toInterface.block? sourceId =
      some source.toInterface := by
    unfold Interface.State.block? Lazy.State.toInterface
    simpa using congrArg (Option.map Lazy.Block.toInterface) sourceFound
  have firstGeometric :=
    plan.first_geometricMatching_of_allocation firstAllocation
      sourceInterfaceFound sourceElements sourceShrinking
  let firstRestored := restoreArticlePairingLosers state.view middle
    firstAllocation.matching
  have firstRestoredValues : firstRestored.ValuesRealizeGaps := by
    apply firstAllocation.valuesRealizeGaps_after_loserRestoration sourceFound
      firstGeometric valid values afterFirst
    · calc
        middle.blocks = firstPassed.blocks := by simp [middle]
        _ = Lazy.Block.passBlocks firstPrepared.blocks sourceId source
            firstAllocation.matching firstIntervalGap := rfl
        _ = Lazy.Block.passBlocks state.blocks sourceId source
            firstAllocation.matching source.intervalGap := by
              rw [firstIntervalGapEq]
              simp [firstPrepared, firstWinners]
    · simp [middle, firstPassed, firstPrepared, firstWinners]
    · exact middleValueEq
    · intro pairing pairingMember
      rw [rankEq]
      exact firstAllocation.agreement.rank_lt pairingMember
  have firstRestorationTrace : Trace params middle
      (restoreArticlePairingLoserEvents state.view middle
        firstAllocation.matching) firstRestored := by
    apply restoreArticlePairingLosers_trace state.view middle
      firstAllocation.matching middleValid
    · intro pairing pairingMember
      exact positive pairing (by
        exact List.mem_append_left _ pairingMember)
    · intro pairing pairingMember
      exact bounded pairing (by
        exact List.mem_append_left _ pairingMember)
  have firstRestoredValid : firstRestored.Valid params :=
    firstRestorationTrace.final_valid
  let stableSecondAllocation :
      ArticleBatchDestinationAllocation .second batches firstRestored :=
    secondAllocation.transport_blocks_eq (by
      exact restoreArticlePairingLosers_blocks state.view middle
        firstAllocation.matching)
  have middleSourceFound : middle.blocks[sourceId]? = some secondSource := by
    simp only [middle, increaseEach_blocks, firstPassed,
      Lazy.State.passAtView_blocks]
    change (Lazy.Block.passBlocks firstPrepared.blocks sourceId source
      firstAllocation.matching firstIntervalGap)[sourceId]? = _
    rw [show firstPrepared.blocks = state.blocks by
      simp [firstPrepared, firstWinners]]
    apply Lazy.Block.passBlocks_source_getElem? state.blocks sourceId source
      firstAllocation.matching firstIntervalGap sourceFound
    intro pairing pairingMember
    exact (firstGeometric.2.2.2 pairing pairingMember).2.1
  have firstRestoredSourceFound : firstRestored.blocks[sourceId]? =
      some secondSource := by
    simpa [firstRestored] using middleSourceFound
  have secondSourceElements : secondSource.elements =
      batches.firstLosers.foldl List.erase elements := by
    simpa [secondSource, sourceElements] using
      firstAllocation.agreement.afterPassSource_elements_eq
        (source := source) firstIntervalGap
  have firstRestoredSourceInterfaceFound :
      firstRestored.toInterface.block? sourceId =
        some secondSource.toInterface := by
    unfold Interface.State.block? Lazy.State.toInterface
    simpa using congrArg (Option.map Lazy.Block.toInterface)
      firstRestoredSourceFound
  have secondGeometric :=
    plan.second_geometricMatching_of_allocation
      stableSecondAllocation firstRestoredSourceInterfaceFound
      secondSourceElements (by
        change source.mode = .shrinking
        exact sourceShrinking)
  have stableSecondMatchingEq : stableSecondAllocation.matching =
      secondAllocation.matching := rfl
  have firstRestoredViewEq : firstRestored.view = middle.view := by
    simp [firstRestored]
  let stableAfterSecond : BatchReparentedView firstRestored.view
      stableSecondAllocation.matching := {
    view := afterSecond.view
    rank_eq := by
      calc
        afterSecond.view.rank = middle.view.rank := afterSecond.rank_eq
        _ = firstRestored.view.rank := by simp [firstRestored]
    root_eq := by
      calc
        afterSecond.view.root = middle.view.root := afterSecond.root_eq
        _ = firstRestored.view.root := by simp [firstRestored]
    ordered := afterSecond.ordered
    paired_parent := by
      intro pairing pairingMember
      apply afterSecond.paired_parent pairing
      rw [← stableSecondMatchingEq]
      exact pairingMember
    paired_side := by
      intro pairing pairingMember
      apply afterSecond.paired_side pairing
      rw [← stableSecondMatchingEq]
      exact pairingMember
    unpaired_parent := by
      intro element notLoser
      have originalNotLoser : ∀ pairing ∈ secondAllocation.matching,
          element ≠ pairing.loser := by
        intro pairing pairingMember
        apply notLoser pairing
        rw [stableSecondMatchingEq]
        exact pairingMember
      rw [firstRestoredViewEq]
      exact afterSecond.unpaired_parent element originalNotLoser
    unpaired_side := by
      intro element notLoser
      have originalNotLoser : ∀ pairing ∈ secondAllocation.matching,
          element ≠ pairing.loser := by
        intro pairing pairingMember
        apply notLoser pairing
        rw [stableSecondMatchingEq]
        exact pairingMember
      rw [firstRestoredViewEq]
      exact afterSecond.unpaired_side element originalNotLoser
  }
  let secondBase := restoreArticlePairingLosers state.view passFinal
    firstAllocation.matching
  have secondSourceGapEq : secondSource.intervalGap = source.intervalGap := by
    change firstIntervalGap = source.intervalGap
    exact firstIntervalGapEq
  have secondGapEqSource : secondIntervalGap = secondSource.intervalGap :=
    secondIntervalGapEq.trans secondSourceGapEq.symm
  have secondBaseValue : secondBase.value = firstRestored.value := by
    apply restoreArticlePairingLosers_value_congr state.view
    exact passValueEq.trans middleValueEq.symm
  have firstRestoredRankEq : firstRestored.view.rank = snapshot.rank := by
    calc
      firstRestored.view.rank = afterFirst.view.rank := by
        simp [firstRestored, middle, firstPassed, firstPrepared, firstWinners]
      _ = state.view.rank := afterFirst.rank_eq
      _ = snapshot.rank := rankEq
  have secondFinalValues :
      (restoreArticlePairingLosers firstRestored.view secondBase
        stableSecondAllocation.matching).ValuesRealizeGaps := by
    apply stableSecondAllocation.valuesRealizeGaps_after_loserRestoration
      firstRestoredSourceFound secondGeometric firstRestoredValid
      firstRestoredValues stableAfterSecond
    · calc
        secondBase.blocks = passFinal.blocks := by simp [secondBase]
        _ = secondPassed.blocks := by simp [passFinal]
        _ = Lazy.Block.passBlocks secondPrepared.blocks sourceId secondSource
            secondAllocation.matching secondIntervalGap := rfl
        _ = Lazy.Block.passBlocks middle.blocks sourceId secondSource
            secondAllocation.matching secondSource.intervalGap := by
              rw [secondGapEqSource]
              simp [secondPrepared, secondWinners]
        _ = Lazy.Block.passBlocks firstRestored.blocks sourceId secondSource
            stableSecondAllocation.matching secondSource.intervalGap := by
              rw [stableSecondMatchingEq]
              simp [firstRestored]
    · simp [secondBase, passFinal, secondPassed, secondPrepared,
        secondWinners, stableAfterSecond]
    · exact secondBaseValue
    · intro pairing pairingMember
      rw [firstRestoredRankEq]
      exact stableSecondAllocation.agreement.rank_lt pairingMember
  have restorationViewRankEq : firstRestored.view.rank = state.view.rank :=
    firstRestoredRankEq.trans rankEq.symm
  have finalValues : final.ValuesRealizeGaps := by
    have viewTransport := restoreArticlePairingLosers_eq_of_rank_eq
      restorationViewRankEq secondBase stableSecondAllocation.matching
    have finalEq :
        restoreArticlePairingLosers firstRestored.view secondBase
            stableSecondAllocation.matching = final := by
      calc
        restoreArticlePairingLosers firstRestored.view secondBase
            stableSecondAllocation.matching =
            restoreArticlePairingLosers state.view secondBase
              stableSecondAllocation.matching := viewTransport
        _ = restoreArticlePairingLosers state.view
              (restoreArticlePairingLosers state.view passFinal
                firstAllocation.matching) secondAllocation.matching := by
              rfl
        _ = restoreArticlePairingLosers state.view passFinal
              (firstAllocation.matching ++ secondAllocation.matching) := by
              rw [restoreArticlePairingLosers_append]
        _ = final := rfl
    rw [← finalEq]
    exact secondFinalValues
  have finalComplete : final.Complete := by
    rw [State.Complete]
    simpa only [State.Complete, final, State.allElements,
      restoreArticlePairingLosers_blocks,
      restoreArticlePairingLosers_view] using passComplete
  have finalOneGrowing : final.OneGrowingPerSide := by
    have blocksEq : final.blocks = passFinal.blocks := by simp [final]
    rw [State.OneGrowingPerSide, blocksEq]
    exact passOneGrowing
  have finalGrowingTopmost : final.GrowingTopmost := by
    have blocksEq : final.blocks = passFinal.blocks := by simp [final]
    have viewEq : final.view = passFinal.view := by simp [final]
    rw [State.GrowingTopmost, blocksEq, viewEq]
    exact passGrowingTopmost
  have finalOrdered : final.view.HeapOrdered := by
    have viewEq : final.view = passFinal.view := by simp [final]
    rw [viewEq]
    intro element owner parentEq
    exact passOrdered parentEq
  have finalStable : final.Stable params :=
    ⟨restorationTrace.final_valid, finalComplete, finalOrdered,
      finalOneGrowing, finalGrowingTopmost, finalValues⟩
  refine ⟨?_,
    totalInserts_restoreArticlePairingLoserEvents_eq_zero
      state.view passFinal matching,
    totalIncreases_restoreArticlePairingLoserEvents_eq_zero
      state.view passFinal losersNodup targetLeFinal,
    ?_, ?_, finalValues, finalStable⟩
  · simpa [firstWinners, firstPrepared, firstPassed, middle, secondSource,
      secondWinners, secondPrepared, secondPassed, passFinal, matching,
      final, restorationEvents, List.append_assoc] using
        passTrace.append restorationTrace
  · simp [final, passFinal, secondPassed, secondPrepared, secondWinners]
  · intro pairing pairingMember
    exact restoreArticlePairingLosers_value_loser state.view passFinal
      losersNodup pairingMember (positive pairing pairingMember)

theorem ArticleInternalPairingFractionCertificate.TwoPhaseRichPassTrace.with_loserRestoration_of_invariants
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    {certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0)}
    {batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups}
    {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    {firstAllocation :
      ArticleBatchDestinationAllocation .first batches state}
    (twoPhase : certificate.TwoPhaseRichPassTrace batches params state
      sourceId source firstAllocation)
    (valid : state.Valid params)
    (values : state.ValuesRealizeGaps)
    (rankEq : state.view.rank = snapshot.rank)
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (sourceShrinking : source.mode = .shrinking) :
    certificate.RestoredTwoPhaseRichPassTrace batches params state
      sourceId source firstAllocation := by
  exact (certificate.sourcePairings batches).with_loserRestoration_of_invariants
    twoPhase valid values rankEq sourceFound sourceElements sourceShrinking

/-- Stable-state entry point for one complete article source-block macro.
Unlike the canonical wrapper below, this theorem does not require the current
heap view still to be the initial BST view.  The two local outermost-order
witnesses are precisely the geometric facts that a global sequential
execution must transport from that initial view. -/
theorem ArticleInternalPairingFractionCertificate.restoredTwoPhaseRichPassTrace_of_allocations_and_outermost
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (sourceShrinking : source.mode = .shrinking)
    (stable : state.Stable params)
    (rankEq : state.view.rank = snapshot.rank)
    (articleFraction :
      10 * params.matchingNumerator ≤ params.matchingDenominator)
    (groupsNonempty : certificate.fraction.groups ≠ [])
    (firstAllocation :
      ArticleBatchDestinationAllocation .first batches state)
    (originalSecondAllocation :
      ArticleBatchDestinationAllocation .second batches state)
    (firstOutermost :
      BatchOutermostOrder state.view firstAllocation.matching)
    (secondOutermost :
      BatchOutermostOrder state.view originalSecondAllocation.matching) :
    certificate.RestoredTwoPhaseRichPassTrace batches params state
      sourceId source firstAllocation := by
  have twoPhase : certificate.TwoPhaseRichPassTrace batches params state
      sourceId source firstAllocation := by
    unfold ArticleInternalPairingFractionCertificate.TwoPhaseRichPassTrace
    exact certificate.exists_twoPhaseRichPassTrace_of_allocations_and_outermost
      batches sourceFound sourceElements sourceShrinking stable.valid
      stable.2.2.2.2.2 stable.2.1 stable.2.2.2.1 stable.2.2.2.2.1
      rankEq stable.2.2.1 articleFraction groupsNonempty firstAllocation
      originalSecondAllocation firstOutermost secondOutermost
  exact twoPhase.with_loserRestoration_of_invariants stable.valid
    stable.2.2.2.2.2 rankEq sourceFound sourceElements sourceShrinking

/-- A represented state supplies the three invariant hypotheses needed by
`with_loserRestoration_of_invariants`.  Keeping this wrapper preserves the
canonical one-source API while allowing later executions to start from a
stable, already reparented state. -/
theorem ArticleInternalPairingFractionCertificate.TwoPhaseRichPassTrace.with_loserRestoration
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    {certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0)}
    {batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups}
    {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    {firstAllocation :
      ArticleBatchDestinationAllocation .first batches state}
    (twoPhase : certificate.TwoPhaseRichPassTrace batches params state
      sourceId source firstAllocation)
    (represents : state.Represents params snapshot before)
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (sourceShrinking : source.mode = .shrinking) :
    certificate.RestoredTwoPhaseRichPassTrace batches params state
      sourceId source firstAllocation := by
  exact twoPhase.with_loserRestoration_of_invariants represents.valid
    represents.valuesRealizeGaps represents.view_rank_eq sourceFound
    sourceElements sourceShrinking

end Splay.Accounting
