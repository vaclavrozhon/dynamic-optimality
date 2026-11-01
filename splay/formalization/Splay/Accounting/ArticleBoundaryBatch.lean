import Splay.Accounting.ArticleBoundaryRelocationFootprint
import Splay.Accounting.ArticleRootPairingGeometry
import Splay.Accounting.ArticleBoundaryMoveWitness
import Splay.Accounting.BoundaryPairingMoveComposition
import Splay.Accounting.BoundaryRelocationCredit

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical
open ArticleBatchDestinationAllocation

/-- A complete actual boundary batch, with one delete/insert per selected
loser and a single common trace for the endpoint and all cost statements. -/
structure ArticleBoundaryBatchExecution {n : ℕ} (params : Interface.Parameters)
    (initial : Lazy.State n) (matching : List (Interface.Pairing n)) where
  final : Lazy.State n
  events : List (Event n)
  trace : Trace params initial events final
  stable : final.Stable params
  reparented : BatchReparentedView initial.view matching
  view_eq : reparented.view = final.view
  leaving : operationLeavingElementsList (eraseOperations events) = Interface.pairingLosers matching
  inserts : Interface.totalInserts (eraseOperations events) = matching.length
  increases : Interface.totalIncreases (eraseOperations events) ≤ 4 * params.valueBound * matching.length
  blocks_length_eq : final.blocks.length = initial.blocks.length
  shrinkingRefines : State.ShrinkingRefinement (fun _ => False) initial final
  sources : ∀ pairing ∈ matching, ∃ (id : Interface.BlockId) (source : Lazy.Block n),
    initial.blocks[id]? = some source ∧ source.mode = .shrinking ∧ pairing.loser ∈ source.elements
  smallCredit : ∀ (cutoff : ℕ) (marked : Interface.Element n → Bool),
    (∀ pairing ∈ matching, marked pairing.loser = true →
      ∃ (id : Interface.BlockId) (source : Lazy.Block n),
        initial.blocks[id]? = some source ∧ source.mode = .shrinking ∧
          pairing.loser ∈ source.elements ∧ source.elements.length ≤ 12) →
    Interface.boundaryCredit cutoff final.toInterface +
      (matching.filter fun pairing => marked pairing.loser).length ≤
        Interface.boundaryCredit cutoff initial.toInterface
  occurrence : ∀ pairing ∈ matching, ∀ slot : PairingSlot,
    Nonempty { move : BoundaryPairingMove trace //
      move.slot = slot ∧ move.winner = pairing.winner ∧ move.loser = pairing.loser ∧
        move.destination = pairing.destination }
  growing : ∀ {id : Interface.BlockId} {block : Lazy.Block n},
    initial.blocks[id]? = some block → block.mode = .growing →
      ∃ current : Lazy.Block n, final.blocks[id]? = some current ∧
        current.mode = .growing ∧ current.owner = block.owner ∧
        current.side = block.side ∧ current.creator = block.creator

  preservesGrowingBlock : ∀ {id : Interface.BlockId} {block : Lazy.Block n},
    initial.blocks[id]? = some block → block.mode = .growing →
      (∀ pairing ∈ matching, pairing.winner ≠ block.owner) → final.blocks[id]? = some block

/-- Run a phase's boundary pairs in order. Later sources are recovered from
actual residence preservation; destinations retain their original IDs. -/
theorem ArticleBoundaryBatchExecution.exists_of_ready {n : ℕ} {params : Interface.Parameters}
    {initial : Lazy.State n} (matching : List (Interface.Pairing n))
    (stable : initial.Stable params)
    (endpointsNodup : (matching.flatMap fun pairing => [pairing.winner, pairing.loser]).Nodup)
    (sources : ∀ pairing ∈ matching, ∃ (id : Interface.BlockId) (source : Lazy.Block n),
      initial.blocks[id]? = some source ∧ source.mode = .shrinking ∧ pairing.loser ∈ source.elements)
    (destinations : ∀ pairing ∈ matching, ∃ destination : Lazy.Block n,
      initial.blocks[pairing.destination]? = some destination ∧ destination.mode = .growing ∧
        destination.owner = pairing.winner ∧ destination.side = sideOf pairing.winner pairing.loser)
    (rankLt : ∀ pairing ∈ matching, initial.view.rank pairing.winner < initial.view.rank pairing.loser)
    (bounded : ∀ pairing ∈ matching,
      Analysis.contractedGap (initial.view.rank pairing.loser - initial.view.rank pairing.winner) ≤ params.valueBound)
    (outermost : BatchOutermostOrder initial.view matching) :
    Nonempty (ArticleBoundaryBatchExecution params initial matching) := by
  induction matching generalizing initial with
  | nil =>
      exact ⟨{
        final := initial, events := [], trace := .nil stable.valid, stable,
        reparented := .nil initial.view stable.2.2.1, view_eq := rfl,
        leaving := rfl, inserts := rfl, increases := by simp [Interface.totalIncreases, eraseOperations],
        blocks_length_eq := rfl,
        shrinkingRefines := State.ShrinkingRefinement.refl _ _,
        sources := sources,
        smallCredit := by intros; simp,
        occurrence := by intro pairing member; simp at member,
        growing := by intro id block found growing; exact ⟨block, found, growing, rfl, rfl, rfl⟩,
        preservesGrowingBlock := by intro id block found _ _; exact found
      }⟩
  | cons head tail ih =>
      have parts : ([head.winner, head.loser] ++
          tail.flatMap fun pairing => [pairing.winner, pairing.loser]).Nodup := endpointsNodup
      have tailNodup := (List.nodup_append.mp parts).2.1
      have separated := (List.nodup_append.mp parts).2.2
      have winnersNe : ∀ pairing ∈ tail, head.winner ≠ pairing.winner := by
        intro pairing member equal
        exact separated head.winner (by simp) pairing.winner
          (List.mem_flatMap.mpr ⟨pairing, member, by simp⟩) equal
      have losersNe : ∀ pairing ∈ tail, head.loser ≠ pairing.loser := by
        intro pairing member equal
        exact separated head.loser (by simp) pairing.loser
          (List.mem_flatMap.mpr ⟨pairing, member, by simp⟩) equal
      obtain ⟨sourceId, source, sourceFound, sourceShrinking, loserMember⟩ := sources head (by simp)
      obtain ⟨destination, destinationFound, destinationGrowing, destinationOwner, destinationSide⟩ :=
        destinations head (by simp)
      have different : head.winner ≠ head.loser := by
        intro equal
        have strict := rankLt head (by simp)
        rw [equal] at strict
        exact Nat.lt_irrefl _ strict
      have selectedRank : initial.view.rank destination.owner < initial.view.rank head.loser := by
        rw [destinationOwner]
        exact rankLt head (by simp)
      have selectedSide : match destination.side with
          | .left => head.loser.val < destination.owner.val
          | .right => destination.owner.val < head.loser.val := by
        rw [destinationOwner, destinationSide]
        exact sideOf_order_of_ne different
      have selectedOuter : ∀ child ∈ initial.view.topDown destination.owner destination.side,
          if destination.side = .left then head.loser.val < child.val else child.val < head.loser.val := by
        rw [destinationOwner, destinationSide]
        intro child member
        have result := outermost head (by simp) child member
        by_cases left : head.loser.val < head.winner.val <;> simpa [sideOf, left] using result
      have selectedBound : Analysis.contractedGap
          (initial.view.rank head.loser - initial.view.rank destination.owner) ≤ params.valueBound := by
        rw [destinationOwner]
        exact bounded head (by simp)
      obtain ⟨afterView, relocation, nextStable, parent, side⟩ :=
        State.exists_stableBoundaryPairing stable sourceFound sourceShrinking destinationFound
          destinationGrowing head.loser loserMember selectedRank selectedSide selectedOuter selectedBound
      have actualParent : relocation.final.view.parent head.loser = some head.winner := by
        have blockEq : relocation.destination = destination :=
          Option.some.inj (relocation.destinationFound.symm.trans destinationFound)
        simpa [destinationOwner] using parent
      have actualSide : relocation.final.view.side head.loser = sideOf head.winner head.loser := by
        simpa [destinationSide] using side
      let first := relocation.singletonReparented nextStable head rfl actualParent actualSide
      have tailSources : ∀ pairing ∈ tail, ∃ (id : Interface.BlockId) (source : Lazy.Block n),
          relocation.final.blocks[id]? = some source ∧ source.mode = .shrinking ∧ pairing.loser ∈ source.elements := by
        intro pairing member
        obtain ⟨id, block, found, shrinking, inside⟩ := sources pairing (by simp [member])
        apply shrinkingResidence_after_trace relocation.trace found shrinking inside
        rw [boundaryRelocation_leavingElements relocation]
        simpa only [List.mem_singleton] using (losersNe pairing member).symm
      have tailDestinations : ∀ pairing ∈ tail, ∃ destination : Lazy.Block n,
          relocation.final.blocks[pairing.destination]? = some destination ∧ destination.mode = .growing ∧
            destination.owner = pairing.winner ∧ destination.side = sideOf pairing.winner pairing.loser := by
        intro pairing member
        obtain ⟨block, found, growing, owner, side⟩ := destinations pairing (by simp [member])
        obtain ⟨current, currentFound, currentGrowing, currentOwner, currentSide, _⟩ :=
          relocation.preservesGrowingPlacement found growing
        exact ⟨current, currentFound, currentGrowing, currentOwner.trans owner, currentSide.trans side⟩
      have tailOuter : BatchOutermostOrder relocation.final.view tail := by
        apply first.outermostOrder_after_of_winners_ne
          (fun pairing member => outermost pairing (by simp [member]))
        intro earlier earlierMember later laterMember
        have equal : earlier = head := by simpa using earlierMember
        subst earlier
        exact winnersNe later laterMember
      obtain ⟨rest⟩ := ih nextStable tailNodup tailSources tailDestinations
        (by intro pairing member; rw [relocation.rank_eq]; exact rankLt pairing (by simp [member]))
        (by intro pairing member; rw [relocation.rank_eq]; exact bounded pairing (by simp [member])) tailOuter
      let combined := first.append rest.reparented (by
        intro earlier earlierMember later laterMember
        have equal : earlier = head := by simpa using earlierMember
        subst earlier
        exact losersNe later laterMember)
      refine ⟨{
        final := rest.final, events := relocation.events ++ rest.events,
        trace := relocation.trace.append rest.trace, stable := rest.stable,
        reparented := combined, view_eq := rest.view_eq,
        leaving := ?_, inserts := ?_, increases := ?_,
        blocks_length_eq := rest.blocks_length_eq.trans relocation.blocks_length_eq,
        shrinkingRefines := relocation.shrinkingRefines.trans rest.shrinkingRefines,
        sources := sources, smallCredit := ?_,
        occurrence := ?_, growing := ?_, preservesGrowingBlock := ?_
      }⟩
      · rw [eraseOperations_append, operationLeavingElementsList_append,
          boundaryRelocation_leavingElements relocation, rest.leaving]
        rfl
      · rw [eraseOperations_append, Interface.totalInserts_append, relocation.inserts, rest.inserts]
        simp [Nat.add_comm]
      · rw [eraseOperations_append, Interface.totalIncreases_append, List.length_cons, Nat.mul_add, Nat.mul_one]
        have headCost := relocation.increases
        have tailCost := rest.increases
        omega
      · intro cutoff marked small
        have tailPaid := rest.smallCredit cutoff marked (by
          intro pairing member selected
          obtain ⟨oldId, old, oldFound, _, oldMember, oldSmall⟩ :=
            small pairing (List.mem_cons_of_mem _ member) selected
          obtain ⟨nextId, next, nextFound, nextShrinking, nextMember⟩ := tailSources pairing member
          have sublist := relocation.shrinkingRefines.elements_sublist_of_common_element stable.valid
            oldFound oldMember nextFound nextShrinking nextMember
          exact ⟨nextId, next, nextFound, nextShrinking, nextMember, sublist.length_le.trans oldSmall⟩)
        have headPaid := relocation.boundaryCredit_drop (cutoff := cutoff)
        by_cases selected : marked head.loser = true
        · obtain ⟨oldId, old, oldFound, _, oldMember, oldSmall⟩ := small head (by simp) selected
          have sublist := (State.ShrinkingRefinement.refl (fun _ => False) initial).elements_sublist_of_common_element
            stable.valid oldFound oldMember relocation.sourceFound relocation.sourceShrinking relocation.elementMem
          have headSmall := sublist.length_le.trans oldSmall
          rw [if_pos headSmall] at headPaid
          simp only [List.filter_cons, selected, ↓reduceIte, List.length_cons]
          omega
        · simp [List.filter_cons, selected]
          omega
      · intro pairing member slot
        rcases List.mem_cons.mp member with rfl | member
        · obtain ⟨move, slotEq, winnerEq, loserEq, sourceEq, destinationEq, zeroIndex⟩ :=
            boundaryRelocation_exists_move relocation slot
          have blockEq : relocation.destination = destination :=
            Option.some.inj (relocation.destinationFound.symm.trans destinationFound)
          exact ⟨BoundaryPairingMove.append rest.trace move, slotEq,
            winnerEq.trans ((congrArg Lazy.Block.owner blockEq).trans destinationOwner),
            loserEq, destinationEq⟩
        · obtain ⟨move, slotEq, winnerEq, loserEq, destinationEq⟩ := rest.occurrence pairing member slot
          exact ⟨BoundaryPairingMove.prepend relocation.trace move, slotEq, winnerEq, loserEq, destinationEq⟩
      · intro id block found growing
        obtain ⟨middle, middleFound, middleGrowing, middleOwner, middleSide, middleCreator⟩ :=
          relocation.preservesGrowingPlacement found growing
        obtain ⟨current, currentFound, currentGrowing, currentOwner, currentSide, currentCreator⟩ :=
          rest.growing middleFound middleGrowing
        exact ⟨current, currentFound, currentGrowing, currentOwner.trans middleOwner,
          currentSide.trans middleSide, currentCreator.trans middleCreator⟩
      · intro id block found growing notWinner
        have blockEq : relocation.destination = destination :=
          Option.some.inj (relocation.destinationFound.symm.trans destinationFound)
        have middleFound := relocation.preservesGrowingBlock found growing (by
          rw [blockEq, destinationOwner]
          exact (notWinner head (by simp)).symm)
        exact rest.preservesGrowingBlock middleFound growing
          (fun pairing member => notWinner pairing (List.mem_cons_of_mem _ member))

end Splay.Accounting
