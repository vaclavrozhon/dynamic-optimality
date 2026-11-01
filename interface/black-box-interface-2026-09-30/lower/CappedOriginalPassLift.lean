import VirtualOriginalPassLift

namespace Splay.Research.CappedOriginalPassLift
open Splay.Interface Splay.Interface.MatchingValid
open Splay.Research.VirtualNumericInsertion Splay.Research.VirtualRetainedPass
open Splay.Research.VirtualMonotoneNormalization

theorem winner_sublist {n : ℕ} (matching : List (Pairing n)) :
    (matching.map Pairing.winner).Sublist
      (matching.flatMap fun pair => [pair.winner, pair.loser]) := by
  induction matching with
  | nil => exact .slnil
  | cons pair rest ih => exact (ih.cons pair.loser).cons_cons pair.winner

theorem separate {n : ℕ} (matching : List (Pairing n))
    (distinct : (matching.flatMap fun pair => [pair.winner, pair.loser]).Nodup) :
    List.Disjoint (matching.map Pairing.winner) (matching.map Pairing.loser) := by
  induction matching with
  | nil => simp
  | cons pair rest ih =>
      obtain ⟨wa, tail⟩ := List.nodup_cons.mp distinct
      obtain ⟨la, nd⟩ := List.nodup_cons.mp tail
      have di := List.disjoint_left.mp (ih nd)
      apply List.disjoint_left.mpr
      intro x wx lx
      rcases List.mem_cons.mp wx with eqw | wr
      · subst x
        rcases List.mem_cons.mp lx with eql | lr
        · exact wa (by simp [eql])
        · exact wa (List.mem_cons_of_mem _ ((pairingLosers_sublist rest).subset lr))
      · rcases List.mem_cons.mp lx with eql | lr
        · subst x
          exact la ((winner_sublist rest).subset wr)
        · exact di wr lr

theorem deficit_identity {R a o : ℕ} (two : 2 ≤ R) (aBound : a ≤ R)
    (oBound : o ≤ R) :
    (min a (R-1)+1-o)+(a-min a (R-1)) = a+1-o := by omega

theorem realize {n R : ℕ} {oldParams params : Parameters} {physical nextPhysical shadow : State n}
    (id : ℕ) (matching : List (Pairing n))
    (original : Step oldParams physical (.pass id matching) nextPhysical)
    (sameShape : params.toShape = oldParams.toShape) (blocks : shadow.blocks = physical.blocks)
    (valid : shadow.Valid params) (two : 2 ≤ R)
    (oldBound : ∀ element, shadow.value element ≤ R) (cap : R ≤ params.valueBound)
    (target : Element n → ℕ) (positive : ∀ element, 1 ≤ target element)
    (bounded : ∀ element, target element ≤ params.valueBound) :
    ∃ operations,
      Trace params shadow operations (State.mk nextPhysical.blocks target) ∧
      totalActivity operations = matching.length ∧ totalBlockGrowth operations = 0 ∧
      totalInserts operations = 0 ∧
      totalIncreases operations ≤
        (matching.map (VirtualLoserPreparation.deficit shadow)).sum +
        ((List.finRange (2*n+1)).map fun element => target element-shadow.value element).sum := by
  cases original.2.1 with
  | @pass _ _ source _ found matchingValid endpoint values =>
    let winners := matching.map Pairing.winner
    let lowerTarget := fun element => min (shadow.value element) (R-1)
    let lowered := updateState shadow lowerTarget winners
    have shape := VirtualOriginalPassLift.structural sameShape blocks matchingValid
    have nd := (winner_sublist matching).nodup shape.endpoints
    have sep := List.disjoint_left.mp (separate matching shape.endpoints)
    have lowPositive : ∀ element, 1 ≤ lowerTarget element := by
      intro element
      have := (valid.2.1 element).1
      dsimp [lowerTarget]
      omega
    have lowBound : ∀ element, lowerTarget element ≤ params.valueBound := by
      intro element
      exact (min_le_left _ _).trans ((oldBound element).trans cap)
    have lowerTrace := VirtualFiniteRelabel.trace shadow lowerTarget winners valid lowPositive lowBound
    have loweredValid : lowered.Valid params := VirtualGrowingSlot.trace_valid_after lowerTrace
    have lowerBlocks : lowered.blocks = shadow.blocks := updateState_blocks _ _ _
    have winnerValue : ∀ pair ∈ matching, lowered.value pair.winner = lowerTarget pair.winner := by
      intro pair member
      simp [lowered, updateState_values, winners, List.mem_map.mpr ⟨pair, member, rfl⟩]
    have loserValue : ∀ pair ∈ matching, lowered.value pair.loser = shadow.value pair.loser := by
      intro pair member
      have absent : pair.loser ∉ winners := by
        intro present
        exact sep present (List.mem_map.mpr ⟨pair, member, rfl⟩)
      simp [lowered, updateState_values, absent]
    have room : ∀ pair ∈ matching, lowered.value pair.winner+1 ≤ params.valueBound := by
      intro pair member
      rw [winnerValue pair member]
      dsimp [lowerTarget]
      omega
    have lowerUp : totalIncreases (VirtualFiniteRelabel.events shadow lowerTarget winners) = 0 := by
      rw [VirtualFiniteRelabel.increases _ _ _ nd]
      apply List.sum_eq_zero
      intro x member
      obtain ⟨element, _, rfl⟩ := List.mem_map.mp member
      exact Nat.sub_eq_zero_of_le (min_le_left _ _)
    have lowerCounts := VirtualFiniteRelabel.counters shadow lowerTarget winners
    obtain ⟨passTrace, passBlocks, passActivity, passGrowth, passInserts, passUp⟩ :=
      VirtualLoserPreparation.realize lowered id source matching loweredValid
        (by rw [lowerBlocks, blocks]; exact found) (shape.of_blocks_eq lowerBlocks) room
    let passed := afterPass (VirtualLoserPreparation.lifted lowered matching) id source matching
    have passedValid : passed.Valid params := VirtualGrowingSlot.trace_valid_after passTrace
    let restored := updateState passed shadow.value winners
    have restoreTrace := VirtualFiniteRelabel.trace passed shadow.value winners passedValid
      (fun element => (valid.2.1 element).1) (fun element => (oldBound element).trans cap)
    have restoredValid : restored.Valid params := VirtualGrowingSlot.trace_valid_after restoreTrace
    have passedWinner : ∀ pair ∈ matching, passed.value pair.winner = lowerTarget pair.winner := by
      intro pair member
      have absent : pair.winner ∉ matching.map Pairing.loser := by
        exact sep (List.mem_map.mpr ⟨pair, member, rfl⟩)
      change (VirtualLoserPreparation.lifted lowered matching).value pair.winner = _
      rw [VirtualLoserPreparation.lifted_outside _ _ _ absent, winnerValue pair member]
    have restoreUp : totalIncreases (VirtualFiniteRelabel.events passed shadow.value winners) =
        (matching.map fun pair => shadow.value pair.winner-lowerTarget pair.winner).sum := by
      rw [VirtualFiniteRelabel.increases _ _ _ nd]
      simp only [winners, List.map_map]
      congr 1
      apply List.map_congr_left
      intro pair member
      simp [Function.comp_def, passedWinner pair member]
    have restoredMono : ∀ element, shadow.value element ≤ restored.value element := by
      intro element
      rw [show restored.value element = if element ∈ winners then shadow.value element else passed.value element
        from updateState_values _ _ _ _]
      by_cases member : element ∈ winners
      · simp [member]
      · simp only [member, ↓reduceIte]
        have lowEq : lowered.value element = shadow.value element := by
          simp [lowered, updateState_values, member]
        rw [← lowEq]
        exact VirtualLoserPreparation.lifted_mono lowered matching element
    have combinedUp : totalIncreases (VirtualLoserPreparation.events lowered id matching) +
        totalIncreases (VirtualFiniteRelabel.events passed shadow.value winners) =
        (matching.map (VirtualLoserPreparation.deficit shadow)).sum := by
      rw [passUp, restoreUp, ← List.sum_map_add]
      congr 1
      apply List.map_congr_left
      intro pair member
      dsimp [VirtualLoserPreparation.deficit]
      rw [winnerValue pair member, loserValue pair member]
      exact deficit_identity two (oldBound pair.winner) (oldBound pair.loser)
    obtain ⟨normalization, normUp, normA, normQ, normI⟩ :=
      VirtualFiniteRelabel.realize restored target restoredValid positive bounded
    have normBound : totalIncreases (VirtualFiniteRelabel.events restored target (List.finRange (2*n+1))) ≤
        ((List.finRange (2*n+1)).map fun element => target element-shadow.value element).sum := by
      rw [normUp]
      apply List.sum_le_sum
      intro element member
      exact Nat.sub_le_sub_left (restoredMono element) (target element)
    have restoredBlocks : restored.blocks = nextPhysical.blocks := by
      rw [show restored.blocks = passed.blocks from updateState_blocks _ _ _]
      change (afterPass (VirtualLoserPreparation.lifted lowered matching) id source matching).blocks = _
      rw [passBlocks]
      simp only [afterPass, lowerBlocks]
      exact (congrArg (fun bs => Splay.Interface.passBlocks bs id source matching) blocks).trans endpoint.symm
    rw [restoredBlocks] at normalization
    have restoreCounts := VirtualFiniteRelabel.counters passed shadow.value winners
    refine ⟨_, trace_append (trace_append (trace_append lowerTrace passTrace) restoreTrace) normalization,
      ?_, ?_, ?_, ?_⟩
    · simp only [totalActivity_append, lowerCounts.1, passActivity, restoreCounts.1, normA, zero_add, add_zero]
    · simp only [totalBlockGrowth_append, lowerCounts.2.1, passGrowth, restoreCounts.2.1, normQ, zero_add, add_zero]
    · simp only [totalInserts_append, lowerCounts.2.2, passInserts, restoreCounts.2.2, normI, zero_add, add_zero]
    · rw [totalIncreases_append, totalIncreases_append, totalIncreases_append, lowerUp]
      omega

end Splay.Research.CappedOriginalPassLift

#print axioms Splay.Research.CappedOriginalPassLift.realize
