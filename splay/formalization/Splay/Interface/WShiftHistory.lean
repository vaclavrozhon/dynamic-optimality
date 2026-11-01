import Splay.Interface.LifetimeHistory
import Splay.Interface.ShiftAccounting

namespace Splay.Interface

/--
One directed edge in a creator-snapshot chain.

The first component is the creator value frozen when the current episode
opened.  The second component is the creator value frozen when the next
episode opens after the element loses a pass pairing.
-/
abbrev WTransition :=
  ℕ × ℕ

namespace WTransition

/-- Signed contribution of one creator-snapshot transition. -/
def shift (transition : WTransition) : ℤ :=
  (transition.2 : ℤ) - (transition.1 : ℤ)

end WTransition

namespace PairShiftSnapshot

/-- The `w`-shift projection of one complete pair snapshot. -/
def wTransition (snapshot : PairShiftSnapshot) : WTransition :=
  (snapshot.loserCreatorAtJoin, snapshot.winnerNow)

/--
Build the complete pair snapshot from the two active lifetime episodes at a
pass pairing.  The winner episode supplies the pair-rank fields; the loser
episode supplies the old endpoint of the `w`-transition.
-/
def ofEpisodeStarts {n : ℕ}
    (before : State n) (pairing : Pairing n)
    (winnerStart loserStart : EpisodeStart n)
    (winnerValid : winnerStart.JoinValid) :
    PairShiftSnapshot :=
  { winnerAtJoin := winnerStart.join.valueAtJoin
    winnerCreatorAtJoin := winnerStart.creatorValueAtJoin
    winnerNow := before.value pairing.winner
    loserCreatorAtJoin := loserStart.creatorValueAtJoin
    joinedAboveCreator := winnerValid }

@[simp]
theorem wTransition_ofEpisodeStarts
    {n : ℕ} (before : State n) (pairing : Pairing n)
    (winnerStart loserStart : EpisodeStart n)
    (winnerValid : winnerStart.JoinValid) :
    (ofEpisodeStarts before pairing winnerStart loserStart
        winnerValid).wTransition =
      (loserStart.creatorValueAtJoin,
        before.value pairing.winner) :=
  rfl

/--
Canonical complete snapshot of one legal pass pairing, using the starts chosen
by `LifetimeHistory`'s exact-ledger API.
-/
noncomputable def ofLifetimePass
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length)
    (pairing_mem : pairing ∈ matching) :
    PairShiftSnapshot :=
  let starts :=
    exact.pass_pairing_starts step aligned pairing_mem
  ofEpisodeStarts before pairing starts.winnerStart starts.loserStart
    starts.winnerJoinValid

@[simp]
theorem wTransition_ofLifetimePass
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length)
    (pairing_mem : pairing ∈ matching) :
    (ofLifetimePass exact step aligned pairing_mem).wTransition =
      ((exact.pass_pairing_starts step aligned pairing_mem).loserStart.creatorValueAtJoin,
        before.value pairing.winner) := by
  rfl

/-- Canonical complete snapshot list of every pairing in one legal pass. -/
noncomputable def lifetimePassSnapshots
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length) :
    List PairShiftSnapshot :=
  matching.attach.map fun attached =>
    ofLifetimePass exact step aligned attached.2

@[simp]
theorem length_lifetimePassSnapshots
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length) :
    (lifetimePassSnapshots exact step aligned).length =
      matching.length := by
  simp [lifetimePassSnapshots]

@[simp]
theorem shift_wTransition (snapshot : PairShiftSnapshot) :
    snapshot.wTransition.shift = snapshot.wShift :=
  rfl

end PairShiftSnapshot

/-- Chronological `w`-transition projection of all pass-pair snapshots. -/
def snapshotWTransitions
    (snapshots : List PairShiftSnapshot) : List WTransition :=
  snapshots.map PairShiftSnapshot.wTransition

/-- All adjacent transitions beginning at one initial creator snapshot. -/
def snapshotTransitionsFrom : ℕ → List ℕ → List WTransition
  | _, [] => []
  | previous, next :: tail =>
      (previous, next) :: snapshotTransitionsFrom next tail

/-- All adjacent transitions of one insert-rooted snapshot chain. -/
def snapshotChainTransitions (chain : SnapshotChain) : List WTransition :=
  snapshotTransitionsFrom chain.1 chain.2

/-- Transition multiset of a finite family of insert-rooted chains. -/
def snapshotChainsTransitions
    (chains : List SnapshotChain) : List WTransition :=
  chains.flatMap snapshotChainTransitions

/-- Signed sum of a chronological or permuted transition collection. -/
def totalWTransitionShift
    (transitions : List WTransition) : ℤ :=
  (transitions.map WTransition.shift).sum

@[simp]
theorem totalWTransitionShift_nil :
    totalWTransitionShift [] = 0 :=
  rfl

@[simp]
theorem totalWTransitionShift_cons
    (transition : WTransition) (transitions : List WTransition) :
    totalWTransitionShift (transition :: transitions) =
      transition.shift + totalWTransitionShift transitions :=
  rfl

@[simp]
theorem totalWTransitionShift_append
    (first second : List WTransition) :
    totalWTransitionShift (first ++ second) =
      totalWTransitionShift first + totalWTransitionShift second := by
  simp [totalWTransitionShift]

/-- Projecting complete pair snapshots preserves their exact total `w`-shift. -/
theorem totalWTransitionShift_snapshotWTransitions
    (snapshots : List PairShiftSnapshot) :
    totalWTransitionShift (snapshotWTransitions snapshots) =
      totalWShift snapshots := by
  simp [totalWTransitionShift, snapshotWTransitions, totalWShift,
    Function.comp_def]

/-- The edge sum of one chain is exactly its recursive telescoping shift. -/
theorem totalWTransitionShift_snapshotChainTransitions
    (chain : SnapshotChain) :
    totalWTransitionShift (snapshotChainTransitions chain) =
      snapshotShift chain.1 chain.2 := by
  rcases chain with ⟨initial, rest⟩
  induction rest generalizing initial with
  | nil =>
      rfl
  | cons next rest ih =>
      simp only [snapshotChainTransitions, snapshotTransitionsFrom,
        totalWTransitionShift_cons, WTransition.shift, snapshotShift_cons]
      have tail := ih next
      simp only [snapshotChainTransitions] at tail
      rw [tail]

/-- Flattening a family of chains preserves the sum of their telescoping shifts. -/
theorem totalWTransitionShift_snapshotChainsTransitions
    (chains : List SnapshotChain) :
    totalWTransitionShift (snapshotChainsTransitions chains) =
      totalSnapshotShift chains := by
  induction chains with
  | nil =>
      rfl
  | cons chain chains ih =>
      simp only [snapshotChainsTransitions, List.flatMap_cons,
        totalWTransitionShift_append, totalSnapshotShift,
        List.map_cons, List.sum_cons]
      rw [totalWTransitionShift_snapshotChainTransitions]
      change
        snapshotShift chain.1 chain.2 +
            totalWTransitionShift (snapshotChainsTransitions chains) =
          snapshotShift chain.1 chain.2 +
            totalSnapshotShift chains
      rw [ih]

/-- A permutation of transition edges does not change their signed sum. -/
theorem totalWTransitionShift_eq_of_perm
    {first second : List WTransition}
    (permuted : first.Perm second) :
    totalWTransitionShift first =
      totalWTransitionShift second :=
  (permuted.map WTransition.shift).sum_eq

/--
Explicit global partition certificate for the manuscript's `w`-shift
telescoping argument.

The permutation field says that every pass-pair `w`-transition occurs exactly
once in one insert-rooted chain.  `chain_count` is the promised bijection
between chains and `Insert` operations.  The terminal bound is the only
arithmetic fact needed after cancellation; for certificates extracted from a
legal lifetime history it follows from `State.Valid`.
-/
structure SnapshotChainPartition {n : ℕ}
    (params : Parameters) (operations : List (Operation n))
    (snapshots : List PairShiftSnapshot) where
  chains : List SnapshotChain
  transitions_perm :
    (snapshotWTransitions snapshots).Perm
      (snapshotChainsTransitions chains)
  chain_count :
    chains.length = totalInserts operations
  terminal_le :
    ∀ chain ∈ chains,
      terminalSnapshot chain.1 chain.2 ≤ params.valueBound

namespace SnapshotChainPartition

/-- The certificate turns the complete `w`-sum into a family of chain sums. -/
theorem totalWShift_eq_totalSnapshotShift
    {n : ℕ} {params : Parameters}
    {operations : List (Operation n)}
    {snapshots : List PairShiftSnapshot}
  (partition :
      SnapshotChainPartition params operations snapshots) :
    totalWShift snapshots =
      totalSnapshotShift partition.chains := by
  rw [← totalWTransitionShift_snapshotWTransitions]
  rw [totalWTransitionShift_eq_of_perm partition.transitions_perm]
  exact totalWTransitionShift_snapshotChainsTransitions partition.chains

/--
Global `w`-shift bound for snapshots partitioned by their exact lifetime
chains.  The result has precisely the form consumed by
`shiftCharge_of_aggregateBounds`.
-/
theorem totalWShift_le_valueBound_mul_totalInserts
    {n : ℕ} {params : Parameters}
    {operations : List (Operation n)}
    {snapshots : List PairShiftSnapshot}
    (partition :
      SnapshotChainPartition params operations snapshots) :
    totalWShift snapshots ≤
      ((params.valueBound * totalInserts operations : ℕ) : ℤ) := by
  rw [partition.totalWShift_eq_totalSnapshotShift]
  have bounded :=
    totalSnapshotShift_le partition.chains params.valueBound
      partition.terminal_le
  calc
    totalSnapshotShift partition.chains ≤
        ((partition.chains.length * params.valueBound : ℕ) : ℤ) :=
      bounded
    _ = ((params.valueBound * totalInserts operations : ℕ) : ℤ) := by
      rw [partition.chain_count]
      simp only [Nat.cast_mul]
      ring

end SnapshotChainPartition

/--
The creator snapshot installed by any legal join is inside the global value
range.  This is the local source of `SnapshotChainPartition.terminal_le`.
-/
theorem EpisodeStart.ofJoin_creatorValue_bounds
    {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    (step : Step params before operation after)
    (join : JoinOccurrence n) :
    1 ≤ (EpisodeStart.ofJoin before join).creatorValueAtJoin ∧
      (EpisodeStart.ofJoin before join).creatorValueAtJoin ≤
        params.valueBound := by
  simpa [EpisodeStart.ofJoin] using
    step.1.2.1 join.destinationCreator

namespace EpisodeLedger

/-- Every currently open episode has a bounded frozen creator snapshot. -/
def CreatorSnapshotsBound {n : ℕ}
    (params : Parameters) (ledger : EpisodeLedger n) : Prop :=
  ∀ element start, ledger element = some start →
    start.creatorValueAtJoin ≤ params.valueBound

theorem creatorSnapshotsBound_empty
    {n : ℕ} (params : Parameters) :
    CreatorSnapshotsBound params (EpisodeLedger.empty : EpisodeLedger n) := by
  intro element start active
  simp [EpisodeLedger.empty] at active

/--
Installing a pass matching preserves the historical bound, because every new
creator snapshot is read from the same valid pre-state.
-/
theorem creatorSnapshotsBound_installPassJoins
    {n : ℕ} {params : Parameters}
    (before : State n) (labels : RootLabels) (source : BlockId)
    (before_valid : before.Valid params)
    (matching : List (Pairing n)) (ledger : EpisodeLedger n)
    (bounded : CreatorSnapshotsBound params ledger) :
    CreatorSnapshotsBound params
      (EpisodeLedger.installPassJoins
        before labels source ledger matching) := by
  induction matching generalizing ledger with
  | nil =>
      exact bounded
  | cons pairing matching ih =>
      rw [EpisodeLedger.installPassJoins_cons]
      apply ih
      intro element start active
      by_cases element_eq : element = pairing.loser
      · subst element
        simp only [Function.update_self, Option.some.injEq] at active
        subst start
        simp only [EpisodeStart.ofJoin_creatorValueAtJoin]
        exact before_valid.2.1
          (makeJoinOccurrence before labels
            (.pass source pairing.winner) pairing.loser
            pairing.destination pairing.winner).destinationCreator |>.2
      · have unchanged : ledger element = some start := by
          simpa [Function.update, element_eq] using active
        exact bounded element start unchanged

/-- The bounded-snapshot invariant is preserved by every legal operation. -/
theorem CreatorSnapshotsBound.after_step
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n} {ledger : EpisodeLedger n}
    (bounded : CreatorSnapshotsBound params ledger)
    (step : Step params before operation after) :
    CreatorSnapshotsBound params
      (EpisodeLedger.after before labels ledger operation) := by
  cases operation with
  | convert blockId =>
      simpa using bounded
  | create creator =>
      simpa using bounded
  | insert destination inserted =>
      intro element start active
      by_cases element_eq : element = inserted
      · subst element
        simp only [EpisodeLedger.after, Function.update_self,
          Option.some.injEq] at active
        subst start
        exact
          (EpisodeStart.ofJoin_creatorValue_bounds step
            (makeJoinOccurrence before labels .insert inserted
              destination inserted)).2
      · have unchanged : ledger element = some start := by
          simpa [EpisodeLedger.after,
            Function.update, element_eq] using active
        exact bounded element start unchanged
  | delete source deleted =>
      intro element start active
      by_cases element_eq : element = deleted
      · subst element
        simp [EpisodeLedger.after] at active
      · have unchanged : ledger element = some start := by
          simpa [EpisodeLedger.after,
            Function.update, element_eq] using active
        exact bounded element start unchanged
  | pass source matching =>
      exact
        creatorSnapshotsBound_installPassJoins
          before labels source step.1 matching ledger bounded
  | split source prefixLength =>
      simpa using bounded
  | valueChange element delta =>
      simpa using bounded

end EpisodeLedger

/--
An exact insert opens one bounded initial snapshot, hence one future
insert-rooted chain.
-/
theorem insert_opens_creatorSnapshot
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {destination : BlockId} {element : Element n}
    (step :
      Step params before (.insert destination element) after)
    (ledger : EpisodeLedger n) :
    ∃ start : EpisodeStart n,
      EpisodeLedger.after before labels ledger
          (.insert destination element) element =
        some start ∧
      start.creatorValueAtJoin ≤ params.valueBound := by
  let joined :=
    makeJoinOccurrence before labels .insert element destination element
  have joined_mem :
      joined ∈
        operationJoinOccurrences before labels
          (.insert destination element) := by
    simp [joined]
  have installed :
      EpisodeLedger.after before labels ledger
          (.insert destination element) element =
        some (EpisodeStart.ofJoin before joined) :=
    EpisodeLedger.after_apply_eq_some_of_join
      step ledger joined_mem
  exact
    ⟨EpisodeStart.ofJoin before joined, installed,
      (EpisodeStart.ofJoin_creatorValue_bounds step joined).2⟩

/-- An exact delete closes the selected chain and leaves no active episode. -/
@[simp]
theorem delete_closes_creatorSnapshot
    {n : ℕ} (before : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (source : BlockId)
    (element : Element n) :
    EpisodeLedger.after before labels ledger
        (.delete source element) element = none := by
  simp [EpisodeLedger.after]

/--
Lifetime-ledger extraction of the `w`-transition made by one pass pairing.

The old endpoint is the immutable creator snapshot of the loser's active
episode.  The new endpoint is the current value of the pairing winner, which
is also the creator snapshot installed for the new destination episode.
-/
def lifetimePassWTransition {n : ℕ}
    (before : State n) (ledger : EpisodeLedger n)
    (pairing : Pairing n) : Option WTransition :=
  (ledger pairing.loser).map fun start =>
    (start.creatorValueAtJoin, before.value pairing.winner)

/-- Extract all lifetime-ledger `w`-transitions of one matching, in order. -/
def lifetimePassWTransitions {n : ℕ}
    (before : State n) (ledger : EpisodeLedger n)
    (matching : List (Pairing n)) : List WTransition :=
  matching.filterMap (lifetimePassWTransition before ledger)

@[simp]
theorem lifetimePassWTransition_of_active
    {n : ℕ} (before : State n) (ledger : EpisodeLedger n)
    (pairing : Pairing n) (start : EpisodeStart n)
    (active : ledger pairing.loser = some start) :
    lifetimePassWTransition before ledger pairing =
      some (start.creatorValueAtJoin, before.value pairing.winner) := by
  simp [lifetimePassWTransition, active]

/--
One exact lifetime pass replaces the loser's active creator snapshot by the
second endpoint of its extracted `w`-transition.
-/
theorem pass_installs_wTransition_endpoint
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {source : BlockId} {matching : List (Pairing n)}
    (step : Step params before (.pass source matching) after)
    (ledger : EpisodeLedger n)
    {pairing : Pairing n} (pairing_mem : pairing ∈ matching)
    {start : EpisodeStart n}
    (active : ledger pairing.loser = some start) :
    ∃ newStart : EpisodeStart n,
      EpisodeLedger.after before labels ledger
          (.pass source matching) pairing.loser =
        some newStart ∧
      newStart.creatorValueAtJoin = before.value pairing.winner ∧
      lifetimePassWTransition before ledger pairing =
        some
          (start.creatorValueAtJoin,
            newStart.creatorValueAtJoin) := by
  let joined :=
    makeJoinOccurrence before labels
      (.pass source pairing.winner) pairing.loser
      pairing.destination pairing.winner
  have joined_mem :
      joined ∈
        operationJoinOccurrences before labels
          (.pass source matching) := by
    apply List.mem_map.mpr
    exact ⟨pairing, pairing_mem, rfl⟩
  have installed :
      EpisodeLedger.after before labels ledger
          (.pass source matching) pairing.loser =
        some (EpisodeStart.ofJoin before joined) :=
    EpisodeLedger.after_apply_eq_some_of_join
      step ledger joined_mem
  obtain ⟨sourceBlock, source_found, valid_matching⟩ :
      ∃ sourceBlock,
        before.block? source = some sourceBlock ∧
          MatchingValid params before source sourceBlock matching := by
    cases step.2.1 with
    | pass found valid_matching blocks_eq values_eq =>
        exact ⟨_, found, valid_matching⟩
  have pairing_valid :=
    valid_matching.2.2.2.1 pairing pairing_mem
  obtain ⟨destinationBlock, destination_found,
      destination_growing, destination_creator⟩ :=
    pairing_valid.2.2.2
  have creator_eq :
      (EpisodeStart.ofJoin before joined).creatorValueAtJoin =
        before.value pairing.winner := by
    simp [EpisodeStart.ofJoin, joined, makeJoinOccurrence,
      destination_found, destination_creator]
  refine
    ⟨EpisodeStart.ofJoin before joined, installed, creator_eq, ?_⟩
  rw [lifetimePassWTransition_of_active
    before ledger pairing start active]
  exact congrArg
    (fun value =>
      some (start.creatorValueAtJoin, value))
    creator_eq.symm

/--
Consequently the extracted edge contributes exactly the `new - old` term
used in `PairShiftSnapshot.wShift`.
-/
theorem shift_lifetimePassWTransition_of_active
    {n : ℕ} (before : State n) (ledger : EpisodeLedger n)
    (pairing : Pairing n) (start : EpisodeStart n)
    (_active : ledger pairing.loser = some start) :
    WTransition.shift
        (start.creatorValueAtJoin, before.value pairing.winner) =
      (before.value pairing.winner : ℤ) -
        (start.creatorValueAtJoin : ℤ) := by
  rfl

/-- Membership in a found block implies membership in the state's payload. -/
theorem element_mem_allElements_of_block_found
    {n : ℕ} {state : State n} {blockId : BlockId}
    {block : Block n} {element : Element n}
    (found : state.block? blockId = some block)
    (member : element ∈ block.elements) :
    element ∈ state.allElements := by
  obtain ⟨block_lt, block_eq⟩ :=
    List.getElem?_eq_some_iff.mp found
  unfold State.allElements
  apply List.mem_flatMap_of_mem (List.getElem_mem block_lt)
  simpa [block_eq] using member

/--
Every legal pass pairing has a complete `PairShiftSnapshot` extracted from
the exact lifetime ledger, and its `w`-projection is precisely the ledger
transition used by the chain partition.
-/
theorem exists_pairShiftSnapshot_of_pass
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {source : BlockId} {matching : List (Pairing n)}
    (step : Step params before (.pass source matching) after)
    (ledger : EpisodeLedger n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    {pairing : Pairing n} (pairing_mem : pairing ∈ matching) :
    ∃ winnerStart loserStart : EpisodeStart n,
      ∃ winnerValid : winnerStart.JoinValid,
        ledger pairing.winner = some winnerStart ∧
        ledger pairing.loser = some loserStart ∧
        (PairShiftSnapshot.ofEpisodeStarts before pairing
            winnerStart loserStart winnerValid).wTransition =
          (loserStart.creatorValueAtJoin,
            before.value pairing.winner) := by
  obtain ⟨sourceBlock, source_found, valid_matching⟩ :
      ∃ sourceBlock,
        before.block? source = some sourceBlock ∧
          MatchingValid params before source sourceBlock matching := by
    cases step.2.1 with
    | pass found valid_matching blocks_eq values_eq =>
        exact ⟨_, found, valid_matching⟩
  have pairing_valid :=
    valid_matching.2.2.2.1 pairing pairing_mem
  have winner_assigned :
      pairing.winner ∈ before.allElements :=
    element_mem_allElements_of_block_found source_found
      pairing_valid.1.first_mem
  have loser_assigned :
      pairing.loser ∈ before.allElements :=
    element_mem_allElements_of_block_found source_found
      pairing_valid.1.second_mem
  obtain ⟨winnerStart, winner_active⟩ :=
    exact.complete pairing.winner winner_assigned
  obtain ⟨loserStart, loser_active⟩ :=
    exact.complete pairing.loser loser_assigned
  have winner_valid :
      winnerStart.JoinValid :=
    exact.joinSound pairing.winner winnerStart winner_active
  exact
    ⟨winnerStart, loserStart, winner_valid, winner_active,
      loser_active, rfl⟩

end Splay.Interface
