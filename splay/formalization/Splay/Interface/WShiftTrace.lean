import Splay.Interface.ValueShiftHistory

namespace Splay.Interface

/-- Complete pair snapshots contributed by one exact lifetime-history step. -/
noncomputable def operationPairShiftSnapshots
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length) :
    List PairShiftSnapshot :=
  match operation with
  | .pass _ _ =>
      PairShiftSnapshot.lifetimePassSnapshots exact step aligned
  | _ => []

/-- One exact step produces exactly one complete snapshot per activity unit. -/
@[simp]
theorem length_operationPairShiftSnapshots
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length) :
    (operationPairShiftSnapshots before after labels ledger operation
        exact step aligned).length =
      operation.activity := by
  cases operation <;>
    simp [operationPairShiftSnapshots, Operation.activity]

/-- Every complete snapshot extracted by one step is globally value-bounded. -/
theorem valuesBound_operationPairShiftSnapshots
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (frozen : EpisodeLedger.FrozenValuesBound params ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length) :
    ∀ snapshot ∈
        operationPairShiftSnapshots before after labels ledger operation
          exact step aligned,
      snapshot.ValuesBound params.valueBound := by
  cases operation with
  | pass source matching =>
      exact
        PairShiftSnapshot.valuesBound_lifetimePassSnapshots
          exact frozen step aligned
  | convert blockId =>
      simp [operationPairShiftSnapshots]
  | create creator =>
      simp [operationPairShiftSnapshots]
  | insert destination element =>
      simp [operationPairShiftSnapshots]
  | delete source element =>
      simp [operationPairShiftSnapshots]
  | split source prefixLength =>
      simp [operationPairShiftSnapshots]
  | valueChange element delta =>
      simp [operationPairShiftSnapshots]

/-- One insert-rooted chain tagged by the element whose episodes it follows. -/
abbrev TaggedSnapshotChain (n : ℕ) :=
  Element n × SnapshotChain

/-- All chains opened so far, newest first. Closed chains remain archived. -/
abbrev SnapshotChainArchive (n : ℕ) :=
  List (TaggedSnapshotChain n)

namespace SnapshotChainArchive

/-- Erase element tags before applying the arithmetic chain accounting. -/
def chains {n : ℕ}
    (archive : SnapshotChainArchive n) : List SnapshotChain :=
  archive.map Prod.snd

/-- All transition edges currently stored in the archive. -/
def transitions {n : ℕ}
    (archive : SnapshotChainArchive n) : List WTransition :=
  snapshotChainsTransitions archive.chains

/-- The newest chain of an element, whether active or already closed. -/
def current? {n : ℕ} (archive : SnapshotChainArchive n)
    (element : Element n) : Option SnapshotChain :=
  match archive with
  | [] => none
  | tagged :: tail =>
      if tagged.1 = element then some tagged.2
      else current? tail element

/-- Open a new insert-rooted chain. -/
def openChain {n : ℕ} (archive : SnapshotChainArchive n)
    (element : Element n) (initial : ℕ) : SnapshotChainArchive n :=
  (element, (initial, [])) :: archive

/-- Append one creator snapshot to a chain. -/
def extendChain (chain : SnapshotChain) (next : ℕ) : SnapshotChain :=
  (chain.1, chain.2 ++ [next])

/-- Extend the newest chain of an element, if it exists. -/
def advance {n : ℕ} (archive : SnapshotChainArchive n)
    (element : Element n) (next : ℕ) : SnapshotChainArchive n :=
  match archive with
  | [] => []
  | tagged :: tail =>
      if tagged.1 = element then
        (tagged.1, extendChain tagged.2 next) :: tail
      else tagged :: advance tail element next

@[simp]
theorem chains_nil {n : ℕ} :
    chains ([] : SnapshotChainArchive n) = [] :=
  rfl

@[simp]
theorem chains_open {n : ℕ} (archive : SnapshotChainArchive n)
    (element : Element n) (initial : ℕ) :
    chains (openChain archive element initial) =
      (initial, []) :: archive.chains :=
  rfl

@[simp]
theorem current?_open_self {n : ℕ}
    (archive : SnapshotChainArchive n) (element : Element n)
    (initial : ℕ) :
    current? (openChain archive element initial) element =
      some (initial, []) := by
  simp [openChain, current?]

@[simp]
theorem current?_open_of_ne {n : ℕ}
    (archive : SnapshotChainArchive n) {opened other : Element n}
    (initial : ℕ) (different : opened ≠ other) :
    current? (openChain archive opened initial) other =
      current? archive other := by
  simp [openChain, current?, different]

@[simp]
theorem terminalSnapshot_extend
    (chain : SnapshotChain) (next : ℕ) :
    terminalSnapshot (extendChain chain next).1 (extendChain chain next).2 =
      next := by
  rcases chain with ⟨initial, rest⟩
  induction rest generalizing initial with
  | nil =>
      rfl
  | cons head tail ih =>
      simpa [extendChain, terminalSnapshot] using ih head

theorem current?_advance_of_current
    {n : ℕ} {archive : SnapshotChainArchive n}
    {element : Element n} {chain : SnapshotChain} (next : ℕ)
    (current : current? archive element = some chain) :
    current? (advance archive element next) element =
      some (extendChain chain next) := by
  induction archive with
  | nil =>
      simp [current?] at current
  | cons tagged tail ih =>
      rcases tagged with ⟨tag, headChain⟩
      by_cases same : tag = element
      · subst tag
        simp [current?, advance] at current ⊢
        exact congrArg (fun old => extendChain old next) current
      · simp [current?, advance, same] at current ⊢
        exact ih current

theorem current?_advance_of_ne
    {n : ℕ} (archive : SnapshotChainArchive n)
    {advanced other : Element n} (next : ℕ)
    (different : advanced ≠ other) :
    current? (advance archive advanced next) other =
      current? archive other := by
  induction archive with
  | nil =>
      rfl
  | cons tagged tail ih =>
      rcases tagged with ⟨tag, headChain⟩
      by_cases advances_head : tag = advanced
      · subst tag
        have not_other : advanced ≠ other := different
        simp [advance, current?, not_other]
      · by_cases is_other : tag = other
        · subst tag
          simp [advance, current?, advances_head]
        · simp [advance, current?, advances_head, is_other, ih]

/-- Extending a chain appends exactly its terminal-to-new transition. -/
theorem snapshotChainTransitions_extend
    (chain : SnapshotChain) (next : ℕ) :
    snapshotChainTransitions (extendChain chain next) =
      snapshotChainTransitions chain ++
        [(terminalSnapshot chain.1 chain.2, next)] := by
  rcases chain with ⟨initial, rest⟩
  induction rest generalizing initial with
  | nil =>
      rfl
  | cons head tail ih =>
      simp only [extendChain, snapshotChainTransitions,
        snapshotTransitionsFrom, terminalSnapshot_cons,
        List.cons_append]
      congr 1
      have tail_result := ih head
      simpa only [extendChain, snapshotChainTransitions] using tail_result

/--
One successful archive advance adds exactly one transition edge, up to the
irrelevant order in which different element chains are flattened.
-/
theorem transitions_append_singleton_perm_advance
    {n : ℕ} {archive : SnapshotChainArchive n}
    {element : Element n} {chain : SnapshotChain} {next : ℕ}
    (current : current? archive element = some chain) :
    (transitions archive ++
        [(terminalSnapshot chain.1 chain.2, next)]).Perm
      (transitions (advance archive element next)) := by
  induction archive with
  | nil =>
      simp [current?] at current
  | cons tagged tail ih =>
      rcases tagged with ⟨tag, headChain⟩
      by_cases same : tag = element
      · subst tag
        simp [current?] at current
        have chain_eq : headChain = chain := current
        subst chain
        simp only [transitions, chains, List.map_cons,
          snapshotChainsTransitions, List.flatMap_cons, advance,
          if_pos]
        rw [snapshotChainTransitions_extend]
        simpa only [snapshotChainsTransitions, List.append_assoc] using
          List.Perm.append_left
            (snapshotChainTransitions headChain)
            (List.perm_append_comm
              (l₁ := snapshotChainsTransitions (List.map Prod.snd tail))
              (l₂ := [(terminalSnapshot headChain.1 headChain.2, next)]))
      · simp [current?, same] at current
        have tail_perm := ih current
        simp only [transitions, chains, List.map_cons,
          snapshotChainsTransitions, List.flatMap_cons, advance,
          if_neg same]
        simpa only [transitions, chains, snapshotChainsTransitions,
          List.append_assoc] using
          List.Perm.append_left
            (snapshotChainTransitions headChain) tail_perm

/-- Advance all loser chains of one pass, in matching order. -/
def advancePass {n : ℕ} (before : State n) :
    SnapshotChainArchive n → List (Pairing n) → SnapshotChainArchive n
  | archive, [] => archive
  | archive, pairing :: matching =>
      advancePass before
        (advance archive pairing.loser (before.value pairing.winner))
        matching

@[simp]
theorem advancePass_nil {n : ℕ} (before : State n)
    (archive : SnapshotChainArchive n) :
    advancePass before archive [] = archive :=
  rfl

@[simp]
theorem advancePass_cons {n : ℕ} (before : State n)
    (archive : SnapshotChainArchive n) (pairing : Pairing n)
    (matching : List (Pairing n)) :
    advancePass before archive (pairing :: matching) =
      advancePass before
        (advance archive pairing.loser (before.value pairing.winner))
        matching :=
  rfl

/-- A pass does not alter the newest chain of an element that is not a loser. -/
theorem current?_advancePass_of_not_mem
    {n : ℕ} (before : State n) (archive : SnapshotChainArchive n)
    (matching : List (Pairing n)) (element : Element n)
    (not_loser : element ∉ pairingLosers matching) :
    current? (advancePass before archive matching) element =
      current? archive element := by
  induction matching generalizing archive with
  | nil =>
      rfl
  | cons pairing matching ih =>
      have not_cons :
          element ∉ pairing.loser :: pairingLosers matching := by
        simpa [pairingLosers] using not_loser
      have different : pairing.loser ≠ element :=
        Ne.symm (List.ne_and_not_mem_of_not_mem_cons not_cons).1
      have not_tail : element ∉ pairingLosers matching :=
        (List.ne_and_not_mem_of_not_mem_cons not_cons).2
      rw [advancePass_cons, ih _ not_tail]
      exact
        current?_advance_of_ne archive
          (before.value pairing.winner) different

/--
With distinct losers, the final newest chain at a selected loser is exactly
its old chain extended by that pairing's new creator snapshot.
-/
theorem current?_advancePass_of_mem
    {n : ℕ} (before : State n) (archive : SnapshotChainArchive n)
    {matching : List (Pairing n)}
    (losers_nodup : (pairingLosers matching).Nodup)
    {pairing : Pairing n} (pairing_mem : pairing ∈ matching)
    {chain : SnapshotChain}
    (current : current? archive pairing.loser = some chain) :
    current? (advancePass before archive matching) pairing.loser =
      some (extendChain chain (before.value pairing.winner)) := by
  induction matching generalizing archive pairing chain with
  | nil =>
      simp at pairing_mem
  | cons head matching ih =>
      have nodup_cons :
          (head.loser :: pairingLosers matching).Nodup := by
        simpa [pairingLosers] using losers_nodup
      rcases List.mem_cons.mp pairing_mem with pairing_eq | pairing_tail
      · subst pairing
        have head_not_tail :
            head.loser ∉ pairingLosers matching := by
          exact (List.nodup_cons.mp nodup_cons).1
        rw [advancePass_cons,
          current?_advancePass_of_not_mem
            before _ matching head.loser head_not_tail]
        exact
          current?_advance_of_current
            (before.value head.winner) current
      · have tail_nodup : (pairingLosers matching).Nodup := by
          exact (List.nodup_cons.mp nodup_cons).2
        have different : head.loser ≠ pairing.loser := by
          intro same
          have head_mem_tail : head.loser ∈ pairingLosers matching := by
            rw [same]
            exact List.mem_map.mpr ⟨pairing, pairing_tail, rfl⟩
          exact
            (List.nodup_cons.mp nodup_cons).1 head_mem_tail
        rw [advancePass_cons]
        apply ih
          (archive :=
            advance archive head.loser (before.value head.winner))
          tail_nodup pairing_tail
        rw [current?_advance_of_ne archive
          (before.value head.winner) different]
        exact current

/--
Advancing a pass adds precisely one edge per matching pair.  The archive
flattening order is intentionally recorded only up to permutation.
-/
theorem transitions_append_map_perm_advancePass
    {n : ℕ} (before : State n) (archive : SnapshotChainArchive n)
    (matching : List (Pairing n)) (old : Pairing n → ℕ)
    (losers_nodup : (pairingLosers matching).Nodup)
    (current :
      ∀ pairing ∈ matching,
        ∃ chain,
          current? archive pairing.loser = some chain ∧
            terminalSnapshot chain.1 chain.2 = old pairing) :
    (transitions archive ++
        matching.map fun pairing =>
          (old pairing, before.value pairing.winner)).Perm
      (transitions (advancePass before archive matching)) := by
  induction matching generalizing archive with
  | nil =>
      simp
  | cons head matching ih =>
      have nodup_cons :
          (head.loser :: pairingLosers matching).Nodup := by
        simpa [pairingLosers] using losers_nodup
      obtain ⟨headChain, head_current, head_terminal⟩ :=
        current head (by simp)
      have head_perm :=
        transitions_append_singleton_perm_advance
          (next := before.value head.winner) head_current
      have tail_current :
          ∀ pairing ∈ matching,
            ∃ chain,
              current?
                  (advance archive head.loser (before.value head.winner))
                  pairing.loser =
                some chain ∧
                terminalSnapshot chain.1 chain.2 = old pairing := by
        intro pairing pairing_mem
        obtain ⟨chain, chain_current, chain_terminal⟩ :=
          current pairing (by simp [pairing_mem])
        have different : head.loser ≠ pairing.loser := by
          intro same
          apply (List.nodup_cons.mp nodup_cons).1
          rw [same]
          exact List.mem_map.mpr ⟨pairing, pairing_mem, rfl⟩
        refine ⟨chain, ?_, chain_terminal⟩
        rw [current?_advance_of_ne archive
          (before.value head.winner) different]
        exact chain_current
      have tail_perm :=
        ih
          (archive :=
            advance archive head.loser (before.value head.winner))
          (List.nodup_cons.mp nodup_cons).2 tail_current
      rw [advancePass_cons]
      have head_perm' :
          (transitions archive ++
              [(old head, before.value head.winner)]).Perm
            (transitions
              (advance archive head.loser
                (before.value head.winner))) := by
        simpa [head_terminal] using head_perm
      have combined :
          (transitions archive ++
              (old head, before.value head.winner) ::
                matching.map fun pairing =>
                  (old pairing, before.value pairing.winner)).Perm
            (transitions
                (advance archive head.loser
                  (before.value head.winner)) ++
              matching.map fun pairing =>
                (old pairing, before.value pairing.winner)) := by
        simpa [List.append_assoc] using
          head_perm'.append_right
            (matching.map fun pairing =>
              (old pairing, before.value pairing.winner))
      exact combined.trans tail_perm

end SnapshotChainArchive

namespace EpisodeLedger

/-- Total projection of an active episode's frozen creator value. -/
def activeCreatorSnapshot {n : ℕ} (ledger : EpisodeLedger n)
    (element : Element n) : ℕ :=
  ((ledger element).map EpisodeStart.creatorValueAtJoin).getD 0

@[simp]
theorem activeCreatorSnapshot_of_active
    {n : ℕ} (ledger : EpisodeLedger n) (element : Element n)
    (start : EpisodeStart n)
    (active : ledger element = some start) :
    activeCreatorSnapshot ledger element =
      start.creatorValueAtJoin := by
  simp [activeCreatorSnapshot, active]

end EpisodeLedger

/--
The canonical exact snapshots of one pass project to the ledger's active
creator endpoints, in the original matching order.
-/
theorem snapshotWTransitions_lifetimePassSnapshots
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length) :
    snapshotWTransitions
        (PairShiftSnapshot.lifetimePassSnapshots exact step aligned) =
      matching.map fun pairing =>
        (ledger.activeCreatorSnapshot pairing.loser,
          before.value pairing.winner) := by
  unfold snapshotWTransitions PairShiftSnapshot.lifetimePassSnapshots
  rw [List.map_map]
  calc
    matching.attach.map
          (fun attached =>
            PairShiftSnapshot.wTransition
              (PairShiftSnapshot.ofLifetimePass
                exact step aligned attached.2)) =
        matching.attach.map
          (fun attached =>
            (ledger.activeCreatorSnapshot attached.1.loser,
              before.value attached.1.winner)) := by
      apply List.map_congr_left
      intro attached attached_mem
      rw [PairShiftSnapshot.wTransition_ofLifetimePass]
      let starts :=
        exact.pass_pairing_starts step aligned attached.2
      simpa [starts] using
        (EpisodeLedger.activeCreatorSnapshot_of_active
          ledger (attached.1).loser starts.loserStart
          starts.loserActive).symm
    _ = matching.map
          (fun pairing =>
            (ledger.activeCreatorSnapshot pairing.loser,
              before.value pairing.winner)) := by
      simp

namespace SnapshotChainArchive

/--
Every active ledger episode is represented by the newest chain with the same
element tag, and that chain ends at the episode's frozen creator snapshot.
-/
def ActiveAligned {n : ℕ} (archive : SnapshotChainArchive n)
    (ledger : EpisodeLedger n) : Prop :=
  ∀ element start, ledger element = some start →
    ∃ chain,
      current? archive element = some chain ∧
        terminalSnapshot chain.1 chain.2 =
          start.creatorValueAtJoin

/-- Every archived chain has a globally bounded terminal snapshot. -/
def TerminalsBound {n : ℕ} (params : Parameters)
    (archive : SnapshotChainArchive n) : Prop :=
  ∀ tagged ∈ archive,
    terminalSnapshot tagged.2.1 tagged.2.2 ≤ params.valueBound

theorem activeAligned_empty {n : ℕ} :
    ActiveAligned ([] : SnapshotChainArchive n)
      (EpisodeLedger.empty : EpisodeLedger n) := by
  intro element start active
  simp [EpisodeLedger.empty] at active

theorem terminalsBound_empty {n : ℕ} (params : Parameters) :
    TerminalsBound params ([] : SnapshotChainArchive n) := by
  simp [TerminalsBound]

theorem TerminalsBound.openChain
    {n : ℕ} {params : Parameters}
    {archive : SnapshotChainArchive n}
    (bounded : TerminalsBound params archive)
    (element : Element n) {initial : ℕ}
    (initial_le : initial ≤ params.valueBound) :
    TerminalsBound params (openChain archive element initial) := by
  intro tagged member
  rcases List.mem_cons.mp member with tagged_eq | tail_mem
  · subst tagged
    exact initial_le
  · exact bounded tagged tail_mem

theorem TerminalsBound.advance
    {n : ℕ} {params : Parameters}
    {archive : SnapshotChainArchive n}
    (bounded : TerminalsBound params archive)
    (element : Element n) {next : ℕ}
    (next_le : next ≤ params.valueBound) :
    TerminalsBound params (advance archive element next) := by
  induction archive with
  | nil =>
      exact bounded
  | cons tagged tail ih =>
      rcases tagged with ⟨tag, chain⟩
      have head_le :
          terminalSnapshot chain.1 chain.2 ≤ params.valueBound :=
        bounded (tag, chain) (by simp)
      have tail_bound : TerminalsBound params tail := by
        intro tagged member
        exact bounded tagged (by simp [member])
      by_cases same : tag = element
      · subst tag
        simp only [SnapshotChainArchive.advance, if_pos]
        change
          TerminalsBound params
            ((element, extendChain chain next) :: tail)
        intro tagged member
        rcases List.mem_cons.mp member with tagged_eq | tail_mem
        · subst tagged
          simpa using next_le
        · exact tail_bound tagged tail_mem
      · simp only [SnapshotChainArchive.advance, if_neg same]
        change
          TerminalsBound params
            ((tag, chain) ::
              SnapshotChainArchive.advance tail element next)
        intro tagged member
        rcases List.mem_cons.mp member with tagged_eq | tail_mem
        · subst tagged
          exact head_le
        · exact ih tail_bound tagged tail_mem

theorem TerminalsBound.advancePass
    {n : ℕ} {params : Parameters}
    {archive : SnapshotChainArchive n}
    (bounded : TerminalsBound params archive)
    (before : State n) (matching : List (Pairing n))
    (before_valid : before.Valid params) :
    TerminalsBound params (advancePass before archive matching) := by
  induction matching generalizing archive with
  | nil =>
      exact bounded
  | cons pairing matching ih =>
      exact
        ih
          (bounded.advance pairing.loser
            (before_valid.2.1 pairing.winner).2)

@[simp]
theorem length_chains {n : ℕ}
    (archive : SnapshotChainArchive n) :
    archive.chains.length = archive.length := by
  simp [chains]

@[simp]
theorem length_advance {n : ℕ}
    (archive : SnapshotChainArchive n)
    (element : Element n) (next : ℕ) :
    (advance archive element next).length = archive.length := by
  induction archive with
  | nil =>
      rfl
  | cons tagged tail ih =>
      rcases tagged with ⟨tag, chain⟩
      by_cases same : tag = element
      · simp [advance, same]
      · simp [advance, same, ih]

@[simp]
theorem length_advancePass {n : ℕ}
    (before : State n) (archive : SnapshotChainArchive n)
    (matching : List (Pairing n)) :
    (advancePass before archive matching).length =
      archive.length := by
  induction matching generalizing archive with
  | nil =>
      rfl
  | cons pairing matching ih =>
      rw [advancePass_cons, ih, length_advance]

/-- The archive update corresponding to one exact interface operation. -/
def afterOperation {n : ℕ} (before : State n) (labels : RootLabels)
    (archive : SnapshotChainArchive n) :
    Operation n → SnapshotChainArchive n
  | .insert destination element =>
      openChain archive element
        (EpisodeStart.ofJoin before
          (makeJoinOccurrence before labels .insert element
            destination element)).creatorValueAtJoin
  | .pass _ matching =>
      advancePass before archive matching
  | _ => archive

@[simp]
theorem transitions_openChain {n : ℕ}
    (archive : SnapshotChainArchive n) (element : Element n)
    (initial : ℕ) :
    transitions (openChain archive element initial) =
      transitions archive :=
  rfl

@[simp]
theorem length_afterOperation
    {n : ℕ} (before : State n) (labels : RootLabels)
    (archive : SnapshotChainArchive n) (operation : Operation n) :
    (afterOperation before labels archive operation).length =
      archive.length + operation.insertCount := by
  cases operation with
  | convert blockId =>
      rfl
  | create creator =>
      rfl
  | insert destination element =>
      rfl
  | delete source element =>
      rfl
  | pass source matching =>
      simp [SnapshotChainArchive.afterOperation,
        Operation.insertCount]
  | split source prefixLength =>
      rfl
  | valueChange element delta =>
      rfl

/--
For one exact operation, the chronological snapshot edges are exactly the
new edges added to the archive.
-/
theorem transitions_append_operation_perm_afterOperation
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {operation : Operation n}
    (archive : SnapshotChainArchive n)
    (active_aligned : ActiveAligned archive ledger)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length) :
    (transitions archive ++
        snapshotWTransitions
          (operationPairShiftSnapshots before after labels ledger
            operation exact step aligned)).Perm
      (transitions
        (afterOperation before labels archive operation)) := by
  cases operation with
  | convert blockId =>
      simp [operationPairShiftSnapshots,
        SnapshotChainArchive.afterOperation, snapshotWTransitions]
  | create creator =>
      simp [operationPairShiftSnapshots,
        SnapshotChainArchive.afterOperation, snapshotWTransitions]
  | insert destination element =>
      simp [operationPairShiftSnapshots,
        SnapshotChainArchive.afterOperation, snapshotWTransitions]
  | delete source element =>
      simp [operationPairShiftSnapshots,
        SnapshotChainArchive.afterOperation, snapshotWTransitions]
  | pass source matching =>
      have losers_nodup : (pairingLosers matching).Nodup := by
        cases step.2.1 with
        | pass source_found valid_matching blocks_eq values_eq =>
            exact pairingLosers_nodup valid_matching.2.1
      have current :
          ∀ pairing ∈ matching,
            ∃ chain,
              current? archive pairing.loser = some chain ∧
                terminalSnapshot chain.1 chain.2 =
                  ledger.activeCreatorSnapshot pairing.loser := by
        intro pairing pairing_mem
        let starts :=
          exact.pass_pairing_starts step aligned pairing_mem
        obtain ⟨chain, chain_current, chain_terminal⟩ :=
          active_aligned pairing.loser starts.loserStart
            starts.loserActive
        refine ⟨chain, chain_current, ?_⟩
        rw [chain_terminal]
        exact
          (EpisodeLedger.activeCreatorSnapshot_of_active
            ledger pairing.loser starts.loserStart
              starts.loserActive).symm
      rw [operationPairShiftSnapshots,
        snapshotWTransitions_lifetimePassSnapshots exact step aligned]
      exact
        transitions_append_map_perm_advancePass before archive matching
          (fun pairing =>
            ledger.activeCreatorSnapshot pairing.loser)
          losers_nodup current
  | split source prefixLength =>
      simp [operationPairShiftSnapshots,
        SnapshotChainArchive.afterOperation, snapshotWTransitions]
  | valueChange element delta =>
      simp [operationPairShiftSnapshots,
        SnapshotChainArchive.afterOperation, snapshotWTransitions]

/-- One exact operation preserves the active-ledger/archive alignment. -/
theorem ActiveAligned.afterOperation
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {operation : Operation n}
    {archive : SnapshotChainArchive n}
    (active_aligned : ActiveAligned archive ledger)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length) :
    ActiveAligned
      (afterOperation before labels archive operation)
      (EpisodeLedger.after before labels ledger operation) := by
  cases operation with
  | convert blockId =>
      simpa [SnapshotChainArchive.afterOperation] using active_aligned
  | create creator =>
      simpa [SnapshotChainArchive.afterOperation] using active_aligned
  | insert destination inserted =>
      intro element start active
      by_cases element_eq : element = inserted
      · subst element
        simp only [EpisodeLedger.after, Function.update_self,
          Option.some.injEq] at active
        subst start
        refine
          ⟨((EpisodeStart.ofJoin before
              (makeJoinOccurrence before labels .insert inserted
                destination inserted)).creatorValueAtJoin, []),
            ?_, rfl⟩
        exact current?_open_self archive inserted _
      · have old_active : ledger element = some start := by
          simpa [EpisodeLedger.after, Function.update,
            element_eq] using active
        obtain ⟨chain, chain_current, chain_terminal⟩ :=
          active_aligned element start old_active
        refine ⟨chain, ?_, chain_terminal⟩
        exact
          current?_open_of_ne archive
            (initial :=
              (EpisodeStart.ofJoin before
                (makeJoinOccurrence before labels .insert inserted
                  destination inserted)).creatorValueAtJoin)
            (Ne.symm element_eq) |>.trans chain_current
  | delete source deleted =>
      intro element start active
      by_cases element_eq : element = deleted
      · subst element
        simp [EpisodeLedger.after] at active
      · apply active_aligned element start
        simpa [EpisodeLedger.after, Function.update,
          element_eq] using active
  | pass source matching =>
      intro element start active
      have losers_nodup : (pairingLosers matching).Nodup := by
        cases step.2.1 with
        | pass source_found valid_matching blocks_eq values_eq =>
            exact pairingLosers_nodup valid_matching.2.1
      by_cases loser_mem : element ∈ pairingLosers matching
      · obtain ⟨pairing, pairing_mem, loser_eq⟩ :=
          List.mem_map.mp (by
            simpa [pairingLosers] using loser_mem)
        let starts :=
          exact.pass_pairing_starts step aligned pairing_mem
        obtain ⟨chain, chain_current, chain_terminal⟩ :=
          active_aligned pairing.loser starts.loserStart
            starts.loserActive
        obtain ⟨newStart, new_active, new_creator, edge_eq⟩ :=
          pass_installs_wTransition_endpoint
            step ledger pairing_mem starts.loserActive
        have start_eq : start = newStart := by
          apply Option.some.inj
          calc
            some start =
                EpisodeLedger.after before labels ledger
                  (.pass source matching) element :=
              active.symm
            _ = EpisodeLedger.after before labels ledger
                  (.pass source matching) pairing.loser := by
              rw [loser_eq]
            _ = some newStart := new_active
        subst start
        refine
          ⟨extendChain chain (before.value pairing.winner),
            ?_, ?_⟩
        · simpa [SnapshotChainArchive.afterOperation, loser_eq] using
            current?_advancePass_of_mem before archive
              losers_nodup pairing_mem chain_current
        · rw [terminalSnapshot_extend, new_creator]
      · have old_active : ledger element = some start := by
          change
            EpisodeLedger.installPassJoins
                before labels source ledger matching element =
              some start at active
          rw [EpisodeLedger.installPassJoins_apply_of_not_mem
            before labels source ledger matching element loser_mem] at active
          exact active
        obtain ⟨chain, chain_current, chain_terminal⟩ :=
          active_aligned element start old_active
        refine ⟨chain, ?_, chain_terminal⟩
        simpa [SnapshotChainArchive.afterOperation] using
          (current?_advancePass_of_not_mem
            before archive matching element loser_mem).trans chain_current
  | split source prefixLength =>
      simpa [SnapshotChainArchive.afterOperation] using active_aligned
  | valueChange element delta =>
      simpa [SnapshotChainArchive.afterOperation] using active_aligned

/-- One legal operation preserves the archive terminal bound. -/
theorem TerminalsBound.afterOperation
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n} {archive : SnapshotChainArchive n}
    (bounded : TerminalsBound params archive)
    (step : Step params before operation after) :
    TerminalsBound params
      (afterOperation before labels archive operation) := by
  cases operation with
  | convert blockId =>
      exact bounded
  | create creator =>
      exact bounded
  | insert destination inserted =>
      apply bounded.openChain inserted
      exact
        (step.1.2.1
          (makeJoinOccurrence before labels .insert inserted
            destination inserted).destinationCreator).2
  | delete source deleted =>
      exact bounded
  | pass source matching =>
      exact bounded.advancePass before matching step.1
  | split source prefixLength =>
      exact bounded
  | valueChange element delta =>
      exact bounded

end SnapshotChainArchive

namespace LifetimeHistory

/--
Chronological complete pair snapshots threaded alongside the same state,
label, ledger, and operation sequence as a lifetime history.
-/
inductive PairShiftSnapshotHistory {n : ℕ} (params : Parameters) :
    State n → RootLabels → EpisodeLedger n →
      List (Operation n) → List PairShiftSnapshot →
      State n → RootLabels → EpisodeLedger n → Prop
  | nil {state : State n} {labels : RootLabels}
      {ledger : EpisodeLedger n}
      (valid : state.Valid params) :
      PairShiftSnapshotHistory params state labels ledger
        [] [] state labels ledger
  | cons {before middle final : State n}
      {beforeLabels finalLabels : RootLabels}
      {beforeLedger finalLedger : EpisodeLedger n}
      {operation : Operation n} {operations : List (Operation n)}
      {tailSnapshots : List PairShiftSnapshot}
      (aligned : beforeLabels.length = before.blocks.length)
      (exact :
        EpisodeLedger.ExactAt before beforeLabels beforeLedger)
      (head : Step params before operation middle)
      (tail :
        PairShiftSnapshotHistory params middle
          (RootLabels.after beforeLabels operation)
          (EpisodeLedger.after before beforeLabels beforeLedger operation)
          operations tailSnapshots final finalLabels finalLedger) :
      PairShiftSnapshotHistory params before beforeLabels beforeLedger
        (operation :: operations)
        (operationPairShiftSnapshots before middle beforeLabels
            beforeLedger operation exact head aligned ++ tailSnapshots)
        final finalLabels finalLedger

/-- Every exact lifetime history admits its chronological snapshot history. -/
theorem lift_pairShiftSnapshots
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history :
      LifetimeHistory params initial initialLabels initialLedger
        operations joins leaves closed final finalLabels finalLedger)
    (aligned : initialLabels.length = initial.blocks.length)
    (exact :
      EpisodeLedger.ExactAt initial initialLabels initialLedger) :
    ∃ snapshots,
      PairShiftSnapshotHistory params initial initialLabels initialLedger
        operations snapshots final finalLabels finalLedger := by
  induction history with
  | nil valid =>
      exact ⟨[], .nil valid⟩
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger operation operations tailJoins tailLeaves tailClosed
      head tail ih =>
      have middle_aligned :
          (RootLabels.after beforeLabels operation).length =
            middle.blocks.length :=
        (HistoryStep.mk head rfl).labels_length aligned
      have middle_exact :=
        exact.after_step head aligned
      obtain ⟨tailSnapshots, tail_chronological⟩ :=
        ih middle_aligned middle_exact
      exact
        ⟨operationPairShiftSnapshots before middle beforeLabels
            beforeLedger operation exact head aligned ++ tailSnapshots,
          .cons aligned exact head tail_chronological⟩

/-- Selected chronological global snapshot list. -/
noncomputable def pairShiftSnapshots
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history :
      LifetimeHistory params initial initialLabels initialLedger
        operations joins leaves closed final finalLabels finalLedger)
    (aligned : initialLabels.length = initial.blocks.length)
    (exact :
      EpisodeLedger.ExactAt initial initialLabels initialLedger) :
    List PairShiftSnapshot :=
  Classical.choose
    (history.lift_pairShiftSnapshots aligned exact)

/-- The selected list carries its chronological snapshot-history proof. -/
theorem pairShiftSnapshots_history
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history :
      LifetimeHistory params initial initialLabels initialLedger
        operations joins leaves closed final finalLabels finalLedger)
    (aligned : initialLabels.length = initial.blocks.length)
    (exact :
      EpisodeLedger.ExactAt initial initialLabels initialLedger) :
    PairShiftSnapshotHistory params initial initialLabels initialLedger
      operations (history.pairShiftSnapshots aligned exact)
      final finalLabels finalLedger :=
  Classical.choose_spec
    (history.lift_pairShiftSnapshots aligned exact)

/-- Every chronological snapshot history has exactly total pass activity. -/
theorem PairShiftSnapshotHistory.snapshots_length
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {snapshots : List PairShiftSnapshot}
    (history :
      PairShiftSnapshotHistory params initial initialLabels initialLedger
        operations snapshots final finalLabels finalLedger) :
    snapshots.length = totalActivity operations := by
  induction history with
  | nil valid =>
      rfl
  | cons aligned exact head tail ih =>
      rw [List.length_append,
        length_operationPairShiftSnapshots,
        ih]
      rfl

/-- Frozen ledger bounds make every global chronological snapshot bounded. -/
theorem PairShiftSnapshotHistory.snapshots_valuesBound
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {snapshots : List PairShiftSnapshot}
    (history :
      PairShiftSnapshotHistory params initial initialLabels initialLedger
        operations snapshots final finalLabels finalLedger)
    (frozen :
      EpisodeLedger.FrozenValuesBound params initialLedger) :
    ∀ snapshot ∈ snapshots,
      snapshot.ValuesBound params.valueBound := by
  induction history with
  | nil valid =>
      simp
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger operation operations tailSnapshots aligned exact head tail
      ih =>
      intro snapshot member
      rcases List.mem_append.mp member with head_mem | tail_mem
      · exact
          valuesBound_operationPairShiftSnapshots
            before middle beforeLabels beforeLedger operation
            exact frozen head aligned snapshot head_mem
      · exact ih (frozen.after_step head) snapshot tail_mem

/--
Fold a chronological snapshot history into the concrete insert-rooted archive.
The four conclusions are the active alignment, terminal bound, exact chain
count, and exact transition permutation needed by the global certificate.
-/
theorem PairShiftSnapshotHistory.buildArchive
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {snapshots : List PairShiftSnapshot}
    (history :
      PairShiftSnapshotHistory params initial initialLabels initialLedger
        operations snapshots final finalLabels finalLedger)
    (initialArchive : SnapshotChainArchive n)
    (active_aligned :
      SnapshotChainArchive.ActiveAligned initialArchive initialLedger)
    (terminals_bounded :
      SnapshotChainArchive.TerminalsBound params initialArchive) :
    ∃ finalArchive : SnapshotChainArchive n,
      SnapshotChainArchive.ActiveAligned finalArchive finalLedger ∧
        SnapshotChainArchive.TerminalsBound params finalArchive ∧
        finalArchive.length =
          initialArchive.length + totalInserts operations ∧
        (initialArchive.transitions ++
            snapshotWTransitions snapshots).Perm
          finalArchive.transitions := by
  induction history generalizing initialArchive with
  | nil valid =>
      exact
        ⟨initialArchive, active_aligned, terminals_bounded,
          by simp [totalInserts],
          by simp [snapshotWTransitions]⟩
  | @cons before middle final beforeLabels finalLabels beforeLedger
      finalLedger operation operations tailSnapshots aligned exact head tail
      ih =>
      let middleArchive :=
        SnapshotChainArchive.afterOperation
          before beforeLabels initialArchive operation
      have middle_aligned :
          SnapshotChainArchive.ActiveAligned middleArchive
            (EpisodeLedger.after before beforeLabels beforeLedger operation) :=
        active_aligned.afterOperation exact head aligned
      have middle_bounded :
          SnapshotChainArchive.TerminalsBound params middleArchive :=
        terminals_bounded.afterOperation head
      obtain
          ⟨finalArchive, final_aligned, final_bounded,
            final_length, tail_perm⟩ :=
        ih middleArchive middle_aligned middle_bounded
      have head_perm :=
        SnapshotChainArchive.transitions_append_operation_perm_afterOperation
          initialArchive active_aligned exact head aligned
      refine
        ⟨finalArchive, final_aligned, final_bounded, ?_, ?_⟩
      · rw [final_length]
        simp only [middleArchive,
          SnapshotChainArchive.length_afterOperation,
          totalInserts, List.map_cons, List.sum_cons]
        omega
      · let tailTransitions :=
          snapshotWTransitions tailSnapshots
        have head_with_tail :
            (initialArchive.transitions ++
                snapshotWTransitions
                    (operationPairShiftSnapshots before middle
                      beforeLabels beforeLedger operation exact head
                      aligned) ++
                  tailTransitions).Perm
              (middleArchive.transitions ++ tailTransitions) := by
          simpa [middleArchive, List.append_assoc] using
            head_perm.append_right tailTransitions
        have chronological :
            snapshotWTransitions
                (operationPairShiftSnapshots before middle beforeLabels
                    beforeLedger operation exact head aligned ++
                  tailSnapshots) =
              snapshotWTransitions
                  (operationPairShiftSnapshots before middle beforeLabels
                    beforeLedger operation exact head aligned) ++
                tailTransitions := by
          simp [snapshotWTransitions, tailTransitions]
        rw [chronological]
        simpa [List.append_assoc] using
          head_with_tail.trans tail_perm

/--
Starting from the empty ledger and empty archive, every chronological exact
history constructs the unconditional global chain-partition certificate.
-/
theorem PairShiftSnapshotHistory.snapshotChainPartition_nonempty
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {snapshots : List PairShiftSnapshot}
    (history :
      PairShiftSnapshotHistory params initial initialLabels
        (EpisodeLedger.empty : EpisodeLedger n)
        operations snapshots final finalLabels finalLedger) :
    Nonempty (SnapshotChainPartition params operations snapshots) := by
  obtain
      ⟨archive, active_aligned, terminals_bounded,
        archive_length, transitions_perm⟩ :=
    history.buildArchive ([] : SnapshotChainArchive n)
      SnapshotChainArchive.activeAligned_empty
      (SnapshotChainArchive.terminalsBound_empty params)
  refine
    ⟨{ chains := archive.chains
       transitions_perm := ?_
       chain_count := ?_
       terminal_le := ?_ }⟩
  · simpa [SnapshotChainArchive.transitions,
      SnapshotChainArchive.chains, snapshotChainsTransitions,
      snapshotWTransitions] using transitions_perm
  · simpa using archive_length
  · intro chain chain_mem
    change chain ∈ archive.map Prod.snd at chain_mem
    obtain ⟨tagged, tagged_mem, rfl⟩ :=
      List.mem_map.mp chain_mem
    exact terminals_bounded tagged tagged_mem

/-- The selected global chronological snapshot list has total pass activity. -/
@[simp]
theorem length_pairShiftSnapshots
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history :
      LifetimeHistory params initial initialLabels initialLedger
        operations joins leaves closed final finalLabels finalLedger)
    (aligned : initialLabels.length = initial.blocks.length)
    (exact :
      EpisodeLedger.ExactAt initial initialLabels initialLedger) :
    (history.pairShiftSnapshots aligned exact).length =
      totalActivity operations :=
  (history.pairShiftSnapshots_history aligned exact).snapshots_length

/-- The selected global list has an unconditional insert-rooted partition. -/
theorem pairShiftSnapshots_snapshotChainPartition_nonempty
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history :
      LifetimeHistory params initial initialLabels
        (EpisodeLedger.empty : EpisodeLedger n)
        operations joins leaves closed final finalLabels finalLedger)
    (aligned : initialLabels.length = initial.blocks.length)
    (exact :
      EpisodeLedger.ExactAt initial initialLabels
        (EpisodeLedger.empty : EpisodeLedger n)) :
    Nonempty
      (SnapshotChainPartition params operations
        (history.pairShiftSnapshots aligned exact)) :=
  PairShiftSnapshotHistory.snapshotChainPartition_nonempty
    (history.pairShiftSnapshots_history aligned exact)

/-- Canonical selected chain-partition certificate for the global list. -/
noncomputable def pairShiftSnapshotsSnapshotChainPartition
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history :
      LifetimeHistory params initial initialLabels
        (EpisodeLedger.empty : EpisodeLedger n)
        operations joins leaves closed final finalLabels finalLedger)
    (aligned : initialLabels.length = initial.blocks.length)
    (exact :
      EpisodeLedger.ExactAt initial initialLabels
        (EpisodeLedger.empty : EpisodeLedger n)) :
    SnapshotChainPartition params operations
      (history.pairShiftSnapshots aligned exact) :=
  Classical.choice
    (history.pairShiftSnapshots_snapshotChainPartition_nonempty
      aligned exact)

/-- The selected exact lifetime snapshots satisfy the global telescoping bound. -/
theorem totalWShift_pairShiftSnapshots_le
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history :
      LifetimeHistory params initial initialLabels
        (EpisodeLedger.empty : EpisodeLedger n)
        operations joins leaves closed final finalLabels finalLedger)
    (aligned : initialLabels.length = initial.blocks.length)
    (exact :
      EpisodeLedger.ExactAt initial initialLabels
        (EpisodeLedger.empty : EpisodeLedger n)) :
    totalWShift (history.pairShiftSnapshots aligned exact) ≤
      ((params.valueBound * totalInserts operations : ℕ) : ℤ) :=
  SnapshotChainPartition.totalWShift_le_valueBound_mul_totalInserts
    (history.pairShiftSnapshotsSnapshotChainPartition aligned exact)

/--
Every ordinary trace from an initial state admits a chronological global
snapshot list with exact activity length, an unconditional chain partition,
and the resulting global `w`-shift bound.
-/
theorem exists_pairShiftSnapshots_partition_of_trace
    {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (initialState : initial.Initial params)
    (trace : Trace params initial operations final) :
    ∃ snapshots : List PairShiftSnapshot,
      snapshots.length = totalActivity operations ∧
        Nonempty (SnapshotChainPartition params operations snapshots) ∧
        totalWShift snapshots ≤
          ((params.valueBound * totalInserts operations : ℕ) : ℤ) := by
  obtain
      ⟨finalLabels, finalLedger, joins, leaves, closed,
        history, final_aligned, final_exact,
        joins_length, leaves_length, closed_length⟩ :=
    LifetimeHistory.lift_initial initialState trace
  have initial_aligned :
      ([] : RootLabels).length = initial.blocks.length := by
    simp [initialState.2]
  have initial_exact :
      EpisodeLedger.ExactAt initial []
        (EpisodeLedger.empty : EpisodeLedger n) :=
    EpisodeLedger.ExactAt.initial initialState
  let snapshots :=
    history.pairShiftSnapshots initial_aligned initial_exact
  have partition_nonempty :
      Nonempty (SnapshotChainPartition params operations snapshots) :=
    history.pairShiftSnapshots_snapshotChainPartition_nonempty
      initial_aligned initial_exact
  let partition :=
    history.pairShiftSnapshotsSnapshotChainPartition
      initial_aligned initial_exact
  exact
    ⟨snapshots,
      history.length_pairShiftSnapshots initial_aligned initial_exact,
      partition_nonempty,
      partition.totalWShift_le_valueBound_mul_totalInserts⟩

end LifetimeHistory

end Splay.Interface
