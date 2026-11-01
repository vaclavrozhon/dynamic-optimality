import Splay.Interface.Model
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Splay.Interface

namespace Operation

/--
Signed contribution of one operation to the value of a fixed element.
Unrelated operations and value changes of other elements contribute zero.
-/
def signedValueChange {n : ℕ} (target : Element n) :
    Operation n → ℤ
  | .valueChange element .decrease =>
      if element = target then -1 else 0
  | .valueChange element .increase =>
      if element = target then 1 else 0
  | _ => 0

end Operation

/-- Net signed value drift of one element along an operation list. -/
def totalSignedValueChange {n : ℕ}
    (target : Element n) (operations : List (Operation n)) : ℤ :=
  (operations.map (Operation.signedValueChange target)).sum

/-- One exact interface effect realizes its advertised signed unit drift. -/
theorem Effect.value_eq_add_signedValueChange
    {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    (effect : Effect params before operation after)
    (target : Element n) :
    (after.value target : ℤ) =
      (before.value target : ℤ) +
        operation.signedValueChange target := by
  cases effect with
  | convert found growing blocks_eq values_eq =>
      simp [values_eq, Operation.signedValueChange]
  | create room blocks_eq values_eq =>
      simp [values_eq, Operation.signedValueChange]
  | insert found growing unassigned value_order blocks_eq values_eq =>
      simp [values_eq, Operation.signedValueChange]
  | delete found shrinking present blocks_eq values_eq =>
      simp [values_eq, Operation.signedValueChange]
  | pass found valid_matching blocks_eq values_eq =>
      simp [values_eq, Operation.signedValueChange]
  | split found shrinking prefix_le blocks_eq values_eq =>
      simp [values_eq, Operation.signedValueChange]
  | decrease can_decrease blocks_eq values_eq =>
      rename_i element
      by_cases same : element = target
      · subst target
        simp only [values_eq, Function.update_self,
          Operation.signedValueChange]
        rw [Nat.cast_sub (by omega : 1 ≤ before.value element)]
        simp only [if_pos]
        ring
      · have target_ne : target ≠ element := Ne.symm same
        simp [values_eq, Operation.signedValueChange, same, target_ne]
  | increase can_increase blocks_eq values_eq =>
      rename_i element
      by_cases same : element = target
      · subst target
        simp [values_eq, Operation.signedValueChange]
      · have target_ne : target ≠ element := Ne.symm same
        simp [values_eq, Operation.signedValueChange, same, target_ne]

/--
Pointwise value drift telescopes over a complete trace.  This supplies the
exact interval identity used when `v`- and `u`-shifts are expanded into unit
`ValueChange` events.
-/
theorem Trace.value_eq_add_totalSignedValueChange
    {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (trace : Trace params initial operations final)
    (target : Element n) :
    (final.value target : ℤ) =
      (initial.value target : ℤ) +
        totalSignedValueChange target operations := by
  induction trace with
  | nil valid =>
      simp [totalSignedValueChange]
  | @cons before middle final operation operations head tail ih =>
      have headDrift :=
        head.2.1.value_eq_add_signedValueChange target
      unfold totalSignedValueChange at ih ⊢
      simp only [List.map_cons, List.sum_cons]
      rw [ih, headDrift]
      ring

/--
The net signed drift of one element is at most the total number of value
changes, even before exploiting the much sharper bounded-incidence argument.
-/
theorem totalSignedValueChange_le_totalValueChanges
    {n : ℕ} (target : Element n)
    (operations : List (Operation n)) :
    totalSignedValueChange target operations ≤
      (totalValueChanges operations : ℤ) := by
  induction operations with
  | nil =>
      simp [totalSignedValueChange, totalValueChanges]
  | cons operation operations ih =>
      simp only [totalSignedValueChange, totalValueChanges,
        List.map_cons, List.sum_cons]
      have head_le :
          operation.signedValueChange target ≤
            (operation.valueChangeCount : ℤ) := by
        cases operation with
        | convert =>
            simp [Operation.signedValueChange,
              Operation.valueChangeCount]
        | create =>
            simp [Operation.signedValueChange,
              Operation.valueChangeCount]
        | insert =>
            simp [Operation.signedValueChange,
              Operation.valueChangeCount]
        | delete =>
            simp [Operation.signedValueChange,
              Operation.valueChangeCount]
        | pass =>
            simp [Operation.signedValueChange,
              Operation.valueChangeCount]
        | split =>
            simp [Operation.signedValueChange,
              Operation.valueChangeCount]
        | valueChange element delta =>
            cases delta <;>
              simp [Operation.signedValueChange,
                Operation.valueChangeCount] <;>
              split <;> simp_all
      rw [Nat.cast_add]
      exact add_le_add head_le ih

/--
The four value snapshots attached to one pass pairing.

The winner and the source creator are frozen when the winner entered the
source lineage.  The loser's creator snapshot is frozen when the loser entered
that same lineage.  `winnerNow` is the value at the later pass operation.
-/
structure PairShiftSnapshot where
  winnerAtJoin : ℕ
  winnerCreatorAtJoin : ℕ
  winnerNow : ℕ
  loserCreatorAtJoin : ℕ
  joinedAboveCreator :
    winnerCreatorAtJoin + 1 ≤ winnerAtJoin

namespace PairShiftSnapshot

/-- All four values sampled by a pair snapshot lie below one common bound. -/
def ValuesBound (valueBound : ℕ)
    (snapshot : PairShiftSnapshot) : Prop :=
  snapshot.winnerAtJoin ≤ valueBound ∧
    snapshot.winnerCreatorAtJoin ≤ valueBound ∧
    snapshot.winnerNow ≤ valueBound ∧
    snapshot.loserCreatorAtJoin ≤ valueBound

/-- Nonnegative pair rank used to pay one unit of pass activity. -/
def pairRank (snapshot : PairShiftSnapshot) : ℕ :=
  snapshot.winnerAtJoin - snapshot.winnerCreatorAtJoin

/-- Drift of the winner between its join and the current pass. -/
def vShift (snapshot : PairShiftSnapshot) : ℤ :=
  (snapshot.winnerAtJoin : ℤ) - (snapshot.winnerNow : ℤ)

/-- Change from the loser's old creator snapshot to the new winner. -/
def wShift (snapshot : PairShiftSnapshot) : ℤ :=
  (snapshot.winnerNow : ℤ) -
    (snapshot.loserCreatorAtJoin : ℤ)

/-- Difference between the two source-creator join snapshots. -/
def uShift (snapshot : PairShiftSnapshot) : ℤ :=
  (snapshot.loserCreatorAtJoin : ℤ) -
    (snapshot.winnerCreatorAtJoin : ℤ)

/-- Every legal winner join gives a pair rank of at least one. -/
theorem one_le_pairRank (snapshot : PairShiftSnapshot) :
    1 ≤ snapshot.pairRank := by
  unfold pairRank
  have joined := snapshot.joinedAboveCreator
  omega

/--
The manuscript's three-way shift decomposition, stated over integers so that
individual transient shifts may be negative.
-/
theorem pairRank_eq_shifts (snapshot : PairShiftSnapshot) :
    (snapshot.pairRank : ℤ) =
      snapshot.vShift + snapshot.wShift + snapshot.uShift := by
  unfold pairRank vShift wShift uShift
  have creator_le :
      snapshot.winnerCreatorAtJoin ≤ snapshot.winnerAtJoin :=
    Nat.le_trans (Nat.le_add_right _ 1) snapshot.joinedAboveCreator
  rw [Nat.cast_sub creator_le]
  ring

/-- A bounded snapshot contributes at most `valueBound` to its v-shift. -/
theorem vShift_le_valueBound
    {snapshot : PairShiftSnapshot} {valueBound : ℕ}
    (bounded : snapshot.ValuesBound valueBound) :
    snapshot.vShift ≤ (valueBound : ℤ) := by
  unfold vShift
  rcases bounded with ⟨winner_le, _creator_le, _now_le, _loser_le⟩
  omega

/-- A bounded snapshot contributes at most `valueBound` to its u-shift. -/
theorem uShift_le_valueBound
    {snapshot : PairShiftSnapshot} {valueBound : ℕ}
    (bounded : snapshot.ValuesBound valueBound) :
    snapshot.uShift ≤ (valueBound : ℤ) := by
  unfold uShift
  rcases bounded with ⟨_winner_le, _creator_le, _now_le, loser_le⟩
  omega

end PairShiftSnapshot

/-- Total pair rank of a chronological list of pass-pair snapshots. -/
def totalPairRank (snapshots : List PairShiftSnapshot) : ℕ :=
  (snapshots.map PairShiftSnapshot.pairRank).sum

def totalVShift (snapshots : List PairShiftSnapshot) : ℤ :=
  (snapshots.map PairShiftSnapshot.vShift).sum

def totalWShift (snapshots : List PairShiftSnapshot) : ℤ :=
  (snapshots.map PairShiftSnapshot.wShift).sum

def totalUShift (snapshots : List PairShiftSnapshot) : ℤ :=
  (snapshots.map PairShiftSnapshot.uShift).sum

/-- The pointwise three-way decomposition sums over the complete history. -/
theorem totalPairRank_eq_shifts (snapshots : List PairShiftSnapshot) :
    (totalPairRank snapshots : ℤ) =
      totalVShift snapshots +
        totalWShift snapshots +
        totalUShift snapshots := by
  induction snapshots with
  | nil =>
      simp [totalPairRank, totalVShift, totalWShift, totalUShift]
  | cons snapshot snapshots ih =>
      unfold totalPairRank totalVShift totalWShift totalUShift at ih ⊢
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      rw [snapshot.pairRank_eq_shifts, ih]
      ring

/-- One pair-rank unit pays each pass-pair snapshot. -/
theorem snapshots_length_le_totalPairRank
    (snapshots : List PairShiftSnapshot) :
    snapshots.length ≤ totalPairRank snapshots := by
  induction snapshots with
  | nil =>
      simp [totalPairRank]
  | cons snapshot snapshots ih =>
      unfold totalPairRank at ih ⊢
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have one_le := snapshot.one_le_pairRank
      omega

/-- Bounded v-shifts sum to at most one value-bound unit per snapshot. -/
theorem totalVShift_le_length_mul_valueBound
    (snapshots : List PairShiftSnapshot) (valueBound : ℕ)
    (bounded :
      ∀ snapshot ∈ snapshots, snapshot.ValuesBound valueBound) :
    totalVShift snapshots ≤
      ((snapshots.length * valueBound : ℕ) : ℤ) := by
  induction snapshots with
  | nil =>
      simp [totalVShift]
  | cons snapshot snapshots ih =>
      have headBound :=
        snapshot.vShift_le_valueBound
          (bounded snapshot (by simp))
      have tailBound :
          ∀ tailSnapshot ∈ snapshots,
            tailSnapshot.ValuesBound valueBound := by
        intro tailSnapshot tail_mem
        exact bounded tailSnapshot (by simp [tail_mem])
      have tail := ih tailBound
      unfold totalVShift at tail ⊢
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        snapshot.vShift +
              (snapshots.map PairShiftSnapshot.vShift).sum ≤
            (valueBound : ℤ) +
              ((snapshots.length * valueBound : ℕ) : ℤ) :=
          add_le_add headBound tail
        _ = ((((snapshot :: snapshots).length) *
            valueBound : ℕ) : ℤ) := by
          simp only [List.length_cons, Nat.cast_mul, Nat.cast_add,
            Nat.cast_one]
          ring

/-- Bounded u-shifts obey the same pointwise list estimate. -/
theorem totalUShift_le_length_mul_valueBound
    (snapshots : List PairShiftSnapshot) (valueBound : ℕ)
    (bounded :
      ∀ snapshot ∈ snapshots, snapshot.ValuesBound valueBound) :
    totalUShift snapshots ≤
      ((snapshots.length * valueBound : ℕ) : ℤ) := by
  induction snapshots with
  | nil =>
      simp [totalUShift]
  | cons snapshot snapshots ih =>
      have headBound :=
        snapshot.uShift_le_valueBound
          (bounded snapshot (by simp))
      have tailBound :
          ∀ tailSnapshot ∈ snapshots,
            tailSnapshot.ValuesBound valueBound := by
        intro tailSnapshot tail_mem
        exact bounded tailSnapshot (by simp [tail_mem])
      have tail := ih tailBound
      unfold totalUShift at tail ⊢
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        snapshot.uShift +
              (snapshots.map PairShiftSnapshot.uShift).sum ≤
            (valueBound : ℤ) +
              ((snapshots.length * valueBound : ℕ) : ℤ) :=
          add_le_add headBound tail
        _ = ((((snapshot :: snapshots).length) *
            valueBound : ℕ) : ℤ) := by
          simp only [List.length_cons, Nat.cast_mul, Nat.cast_add,
            Nat.cast_one]
          ring

/-- Permuting snapshots preserves every aggregate shift sum. -/
theorem totalVShift_eq_of_perm
    {first second : List PairShiftSnapshot}
    (permuted : first.Perm second) :
    totalVShift first = totalVShift second :=
  (permuted.map PairShiftSnapshot.vShift).sum_eq

theorem totalUShift_eq_of_perm
    {first second : List PairShiftSnapshot}
    (permuted : first.Perm second) :
    totalUShift first = totalUShift second :=
  (permuted.map PairShiftSnapshot.uShift).sum_eq

theorem totalWShift_eq_of_perm
    {first second : List PairShiftSnapshot}
    (permuted : first.Perm second) :
    totalWShift first = totalWShift second :=
  (permuted.map PairShiftSnapshot.wShift).sum_eq

/--
Exact partition of pair snapshots into significant and insignificant passes.
The semantic history later classifies by inherited pass count; this structure
contains only the finite accounting facts needed by the arithmetic proof.
-/
structure SnapshotSignificancePartition
    (valueBound insignificantActivity : ℕ)
    (snapshots : List PairShiftSnapshot) where
  significant : List PairShiftSnapshot
  insignificant : List PairShiftSnapshot
  permuted :
    snapshots.Perm (significant ++ insignificant)
  insignificant_count :
    insignificant.length = insignificantActivity
  values_bound :
    ∀ snapshot ∈ snapshots, snapshot.ValuesBound valueBound

namespace SnapshotSignificancePartition

theorem significant_values_bound
    {valueBound insignificantActivity : ℕ}
    {snapshots : List PairShiftSnapshot}
    (partition :
      SnapshotSignificancePartition valueBound
        insignificantActivity snapshots) :
    ∀ snapshot ∈ partition.significant,
      snapshot.ValuesBound valueBound := by
  intro snapshot member
  apply partition.values_bound snapshot
  have appended :
      snapshot ∈ partition.significant ++ partition.insignificant := by
    simp [member]
  exact partition.permuted.symm.subset appended

theorem insignificant_values_bound
    {valueBound insignificantActivity : ℕ}
    {snapshots : List PairShiftSnapshot}
    (partition :
      SnapshotSignificancePartition valueBound
        insignificantActivity snapshots) :
    ∀ snapshot ∈ partition.insignificant,
      snapshot.ValuesBound valueBound := by
  intro snapshot member
  apply partition.values_bound snapshot
  have appended :
      snapshot ∈ partition.significant ++ partition.insignificant := by
    simp [member]
  exact partition.permuted.symm.subset appended

/--
Once significant v-shifts are charged, all insignificant v-shifts cost one
value-bound unit each.
-/
theorem totalVShift_le_of_significant
    {valueBound insignificantActivity : ℕ}
    {snapshots : List PairShiftSnapshot}
    (partition :
      SnapshotSignificancePartition valueBound
        insignificantActivity snapshots)
    {significantBudget : ℤ}
    (significantBound :
      totalVShift partition.significant ≤ significantBudget) :
    totalVShift snapshots ≤
      ((valueBound * insignificantActivity : ℕ) : ℤ) +
        significantBudget := by
  have insignificantBound :=
    totalVShift_le_length_mul_valueBound
      partition.insignificant valueBound
      partition.insignificant_values_bound
  rw [partition.insignificant_count] at insignificantBound
  rw [totalVShift_eq_of_perm partition.permuted]
  unfold totalVShift
  rw [List.map_append, List.sum_append]
  calc
    (partition.significant.map PairShiftSnapshot.vShift).sum +
          (partition.insignificant.map PairShiftSnapshot.vShift).sum ≤
        significantBudget +
          ((insignificantActivity * valueBound : ℕ) : ℤ) :=
      add_le_add significantBound insignificantBound
    _ =
        ((valueBound * insignificantActivity : ℕ) : ℤ) +
          significantBudget := by
      push_cast
      ring

/-- The identical reduction for u-shifts. -/
theorem totalUShift_le_of_significant
    {valueBound insignificantActivity : ℕ}
    {snapshots : List PairShiftSnapshot}
    (partition :
      SnapshotSignificancePartition valueBound
        insignificantActivity snapshots)
    {significantBudget : ℤ}
    (significantBound :
      totalUShift partition.significant ≤ significantBudget) :
    totalUShift snapshots ≤
      ((valueBound * insignificantActivity : ℕ) : ℤ) +
        significantBudget := by
  have insignificantBound :=
    totalUShift_le_length_mul_valueBound
      partition.insignificant valueBound
      partition.insignificant_values_bound
  rw [partition.insignificant_count] at insignificantBound
  rw [totalUShift_eq_of_perm partition.permuted]
  unfold totalUShift
  rw [List.map_append, List.sum_append]
  calc
    (partition.significant.map PairShiftSnapshot.uShift).sum +
          (partition.insignificant.map PairShiftSnapshot.uShift).sum ≤
        significantBudget +
          ((insignificantActivity * valueBound : ℕ) : ℤ) :=
      add_le_add significantBound insignificantBound
    _ =
        ((valueBound * insignificantActivity : ℕ) : ℤ) +
          significantBudget := by
      push_cast
      ring

end SnapshotSignificancePartition

/--
Pure arithmetic endpoint of the v/u/w argument.

`insignificantActivity` pays the two bounded transient shift types.  A
significant v-shift is charged at most `threshold` times per changed element;
the u-shift has the additional simultaneous-growing factor.  The w-shifts
telescope to one bounded terminal charge per insert episode.
-/
theorem shiftCharge_of_aggregateBounds
    {activity insignificantActivity inserts changes valueBound
      threshold growingLimit : ℕ}
    {rankSum vSum wSum uSum : ℤ}
    (activity_le_rank : (activity : ℤ) ≤ rankSum)
    (decompose : rankSum = vSum + wSum + uSum)
    (v_bound :
      vSum ≤
        ((valueBound * insignificantActivity +
          threshold * changes : ℕ) : ℤ))
    (u_bound :
      uSum ≤
        ((valueBound * insignificantActivity +
          growingLimit * threshold * changes : ℕ) : ℤ))
    (w_bound :
      wSum ≤ ((valueBound * inserts : ℕ) : ℤ)) :
    activity ≤
      2 * valueBound * insignificantActivity +
        valueBound * inserts +
        (growingLimit + 1) * threshold * changes := by
  have signed_bound :
      (activity : ℤ) ≤
        ((2 * valueBound * insignificantActivity +
          valueBound * inserts +
          (growingLimit + 1) * threshold * changes : ℕ) : ℤ) := by
    calc
      (activity : ℤ) ≤ rankSum :=
        activity_le_rank
      _ = vSum + wSum + uSum :=
        decompose
      _ ≤
          ((valueBound * insignificantActivity +
            threshold * changes : ℕ) : ℤ) +
            ((valueBound * inserts : ℕ) : ℤ) +
            ((valueBound * insignificantActivity +
              growingLimit * threshold * changes : ℕ) : ℤ) :=
        add_le_add (add_le_add v_bound w_bound) u_bound
      _ =
          ((2 * valueBound * insignificantActivity +
            valueBound * inserts +
            (growingLimit + 1) * threshold * changes : ℕ) : ℤ) := by
        push_cast
        ring
  exact_mod_cast signed_bound

/--
Replace the explicit significant-pass threshold by its logarithmic upper
bound.  This is the exact shape needed by `ShiftChargingHypothesis`.
-/
theorem shiftCharge_of_logarithmicThreshold
    {activity insignificantActivity inserts changes valueBound
      logarithm threshold growingLimit thresholdConstant : ℕ}
    (shiftCharge :
      activity ≤
        2 * valueBound * insignificantActivity +
          valueBound * inserts +
          (growingLimit + 1) * threshold * changes)
    (threshold_le : threshold ≤ thresholdConstant * logarithm) :
    activity ≤
      2 * valueBound * insignificantActivity +
        valueBound * inserts +
        ((growingLimit + 1) * thresholdConstant) *
          logarithm * changes := by
  calc
    activity ≤
        2 * valueBound * insignificantActivity +
          valueBound * inserts +
          (growingLimit + 1) * threshold * changes :=
      shiftCharge
    _ ≤
        2 * valueBound * insignificantActivity +
          valueBound * inserts +
          (growingLimit + 1) *
            (thresholdConstant * logarithm) * changes := by
      gcongr
    _ =
        2 * valueBound * insignificantActivity +
          valueBound * inserts +
          ((growingLimit + 1) * thresholdConstant) *
            logarithm * changes := by
      ring

/--
The terminal value obtained by following a (possibly empty) chain of value
snapshots.  Keeping the initial value explicit makes the empty-chain case
total and is convenient for episode accounting.
-/
def terminalSnapshot (initial : ℕ) : List ℕ → ℕ
  | [] => initial
  | next :: rest => terminalSnapshot next rest

/--
Signed telescoping sum along a chain of snapshots.  A transition from `old`
to `new` contributes `new - old`, exactly as the manuscript's `w`-shift.
-/
def snapshotShift (initial : ℕ) : List ℕ → ℤ
  | [] => 0
  | next :: rest =>
      (next : ℤ) - (initial : ℤ) + snapshotShift next rest

@[simp]
theorem terminalSnapshot_nil (initial : ℕ) :
    terminalSnapshot initial [] = initial :=
  rfl

@[simp]
theorem terminalSnapshot_cons (initial next : ℕ) (rest : List ℕ) :
    terminalSnapshot initial (next :: rest) =
      terminalSnapshot next rest :=
  rfl

@[simp]
theorem snapshotShift_nil (initial : ℕ) :
    snapshotShift initial [] = 0 :=
  rfl

@[simp]
theorem snapshotShift_cons (initial next : ℕ) (rest : List ℕ) :
    snapshotShift initial (next :: rest) =
      (next : ℤ) - (initial : ℤ) + snapshotShift next rest :=
  rfl

/--
All intermediate creator snapshots cancel: only the terminal and initial
values remain.  This is the algebraic core of the global `w`-shift charge.
-/
theorem snapshotShift_eq_terminal_sub (initial : ℕ) (rest : List ℕ) :
    snapshotShift initial rest =
      (terminalSnapshot initial rest : ℤ) - (initial : ℤ) := by
  induction rest generalizing initial with
  | nil =>
      simp
  | cons next rest ih =>
      simp only [snapshotShift_cons, terminalSnapshot_cons, ih]
      ring

/--
If the terminal snapshot is at most the interface value bound, the whole
signed telescoping chain is at most that bound.
-/
theorem snapshotShift_le_valueBound
    (initial valueBound : ℕ) (rest : List ℕ)
    (terminal_le :
      terminalSnapshot initial rest ≤ valueBound) :
    snapshotShift initial rest ≤ (valueBound : ℤ) := by
  rw [snapshotShift_eq_terminal_sub]
  omega

/-- One creator-snapshot chain, beginning at an `Insert` episode. -/
abbrev SnapshotChain :=
  ℕ × List ℕ

/-- Sum of the signed telescoping shifts of a finite family of chains. -/
def totalSnapshotShift (chains : List SnapshotChain) : ℤ :=
  (chains.map fun chain => snapshotShift chain.1 chain.2).sum

/--
If every chain ends at a bounded value, the family contributes at most one
`valueBound` charge per chain.  Later the lifetime ledger identifies those
chains bijectively with `Insert` operations.
-/
theorem totalSnapshotShift_le
    (chains : List SnapshotChain) (valueBound : ℕ)
    (terminal_le :
      ∀ chain ∈ chains,
        terminalSnapshot chain.1 chain.2 ≤ valueBound) :
    totalSnapshotShift chains ≤
      ((chains.length * valueBound : ℕ) : ℤ) := by
  induction chains with
  | nil =>
      simp [totalSnapshotShift]
  | cons chain chains ih =>
      have head_le :
          snapshotShift chain.1 chain.2 ≤ (valueBound : ℤ) :=
        snapshotShift_le_valueBound _ _ _
          (terminal_le chain (by simp))
      have tail_terminal :
          ∀ tailChain ∈ chains,
            terminalSnapshot tailChain.1 tailChain.2 ≤ valueBound := by
        intro tailChain tail_mem
        exact terminal_le tailChain (by simp [tail_mem])
      have tail_le := ih tail_terminal
      simp only [totalSnapshotShift, List.map_cons, List.sum_cons] at tail_le ⊢
      calc
        snapshotShift chain.1 chain.2 +
              (List.map
                (fun tailChain =>
                  snapshotShift tailChain.1 tailChain.2) chains).sum ≤
            (valueBound : ℤ) +
              ((chains.length * valueBound : ℕ) : ℤ) :=
          add_le_add head_le tail_le
        _ = ((((chain :: chains).length) * valueBound : ℕ) : ℤ) := by
          simp only [List.length_cons, Nat.cast_mul, Nat.cast_add,
            Nat.cast_one]
          ring

end Splay.Interface
