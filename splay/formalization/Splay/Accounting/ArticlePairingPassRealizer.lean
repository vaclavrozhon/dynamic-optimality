import Splay.Accounting.ArticleInternalPairingFraction
import Splay.Accounting.ArticleSourcePairingGeometry
import Splay.Interface.Decay
import Splay.Lazy.CanonicalTrace
import Splay.Lazy.Dynamic
import Splay.Lazy.GeometricPairUp

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

/-- The article's good/bad value dichotomy inside one lazy interval.

Strict comparison-rank order gives strict point-gap order because both
endpoints have the same heap owner and interval gap.  Contracting those gaps
either leaves a strict value order (a directly legal "bad" pairing), or puts
both endpoints in one bucket; in the latter case the winner's value is above
one and can be temporarily decreased. -/
theorem pairingValueOrder_or_equalCanDecrease
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    {source : Lazy.Block n} (sourceMember : source ∈ state.blocks)
    {winner loser : Interface.Element n}
    (winnerMember : winner ∈ source.elements)
    (loserMember : loser ∈ source.elements)
    (rankOrder : state.view.rank winner < state.view.rank loser) :
    state.value winner + 1 ≤ state.value loser ∨
      (state.value winner = state.value loser ∧
        1 < state.value winner) := by
  have structural := valid.2 source sourceMember
  have winnerParent := structural.parent_eq winnerMember
  have loserParent := structural.parent_eq loserMember
  have winnerMinimum := structural.intervalGap_le_raw winnerMember
  have loserMinimum := structural.intervalGap_le_raw loserMember
  have rawOrder :
      state.view.rawGap winner < state.view.rawGap loser := by
    simp only [Lazy.HeapView.rawGap, winnerParent, loserParent]
    have rankOrderInt :
        (state.view.rank winner : ℤ) < state.view.rank loser := by
      exact_mod_cast rankOrder
    omega
  have pointOrder :
      Analysis.transientPointGap
          (state.view.rawGap winner) source.intervalGap <
        Analysis.transientPointGap
          (state.view.rawGap loser) source.intervalGap := by
    have winnerPoint := structural.pointGap_coe_eq winnerMember
    have loserPoint := structural.pointGap_coe_eq loserMember
    have pointOrderInt :
        (Analysis.transientPointGap
            (state.view.rawGap winner) source.intervalGap : ℤ) <
          Analysis.transientPointGap
            (state.view.rawGap loser) source.intervalGap := by
      rw [winnerPoint, loserPoint]
      omega
    exact_mod_cast pointOrderInt
  have winnerValue := values.2 source sourceMember winner winnerMember
  have loserValue := values.2 source sourceMember loser loserMember
  have valueLe : state.value winner ≤ state.value loser := by
    rw [winnerValue, loserValue]
    exact Analysis.contractedGap_mono (Nat.le_of_lt pointOrder)
  rcases Nat.lt_or_eq_of_le valueLe with valueLt | valueEq
  · exact Or.inl (by omega)
  · refine Or.inr ⟨valueEq, ?_⟩
    rw [winnerValue]
    apply Analysis.one_lt_contractedGap_of_lt_of_eq pointOrder
    simpa only [Analysis.transientContractedGap] using
      winnerValue.symm.trans (valueEq.trans loserValue)

/-- Numeric post-pairing target for the loser.

Once the loser is reattached below the winner in a zero-gap growing interval,
its point gap is `rank loser - rank winner`.  This target never exceeds the
loser's old realized value; for a good (equal-valued) pairing it is smaller by
at least one.  This is the value-restoration statement used immediately after
the article's `Pass`. -/
theorem internalPairingLoserTarget_le
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    {source : Lazy.Block n} (sourceMember : source ∈ state.blocks)
    {winner loser : Interface.Element n}
    (winnerMember : winner ∈ source.elements)
    (loserMember : loser ∈ source.elements)
    (rankOrder : state.view.rank winner < state.view.rank loser) :
    let target := Analysis.contractedGap
      (state.view.rank loser - state.view.rank winner)
    target ≤ state.value loser ∧
      (state.value winner = state.value loser →
        target + 1 ≤ state.value loser) := by
  dsimp only
  have structural := valid.2 source sourceMember
  have winnerParent := structural.parent_eq winnerMember
  have loserParent := structural.parent_eq loserMember
  have winnerPoint := structural.pointGap_coe_eq winnerMember
  have loserPoint := structural.pointGap_coe_eq loserMember
  have pointOrder :
      Analysis.transientPointGap
          (state.view.rawGap winner) source.intervalGap <
        Analysis.transientPointGap
          (state.view.rawGap loser) source.intervalGap := by
    have pointOrderInt :
        (Analysis.transientPointGap
            (state.view.rawGap winner) source.intervalGap : ℤ) <
          Analysis.transientPointGap
            (state.view.rawGap loser) source.intervalGap := by
      rw [winnerPoint, loserPoint]
      simp only [Lazy.HeapView.rawGap, winnerParent, loserParent]
      have rankOrderInt :
          (state.view.rank winner : ℤ) < state.view.rank loser := by
        exact_mod_cast rankOrder
      omega
    exact_mod_cast pointOrderInt
  have balanceInt :
      (state.view.rank loser : ℤ) +
          Analysis.transientPointGap
            (state.view.rawGap winner) source.intervalGap =
        (state.view.rank winner : ℤ) +
          Analysis.transientPointGap
            (state.view.rawGap loser) source.intervalGap := by
    rw [winnerPoint, loserPoint]
    simp only [Lazy.HeapView.rawGap, winnerParent, loserParent]
    omega
  have balanceNat :
      state.view.rank loser +
          Analysis.transientPointGap
            (state.view.rawGap winner) source.intervalGap =
        state.view.rank winner +
          Analysis.transientPointGap
            (state.view.rawGap loser) source.intervalGap := by
    exact_mod_cast balanceInt
  have afterGap :
      state.view.rank loser - state.view.rank winner =
        Analysis.transientPointGap
            (state.view.rawGap loser) source.intervalGap -
          Analysis.transientPointGap
            (state.view.rawGap winner) source.intervalGap := by
    omega
  have gapDrop := Analysis.internalPairingGap
    (winner := Analysis.transientPointGap
      (state.view.rawGap winner) source.intervalGap)
    (loserBefore := Analysis.transientPointGap
      (state.view.rawGap loser) source.intervalGap)
    (loserAfter := state.view.rank loser - state.view.rank winner)
    pointOrder afterGap
  have winnerValue := values.2 source sourceMember winner winnerMember
  have loserValue := values.2 source sourceMember loser loserMember
  constructor
  · rw [loserValue]
    simpa only [Analysis.transientContractedGap] using gapDrop.1
  · intro equalValues
    rw [loserValue]
    apply gapDrop.2
    simpa only [Analysis.transientContractedGap] using
      winnerValue.symm.trans (equalValues.trans loserValue)

/-- The good pairings are precisely the equal-valued pairings of the
manuscript. -/
def articleGoodPairings {n : ℕ} (state : Lazy.State n)
    (matching : List (Interface.Pairing n)) :
    List (Interface.Pairing n) :=
  matching.filter fun pairing =>
    decide (state.value pairing.winner = state.value pairing.loser)

/-- Winners to decrease before executing an article pass. -/
def articleGoodWinners {n : ℕ} (state : Lazy.State n)
    (matching : List (Interface.Pairing n)) :
    List (Interface.Element n) :=
  (articleGoodPairings state matching).map Interface.Pairing.winner

/-- Visible rich events implementing one article batch: prepare exactly the
equal-valued winners, perform the simultaneous pass, and restore them. -/
def articlePairingPassEvents {n : ℕ} (state : Lazy.State n)
    (sourceId : Interface.BlockId)
    (matching : List (Interface.Pairing n)) : List (Lazy.Event n) :=
  let winners := articleGoodWinners state matching
  (winners.map fun winner =>
      .operation (.valueChange winner .decrease)) ++
    [.operation (.pass sourceId matching)] ++
    (winners.map fun winner =>
      .operation (.valueChange winner .increase))

@[simp]
theorem articleGoodWinners_cons
    {n : ℕ} (state : Lazy.State n) (pairing : Interface.Pairing n)
    (matching : List (Interface.Pairing n)) :
    articleGoodWinners state (pairing :: matching) =
      if state.value pairing.winner = state.value pairing.loser then
        pairing.winner :: articleGoodWinners state matching
      else
        articleGoodWinners state matching := by
  by_cases equal : state.value pairing.winner = state.value pairing.loser
  · simp [articleGoodWinners, articleGoodPairings, equal]
  · simp [articleGoodWinners, articleGoodPairings, equal]

private theorem pairingWinners_sublist
    {n : ℕ} (matching : List (Interface.Pairing n)) :
    (matching.map Interface.Pairing.winner).Sublist
      (matching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]) := by
  induction matching with
  | nil => exact .slnil
  | cons pairing matching ih =>
      exact (ih.cons pairing.loser).cons_cons pairing.winner

private theorem articleGoodWinners_sublist
    {n : ℕ} (state : Lazy.State n)
    (matching : List (Interface.Pairing n)) :
    (articleGoodWinners state matching).Sublist
      (matching.map Interface.Pairing.winner) := by
  exact (List.filter_sublist (p := fun pairing : Interface.Pairing n =>
    decide (state.value pairing.winner = state.value pairing.loser))).map _

/-- Endpoint-disjoint pairings have distinct winners. -/
theorem pairingWinners_nodup
    {n : ℕ} {matching : List (Interface.Pairing n)}
    (endpointsNodup :
      (matching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]).Nodup) :
    (matching.map Interface.Pairing.winner).Nodup :=
  (pairingWinners_sublist matching).nodup endpointsNodup

theorem articleGoodWinners_nodup
    {n : ℕ} {state : Lazy.State n}
    {matching : List (Interface.Pairing n)}
    (endpointsNodup :
      (matching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]).Nodup) :
    (articleGoodWinners state matching).Nodup := by
  exact (articleGoodWinners_sublist state matching).nodup
    (pairingWinners_nodup endpointsNodup)

private theorem pairingLoser_not_mem_pairingWinners
    {n : ℕ} {matching : List (Interface.Pairing n)}
    (endpointsNodup :
      (matching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]).Nodup)
    {pairing : Interface.Pairing n} (pairingMember : pairing ∈ matching) :
    pairing.loser ∉ matching.map Interface.Pairing.winner := by
  induction matching with
  | nil => simp at pairingMember
  | cons head matching ih =>
      have expanded :
          (head.winner :: head.loser ::
            (matching.flatMap fun later =>
              [later.winner, later.loser])).Nodup := by
        simpa using endpointsNodup
      have headFresh := (List.nodup_cons.mp expanded).1
      have afterHead := (List.nodup_cons.mp expanded).2
      have loserFresh := (List.nodup_cons.mp afterHead).1
      have tailNodup := (List.nodup_cons.mp afterHead).2
      rcases List.mem_cons.mp pairingMember with rfl | tailMember
      · have headNe : pairing.loser ≠ pairing.winner := by
          intro equal
          exact headFresh (by simp [equal])
        have notTailWinners :
            pairing.loser ∉ matching.map Interface.Pairing.winner := by
          intro member
          exact loserFresh
            ((pairingWinners_sublist matching).subset member)
        simpa [headNe, notTailWinners]
      · have loserInTail : pairing.loser ∈
            matching.flatMap fun later =>
              [later.winner, later.loser] :=
          List.mem_flatMap.mpr ⟨pairing, tailMember, by simp⟩
        have loserNeHead : pairing.loser ≠ head.winner := by
          intro equal
          exact headFresh (by simp [← equal, loserInTail])
        simpa [loserNeHead] using ih tailNodup tailMember

/-- Endpoint disjointness makes membership in the good-winner list equivalent
to the value equality of that very pairing. -/
theorem pairingWinner_mem_articleGoodWinners_iff
    {n : ℕ} {state : Lazy.State n}
    {matching : List (Interface.Pairing n)}
    (endpointsNodup :
      (matching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]).Nodup)
    {pairing : Interface.Pairing n} (pairingMember : pairing ∈ matching) :
    pairing.winner ∈ articleGoodWinners state matching ↔
      state.value pairing.winner = state.value pairing.loser := by
  induction matching with
  | nil => simp at pairingMember
  | cons head matching ih =>
      have expanded :
          (head.winner :: head.loser ::
            (matching.flatMap fun later =>
              [later.winner, later.loser])).Nodup := by
        simpa using endpointsNodup
      have headFresh := (List.nodup_cons.mp expanded).1
      have afterHead := (List.nodup_cons.mp expanded).2
      have tailNodup := (List.nodup_cons.mp afterHead).2
      rcases List.mem_cons.mp pairingMember with rfl | tailMember
      · have notTail :
            pairing.winner ∉ articleGoodWinners state matching := by
          intro member
          apply headFresh
          exact List.mem_cons_of_mem pairing.loser
            ((pairingWinners_sublist matching).subset
              ((articleGoodWinners_sublist state matching).subset member))
        by_cases equal :
            state.value pairing.winner = state.value pairing.loser
        · simp [equal]
        · simp [equal, notTail]
      · have winnerInTail : pairing.winner ∈
            matching.flatMap fun later =>
              [later.winner, later.loser] :=
          List.mem_flatMap.mpr ⟨pairing, tailMember, by simp⟩
        have winnerNeHead : pairing.winner ≠ head.winner := by
          intro equal
          exact headFresh (by simp [← equal, winnerInTail])
        by_cases headEqual :
            state.value head.winner = state.value head.loser
        · simpa [headEqual, winnerNeHead] using ih tailNodup tailMember
        · simpa [headEqual] using
            ih tailNodup tailMember

/-- No loser is changed by the temporary winner preparation. -/
theorem pairingLoser_not_mem_articleGoodWinners
    {n : ℕ} {state : Lazy.State n}
    {matching : List (Interface.Pairing n)}
    (endpointsNodup :
      (matching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]).Nodup)
    {pairing : Interface.Pairing n} (pairingMember : pairing ∈ matching) :
    pairing.loser ∉ articleGoodWinners state matching := by
  intro member
  exact pairingLoser_not_mem_pairingWinners endpointsNodup pairingMember
    ((articleGoodWinners_sublist state matching).subset member)

/-- Apply one unit decrease to each element of a list, in list order. -/
def decreaseEach {n : ℕ} (state : Lazy.State n) :
    List (Interface.Element n) → Lazy.State n
  | [] => state
  | element :: elements =>
      decreaseEach (state.decreaseValue element) elements

@[simp]
theorem decreaseEach_value_of_not_mem
    {n : ℕ} (state : Lazy.State n)
    (elements : List (Interface.Element n))
    {queried : Interface.Element n} (notMember : queried ∉ elements) :
    (decreaseEach state elements).value queried = state.value queried := by
  induction elements generalizing state with
  | nil => rfl
  | cons element elements ih =>
      have parts : queried ≠ element ∧ queried ∉ elements := by
        simpa only [List.mem_cons, not_or] using notMember
      have queriedNe : queried ≠ element := parts.1
      have notTail : queried ∉ elements := parts.2
      rw [decreaseEach, ih (state := state.decreaseValue element) notTail]
      simp [Lazy.State.decreaseValue, queriedNe]

@[simp]
theorem decreaseEach_value_of_mem
    {n : ℕ} (state : Lazy.State n)
    {elements : List (Interface.Element n)} (nodup : elements.Nodup)
    {queried : Interface.Element n} (member : queried ∈ elements) :
    (decreaseEach state elements).value queried =
      state.value queried - 1 := by
  induction elements generalizing state with
  | nil => simp at member
  | cons element elements ih =>
      have parts := List.nodup_cons.mp nodup
      rcases List.mem_cons.mp member with rfl | tailMember
      · rw [decreaseEach,
          decreaseEach_value_of_not_mem
            (state.decreaseValue queried) elements parts.1]
        simp [Lazy.State.decreaseValue]
      · have queriedNe : queried ≠ element := by
          intro equal
          subst queried
          exact parts.1 tailMember
        rw [decreaseEach, ih (state := state.decreaseValue element)
          parts.2 tailMember]
        simp [Lazy.State.decreaseValue, queriedNe]

@[simp]
theorem decreaseEach_blocks
    {n : ℕ} (state : Lazy.State n)
    (elements : List (Interface.Element n)) :
    (decreaseEach state elements).blocks = state.blocks := by
  induction elements generalizing state with
  | nil => rfl
  | cons element elements ih =>
      rw [decreaseEach, ih]
      rfl

@[simp]
theorem decreaseEach_view
    {n : ℕ} (state : Lazy.State n)
    (elements : List (Interface.Element n)) :
    (decreaseEach state elements).view = state.view := by
  induction elements generalizing state with
  | nil => rfl
  | cons element elements ih =>
      rw [decreaseEach, ih]
      rfl

/-- The batch of unit decreases is a legal rich trace whenever every listed
value starts above one and the elements are distinct. -/
theorem decreaseEach_trace
    {n : ℕ} {params : Interface.Parameters} (state : Lazy.State n)
    (elements : List (Interface.Element n))
    (valid : state.Valid params) (nodup : elements.Nodup)
    (canDecrease : ∀ element ∈ elements, 1 < state.value element) :
    Trace params state
      (elements.map fun element =>
        .operation (.valueChange element .decrease))
      (decreaseEach state elements) := by
  induction elements generalizing state with
  | nil => exact Trace.nil valid
  | cons element elements ih =>
      have parts := List.nodup_cons.mp nodup
      have headCan : 1 < state.value element :=
        canDecrease element (by simp)
      have afterValid := state.decreaseValue_valid element valid headCan
      have tailCan : ∀ queried ∈ elements,
          1 < (state.decreaseValue element).value queried := by
        intro queried queriedMember
        have queriedNe : queried ≠ element := by
          intro equal
          subst queried
          exact parts.1 queriedMember
        simpa [Lazy.State.decreaseValue, queriedNe] using
          canDecrease queried (by simp [queriedMember])
      exact Trace.cons
        (state.decreaseValue_step element valid headCan)
        (ih (state := state.decreaseValue element) afterValid parts.2 tailCan)

/-- Apply one unit increase to each rich-state element, in list order. -/
def increaseEach {n : ℕ} (state : Lazy.State n) :
    List (Interface.Element n) → Lazy.State n
  | [] => state
  | element :: elements =>
      increaseEach (state.increaseValue element) elements

@[simp]
theorem increaseEach_value_of_not_mem
    {n : ℕ} (state : Lazy.State n)
    (elements : List (Interface.Element n))
    {queried : Interface.Element n} (notMember : queried ∉ elements) :
    (increaseEach state elements).value queried = state.value queried := by
  induction elements generalizing state with
  | nil => rfl
  | cons element elements ih =>
      have parts : queried ≠ element ∧ queried ∉ elements := by
        simpa only [List.mem_cons, not_or] using notMember
      rw [increaseEach,
        ih (state := state.increaseValue element) parts.2]
      simp [Lazy.State.increaseValue, parts.1]

@[simp]
theorem increaseEach_value_of_mem
    {n : ℕ} (state : Lazy.State n)
    {elements : List (Interface.Element n)} (nodup : elements.Nodup)
    {queried : Interface.Element n} (member : queried ∈ elements) :
    (increaseEach state elements).value queried =
      state.value queried + 1 := by
  induction elements generalizing state with
  | nil => simp at member
  | cons element elements ih =>
      have parts := List.nodup_cons.mp nodup
      rcases List.mem_cons.mp member with rfl | tailMember
      · rw [increaseEach,
          increaseEach_value_of_not_mem
            (state.increaseValue queried) elements parts.1]
        simp [Lazy.State.increaseValue]
      · have queriedNe : queried ≠ element := by
          intro equal
          subst queried
          exact parts.1 tailMember
        rw [increaseEach,
          ih (state := state.increaseValue element) parts.2 tailMember]
        simp [Lazy.State.increaseValue, queriedNe]

@[simp]
theorem increaseEach_blocks
    {n : ℕ} (state : Lazy.State n)
    (elements : List (Interface.Element n)) :
    (increaseEach state elements).blocks = state.blocks := by
  induction elements generalizing state with
  | nil => rfl
  | cons element elements ih =>
      rw [increaseEach, ih]
      rfl

@[simp]
theorem increaseEach_view
    {n : ℕ} (state : Lazy.State n)
    (elements : List (Interface.Element n)) :
    (increaseEach state elements).view = state.view := by
  induction elements generalizing state with
  | nil => rfl
  | cons element elements ih =>
      rw [increaseEach, ih]
      rfl

/-- Distinct bounded rich-state values can all be restored legally. -/
theorem increaseEach_trace
    {n : ℕ} {params : Interface.Parameters} (state : Lazy.State n)
    (elements : List (Interface.Element n))
    (valid : state.Valid params) (nodup : elements.Nodup)
    (canIncrease : ∀ element ∈ elements,
      state.value element < params.valueBound) :
    Trace params state
      (elements.map fun element =>
        .operation (.valueChange element .increase))
      (increaseEach state elements) := by
  induction elements generalizing state with
  | nil => exact Trace.nil valid
  | cons element elements ih =>
      have parts := List.nodup_cons.mp nodup
      have headCan := canIncrease element (by simp)
      have afterValid :=
        state.increaseValue_valid element valid headCan
      have tailCan : ∀ queried ∈ elements,
          (state.increaseValue element).value queried <
            params.valueBound := by
        intro queried queriedMember
        have queriedNe : queried ≠ element := by
          intro equal
          subst queried
          exact parts.1 queriedMember
        simpa [Lazy.State.increaseValue, queriedNe] using
          canIncrease queried (by simp [queriedMember])
      exact Trace.cons
        (state.increaseValue_step element valid headCan)
        (ih (state := state.increaseValue element)
          afterValid parts.2 tailCan)

/-- Increasing the distinct values just decreased restores the full value
function, provided each original value was positive. -/
theorem increaseEach_decreaseEach_value
    {n : ℕ} (state : Lazy.State n)
    (elements : List (Interface.Element n))
    (nodup : elements.Nodup)
    (positive : ∀ element ∈ elements, 1 ≤ state.value element) :
    (increaseEach (decreaseEach state elements) elements).value =
      state.value := by
  funext queried
  by_cases member : queried ∈ elements
  · rw [increaseEach_value_of_mem _ nodup member,
      decreaseEach_value_of_mem state nodup member]
    exact Nat.sub_add_cancel (positive queried member)
  · rw [increaseEach_value_of_not_mem _ elements member,
      decreaseEach_value_of_not_mem state elements member]

/-- Abstract-interface counterpart used after the pass, when the rich heap
view is intentionally not changed by value restoration. -/
def interfaceIncreaseValue {n : ℕ} (state : Interface.State n)
    (element : Interface.Element n) : Interface.State n :=
  { state with
    value :=
      Function.update state.value element
        (state.value element + 1) }

/-- Apply one unit increase to each listed interface element. -/
def interfaceIncreaseEach {n : ℕ} (state : Interface.State n) :
    List (Interface.Element n) → Interface.State n
  | [] => state
  | element :: elements =>
      interfaceIncreaseEach (interfaceIncreaseValue state element) elements

@[simp]
theorem interfaceIncreaseEach_value_of_not_mem
    {n : ℕ} (state : Interface.State n)
    (elements : List (Interface.Element n))
    {queried : Interface.Element n} (notMember : queried ∉ elements) :
    (interfaceIncreaseEach state elements).value queried =
      state.value queried := by
  induction elements generalizing state with
  | nil => rfl
  | cons element elements ih =>
      have parts : queried ≠ element ∧ queried ∉ elements := by
        simpa only [List.mem_cons, not_or] using notMember
      rw [interfaceIncreaseEach,
        ih (state := interfaceIncreaseValue state element) parts.2]
      simp [interfaceIncreaseValue, parts.1]

@[simp]
theorem interfaceIncreaseEach_value_of_mem
    {n : ℕ} (state : Interface.State n)
    {elements : List (Interface.Element n)} (nodup : elements.Nodup)
    {queried : Interface.Element n} (member : queried ∈ elements) :
    (interfaceIncreaseEach state elements).value queried =
      state.value queried + 1 := by
  induction elements generalizing state with
  | nil => simp at member
  | cons element elements ih =>
      have parts := List.nodup_cons.mp nodup
      rcases List.mem_cons.mp member with rfl | tailMember
      · rw [interfaceIncreaseEach,
          interfaceIncreaseEach_value_of_not_mem
            (interfaceIncreaseValue state queried) elements parts.1]
        simp [interfaceIncreaseValue]
      · have queriedNe : queried ≠ element := by
          intro equal
          subst queried
          exact parts.1 tailMember
        rw [interfaceIncreaseEach,
          ih (state := interfaceIncreaseValue state element)
            parts.2 tailMember]
        simp [interfaceIncreaseValue, queriedNe]

@[simp]
theorem interfaceIncreaseEach_blocks
    {n : ℕ} (state : Interface.State n)
    (elements : List (Interface.Element n)) :
    (interfaceIncreaseEach state elements).blocks = state.blocks := by
  induction elements generalizing state with
  | nil => rfl
  | cons element elements ih =>
      rw [interfaceIncreaseEach, ih]
      rfl

private theorem interfaceIncreaseValue_valid
    {n : ℕ} {params : Interface.Parameters}
    (state : Interface.State n) (element : Interface.Element n)
    (valid : state.Valid params)
    (canIncrease : state.value element < params.valueBound) :
    (interfaceIncreaseValue state element).Valid params := by
  refine ⟨valid.1, ?_, valid.2.2⟩
  intro queried
  by_cases equal : queried = element
  · subst queried
    simp only [interfaceIncreaseValue, Function.update_self]
    have bounds := valid.2.1 element
    omega
  · simp only [interfaceIncreaseValue, Function.update_apply, if_neg equal]
    exact valid.2.1 queried

private theorem interfaceIncreaseValue_step
    {n : ℕ} {params : Interface.Parameters}
    (state : Interface.State n) (element : Interface.Element n)
    (valid : state.Valid params)
    (canIncrease : state.value element < params.valueBound) :
    Interface.Step params state (.valueChange element .increase)
      (interfaceIncreaseValue state element) := by
  exact ⟨valid,
    .increase canIncrease rfl rfl,
    interfaceIncreaseValue_valid state element valid canIncrease⟩

/-- Distinct bounded values can all be restored by legal unit increases. -/
theorem interfaceIncreaseEach_trace
    {n : ℕ} {params : Interface.Parameters}
    (state : Interface.State n) (elements : List (Interface.Element n))
    (valid : state.Valid params) (nodup : elements.Nodup)
    (canIncrease : ∀ element ∈ elements,
      state.value element < params.valueBound) :
    Interface.Trace params state
      (elements.map fun element =>
        .valueChange element .increase)
      (interfaceIncreaseEach state elements) := by
  induction elements generalizing state with
  | nil => exact .nil valid
  | cons element elements ih =>
      have parts := List.nodup_cons.mp nodup
      have headCan := canIncrease element (by simp)
      have afterValid :=
        interfaceIncreaseValue_valid state element valid headCan
      have tailCan : ∀ queried ∈ elements,
          (interfaceIncreaseValue state element).value queried <
            params.valueBound := by
        intro queried queriedMember
        have different : queried ≠ element := by
          intro equal
          subst queried
          exact parts.1 queriedMember
        simpa [interfaceIncreaseValue, different] using
          canIncrease queried (by simp [queriedMember])
      exact .cons
        (interfaceIncreaseValue_step state element valid headCan)
        (ih (state := interfaceIncreaseValue state element)
          afterValid parts.2 tailCan)

private theorem interfaceTrace_append
    {n : ℕ} {params : Interface.Parameters}
    {first middle final : Interface.State n}
    {beforeOperations afterOperations : List (Interface.Operation n)}
    (left : Interface.Trace params first beforeOperations middle)
    (right : Interface.Trace params middle afterOperations final) :
    Interface.Trace params first
      (beforeOperations ++ afterOperations) final := by
  induction left with
  | nil _ => simpa using right
  | cons head tail ih =>
      exact .cons head (ih right)

/-- In an increasing full-order list, an endpoint adjacent to the winner is
closer than every other endpoint on the same side of that winner. -/
private theorem outer_of_adjacent_of_pairwise_lt
    {n : ℕ} {elements : List (Interface.Element n)}
    {winner first second : Interface.Element n}
    (ordered : elements.Pairwise fun earlier later =>
      earlier.val < later.val)
    (adjacent : Interface.Adjacent elements winner first)
    (secondMember : second ∈ elements)
    (winnerNeFirst : winner ≠ first)
    (winnerNeSecond : winner ≠ second)
    (firstNeSecond : first ≠ second)
    (sameSide : Splay.Lazy.Canonical.sideOf winner first =
      Splay.Lazy.Canonical.sideOf winner second) :
    match Splay.Lazy.Canonical.sideOf winner second with
    | .left => second.val < first.val
    | .right => first.val < second.val := by
  have sameLeft : (first.val < winner.val) ↔
      (second.val < winner.val) := by
    unfold Splay.Lazy.Canonical.sideOf at sameSide
    by_cases firstLeft : first.val < winner.val <;>
      by_cases secondLeft : second.val < winner.val <;>
      simp_all <;> omega
  obtain ⟨front, back, decomposition⟩ := adjacent
  rcases decomposition with forward | backward
  · rw [forward] at ordered secondMember
    have suffixOrdered := (List.pairwise_append.mp ordered).2.1
    have winnerBeforeFirst : winner.val < first.val :=
      (List.pairwise_cons.mp suffixOrdered).1 first (by simp)
    have firstRelations :=
      (List.pairwise_cons.mp
        (List.pairwise_cons.mp suffixOrdered).2).1
    have alternatives : second.val < winner.val ∨
        first.val < second.val := by
      simp only [List.mem_append, List.mem_cons] at secondMember
      rcases secondMember with frontMember | equalWinner | equalFirst |
          backMember
      · left
        exact (List.pairwise_append.mp ordered).2.2 second frontMember
          winner (by simp)
      · exact False.elim (winnerNeSecond equalWinner.symm)
      · exact False.elim (firstNeSecond equalFirst.symm)
      · right
        exact firstRelations second backMember
    have secondNotLeft : ¬ second.val < winner.val := by
      rw [← sameLeft]
      omega
    have firstBeforeSecond : first.val < second.val :=
      alternatives.resolve_left secondNotLeft
    simp [Splay.Lazy.Canonical.sideOf, secondNotLeft, firstBeforeSecond]
  · rw [backward] at ordered secondMember
    have suffixOrdered := (List.pairwise_append.mp ordered).2.1
    have firstBeforeWinner : first.val < winner.val :=
      (List.pairwise_cons.mp suffixOrdered).1 winner (by simp)
    have alternatives : second.val < first.val ∨
        winner.val < second.val := by
      have winnerRelations :=
        (List.pairwise_cons.mp
          (List.pairwise_cons.mp suffixOrdered).2).1
      simp only [List.mem_append, List.mem_cons] at secondMember
      rcases secondMember with frontMember | equalFirst | equalWinner |
          backMember
      · left
        exact (List.pairwise_append.mp ordered).2.2 second frontMember
          first (by simp)
      · exact False.elim (firstNeSecond equalFirst.symm)
      · exact False.elim (winnerNeSecond equalWinner.symm)
      · right
        exact winnerRelations second backMember
    have secondLeft : second.val < winner.val := sameLeft.mp firstBeforeWinner
    have secondBeforeFirst : second.val < first.val := by
      rcases alternatives with result | winnerBeforeSecond
      · exact result
      · omega
    simp [Splay.Lazy.Canonical.sideOf, secondLeft, secondBeforeFirst]

/-- Decreasing-order counterpart of `outer_of_adjacent_of_pairwise_lt`. -/
private theorem outer_of_adjacent_of_pairwise_gt
    {n : ℕ} {elements : List (Interface.Element n)}
    {winner first second : Interface.Element n}
    (ordered : elements.Pairwise fun earlier later =>
      later.val < earlier.val)
    (adjacent : Interface.Adjacent elements winner first)
    (secondMember : second ∈ elements)
    (winnerNeFirst : winner ≠ first)
    (winnerNeSecond : winner ≠ second)
    (firstNeSecond : first ≠ second)
    (sameSide : Splay.Lazy.Canonical.sideOf winner first =
      Splay.Lazy.Canonical.sideOf winner second) :
    match Splay.Lazy.Canonical.sideOf winner second with
    | .left => second.val < first.val
    | .right => first.val < second.val := by
  have sameLeft : (first.val < winner.val) ↔
      (second.val < winner.val) := by
    unfold Splay.Lazy.Canonical.sideOf at sameSide
    by_cases firstLeft : first.val < winner.val <;>
      by_cases secondLeft : second.val < winner.val <;>
      simp_all <;> omega
  obtain ⟨front, back, decomposition⟩ := adjacent
  rcases decomposition with forward | backward
  · rw [forward] at ordered secondMember
    have suffixOrdered := (List.pairwise_append.mp ordered).2.1
    have firstBeforeWinner : first.val < winner.val :=
      (List.pairwise_cons.mp suffixOrdered).1 first (by simp)
    have firstRelations :=
      (List.pairwise_cons.mp
        (List.pairwise_cons.mp suffixOrdered).2).1
    have alternatives : winner.val < second.val ∨
        second.val < first.val := by
      simp only [List.mem_append, List.mem_cons] at secondMember
      rcases secondMember with frontMember | equalWinner | equalFirst |
          backMember
      · left
        exact (List.pairwise_append.mp ordered).2.2 second frontMember
          winner (by simp)
      · exact False.elim (winnerNeSecond equalWinner.symm)
      · exact False.elim (firstNeSecond equalFirst.symm)
      · right
        exact firstRelations second backMember
    have secondLeft : second.val < winner.val := sameLeft.mp firstBeforeWinner
    have secondBeforeFirst : second.val < first.val := by
      rcases alternatives with winnerBeforeSecond | result
      · omega
      · exact result
    simp [Splay.Lazy.Canonical.sideOf, secondLeft, secondBeforeFirst]
  · rw [backward] at ordered secondMember
    have suffixOrdered := (List.pairwise_append.mp ordered).2.1
    have winnerBeforeFirst : winner.val < first.val :=
      (List.pairwise_cons.mp suffixOrdered).1 winner (by simp)
    have alternatives : first.val < second.val ∨
        second.val < winner.val := by
      have winnerRelations :=
        (List.pairwise_cons.mp
          (List.pairwise_cons.mp suffixOrdered).2).1
      simp only [List.mem_append, List.mem_cons] at secondMember
      rcases secondMember with frontMember | equalFirst | equalWinner |
          backMember
      · left
        exact (List.pairwise_append.mp ordered).2.2 second frontMember
          first (by simp)
      · exact False.elim (firstNeSecond equalFirst.symm)
      · exact False.elim (winnerNeSecond equalWinner.symm)
      · right
        exact winnerRelations second backMember
    have secondNotLeft : ¬ second.val < winner.val := by
      rw [← sameLeft]
      omega
    have firstBeforeSecond : first.val < second.val :=
      alternatives.resolve_right secondNotLeft
    simp [Splay.Lazy.Canonical.sideOf, secondNotLeft, firstBeforeSecond]

/-- Select the endpoint pair of one retained row in the requested article
phase. -/
def articleRowSelection {n : ℕ} (phase : PairingPhase)
    (row : ℕ × (List (Interface.Element n) × List (Interface.Element n))) :
    List (Interface.Element n) :=
  match phase with
  | .first => row.2.1
  | .second => row.2.2

/-- A concrete interface matching uses exactly the endpoint pairs stored in
the retained article rows, without reordering them. -/
def ArticleBatchEndpointAgreement
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ}
    (phase : PairingPhase)
    (batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups)
    (matching : List (Interface.Pairing n)) : Prop :=
  List.Forall₂
    (fun row pairing =>
      articleRowSelection phase row = [pairing.winner, pairing.loser])
    batches.rows matching

namespace ArticleBatchEndpointAgreement

private theorem matchingEndpoints_eq_rows_of_forall₂
    {n : ℕ} {phase : PairingPhase}
    {rows : List
      (ℕ × (List (Interface.Element n) × List (Interface.Element n)))}
    {matching : List (Interface.Pairing n)}
    (agreement : List.Forall₂
      (fun row pairing =>
        articleRowSelection phase row = [pairing.winner, pairing.loser])
      rows matching) :
    (matching.flatMap fun pairing => [pairing.winner, pairing.loser]) =
      (rows.flatMap fun row => articleRowSelection phase row) := by
  induction agreement with
  | nil => rfl
  | @cons row pairing rows matching related rest ih =>
      simp only [List.flatMap_cons]
      rw [related, ih]

private theorem exists_row_of_mem_forall₂
    {n : ℕ} {phase : PairingPhase}
    {rows : List
      (ℕ × (List (Interface.Element n) × List (Interface.Element n)))}
    {matching : List (Interface.Pairing n)}
    (agreement : List.Forall₂
      (fun row pairing =>
        articleRowSelection phase row = [pairing.winner, pairing.loser])
      rows matching)
    {pairing : Interface.Pairing n} (pairingMember : pairing ∈ matching) :
    ∃ row,
      row ∈ rows ∧
        articleRowSelection phase row =
          [pairing.winner, pairing.loser] := by
  induction agreement with
  | nil => simp at pairingMember
  | @cons row head rows matching related rest ih =>
      simp only [List.mem_cons] at pairingMember
      rcases pairingMember with rfl | tailMember
      · exact ⟨row, by simp, related⟩
      · obtain ⟨selected, selectedMember, selectedRelated⟩ := ih tailMember
        exact ⟨selected, by simp [selectedMember], selectedRelated⟩

/-- Agreement identifies the complete flattened endpoint batch. -/
theorem matchingEndpoints_eq_rows
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ} {phase : PairingPhase}
    {batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups}
    {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement phase batches matching) :
    (matching.flatMap fun pairing => [pairing.winner, pairing.loser]) =
      (batches.rows.flatMap fun row => articleRowSelection phase row) := by
  exact matchingEndpoints_eq_rows_of_forall₂ agreement

/-- Every concrete pairing has its unique positionally corresponding row. -/
theorem exists_row_of_mem
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ} {phase : PairingPhase}
    {batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups}
    {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement phase batches matching)
    {pairing : Interface.Pairing n} (pairingMember : pairing ∈ matching) :
    ∃ row,
      row ∈ batches.rows ∧
        articleRowSelection phase row =
          [pairing.winner, pairing.loser] := by
  exact exists_row_of_mem_forall₂ agreement pairingMember

/-- Every concrete pairing retains the strict comparison-rank order selected
by its zig-zig phase. -/
theorem rank_lt
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ} {phase : PairingPhase}
    {batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups}
    {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement phase batches matching)
    {pairing : Interface.Pairing n} (pairingMember : pairing ∈ matching) :
    snapshot.rank pairing.winner < snapshot.rank pairing.loser := by
  obtain ⟨row, rowMember, selectedEq⟩ :=
    agreement.exists_row_of_mem pairingMember
  obtain ⟨extra, winner, firstLoser, secondLoser, candidates,
      firstEq, secondEq, chunkEq, candidateLength, firstAdjacent,
      secondAdjacent, losersNe, candidatePerm, firstRankLt,
      secondRankLt⟩ := batches.aligned row rowMember
  cases phase with
  | first =>
      simp only [articleRowSelection] at selectedEq
      have endpointsEq :
          [winner, firstLoser] = [pairing.winner, pairing.loser] :=
        firstEq.symm.trans selectedEq
      simp at endpointsEq
      simpa [endpointsEq.1, endpointsEq.2] using firstRankLt
  | second =>
      simp only [articleRowSelection] at selectedEq
      have endpointsEq :
          [winner, secondLoser] = [pairing.winner, pairing.loser] :=
        secondEq.symm.trans selectedEq
      simp at endpointsEq
      simpa [endpointsEq.1, endpointsEq.2] using secondRankLt

/-- Each retained group contributes exactly one concrete pairing in either
article phase. -/
theorem matching_length_eq_eligibleGroups_length
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ} {phase : PairingPhase}
    {batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups}
    {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement phase batches matching) :
    matching.length = eligibleGroups.length := by
  calc
    matching.length = batches.rows.length :=
      (List.Forall₂.length_eq agreement).symm
    _ = eligibleGroups.length :=
      batches.length_eq_eligibleGroups_length

private theorem firstLosers_eq_pairingLosers_of_forall₂
    {n : ℕ}
    {rows : List
      (ℕ × (List (Interface.Element n) × List (Interface.Element n)))}
    {matching : List (Interface.Pairing n)}
    (agreement : List.Forall₂
      (fun row pairing =>
        row.2.1 = [pairing.winner, pairing.loser]) rows matching) :
    (rows.filterMap fun row => row.2.1[1]?) =
      Interface.pairingLosers matching := by
  induction agreement with
  | nil => rfl
  | @cons row pairing rows matching related rest ih =>
      simp [related, ih, Interface.pairingLosers]

/-- In the first phase, the batch's stored removal list is exactly the loser
projection of the concrete interface matching. -/
theorem firstLosers_eq_pairingLosers
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ}
    {batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups}
    {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement .first batches matching) :
    batches.firstLosers = Interface.pairingLosers matching := by
  exact firstLosers_eq_pairingLosers_of_forall₂ agreement

end ArticleBatchEndpointAgreement

/-- The constant-six boundary loss in the manuscript implies its advertised
one-tenth matching fraction for every nonempty retained batch.  This form is
deliberately stated for any current source no longer than the interval before
the splay, so it applies both before phase one and after phase-one losers have
been removed. -/
theorem ArticleInternalPairingFractionCertificate.sourceLength_le_ten_mul_matchingLength
    {n lower upper key sourceLength : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {kinds : List SplayStepKind}
    {elements bottomUp : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements bottomUp)
    (batches : ArticleRetainedPairingBatches snapshot before upper_le_n key
      certificate.fraction.groups)
    {phase : PairingPhase} {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement phase batches matching)
    (sourceLength_le : sourceLength ≤ elements.length)
    (matching_nonempty : matching ≠ []) :
    sourceLength ≤ 10 * matching.length := by
  have matching_length :
      matching.length = certificate.fraction.groups.length :=
    agreement.matching_length_eq_eligibleGroups_length
  have matching_positive : 1 ≤ matching.length := by
    cases matching with
    | nil => exact False.elim (matching_nonempty rfl)
    | cons pairing tail => simp
  have interval_bound := certificate.fraction.length_bound
  simp only [List.length_reverse] at interval_bound
  rw [← matching_length] at interval_bound
  omega

/-- Division-free adapter from the article's one-tenth bound to the abstract
interface's configurable matching fraction. -/
theorem ArticleInternalPairingFractionCertificate.matchingFraction_of_nonempty
    {n lower upper key sourceLength : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {kinds : List SplayStepKind}
    {elements bottomUp : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements bottomUp)
    (batches : ArticleRetainedPairingBatches snapshot before upper_le_n key
      certificate.fraction.groups)
    {phase : PairingPhase} {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement phase batches matching)
    {params : Interface.Parameters}
    (article_fraction :
      10 * params.matchingNumerator ≤ params.matchingDenominator)
    (sourceLength_le : sourceLength ≤ elements.length)
    (matching_nonempty : matching ≠ []) :
    params.matchingNumerator * sourceLength ≤
      params.matchingDenominator * matching.length := by
  have source_bound :=
    certificate.sourceLength_le_ten_mul_matchingLength batches agreement
      sourceLength_le matching_nonempty
  calc
    params.matchingNumerator * sourceLength ≤
        params.matchingNumerator * (10 * matching.length) :=
      Nat.mul_le_mul_left _ source_bound
    _ = (10 * params.matchingNumerator) * matching.length := by
      simp only [Nat.mul_assoc, Nat.mul_comm]
    _ ≤ params.matchingDenominator * matching.length :=
      Nat.mul_le_mul_right matching.length article_fraction

/--
The concrete destination choices for one article phase.

The endpoint rows determine only winners and losers.  A stable rich state has
one growing block at every owner-side placement; this record stores the
matching obtained by choosing the block on the loser's side of each winner.
Distinct winners force distinct block identifiers, so destination
duplicate-freeness is a theorem rather than an additional scheduler input.
-/
structure ArticleBatchDestinationAllocation
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ}
    (phase : PairingPhase)
    (batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups)
    (state : Lazy.State n) where
  matching : List (Interface.Pairing n)
  agreement : ArticleBatchEndpointAgreement phase batches matching
  destinationsNodup :
    (matching.map fun pairing => pairing.destination).Nodup
  destinations : ∀ pairing ∈ matching,
    ∃ destination,
      state.toInterface.block? pairing.destination = some destination ∧
        destination.mode = .growing ∧
        destination.creator = pairing.winner
  richDestinations : ∀ pairing ∈ matching,
    ∃ destination : Lazy.Block n,
      state.blocks[pairing.destination]? = some destination ∧
        destination.mode = .growing ∧
        destination.owner = pairing.winner ∧
        destination.side =
          Splay.Lazy.Canonical.sideOf pairing.winner pairing.loser

private theorem exists_matching_with_growing_destinations_of_rows
    {n : ℕ} {params : Interface.Parameters}
    {state : Lazy.State n} (valid : state.Valid params)
    (oneGrowing : state.OneGrowingPerSide)
    (select :
      (ℕ × (List (Interface.Element n) × List (Interface.Element n))) →
        List (Interface.Element n))
    (rows : List
      (ℕ × (List (Interface.Element n) × List (Interface.Element n))))
    (rowPair : ∀ row ∈ rows,
      ∃ winner loser, select row = [winner, loser]) :
    ∃ matching : List (Interface.Pairing n),
      List.Forall₂
        (fun row pairing =>
          select row = [pairing.winner, pairing.loser])
        rows matching ∧
      (∀ pairing ∈ matching,
        ∃ destination,
          state.toInterface.block? pairing.destination = some destination ∧
            destination.mode = .growing ∧
            destination.creator = pairing.winner) ∧
      ∀ pairing ∈ matching,
        ∃ destination : Lazy.Block n,
          state.blocks[pairing.destination]? = some destination ∧
            destination.mode = .growing ∧
            destination.owner = pairing.winner ∧
            destination.side =
              Splay.Lazy.Canonical.sideOf pairing.winner pairing.loser := by
  induction rows with
  | nil =>
      exact ⟨[], .nil, by simp, by simp⟩
  | cons row rows ih =>
      obtain ⟨winner, loser, selected⟩ := rowPair row (by simp)
      have tailPair : ∀ tailRow ∈ rows,
          ∃ winner loser, select tailRow = [winner, loser] := by
        intro tailRow member
        exact rowPair tailRow (by simp [member])
      obtain ⟨tailMatching, tailAgreement, tailDestinations,
          tailRichDestinations⟩ :=
        ih tailPair
      let childSide := Splay.Lazy.Canonical.sideOf winner loser
      obtain ⟨destinationId, destinationProperty, _destinationUnique⟩ :=
        oneGrowing winner childSide
      let destinationBlock := state.blocks.get destinationId
      have destinationMember : destinationBlock ∈ state.blocks :=
        List.get_mem state.blocks destinationId
      have destinationStructural :
          destinationBlock.StructurallyValid state.view state.allElements :=
        valid.2 destinationBlock destinationMember
      have destinationMode : destinationBlock.mode = .growing :=
        destinationProperty.1
      have destinationOwner : destinationBlock.owner = winner :=
        destinationProperty.2.1
      have destinationCreator : destinationBlock.creator = winner := by
        exact
          (destinationStructural.owner_eq_creator_of_growing
            destinationMode).symm.trans destinationOwner
      have destinationFound :
          state.toInterface.block? destinationId.val =
            some destinationBlock.toInterface := by
        unfold Interface.State.block? Lazy.State.toInterface
        simp [destinationBlock, List.get_eq_getElem]
      have richDestinationFound :
          state.blocks[destinationId.val]? = some destinationBlock := by
        simp [destinationBlock, List.get_eq_getElem]
      let pairing : Interface.Pairing n := {
        winner := winner
        loser := loser
        destination := destinationId.val
      }
      refine ⟨pairing :: tailMatching, ?_, ?_, ?_⟩
      · apply List.Forall₂.cons
        · simpa only [pairing] using selected
        · exact tailAgreement
      · intro candidate member
        simp only [List.mem_cons] at member
        rcases member with rfl | tailMember
        · exact
            ⟨destinationBlock.toInterface, destinationFound, destinationMode,
              destinationCreator⟩
        · exact tailDestinations candidate tailMember
      · intro candidate member
        simp only [List.mem_cons] at member
        rcases member with rfl | tailMember
        · exact ⟨destinationBlock, richDestinationFound, destinationMode,
            destinationOwner, destinationProperty.2.2⟩
        · exact tailRichDestinations candidate tailMember

private theorem destinations_nodup_of_endpoints_nodup
    {n : ℕ} {state : Lazy.State n}
    (matching : List (Interface.Pairing n))
    (endpointsNodup :
      (matching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]).Nodup)
    (destinations : ∀ pairing ∈ matching,
      ∃ destination,
        state.toInterface.block? pairing.destination = some destination ∧
          destination.mode = .growing ∧
          destination.creator = pairing.winner) :
    (matching.map fun pairing => pairing.destination).Nodup := by
  induction matching with
  | nil => simp
  | cons pairing matching ih =>
      have expanded :
          ([pairing.winner, pairing.loser] ++
            (matching.flatMap fun tail =>
              [tail.winner, tail.loser])).Nodup := by
        simpa only [List.flatMap_cons] using endpointsNodup
      have appendFacts := List.nodup_append.mp expanded
      have tailEndpointsNodup :
          (matching.flatMap fun tail =>
            [tail.winner, tail.loser]).Nodup :=
        appendFacts.2.1
      have tailDestinations : ∀ tail ∈ matching,
          ∃ destination,
            state.toInterface.block? tail.destination = some destination ∧
              destination.mode = .growing ∧
              destination.creator = tail.winner := by
        intro tail member
        exact destinations tail (by simp [member])
      have tailNodup := ih tailEndpointsNodup tailDestinations
      apply List.nodup_cons.mpr
      constructor
      · intro destinationMember
        obtain ⟨tail, tailMember, destinationEq⟩ :=
          List.mem_map.mp destinationMember
        obtain ⟨headBlock, headFound, _headGrowing, headCreator⟩ :=
          destinations pairing (by simp)
        obtain ⟨tailBlock, tailFound, _tailGrowing, tailCreator⟩ :=
          tailDestinations tail tailMember
        have destinationEq' : tail.destination = pairing.destination :=
          destinationEq
        rw [destinationEq'] at tailFound
        rw [headFound] at tailFound
        have blockEq : tailBlock = headBlock :=
          Option.some.inj tailFound.symm
        have winnerEq : tail.winner = pairing.winner := by
          rw [← tailCreator, blockEq, headCreator]
        have tailWinnerMember :
            tail.winner ∈
              matching.flatMap fun item => [item.winner, item.loser] :=
          List.mem_flatMap.mpr ⟨tail, tailMember, by simp⟩
        have headWinnerMember :
            pairing.winner ∈ [pairing.winner, pairing.loser] := by simp
        exact (appendFacts.2.2 pairing.winner headWinnerMember
          tail.winner (by
            simpa only [winnerEq] using tailWinnerMember)) winnerEq.symm
      · exact tailNodup

/--
Every retained article batch has a canonical allocation to the existing
growing blocks of a stable rich state.  No destination list is supplied by
the caller.
-/
theorem ArticleRetainedPairingBatches.exists_destinationAllocation
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ}
    (phase : PairingPhase)
    (batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups)
    {params : Interface.Parameters} (state : Lazy.State n)
    (valid : state.Valid params)
    (oneGrowing : state.OneGrowingPerSide) :
    Nonempty (ArticleBatchDestinationAllocation phase batches state) := by
  have rowPair : ∀ row ∈ batches.rows,
      ∃ winner loser,
        articleRowSelection phase row = [winner, loser] := by
    intro row rowMember
    obtain ⟨extra, winner, firstLoser, secondLoser, candidates,
        firstEq, secondEq, chunkEq, candidatesLength, firstAdjacent,
        secondAdjacent, losersNe, candidatesPerm, _firstRankLt,
        _secondRankLt⟩ :=
      batches.aligned row rowMember
    cases phase with
    | first => exact ⟨winner, firstLoser, firstEq⟩
    | second => exact ⟨winner, secondLoser, secondEq⟩
  obtain ⟨matching, agreement, destinations, richDestinations⟩ :=
    exists_matching_with_growing_destinations_of_rows
      valid oneGrowing (articleRowSelection phase) batches.rows rowPair
  have endpointsNodup :
      (matching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]).Nodup := by
    rw [ArticleBatchEndpointAgreement.matchingEndpoints_eq_rows agreement]
    cases phase with
    | first => simpa [articleRowSelection] using batches.firstEndpoints_nodup
    | second => simpa [articleRowSelection] using batches.secondEndpoints_nodup
  exact
    ⟨{
      matching := matching
      agreement := agreement
      destinationsNodup :=
        destinations_nodup_of_endpoints_nodup
          matching endpointsNodup destinations
      destinations := destinations
      richDestinations := richDestinations
    }⟩

namespace ArticleBatchDestinationAllocation

/-- Destination allocation depends only on the block list.  Value-only
preparation/restoration therefore preserves the same concrete allocation. -/
noncomputable def transport_blocks_eq
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ} {phase : PairingPhase}
    {batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups}
    {state next : Lazy.State n}
    (allocation : ArticleBatchDestinationAllocation phase batches state)
    (blocksEq : next.blocks = state.blocks) :
    ArticleBatchDestinationAllocation phase batches next := by
  refine {
    matching := allocation.matching
    agreement := allocation.agreement
    destinationsNodup := allocation.destinationsNodup
    destinations := ?_
    richDestinations := ?_
  }
  · intro pairing pairingMember
    obtain ⟨destination, found, growing, creator⟩ :=
      allocation.destinations pairing pairingMember
    refine ⟨destination, ?_, growing, creator⟩
    unfold Interface.State.block? Lazy.State.toInterface at found ⊢
    simpa only [blocksEq] using found
  · intro pairing pairingMember
    obtain ⟨destination, found, growing, owner, side⟩ :=
      allocation.richDestinations pairing pairingMember
    exact ⟨destination, by simpa only [blocksEq] using found,
      growing, owner, side⟩

/-- Heap-view update attached to one concrete article pairing. -/
noncomputable def pairingReparentInstruction {n : ℕ}
    (pairing : Interface.Pairing n) :
    HeapView.ReparentInstruction n where
  winner := pairing.winner
  loser := pairing.loser
  side := Splay.Lazy.Canonical.sideOf pairing.winner pairing.loser

/-- Exact heap-view endpoint of one simultaneous article pairing batch. -/
structure BatchReparentedView {n : ℕ} (beforeView : HeapView n)
    (matching : List (Interface.Pairing n)) where
  view : HeapView n
  rank_eq : view.rank = beforeView.rank
  root_eq : view.root = beforeView.root
  ordered : view.HeapOrdered
  paired_parent : ∀ pairing ∈ matching,
    view.parent pairing.loser = some pairing.winner
  paired_side : ∀ pairing ∈ matching,
    view.side pairing.loser =
      Splay.Lazy.Canonical.sideOf pairing.winner pairing.loser
  unpaired_parent : ∀ element,
    (∀ pairing ∈ matching, element ≠ pairing.loser) →
      view.parent element = beforeView.parent element
  unpaired_side : ∀ element,
    (∀ pairing ∈ matching, element ≠ pairing.loser) →
      view.side element = beforeView.side element

private theorem oneGrowingPerSide_modify_of_preservesPlacement
    {n : ℕ} {state : Lazy.State n}
    (oneGrowing : state.OneGrowingPerSide)
    (index : ℕ) (update : Lazy.Block n → Lazy.Block n)
    (preserves : ∀ block owner childSide,
      (update block).mode = .growing ∧
            (update block).owner = owner ∧
              (update block).side = childSide ↔
        block.mode = .growing ∧ block.owner = owner ∧
          block.side = childSide) :
    ({state with blocks := state.blocks.modify index update})
      |>.OneGrowingPerSide := by
  intro owner childSide
  obtain ⟨oldId, oldProperty, oldUnique⟩ := oneGrowing owner childSide
  let newId : Fin (state.blocks.modify index update).length :=
    ⟨oldId.val, by simp⟩
  have newProperty :
      let block := (state.blocks.modify index update).get newId
      block.mode = .growing ∧ block.owner = owner ∧
        block.side = childSide := by
    change
      ((state.blocks.modify index update).get newId).mode = .growing ∧
        ((state.blocks.modify index update).get newId).owner = owner ∧
          ((state.blocks.modify index update).get newId).side = childSide
    rw [List.get_eq_getElem, List.getElem_modify]
    split
    next selected =>
      apply (preserves state.blocks[oldId.val] owner childSide).mpr
      simpa [List.get_eq_getElem] using oldProperty
    next notSelected =>
      simpa [newId, List.get_eq_getElem] using oldProperty
  refine ⟨newId, newProperty, ?_⟩
  intro candidate candidateProperty
  let oldCandidate : Fin state.blocks.length :=
    ⟨candidate.val, by simpa using candidate.isLt⟩
  have oldCandidateProperty :
      let block := state.blocks.get oldCandidate
      block.mode = .growing ∧ block.owner = owner ∧
        block.side = childSide := by
    change
      (state.blocks.get oldCandidate).mode = .growing ∧
        (state.blocks.get oldCandidate).owner = owner ∧
          (state.blocks.get oldCandidate).side = childSide
    change
      ((state.blocks.modify index update).get candidate).mode = .growing ∧
        ((state.blocks.modify index update).get candidate).owner = owner ∧
          ((state.blocks.modify index update).get candidate).side = childSide
      at candidateProperty
    rw [List.get_eq_getElem, List.getElem_modify] at candidateProperty
    split at candidateProperty
    next selected =>
      exact (preserves state.blocks[candidate.val] owner childSide).mp
        candidateProperty
    next notSelected =>
      simpa [oldCandidate, List.get_eq_getElem] using candidateProperty
  have oldEq := oldUnique oldCandidate oldCandidateProperty
  apply Fin.ext
  simpa [newId, oldCandidate] using congrArg Fin.val oldEq

private theorem oneGrowingPerSide_insertAtDestinations
    {n : ℕ} {state : Lazy.State n}
    (oneGrowing : state.OneGrowingPerSide)
    (matching : List (Interface.Pairing n)) :
    ({state with blocks :=
        Lazy.Block.insertAtDestinations state.blocks matching})
      |>.OneGrowingPerSide := by
  induction matching generalizing state with
  | nil => simpa [Lazy.Block.insertAtDestinations] using oneGrowing
  | cons pairing matching ih =>
      let next : Lazy.State n :=
        {state with blocks := (state.blocks.modify pairing.destination
          (fun destination => destination.inserted pairing.loser))}
      have nextOneGrowing : next.OneGrowingPerSide := by
        apply oneGrowingPerSide_modify_of_preservesPlacement oneGrowing
        intro block owner childSide
        simp [Lazy.Block.inserted]
      simpa [Lazy.Block.insertAtDestinations, next] using
        ih (state := next) nextOneGrowing

/-- A rich pass preserves the unique growing block at every owner-side.
It changes only payloads and the shrinking source's pass counter. -/
theorem State.OneGrowingPerSide.passAtView
    {n : ℕ} {state : Lazy.State n}
    (oneGrowing : state.OneGrowingPerSide)
    (afterView : Lazy.HeapView n) (sourceId : Interface.BlockId)
    (source : Lazy.Block n) (matching : List (Interface.Pairing n))
    (sourceIntervalGap : ℤ)
    (sourceFound : state.blocks[sourceId]? = some source) :
    (state.passAtView afterView sourceId source matching sourceIntervalGap)
      |>.OneGrowingPerSide := by
  let sourceUpdated : Lazy.State n :=
    {state with blocks := state.blocks.modify sourceId fun block =>
      block.afterPassSource matching sourceIntervalGap}
  have sourceUpdatedOneGrowing : sourceUpdated.OneGrowingPerSide := by
    apply oneGrowingPerSide_modify_of_preservesPlacement oneGrowing
    intro block owner childSide
    simp [Lazy.Block.afterPassSource]
  have sourceModifyEq :
      state.blocks.modify sourceId (fun _ =>
          source.afterPassSource matching sourceIntervalGap) =
        state.blocks.modify sourceId (fun block =>
          block.afterPassSource matching sourceIntervalGap) := by
    rw [List.modify_eq_set_getElem?, List.modify_eq_set_getElem?, sourceFound]
    rfl
  have inserted := oneGrowingPerSide_insertAtDestinations
    sourceUpdatedOneGrowing matching
  change
    ({state with blocks := (Lazy.Block.passBlocks state.blocks sourceId source
      matching sourceIntervalGap)}).OneGrowingPerSide
  simpa [Lazy.Block.passBlocks, sourceUpdated, sourceModifyEq] using inserted

/-- Reparenting a pass batch preserves completeness: legal pass blocks
permute the assigned payloads, and the batch keeps the same heap root. -/
theorem BatchReparentedView.complete_after_pass
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    {matching : List (Interface.Pairing n)}
    (after : BatchReparentedView state.view matching)
    (complete : state.Complete)
    (sourceFound : state.blocks[sourceId]? = some source)
    (matchingValid : Interface.MatchingValid params state.toInterface
      sourceId source.toInterface matching)
    (sourceIntervalGap : ℤ) :
    (state.passAtView after.view sourceId source matching sourceIntervalGap)
      |>.Complete := by
  let passed := state.passAtView after.view sourceId source matching
    sourceIntervalGap
  have assignedPerm : passed.allElements.Perm state.allElements :=
    State.passAtView_allElements_perm_of_matching state after.view sourceId
      source matching sourceIntervalGap sourceFound matchingValid
  intro element
  rw [assignedPerm.mem_iff, complete element]
  constructor
  · intro beforeParent
    apply after.view.parent_ne_none_of_ne_root
    intro elementRoot
    have beforeRoot : element = state.view.root :=
      elementRoot.trans after.root_eq
    apply beforeParent
    rw [beforeRoot]
    exact state.view.root_parent
  · intro afterParent
    apply state.view.parent_ne_none_of_ne_root
    intro elementRoot
    have afterRoot : element = after.view.root :=
      elementRoot.trans after.root_eq.symm
    apply afterParent
    change after.view.parent element = none
    rw [afterRoot]
    exact after.view.root_parent

/-- The exact geometric sentence used by the article for an internal
pairing: on the side toward the loser, that loser becomes the new top-most
heap child of the winner.  All other parent changes are already fixed by
`BatchReparentedView`. -/
def BatchTopmostGeometry {n : ℕ} {beforeView : HeapView n}
    {matching : List (Interface.Pairing n)}
    (after : BatchReparentedView beforeView matching) : Prop :=
  ∀ pairing ∈ matching,
    after.view.topDown pairing.winner
        (Splay.Lazy.Canonical.sideOf pairing.winner pairing.loser) =
      pairing.loser :: beforeView.topDown pairing.winner
        (Splay.Lazy.Canonical.sideOf pairing.winner pairing.loser)

/-- Order-theoretic core of the same article claim.  The loser lies before
every old child of the winner on its side in the canonical full-order list.
For a BST-derived heap this is the local nesting fact supplied by the
zig-zig endpoint geometry. -/
def BatchOutermostOrder {n : ℕ} (beforeView : HeapView n)
    (matching : List (Interface.Pairing n)) : Prop :=
  ∀ pairing ∈ matching, ∀ child ∈ beforeView.topDown pairing.winner
      (Splay.Lazy.Canonical.sideOf pairing.winner pairing.loser),
    match Splay.Lazy.Canonical.sideOf pairing.winner pairing.loser with
    | .left => pairing.loser.val < child.val
    | .right => child.val < pairing.loser.val

/-- BST-laminar heap geometry supplies the batch outermost inequalities
directly: every pairing endpoint is a sibling in the shrinking source, and
every queried old destination child is one level below the winner. -/
theorem outermostOrder_of_nestedChildOrder
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    {matching : List (Interface.Pairing n)}
    (valid : state.Valid params)
    (sourceFound : state.blocks[sourceId]? = some source)
    (geometric : GeometricMatchingValid state sourceId source matching)
    (nested : state.view.NestedChildOrder) :
    BatchOutermostOrder state.view matching := by
  have sourceStructural := valid.2 source (List.mem_of_getElem? sourceFound)
  intro pairing pairingMember child childMember
  have endpoints := geometric.2.2.2 pairing pairingMember
  have winnerParent := sourceStructural.parent_eq endpoints.1.first_mem
  have loserParent := sourceStructural.parent_eq endpoints.1.second_mem
  have childFacts := state.view.mem_topDown_iff.mp childMember
  have winnerNeLoser : pairing.winner ≠ pairing.loser := by
    obtain ⟨front, back, matchingEq⟩ := List.mem_iff_append.mp pairingMember
    have endpointsNodup := geometric.2.1
    rw [matchingEq, List.flatMap_append, List.flatMap_cons] at endpointsNodup
    simp only [List.flatMap_append, List.nodup_append,
      List.nodup_cons, List.mem_cons, List.mem_append,
      List.mem_singleton, not_or] at endpointsNodup
    exact endpointsNodup.2.1.1.1.1
  by_cases left : pairing.loser.val < pairing.winner.val
  · have result := nested winnerParent loserParent winnerNeLoser childFacts.1 (by
      simpa [Splay.Lazy.Canonical.sideOf, left] using childFacts.2)
    simpa [Splay.Lazy.Canonical.sideOf, left] using result
  · have result := nested winnerParent loserParent winnerNeLoser childFacts.1 (by
      simpa [Splay.Lazy.Canonical.sideOf, left] using childFacts.2)
    simpa [Splay.Lazy.Canonical.sideOf, left] using result

/-- Canonical laminarity also supplies the outermost inequalities for the
second-phase endpoints before the first phase runs.  They need not yet be
adjacent; only their common source parent is used here. -/
theorem articleSecondOutermostOrder_of_nestedChildOrder
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate : ArticleInternalPairingFractionCertificate kinds elements
      (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (valid : state.Valid params)
    (nested : state.view.NestedChildOrder)
    (secondAllocation :
      ArticleBatchDestinationAllocation .second batches state) :
    BatchOutermostOrder state.view secondAllocation.matching := by
  have sourceStructural := valid.2 source (List.mem_of_getElem? sourceFound)
  intro selected selectedMember child childMember
  obtain ⟨row, rowMember, selectedRowEq⟩ :=
    secondAllocation.agreement.exists_row_of_mem selectedMember
  obtain ⟨winner, firstLoser, secondLoser, candidates, firstEq,
      secondEq, firstAdjacent, secondAdjacent, losersNe, candidatePerm,
      candidateChunk, candidateSegment, firstInBlock, secondInBlock,
      winnerInside, firstInside, secondInside⟩ :=
    certificate.retainedRow_inside batches rowMember
  have selectedPairEq : [winner, secondLoser] =
      [selected.winner, selected.loser] :=
    secondEq.symm.trans selectedRowEq
  have selectedEndpoints : winner = selected.winner ∧
      secondLoser = selected.loser := by
    simpa using selectedPairEq
  have winnerMember : selected.winner ∈ source.elements := by
    simpa [sourceElements, selectedEndpoints.1] using winnerInside
  have loserMember : selected.loser ∈ source.elements := by
    simpa [sourceElements, selectedEndpoints.2] using secondInside
  have winnerParent := sourceStructural.parent_eq winnerMember
  have loserParent := sourceStructural.parent_eq loserMember
  have childFacts := state.view.mem_topDown_iff.mp childMember
  have winnerNeLoser : selected.winner ≠ selected.loser := by
    intro equal
    have rankOrder := secondAllocation.agreement.rank_lt selectedMember
    rw [equal] at rankOrder
    exact Nat.lt_irrefl _ rankOrder
  have result := nested winnerParent loserParent winnerNeLoser childFacts.1
    (by simpa [Splay.Lazy.Canonical.sideOf] using childFacts.2)
  by_cases left : selected.loser.val < selected.winner.val
  · simpa [Splay.Lazy.Canonical.sideOf, left] using result
  · simpa [Splay.Lazy.Canonical.sideOf, left] using result

namespace BatchReparentedView

/-- The article's sequential second pair is outermost after the first batch.

Old winner-children are handled by canonical BST laminarity.  The only new
winner-child can be that row's first loser; adjacency in the source's ordered
full-order segment says that the second loser is farther out whenever both
losers are on the same side. -/
theorem secondOutermostOrder_after_first
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ}
    {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches)
    {params : Interface.Parameters} {state secondState : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (valid : state.Valid params)
    (firstAllocation :
      ArticleBatchDestinationAllocation .first batches state)
    (firstGeometric : GeometricMatchingValid state sourceId source
      firstAllocation.matching)
    (afterFirst : BatchReparentedView state.view firstAllocation.matching)
    (secondAllocation :
      ArticleBatchDestinationAllocation .second batches secondState)
    (secondBaseOutermost :
      BatchOutermostOrder state.view secondAllocation.matching) :
    BatchOutermostOrder afterFirst.view secondAllocation.matching := by
  have sourceStructural := valid.2 source (List.mem_of_getElem? sourceFound)
  have firstWinnersNodup := pairingWinners_nodup firstGeometric.2.1
  have firstWinnerInjective :=
    List.inj_on_of_nodup_map firstWinnersNodup
  intro selected selectedMember child childMember
  have childFacts := afterFirst.view.mem_topDown_iff.mp childMember
  obtain ⟨row, rowMember, selectedRowEq⟩ :=
    secondAllocation.agreement.exists_row_of_mem selectedMember
  obtain ⟨winner, firstLoser, secondLoser, candidates, firstEq,
      secondEq, firstAdjacent, secondAdjacent, losersNe, candidatePerm,
      candidateChunk, candidateSegment, firstInBlock, secondInBlock,
      winnerInside, firstInside, secondInside⟩ :=
    plan.row_inside rowMember
  have selectedPairEq : [winner, secondLoser] =
      [selected.winner, selected.loser] := by
    exact secondEq.symm.trans selectedRowEq
  have selectedEndpoints : winner = selected.winner ∧
      secondLoser = selected.loser := by
    simpa using selectedPairEq
  have winnerMember : selected.winner ∈ source.elements := by
    simpa [sourceElements, selectedEndpoints.1] using winnerInside
  have secondMember : selected.loser ∈ source.elements := by
    simpa [sourceElements, selectedEndpoints.2] using secondInside
  have winnerParent := sourceStructural.parent_eq winnerMember
  have secondParent := sourceStructural.parent_eq secondMember
  have winnerNeSecond : selected.winner ≠ selected.loser := by
    intro equal
    have rankOrder := secondAllocation.agreement.rank_lt selectedMember
    rw [equal] at rankOrder
    exact Nat.lt_irrefl _ rankOrder
  by_cases moved : child ∈
      Interface.pairingLosers firstAllocation.matching
  · obtain ⟨movedPairing, movedMember, movedEq⟩ :=
      List.mem_map.mp (by
        simpa only [Interface.pairingLosers] using moved)
    obtain ⟨rowPairing, rowPairingMember, rowPairingEq⟩ :=
      forall₂_exists_right_of_mem_left firstAllocation.agreement rowMember
    have rowFirstPairEq : [winner, firstLoser] =
        [rowPairing.winner, rowPairing.loser] := by
      exact firstEq.symm.trans rowPairingEq
    have rowFirstEndpoints : winner = rowPairing.winner ∧
        firstLoser = rowPairing.loser := by
      simpa using rowFirstPairEq
    have movedParent := afterFirst.paired_parent movedPairing movedMember
    rw [movedEq] at movedParent
    have movedWinnerEq : movedPairing.winner = selected.winner :=
      Option.some.inj (movedParent.symm.trans childFacts.1)
    have rowWinnerEq : rowPairing.winner = selected.winner := by
      rw [← rowFirstEndpoints.1, selectedEndpoints.1]
    have pairingEq : movedPairing = rowPairing :=
      firstWinnerInjective movedMember rowPairingMember
        (movedWinnerEq.trans rowWinnerEq.symm)
    subst movedPairing
    have childEq : child = firstLoser := by
      exact movedEq.symm.trans rowFirstEndpoints.2.symm
    have childSideEq : afterFirst.view.side firstLoser =
        Splay.Lazy.Canonical.sideOf selected.winner selected.loser := by
      rw [← childEq]
      exact childFacts.2
    have sameSide :
        Splay.Lazy.Canonical.sideOf selected.winner firstLoser =
          Splay.Lazy.Canonical.sideOf selected.winner selected.loser := by
      have pairedSide :=
        afterFirst.paired_side rowPairing rowPairingMember
      have normalizedPairSide : afterFirst.view.side firstLoser =
          Splay.Lazy.Canonical.sideOf selected.winner firstLoser := by
        simpa only [← rowFirstEndpoints.2, rowWinnerEq] using pairedSide
      exact normalizedPairSide.symm.trans childSideEq
    have firstMember : firstLoser ∈ source.elements := by
      simpa [sourceElements] using firstInside
    have winnerNeFirst : selected.winner ≠ firstLoser := by
      intro equal
      have rankOrder :=
        firstAllocation.agreement.rank_lt rowPairingMember
      rw [← rowFirstEndpoints.1, ← rowFirstEndpoints.2,
        selectedEndpoints.1, equal] at rankOrder
      exact Nat.lt_irrefl _ rankOrder
    have firstAdjacentSource : Interface.Adjacent source.elements
        selected.winner firstLoser := by
      simpa [sourceElements, selectedEndpoints.1] using firstInBlock
    cases sourceSide : source.side with
    | left =>
        have attachedOrdered :
            (state.view.attachedTopDown state.allElements source.owner .left).Pairwise
              (fun earlier later => earlier.val < later.val) := by
          change ((state.view.topDown source.owner .left).filter _).Pairwise _
          exact (state.view.topDown_ordered source.owner).1.filter _
        have sourceOrdered : source.elements.Pairwise
            (fun earlier later => earlier.val < later.val) :=
          List.Pairwise.sublist
            (Splay.Lazy.Canonical.IsSegment.sublist sourceStructural.isSegment)
            (by simpa [sourceSide] using attachedOrdered)
        have result := outer_of_adjacent_of_pairwise_lt sourceOrdered
          firstAdjacentSource (by simpa [sourceElements, selectedEndpoints.2] using
            secondInside) winnerNeFirst winnerNeSecond
          (by simpa [selectedEndpoints.2] using losersNe) (by
            simpa [selectedEndpoints.1, selectedEndpoints.2] using sameSide)
        by_cases left : selected.loser.val < selected.winner.val
        · simpa [childEq, selectedEndpoints.2,
            Splay.Lazy.Canonical.sideOf, left] using result
        · simpa [childEq, selectedEndpoints.2,
            Splay.Lazy.Canonical.sideOf, left] using result
    | right =>
        have attachedOrdered :
            (state.view.attachedTopDown state.allElements source.owner .right).Pairwise
              (fun earlier later => later.val < earlier.val) := by
          change ((state.view.topDown source.owner .right).filter _).Pairwise _
          exact (state.view.topDown_ordered source.owner).2.filter _
        have sourceOrdered : source.elements.Pairwise
            (fun earlier later => later.val < earlier.val) :=
          List.Pairwise.sublist
            (Splay.Lazy.Canonical.IsSegment.sublist sourceStructural.isSegment)
            (by simpa [sourceSide] using attachedOrdered)
        have result := outer_of_adjacent_of_pairwise_gt sourceOrdered
          firstAdjacentSource (by simpa [sourceElements, selectedEndpoints.2] using
            secondInside) winnerNeFirst winnerNeSecond
          (by simpa [selectedEndpoints.2] using losersNe) (by
            simpa [selectedEndpoints.1, selectedEndpoints.2] using sameSide)
        by_cases left : selected.loser.val < selected.winner.val
        · simpa [childEq, selectedEndpoints.2,
            Splay.Lazy.Canonical.sideOf, left] using result
        · simpa [childEq, selectedEndpoints.2,
            Splay.Lazy.Canonical.sideOf, left] using result
  · have notMoved : ∀ pairing ∈ firstAllocation.matching,
        child ≠ pairing.loser := by
      intro pairing pairingMember equal
      apply moved
      exact List.mem_map.mpr ⟨pairing, pairingMember, equal.symm⟩
    have originalChildParent :
        state.view.parent child = some selected.winner :=
      (afterFirst.unpaired_parent child notMoved).symm.trans childFacts.1
    have originalChildSide : state.view.side child =
        (if selected.loser.val < selected.winner.val then
          Side.left else Side.right) := by
      have sideEq :=
        (afterFirst.unpaired_side child notMoved).symm.trans childFacts.2
      simpa [Splay.Lazy.Canonical.sideOf] using sideEq
    have originalChildMember :
        child ∈ state.view.topDown selected.winner
          (Splay.Lazy.Canonical.sideOf selected.winner selected.loser) := by
      apply state.view.mem_topDown_iff.mpr
      exact ⟨originalChildParent, by
        simpa [Splay.Lazy.Canonical.sideOf] using originalChildSide⟩
    exact secondBaseOutermost selected selectedMember child originalChildMember

/-- Reparenting an earlier batch preserves the outermost inequalities of a
later batch whenever the two batches use different winners.  Indeed, the
only elements whose parent or side changes are the earlier losers, and such
a loser can become a child only of its earlier winner.  Hence every child of
a later winner in the new view was already there in the old view. -/
theorem outermostOrder_after_of_winners_ne
    {n : ℕ} {beforeView : HeapView n}
    {earlier later : List (Interface.Pairing n)}
    (after : BatchReparentedView beforeView earlier)
    (base : BatchOutermostOrder beforeView later)
    (winnersNe : ∀ earlierPairing ∈ earlier,
      ∀ laterPairing ∈ later,
        earlierPairing.winner ≠ laterPairing.winner) :
    BatchOutermostOrder after.view later := by
  intro selected selectedMember child childMember
  have childFacts := after.view.mem_topDown_iff.mp childMember
  have childNotEarlierLoser : ∀ pairing ∈ earlier,
      child ≠ pairing.loser := by
    intro pairing pairingMember equal
    subst child
    have parentEq := after.paired_parent pairing pairingMember
    have winnerEq : pairing.winner = selected.winner :=
      Option.some.inj (parentEq.symm.trans childFacts.1)
    exact winnersNe pairing pairingMember selected selectedMember winnerEq
  have beforeMember : child ∈ beforeView.topDown selected.winner
      (Splay.Lazy.Canonical.sideOf selected.winner selected.loser) := by
    apply beforeView.mem_topDown_iff.mpr
    exact ⟨(after.unpaired_parent child childNotEarlierLoser).symm.trans
        childFacts.1,
      (after.unpaired_side child childNotEarlierLoser).symm.trans
        childFacts.2⟩
  exact base selected selectedMember child beforeMember

/-- The new signed gap of a paired loser is exactly the winner/loser rank
difference used in the manuscript's internal-pairing calculation. -/
theorem paired_rawGap {n : ℕ} {beforeView : HeapView n}
    {matching : List (Interface.Pairing n)}
    (after : BatchReparentedView beforeView matching)
    {pairing : Interface.Pairing n} (member : pairing ∈ matching) :
    after.view.rawGap pairing.loser =
      (beforeView.rank pairing.loser : ℤ) - beforeView.rank pairing.winner := by
  simp [HeapView.rawGap, after.paired_parent pairing member, after.rank_eq]

/-- Every non-loser keeps its exact signed raw gap. -/
theorem unpaired_rawGap {n : ℕ} {beforeView : HeapView n}
    {matching : List (Interface.Pairing n)}
    (after : BatchReparentedView beforeView matching)
    {element : Element n}
    (notLoser : ∀ pairing ∈ matching, element ≠ pairing.loser) :
    after.view.rawGap element = beforeView.rawGap element := by
  simp [HeapView.rawGap, after.unpaired_parent element notLoser,
    after.rank_eq]

/-- Every batch loser was assigned to the common shrinking source before the
pass. -/
theorem loser_mem_source {n : ℕ} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    {matching : List (Interface.Pairing n)}
    (geometric : GeometricMatchingValid state sourceId source matching)
    {pairing : Interface.Pairing n} (member : pairing ∈ matching) :
    pairing.loser ∈ source.elements :=
  (geometric.2.2.2 pairing member).1.second_mem

/-- No winner in an internal source block can equal that block's heap
owner: the winner itself is one of the owner's proper heap children. -/
theorem winner_ne_sourceOwner
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    {matching : List (Interface.Pairing n)}
    (valid : state.Valid params)
    (sourceFound : state.blocks[sourceId]? = some source)
    (geometric : GeometricMatchingValid state sourceId source matching)
    {pairing : Interface.Pairing n} (member : pairing ∈ matching) :
    pairing.winner ≠ source.owner := by
  intro equal
  have sourceStructural := valid.2 source (List.mem_of_getElem? sourceFound)
  have winnerMember :=
    (geometric.2.2.2 pairing member).1.first_mem
  have winnerParent := sourceStructural.parent_eq winnerMember
  rw [equal] at winnerParent
  exact Nat.lt_irrefl _ (state.view.parent_level_lt winnerParent)

/-- The local outermost-order statement implies the exact top-down list
equation used by `BatchTopmostGeometry`.  Endpoint disjointness rules out a
second loser entering the same winner placement; source placement proves
that no old child there is removed by the batch. -/
theorem topmostGeometry_of_outermostOrder
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    {matching : List (Interface.Pairing n)}
    (after : BatchReparentedView state.view matching)
    (valid : state.Valid params)
    (sourceFound : state.blocks[sourceId]? = some source)
    (geometric : GeometricMatchingValid state sourceId source matching)
    (outermost : BatchOutermostOrder state.view matching) :
    BatchTopmostGeometry after := by
  intro selected selectedMember
  have sourceStructural := valid.2 source (List.mem_of_getElem? sourceFound)
  have selectedWinnerNe :=
    winner_ne_sourceOwner valid sourceFound geometric selectedMember
  have winnersNodup := pairingWinners_nodup geometric.2.1
  have winnerInjective := List.inj_on_of_nodup_map winnersNodup
  have oldChildNotLoser : ∀ child ∈ state.view.topDown selected.winner
        (Splay.Lazy.Canonical.sideOf selected.winner selected.loser),
      ∀ pairing ∈ matching, child ≠ pairing.loser := by
    intro child childMember pairing pairingMember equal
    have childParent := (state.view.mem_topDown_iff.mp childMember).1
    have loserParent := sourceStructural.parent_eq
      (loser_mem_source geometric pairingMember)
    rw [equal] at childParent
    have ownerEq : selected.winner = source.owner :=
      Option.some.inj (childParent.symm.trans loserParent)
    exact selectedWinnerNe ownerEq
  have membership : ∀ element,
      element ∈ after.view.topDown selected.winner
          (Splay.Lazy.Canonical.sideOf selected.winner selected.loser) ↔
        element ∈ selected.loser :: state.view.topDown selected.winner
          (Splay.Lazy.Canonical.sideOf selected.winner selected.loser) := by
    intro element
    constructor
    · intro afterMember
      have afterFacts := after.view.mem_topDown_iff.mp afterMember
      by_cases loserMember : element ∈ Interface.pairingLosers matching
      · obtain ⟨pairing, pairingMember, loserEq⟩ :=
          List.mem_map.mp loserMember
        have pairedParent := after.paired_parent pairing pairingMember
        rw [loserEq] at pairedParent
        have winnerEq : pairing.winner = selected.winner :=
          Option.some.inj (pairedParent.symm.trans afterFacts.1)
        have pairingEq := winnerInjective pairingMember selectedMember winnerEq
        subst pairing
        simp only [List.mem_cons]
        exact Or.inl loserEq.symm
      · have notLoser : ∀ pairing ∈ matching,
            element ≠ pairing.loser := by
          intro pairing pairingMember equal
          apply loserMember
          exact List.mem_map.mpr ⟨pairing, pairingMember, equal.symm⟩
        simp only [List.mem_cons]
        right
        apply state.view.mem_topDown_iff.mpr
        exact ⟨(after.unpaired_parent element notLoser).symm.trans
            afterFacts.1,
          (after.unpaired_side element notLoser).symm.trans afterFacts.2⟩
    · intro beforeMember
      simp only [List.mem_cons] at beforeMember
      rcases beforeMember with rfl | oldMember
      · apply after.view.mem_topDown_iff.mpr
        exact ⟨after.paired_parent selected selectedMember,
          after.paired_side selected selectedMember⟩
      · have notLoser := oldChildNotLoser element oldMember
        have oldFacts := state.view.mem_topDown_iff.mp oldMember
        apply after.view.mem_topDown_iff.mpr
        exact ⟨(after.unpaired_parent element notLoser).trans oldFacts.1,
          (after.unpaired_side element notLoser).trans oldFacts.2⟩
  cases sideEq :
      Splay.Lazy.Canonical.sideOf selected.winner selected.loser with
  | left =>
      have oldOrdered := (state.view.topDown_ordered selected.winner).1
      have newOrdered := (after.view.topDown_ordered selected.winner).1
      have headOrder : ∀ child ∈ state.view.topDown selected.winner .left,
          selected.loser.val < child.val := by
        intro child childMember
        simpa [sideEq] using
          outermost selected selectedMember child (by simpa [sideEq])
      have rhsOrdered :
          (selected.loser :: state.view.topDown selected.winner .left).Pairwise
            (fun earlier later => earlier.val < later.val) :=
        List.pairwise_cons.mpr ⟨headOrder, oldOrdered⟩
      apply List.Pairwise.eq_of_mem_iff newOrdered rhsOrdered
      intro element
      simpa [sideEq] using membership element
  | right =>
      have oldOrdered := (state.view.topDown_ordered selected.winner).2
      have newOrdered := (after.view.topDown_ordered selected.winner).2
      have headOrder : ∀ child ∈ state.view.topDown selected.winner .right,
          child.val < selected.loser.val := by
        intro child childMember
        simpa [sideEq] using
          outermost selected selectedMember child (by simpa [sideEq])
      have rhsOrdered :
          (selected.loser :: state.view.topDown selected.winner .right).Pairwise
            (fun earlier later => later.val < earlier.val) :=
        List.pairwise_cons.mpr ⟨headOrder, oldOrdered⟩
      apply List.Pairwise.eq_of_mem_iff newOrdered rhsOrdered
      intro element
      simpa [sideEq] using membership element

/-- A block different from the pass source contains none of the batch
losers. -/
theorem block_has_no_loser
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId blockId : Interface.BlockId}
    {source block : Lazy.Block n}
    {matching : List (Interface.Pairing n)}
    (valid : state.Valid params)
    (sourceFound : state.blocks[sourceId]? = some source)
    (blockFound : state.blocks[blockId]? = some block)
    (blockNeSource : blockId ≠ sourceId)
    (geometric : GeometricMatchingValid state sourceId source matching) :
    ∀ pairing ∈ matching, pairing.loser ∉ block.elements := by
  intro pairing pairingMember loserMember
  have idsEq := valid.blockId_eq_of_element_mem blockFound loserMember
    sourceFound (loser_mem_source geometric pairingMember)
  exact blockNeSource idsEq

/-- Away from a selected destination placement, reparenting removes exactly
the batch losers from the attached top-down order. -/
theorem attachedTopDown_eq_foldl_erase_of_no_target
    {n : ℕ} {params : Interface.Parameters}
    {state : Lazy.State n} {sourceId : Interface.BlockId}
    {source : Lazy.Block n} {matching : List (Interface.Pairing n)}
    (after : BatchReparentedView state.view matching)
    (valid : state.Valid params)
    (sourceFound : state.blocks[sourceId]? = some source)
    (geometric : GeometricMatchingValid state sourceId source matching)
    (afterAssigned : List (Element n))
    (assignedIff : ∀ element,
      element ∈ afterAssigned ↔ element ∈ state.allElements)
    (owner : Element n) (childSide : Side)
    (noTarget : ∀ pairing ∈ matching,
      pairing.winner ≠ owner ∨
        Splay.Lazy.Canonical.sideOf pairing.winner pairing.loser ≠
          childSide) :
    after.view.attachedTopDown afterAssigned owner childSide =
      (Interface.pairingLosers matching).foldl List.erase
        (state.view.attachedTopDown state.allElements owner childSide) := by
  have oldNodup :
      (state.view.attachedTopDown state.allElements owner childSide).Nodup :=
    (state.view.topDown_nodup owner childSide).filter _
  have membership : ∀ element,
      element ∈ after.view.attachedTopDown afterAssigned owner childSide ↔
        element ∈ state.view.attachedTopDown state.allElements
            owner childSide ∧
          element ∉ Interface.pairingLosers matching := by
    intro element
    constructor
    · intro afterMember
      have afterFacts := after.view.mem_attachedTopDown_iff.mp afterMember
      have notLoser : ∀ pairing ∈ matching,
          element ≠ pairing.loser := by
        intro pairing pairingMember equal
        subst element
        have parentEq := after.paired_parent pairing pairingMember
        have sideEq := after.paired_side pairing pairingMember
        have targetOwner : pairing.winner = owner := by
          exact Option.some.inj
            (parentEq.symm.trans
              (after.view.mem_topDown_iff.mp afterFacts.1).1)
        have targetSide :
            Splay.Lazy.Canonical.sideOf pairing.winner pairing.loser =
              childSide :=
          sideEq.symm.trans
            (after.view.mem_topDown_iff.mp afterFacts.1).2
        rcases noTarget pairing pairingMember with ownerNe | sideNe
        · exact ownerNe targetOwner
        · exact sideNe targetSide
      constructor
      · apply state.view.mem_attachedTopDown_iff.mpr
        constructor
        · apply state.view.mem_topDown_iff.mpr
          exact ⟨(after.unpaired_parent element notLoser).symm.trans
              (after.view.mem_topDown_iff.mp afterFacts.1).1,
            (after.unpaired_side element notLoser).symm.trans
              (after.view.mem_topDown_iff.mp afterFacts.1).2⟩
        · exact (assignedIff element).mp afterFacts.2
      · intro loserMember
        obtain ⟨pairing, pairingMember, loserEq⟩ :=
          List.mem_map.mp loserMember
        exact notLoser pairing pairingMember loserEq.symm
    · rintro ⟨beforeMember, notLoserList⟩
      have notLoser : ∀ pairing ∈ matching,
          element ≠ pairing.loser := by
        intro pairing pairingMember equal
        apply notLoserList
        exact List.mem_map.mpr ⟨pairing, pairingMember, equal.symm⟩
      have beforeFacts := state.view.mem_attachedTopDown_iff.mp beforeMember
      apply after.view.mem_attachedTopDown_iff.mpr
      constructor
      · apply after.view.mem_topDown_iff.mpr
        exact ⟨(after.unpaired_parent element notLoser).trans
            (state.view.mem_topDown_iff.mp beforeFacts.1).1,
          (after.unpaired_side element notLoser).trans
            (state.view.mem_topDown_iff.mp beforeFacts.1).2⟩
      · exact (assignedIff element).mpr beforeFacts.2
  cases childSide with
  | left =>
      apply List.Pairwise.eq_of_mem_iff
        ((after.view.topDown_ordered owner).1.filter _)
        (((state.view.topDown_ordered owner).1.filter _).foldl_erase _)
      intro element
      change
        element ∈ after.view.attachedTopDown afterAssigned owner .left ↔
          element ∈ (Interface.pairingLosers matching).foldl List.erase
            (state.view.attachedTopDown state.allElements owner .left)
      rw [List.mem_foldl_erase_iff oldNodup]
      exact membership element
  | right =>
      apply List.Pairwise.eq_of_mem_iff
        ((after.view.topDown_ordered owner).2.filter _)
        (((state.view.topDown_ordered owner).2.filter _).foldl_erase _)
      intro element
      change
        element ∈ after.view.attachedTopDown afterAssigned owner .right ↔
          element ∈ (Interface.pairingLosers matching).foldl List.erase
            (state.view.attachedTopDown state.allElements owner .right)
      rw [List.mem_foldl_erase_iff oldNodup]
      exact membership element

/-- At a selected destination, the article's top-most-child fact remains
true after restricting both views to assigned elements. -/
theorem attachedTopDown_eq_cons_of_target
    {n : ℕ}
    {state : Lazy.State n} {sourceId : Interface.BlockId}
    {source : Lazy.Block n} {matching : List (Interface.Pairing n)}
    (after : BatchReparentedView state.view matching)
    (topmost : BatchTopmostGeometry after)
    (sourceFound : state.blocks[sourceId]? = some source)
    (geometric : GeometricMatchingValid state sourceId source matching)
    (afterAssigned : List (Element n))
    (assignedIff : ∀ element,
      element ∈ afterAssigned ↔ element ∈ state.allElements)
    {pairing : Interface.Pairing n} (pairingMember : pairing ∈ matching) :
    after.view.attachedTopDown afterAssigned pairing.winner
        (Splay.Lazy.Canonical.sideOf pairing.winner pairing.loser) =
      pairing.loser ::
        state.view.attachedTopDown state.allElements pairing.winner
          (Splay.Lazy.Canonical.sideOf pairing.winner pairing.loser) := by
  have sourceMember : source ∈ state.blocks :=
    List.mem_of_getElem? sourceFound
  have loserAssigned : pairing.loser ∈ state.allElements :=
    State.mem_allElements_iff.mpr
      ⟨source, sourceMember, loser_mem_source geometric pairingMember⟩
  have loserAfter : pairing.loser ∈ afterAssigned :=
    (assignedIff pairing.loser).mpr loserAssigned
  unfold HeapView.attachedTopDown
  rw [topmost pairing pairingMember]
  simp only [List.filter_cons]
  rw [if_pos (decide_eq_true loserAfter)]
  congr 1
  apply List.filter_congr
  intro element _
  exact decide_eq_decide.mpr (assignedIff element)

/-- Every old non-source block remains consecutive in the reparented view.
At a destination placement the new loser is prefixed to the ambient order;
away from destinations all losers are merely erased from outside the block. -/
theorem block_segment_after_reparent
    {n : ℕ} {params : Interface.Parameters}
    {state : Lazy.State n} {sourceId blockId : Interface.BlockId}
    {source block : Lazy.Block n}
    {matching : List (Interface.Pairing n)}
    (after : BatchReparentedView state.view matching)
    (topmost : BatchTopmostGeometry after)
    (valid : state.Valid params)
    (sourceFound : state.blocks[sourceId]? = some source)
    (blockFound : state.blocks[blockId]? = some block)
    (blockNeSource : blockId ≠ sourceId)
    (geometric : GeometricMatchingValid state sourceId source matching)
    (afterAssigned : List (Element n))
    (assignedIff : ∀ element,
      element ∈ afterAssigned ↔ element ∈ state.allElements) :
    IsSegment block.elements
      (after.view.attachedTopDown afterAssigned block.owner block.side) := by
  have blockStructural := valid.2 block (List.mem_of_getElem? blockFound)
  have noLoser := block_has_no_loser valid sourceFound blockFound
    blockNeSource geometric
  by_cases target : ∃ pairing ∈ matching,
      pairing.winner = block.owner ∧
        Splay.Lazy.Canonical.sideOf pairing.winner pairing.loser = block.side
  · obtain ⟨pairing, pairingMember, ownerEq, sideEq⟩ := target
    have attachedEq := after.attachedTopDown_eq_cons_of_target topmost
      sourceFound geometric afterAssigned assignedIff pairingMember
    have sideEq' :
        Splay.Lazy.Canonical.sideOf block.owner pairing.loser = block.side := by
      simpa only [ownerEq] using sideEq
    have specialized :
        after.view.attachedTopDown afterAssigned block.owner block.side =
          pairing.loser ::
            state.view.attachedTopDown state.allElements
              block.owner block.side := by
      simpa only [ownerEq, sideEq'] using attachedEq
    rw [specialized]
    exact blockStructural.isSegment.cons_ambient pairing.loser
  · have noTarget : ∀ pairing ∈ matching,
        pairing.winner ≠ block.owner ∨
          Splay.Lazy.Canonical.sideOf pairing.winner pairing.loser ≠
            block.side := by
      intro pairing pairingMember
      by_contra both
      simp only [not_or, ne_eq, not_not] at both
      exact target ⟨pairing, pairingMember, both.1, both.2⟩
    rw [after.attachedTopDown_eq_foldl_erase_of_no_target valid
      sourceFound geometric afterAssigned assignedIff block.owner block.side
      noTarget]
    apply blockStructural.isSegment.foldl_erase_ambient_of_fresh
    intro loser loserMember
    obtain ⟨pairing, pairingMember, rfl⟩ := List.mem_map.mp loserMember
    exact noLoser pairing pairingMember

/-- Thus every old non-source block, before any destination insertion, keeps
its full structural invariant. -/
theorem block_structurallyValid_after_reparent
    {n : ℕ} {params : Interface.Parameters}
    {state : Lazy.State n} {sourceId blockId : Interface.BlockId}
    {source block : Lazy.Block n}
    {matching : List (Interface.Pairing n)}
    (after : BatchReparentedView state.view matching)
    (topmost : BatchTopmostGeometry after)
    (valid : state.Valid params)
    (sourceFound : state.blocks[sourceId]? = some source)
    (blockFound : state.blocks[blockId]? = some block)
    (blockNeSource : blockId ≠ sourceId)
    (geometric : GeometricMatchingValid state sourceId source matching)
    (afterAssigned : List (Element n))
    (assignedIff : ∀ element,
      element ∈ afterAssigned ↔ element ∈ state.allElements) :
    block.StructurallyValid after.view afterAssigned := by
  have blockStructural := valid.2 block (List.mem_of_getElem? blockFound)
  apply blockStructural.of_rawGap_eq
    (after.block_segment_after_reparent topmost valid sourceFound blockFound
      blockNeSource geometric afterAssigned assignedIff)
  intro element elementMember
  apply after.unpaired_rawGap
  intro pairing pairingMember equal
  have noLoser := block_has_no_loser valid sourceFound blockFound
    blockNeSource geometric pairing pairingMember
  exact noLoser (equal ▸ elementMember)

/-- `GrowingTopmost` restricted to assigned elements says that a found
growing block is a prefix of its attached top-down list. -/
theorem growing_attached_prefix
    {n : ℕ} {state : Lazy.State n} {blockId : Interface.BlockId}
    {block : Lazy.Block n}
    (growingTopmost : state.GrowingTopmost)
    (blockFound : state.blocks[blockId]? = some block)
    (growing : block.mode = .growing) :
    ∃ suffix,
      state.view.attachedTopDown state.allElements block.owner block.side =
        block.elements ++ suffix := by
  obtain ⟨blockLt, blockEq⟩ := List.getElem?_eq_some_iff.mp blockFound
  let id : Fin state.blocks.length := ⟨blockId, blockLt⟩
  have getEq : state.blocks.get id = block := by
    exact blockEq
  have growingAt : (state.blocks.get id).mode = .growing := by
    rw [getEq]
    exact growing
  obtain ⟨suffix, topDownEq⟩ := growingTopmost id growingAt
  rw [getEq] at topDownEq
  let predicate := fun element : Element n =>
    decide (element ∈ state.allElements)
  have payloadFilter : block.elements.filter predicate = block.elements := by
    apply List.filter_eq_self.2
    intro element elementMember
    exact decide_eq_true
      (State.mem_allElements_iff.mpr
        ⟨block, List.mem_of_getElem? blockFound, elementMember⟩)
  refine ⟨suffix.filter predicate, ?_⟩
  unfold HeapView.attachedTopDown
  rw [topDownEq, List.filter_append, payloadFilter]

/-- Every later-phase destination retains an attached prefix after an
earlier top-most batch.  If the block was an earlier destination, both its
payload and ambient list acquire the same loser prefix; otherwise only
source losers are erased from its suffix. -/
theorem destinationPrefixes_after_topmostPass
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ}
    {batches : ArticleRetainedPairingBatches snapshot before upper_le_n key
      eligibleGroups}
    {params : Interface.Parameters} {state : Lazy.State n}
    (firstAllocation :
      ArticleBatchDestinationAllocation .first batches state)
    (laterAllocation :
      ArticleBatchDestinationAllocation .second batches state)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (valid : state.Valid params) (oneGrowing : state.OneGrowingPerSide)
    (growingTopmost : state.GrowingTopmost)
    (firstGeometric : GeometricMatchingValid state sourceId source
      firstAllocation.matching)
    (after : BatchReparentedView state.view firstAllocation.matching)
    (topmost : BatchTopmostGeometry after)
    (matchingValid : Interface.MatchingValid params state.toInterface
      sourceId source.toInterface firstAllocation.matching)
    (sourceIntervalGap : ℤ) :
    let passed := state.passAtView after.view sourceId source
      firstAllocation.matching sourceIntervalGap
    ∀ pairing ∈ laterAllocation.matching,
      ∀ destination : Lazy.Block n,
        passed.blocks[pairing.destination]? = some destination →
          ∃ suffix,
            passed.view.attachedTopDown passed.allElements
                destination.owner destination.side =
              destination.elements ++ suffix := by
  dsimp only
  let passed := state.passAtView after.view sourceId source
    firstAllocation.matching sourceIntervalGap
  have assignedPerm : passed.allElements.Perm state.allElements :=
    State.passAtView_allElements_perm_of_matching state after.view sourceId
      source firstAllocation.matching sourceIntervalGap sourceFound matchingValid
  have assignedIff : ∀ element,
      element ∈ passed.allElements ↔ element ∈ state.allElements :=
    fun element => assignedPerm.mem_iff
  intro pairing pairingMember destination destinationFound
  obtain ⟨oldBlock, oldFound, oldGrowing, oldOwner, oldSide⟩ :=
    laterAllocation.richDestinations pairing pairingMember
  have oldNeSource : pairing.destination ≠ sourceId := by
    intro destinationEq
    rw [destinationEq, sourceFound] at oldFound
    have sourceEq : source = oldBlock := Option.some.inj oldFound
    have sourceGrowing : source.mode = .growing := by
      rw [sourceEq]
      exact oldGrowing
    rw [firstGeometric.1] at sourceGrowing
    simp at sourceGrowing
  obtain ⟨oldSuffix, oldPrefix⟩ :=
    growing_attached_prefix growingTopmost oldFound oldGrowing
  by_cases target : ∃ earlier ∈ firstAllocation.matching,
      earlier.destination = pairing.destination
  · obtain ⟨earlier, earlierMember, destinationEq⟩ := target
    have afterLookup : passed.blocks[pairing.destination]? =
        some (oldBlock.inserted earlier.loser) := by
      change (Block.passBlocks state.blocks sourceId source
        firstAllocation.matching sourceIntervalGap)[pairing.destination]? = _
      rw [← destinationEq]
      exact Block.passBlocks_destination_getElem? state.blocks sourceId source
        firstAllocation.matching sourceIntervalGap
        firstAllocation.destinationsNodup earlier earlierMember oldBlock
        (by simpa only [destinationEq] using oldFound)
        (destinationEq.trans_ne oldNeSource)
    have destinationShape :
        destination = oldBlock.inserted earlier.loser :=
      Option.some.inj (destinationFound.symm.trans afterLookup)
    obtain ⟨earlierBlock, earlierFound, earlierGrowing, earlierOwner,
        earlierSide⟩ :=
      firstAllocation.richDestinations earlier earlierMember
    have earlierBlockEq : earlierBlock = oldBlock := by
      have normalizedEarlierFound :
          state.blocks[pairing.destination]? = some earlierBlock := by
        simpa only [destinationEq] using earlierFound
      exact Option.some.inj (normalizedEarlierFound.symm.trans oldFound)
    subst earlierBlock
    have targetAttached := after.attachedTopDown_eq_cons_of_target topmost
      sourceFound firstGeometric passed.allElements assignedIff earlierMember
    have normalizedAttached :
        passed.view.attachedTopDown passed.allElements
            oldBlock.owner oldBlock.side =
          earlier.loser ::
            state.view.attachedTopDown state.allElements
              oldBlock.owner oldBlock.side := by
      simpa [passed, earlierOwner, earlierSide] using targetAttached
    subst destination
    refine ⟨oldSuffix, ?_⟩
    change passed.view.attachedTopDown passed.allElements
        (oldBlock.inserted earlier.loser).owner
        (oldBlock.inserted earlier.loser).side =
      (oldBlock.inserted earlier.loser).elements ++ oldSuffix
    simpa [Block.inserted, normalizedAttached, oldPrefix]
  · have unchangedLookup : passed.blocks[pairing.destination]? =
        state.blocks[pairing.destination]? := by
      change (Block.passBlocks state.blocks sourceId source
        firstAllocation.matching sourceIntervalGap)[pairing.destination]? = _
      apply Block.passBlocks_getElem?_of_ne state.blocks sourceId
        pairing.destination source firstAllocation.matching sourceIntervalGap
        oldNeSource
      intro earlier earlierMember equal
      exact target ⟨earlier, earlierMember, equal⟩
    have destinationShape : destination = oldBlock :=
      Option.some.inj (destinationFound.symm.trans
        (unchangedLookup.trans oldFound))
    subst destination
    have noTargetPlacement : ∀ earlier ∈ firstAllocation.matching,
        earlier.winner ≠ oldBlock.owner ∨
          Splay.Lazy.Canonical.sideOf earlier.winner earlier.loser ≠
            oldBlock.side := by
      intro earlier earlierMember
      by_contra samePlacement
      simp only [not_or, ne_eq, not_not] at samePlacement
      obtain ⟨earlierBlock, earlierFound, earlierGrowing, earlierOwner,
          earlierSide⟩ :=
        firstAllocation.richDestinations earlier earlierMember
      obtain ⟨oldLt, oldGet⟩ := List.getElem?_eq_some_iff.mp oldFound
      obtain ⟨earlierLt, earlierGet⟩ :=
        List.getElem?_eq_some_iff.mp earlierFound
      let oldId : Fin state.blocks.length := ⟨pairing.destination, oldLt⟩
      let earlierId : Fin state.blocks.length :=
        ⟨earlier.destination, earlierLt⟩
      obtain ⟨canonicalId, canonicalProperty, canonicalUnique⟩ :=
        oneGrowing oldBlock.owner oldBlock.side
      have oldProperty :
          let block := state.blocks.get oldId
          block.mode = .growing ∧ block.owner = oldBlock.owner ∧
            block.side = oldBlock.side := by
        dsimp only
        have getEq : state.blocks.get oldId = oldBlock := by
          simpa [oldId, List.get_eq_getElem] using oldGet
        rw [getEq]
        exact ⟨oldGrowing, rfl, rfl⟩
      have earlierProperty :
          let block := state.blocks.get earlierId
          block.mode = .growing ∧ block.owner = oldBlock.owner ∧
            block.side = oldBlock.side := by
        dsimp only
        have getEq : state.blocks.get earlierId = earlierBlock := by
          simpa [earlierId, List.get_eq_getElem] using earlierGet
        rw [getEq]
        exact ⟨earlierGrowing, earlierOwner.trans samePlacement.1,
          earlierSide.trans samePlacement.2⟩
      have idsEq : earlierId = oldId :=
        (canonicalUnique earlierId earlierProperty).trans
          (canonicalUnique oldId oldProperty).symm
      have destinationIdsEq : earlier.destination = pairing.destination :=
        congrArg Fin.val idsEq
      exact target ⟨earlier, earlierMember, destinationIdsEq⟩
    have attachedEq := after.attachedTopDown_eq_foldl_erase_of_no_target
      valid sourceFound firstGeometric passed.allElements assignedIff
      oldBlock.owner oldBlock.side noTargetPlacement
    have noLoser := block_has_no_loser valid sourceFound oldFound oldNeSource
      firstGeometric
    have losersFresh : ∀ loser ∈
        Interface.pairingLosers firstAllocation.matching,
        loser ∉ oldBlock.elements := by
      intro loser loserMember
      obtain ⟨earlier, earlierMember, loserEq⟩ :=
        List.mem_map.mp loserMember
      simpa only [loserEq] using noLoser earlier earlierMember
    refine ⟨(Interface.pairingLosers firstAllocation.matching).foldl
      List.erase oldSuffix, ?_⟩
    change after.view.attachedTopDown passed.allElements
        oldBlock.owner oldBlock.side = _
    rw [attachedEq, oldPrefix]
    exact List.foldl_erase_append_of_fresh _ _ _ losersFresh

/-- A top-most article pass preserves the global `GrowingTopmost` invariant.
Selected destinations acquire exactly their loser at the front.  At every
other growing placement the pass only erases source losers from the suffix. -/
theorem growingTopmost_after_topmostPass
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ} {phase : PairingPhase}
    {batches : ArticleRetainedPairingBatches snapshot before upper_le_n key
      eligibleGroups}
    {params : Interface.Parameters} {state : Lazy.State n}
    (allocation : ArticleBatchDestinationAllocation phase batches state)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceShrinking : source.mode = .shrinking)
    (valid : state.Valid params) (complete : state.Complete)
    (oneGrowing : state.OneGrowingPerSide)
    (growingTopmost : state.GrowingTopmost)
    (geometric : GeometricMatchingValid state sourceId source
      allocation.matching)
    (after : BatchReparentedView state.view allocation.matching)
    (topmost : BatchTopmostGeometry after)
    (matchingValid : Interface.MatchingValid params state.toInterface
      sourceId source.toInterface allocation.matching)
    (sourceIntervalGap : ℤ) :
    let passed := state.passAtView after.view sourceId source
      allocation.matching sourceIntervalGap
    passed.GrowingTopmost := by
  dsimp only
  let passed := state.passAtView after.view sourceId source
    allocation.matching sourceIntervalGap
  have assignedPerm : passed.allElements.Perm state.allElements :=
    State.passAtView_allElements_perm_of_matching state after.view sourceId
      source allocation.matching sourceIntervalGap sourceFound matchingValid
  have assignedIff : ∀ element,
      element ∈ passed.allElements ↔ element ∈ state.allElements :=
    fun element => assignedPerm.mem_iff
  have passedComplete : passed.Complete :=
    after.complete_after_pass complete sourceFound matchingValid
      sourceIntervalGap
  intro id
  dsimp only
  let block := passed.blocks.get id
  intro blockGrowing
  change block.mode = .growing at blockGrowing
  have blockFound : passed.blocks[id.val]? = some block := by
    apply List.getElem?_eq_some_iff.mpr
    exact ⟨id.isLt, by simp [block, List.get_eq_getElem]⟩
  have attachedEqTopDown :
      passed.view.attachedTopDown passed.allElements block.owner block.side =
        passed.view.topDown block.owner block.side := by
    unfold HeapView.attachedTopDown
    apply List.filter_eq_self.mpr
    intro element elementMember
    apply decide_eq_true
    apply (passedComplete element).2
    exact passed.view.parent_ne_none_of_ne_root (by
      intro elementRoot
      have parentEq := passed.view.mem_topDown_parent elementMember
      rw [elementRoot, passed.view.root_parent] at parentEq
      simp at parentEq)
  have attachedPrefix : ∃ suffix,
      passed.view.attachedTopDown passed.allElements block.owner block.side =
        block.elements ++ suffix := by
    by_cases blockIsSource : id.val = sourceId
    · have sourceAfterFound := Lazy.Block.passBlocks_source_getElem?
        state.blocks sourceId source allocation.matching sourceIntervalGap
        sourceFound (by
          intro pairing pairingMember
          exact (geometric.2.2.2 pairing pairingMember).2.1)
      have blockEq : block =
          source.afterPassSource allocation.matching sourceIntervalGap := by
        have blockFoundAtSource :
            (Lazy.Block.passBlocks state.blocks sourceId source
              allocation.matching sourceIntervalGap)[sourceId]? =
                some block := by
          simpa [passed, State.passAtView, State.pass, blockIsSource] using
            blockFound
        apply Option.some.inj
        exact blockFoundAtSource.symm.trans sourceAfterFound
      rw [blockEq] at blockGrowing
      simp [Lazy.Block.afterPassSource, sourceShrinking] at blockGrowing
    · have oldLt : id.val < state.blocks.length := by
        have lengthEq : passed.blocks.length = state.blocks.length := by
          change
            (Lazy.Block.passBlocks state.blocks sourceId source
              allocation.matching sourceIntervalGap).length =
                state.blocks.length
          exact Lazy.Block.length_passBlocks state.blocks sourceId source
            allocation.matching sourceIntervalGap
        exact lt_of_lt_of_eq id.isLt lengthEq
      let oldId : Fin state.blocks.length := ⟨id.val, oldLt⟩
      let oldBlock := state.blocks.get oldId
      have oldFound : state.blocks[id.val]? = some oldBlock := by
        apply List.getElem?_eq_some_iff.mpr
        exact ⟨oldLt, by simp [oldBlock, oldId, List.get_eq_getElem]⟩
      by_cases selected : ∃ pairing ∈ allocation.matching,
          pairing.destination = id.val
      · obtain ⟨pairing, pairingMember, destinationEq⟩ := selected
        obtain ⟨destination, destinationFound, destinationGrowing,
            destinationOwner, destinationSide⟩ :=
          allocation.richDestinations pairing pairingMember
        have destinationEqOld : destination = oldBlock := by
          have normalizedDestinationFound :
              state.blocks[id.val]? = some destination := by
            simpa only [destinationEq] using destinationFound
          apply Option.some.inj
          exact normalizedDestinationFound.symm.trans oldFound
        subst destination
        have afterLookup : passed.blocks[id.val]? =
            some (oldBlock.inserted pairing.loser) := by
          change
            (Lazy.Block.passBlocks state.blocks sourceId source
              allocation.matching sourceIntervalGap)[id.val]? = _
          rw [← destinationEq]
          exact Lazy.Block.passBlocks_destination_getElem?
            state.blocks sourceId source allocation.matching sourceIntervalGap
            allocation.destinationsNodup pairing pairingMember oldBlock
            (by simpa only [destinationEq] using oldFound)
            (destinationEq.trans_ne blockIsSource)
        have blockEq : block = oldBlock.inserted pairing.loser :=
          Option.some.inj (blockFound.symm.trans afterLookup)
        obtain ⟨oldSuffix, oldPrefix⟩ := growing_attached_prefix
          growingTopmost oldFound destinationGrowing
        have targetAttached := after.attachedTopDown_eq_cons_of_target
          topmost sourceFound geometric passed.allElements assignedIff
          pairingMember
        have normalizedAttached :
            passed.view.attachedTopDown passed.allElements
                oldBlock.owner oldBlock.side =
              pairing.loser ::
                state.view.attachedTopDown state.allElements
                  oldBlock.owner oldBlock.side := by
          simpa [passed, destinationOwner, destinationSide] using targetAttached
        refine ⟨oldSuffix, ?_⟩
        rw [blockEq]
        simpa [Lazy.Block.inserted, normalizedAttached, oldPrefix]
      · have unchangedLookup : passed.blocks[id.val]? =
            state.blocks[id.val]? := by
          change
            (Lazy.Block.passBlocks state.blocks sourceId source
              allocation.matching sourceIntervalGap)[id.val]? = _
          apply Lazy.Block.passBlocks_getElem?_of_ne state.blocks sourceId
            id.val source allocation.matching sourceIntervalGap
            blockIsSource
          intro pairing pairingMember equal
          exact selected ⟨pairing, pairingMember, equal⟩
        have blockEq : block = oldBlock :=
          Option.some.inj (blockFound.symm.trans
            (unchangedLookup.trans oldFound))
        have oldGrowing : oldBlock.mode = .growing := by
          simpa only [blockEq] using blockGrowing
        obtain ⟨oldSuffix, oldPrefix⟩ := growing_attached_prefix
          growingTopmost oldFound oldGrowing
        have noTargetPlacement : ∀ pairing ∈ allocation.matching,
            pairing.winner ≠ oldBlock.owner ∨
              Splay.Lazy.Canonical.sideOf pairing.winner pairing.loser ≠
                oldBlock.side := by
          intro pairing pairingMember
          by_contra samePlacement
          simp only [not_or, ne_eq, not_not] at samePlacement
          obtain ⟨destination, destinationFound, destinationGrowing,
              destinationOwner, destinationSide⟩ :=
            allocation.richDestinations pairing pairingMember
          obtain ⟨destinationLt, destinationGet⟩ :=
            List.getElem?_eq_some_iff.mp destinationFound
          let destinationId : Fin state.blocks.length :=
            ⟨pairing.destination, destinationLt⟩
          obtain ⟨canonicalId, _canonicalProperty, canonicalUnique⟩ :=
            oneGrowing oldBlock.owner oldBlock.side
          have oldProperty :
              let current := state.blocks.get oldId
              current.mode = .growing ∧ current.owner = oldBlock.owner ∧
                current.side = oldBlock.side := by
            simpa [oldBlock]
          have destinationProperty :
              let current := state.blocks.get destinationId
              current.mode = .growing ∧ current.owner = oldBlock.owner ∧
                current.side = oldBlock.side := by
            dsimp only
            have getEq : state.blocks.get destinationId = destination := by
              simpa [destinationId, List.get_eq_getElem] using destinationGet
            rw [getEq]
            exact ⟨destinationGrowing,
              destinationOwner.trans samePlacement.1,
              destinationSide.trans samePlacement.2⟩
          have idsEq : destinationId = oldId :=
            (canonicalUnique destinationId destinationProperty).trans
              (canonicalUnique oldId oldProperty).symm
          apply selected
          exact ⟨pairing, pairingMember, congrArg Fin.val idsEq⟩
        have reparentedAttached :=
          after.attachedTopDown_eq_foldl_erase_of_no_target valid
            sourceFound geometric passed.allElements assignedIff
            oldBlock.owner oldBlock.side noTargetPlacement
        have noLoser := block_has_no_loser valid sourceFound oldFound
          blockIsSource geometric
        have losersFresh : ∀ loser ∈
            Interface.pairingLosers allocation.matching,
            loser ∉ oldBlock.elements := by
          intro loser loserMember
          obtain ⟨pairing, pairingMember, loserEq⟩ :=
            List.mem_map.mp loserMember
          simpa only [loserEq] using noLoser pairing pairingMember
        refine ⟨(Interface.pairingLosers allocation.matching).foldl
          List.erase oldSuffix, ?_⟩
        rw [blockEq]
        change after.view.attachedTopDown passed.allElements
            oldBlock.owner oldBlock.side = _
        rw [reparentedAttached, oldPrefix]
        exact List.foldl_erase_append_of_fresh _ _ _ losersFresh
  obtain ⟨suffix, prefixEq⟩ := attachedPrefix
  refine ⟨suffix, ?_⟩
  rw [← attachedEqTopDown]
  exact prefixEq

/-- A selected growing destination remains structurally valid after its
loser is inserted.  This is the precise local interval-update claim of the
article's internal pairing. -/
theorem destination_inserted_structurallyValid
    {n : ℕ} {params : Interface.Parameters}
    {state : Lazy.State n} {sourceId : Interface.BlockId}
    {source : Lazy.Block n} {matching : List (Interface.Pairing n)}
    (after : BatchReparentedView state.view matching)
    (topmost : BatchTopmostGeometry after)
    (valid : state.Valid params)
    (sourceFound : state.blocks[sourceId]? = some source)
    (geometric : GeometricMatchingValid state sourceId source matching)
    (afterAssigned : List (Element n))
    (assignedIff : ∀ element,
      element ∈ afterAssigned ↔ element ∈ state.allElements)
    {pairing : Interface.Pairing n} (pairingMember : pairing ∈ matching)
    {destination : Lazy.Block n}
    (destinationFound :
      state.blocks[pairing.destination]? = some destination)
    (destinationGrowing : destination.mode = .growing)
    (destinationOwner : destination.owner = pairing.winner)
    (destinationSide : destination.side =
      Splay.Lazy.Canonical.sideOf pairing.winner pairing.loser)
    (destinationPrefix : ∃ suffix,
      state.view.attachedTopDown state.allElements
          destination.owner destination.side =
        destination.elements ++ suffix) :
    (destination.inserted pairing.loser).StructurallyValid
      after.view afterAssigned := by
  have destinationNeSource : pairing.destination ≠ sourceId :=
    (geometric.2.2.2 pairing pairingMember).2.1
  have oldValid := after.block_structurallyValid_after_reparent topmost valid
    sourceFound destinationFound destinationNeSource geometric afterAssigned
      assignedIff
  obtain ⟨suffix, oldPrefix⟩ := destinationPrefix
  have targetAttached := after.attachedTopDown_eq_cons_of_target topmost
    sourceFound geometric afterAssigned assignedIff pairingMember
  have afterSegment :
      IsSegment (destination.inserted pairing.loser).elements
        (after.view.attachedTopDown afterAssigned
          destination.owner destination.side) := by
    have targetAttached' :
        after.view.attachedTopDown afterAssigned
            destination.owner destination.side =
          pairing.loser ::
            state.view.attachedTopDown state.allElements
              destination.owner destination.side := by
      simpa only [destinationOwner, destinationSide] using targetAttached
    rw [targetAttached']
    exact IsSegment.cons_of_eq_append pairing.loser oldPrefix
  have loserGap : 0 ≤ after.view.rawGap pairing.loser := by
    have rankLt := after.ordered (after.paired_parent pairing pairingMember)
    simp [HeapView.rawGap, after.paired_parent pairing pairingMember]
    omega
  exact Block.inserted_structurallyValid oldValid destinationGrowing
    pairing.loser loserGap afterSegment

/-- At the old source placement, the reparented view is exactly the old
attached top-down list with all batch losers erased. -/
theorem source_attachedTopDown_eq_foldl_erase
    {n : ℕ} {params : Interface.Parameters}
    {state : Lazy.State n} {sourceId : Interface.BlockId}
    {source : Lazy.Block n} {matching : List (Interface.Pairing n)}
    (after : BatchReparentedView state.view matching)
    (valid : state.Valid params)
    (sourceFound : state.blocks[sourceId]? = some source)
    (geometric : GeometricMatchingValid state sourceId source matching)
    (afterAssigned : List (Element n))
    (assignedIff : ∀ element,
      element ∈ afterAssigned ↔ element ∈ state.allElements) :
    after.view.attachedTopDown afterAssigned source.owner source.side =
      (Interface.pairingLosers matching).foldl List.erase
        (state.view.attachedTopDown state.allElements
          source.owner source.side) := by
  have sourceMember : source ∈ state.blocks :=
    List.mem_of_getElem? sourceFound
  have sourceStructural := valid.2 source sourceMember
  have oldNodup :
      (state.view.attachedTopDown state.allElements
        source.owner source.side).Nodup := by
    exact (state.view.topDown_nodup source.owner source.side).filter _
  have winnerNeOwner : ∀ pairing ∈ matching,
      pairing.winner ≠ source.owner := by
    intro pairing pairingMember equal
    have winnerMember :=
      (geometric.2.2.2 pairing pairingMember).1.first_mem
    have winnerParent := sourceStructural.parent_eq winnerMember
    rw [equal] at winnerParent
    have impossible := state.view.parent_level_lt winnerParent
    exact Nat.lt_irrefl _ impossible
  have membership : ∀ element,
      element ∈ after.view.attachedTopDown afterAssigned
          source.owner source.side ↔
        element ∈ state.view.attachedTopDown state.allElements
            source.owner source.side ∧
          element ∉ Interface.pairingLosers matching := by
    intro element
    constructor
    · intro afterMember
      have afterFacts := after.view.mem_attachedTopDown_iff.mp afterMember
      have notLoser : ∀ pairing ∈ matching,
          element ≠ pairing.loser := by
        intro pairing pairingMember equal
        subst element
        have pairedParent := after.paired_parent pairing pairingMember
        have ownerEq : pairing.winner = source.owner := by
          rw [after.view.mem_topDown_iff.mp afterFacts.1 |>.1] at pairedParent
          exact Option.some.inj pairedParent.symm
        exact winnerNeOwner pairing pairingMember ownerEq
      constructor
      · apply state.view.mem_attachedTopDown_iff.mpr
        constructor
        · apply state.view.mem_topDown_iff.mpr
          constructor
          · rw [← after.unpaired_parent element notLoser]
            exact (after.view.mem_topDown_iff.mp afterFacts.1).1
          · rw [← after.unpaired_side element notLoser]
            exact (after.view.mem_topDown_iff.mp afterFacts.1).2
        · exact (assignedIff element).mp afterFacts.2
      · intro loserMember
        obtain ⟨pairing, pairingMember, loserEq⟩ :=
          List.mem_map.mp loserMember
        exact notLoser pairing pairingMember loserEq.symm
    · rintro ⟨beforeMember, notLoserList⟩
      have notLoser : ∀ pairing ∈ matching,
          element ≠ pairing.loser := by
        intro pairing pairingMember equal
        apply notLoserList
        exact List.mem_map.mpr ⟨pairing, pairingMember, equal.symm⟩
      have beforeFacts := state.view.mem_attachedTopDown_iff.mp beforeMember
      apply after.view.mem_attachedTopDown_iff.mpr
      constructor
      · apply after.view.mem_topDown_iff.mpr
        exact ⟨(after.unpaired_parent element notLoser).trans
            (state.view.mem_topDown_iff.mp beforeFacts.1).1,
          (after.unpaired_side element notLoser).trans
            (state.view.mem_topDown_iff.mp beforeFacts.1).2⟩
      · exact (assignedIff element).mpr beforeFacts.2
  cases sideEq : source.side with
  | left =>
      apply List.Pairwise.eq_of_mem_iff
        ((after.view.topDown_ordered source.owner).1.filter _)
        (((state.view.topDown_ordered source.owner).1.filter _)
          |>.foldl_erase _)
      intro element
      rw [List.mem_foldl_erase_iff
        ((state.view.topDown_nodup source.owner .left).filter _)]
      simpa [HeapView.attachedTopDown, sideEq] using membership element
  | right =>
      apply List.Pairwise.eq_of_mem_iff
        ((after.view.topDown_ordered source.owner).2.filter _)
        (((state.view.topDown_ordered source.owner).2.filter _)
          |>.foldl_erase _)
      intro element
      rw [List.mem_foldl_erase_iff
        ((state.view.topDown_nodup source.owner .right).filter _)]
      simpa [HeapView.attachedTopDown, sideEq] using membership element

/-- Consequently the shrinking source remainder is automatically a segment
of the reparented view; no source-placement premise remains for the rich
`Pass`. -/
theorem source_afterPass_segment
    {n : ℕ} {params : Interface.Parameters}
    {state : Lazy.State n} {sourceId : Interface.BlockId}
    {source : Lazy.Block n} {matching : List (Interface.Pairing n)}
    (after : BatchReparentedView state.view matching)
    (valid : state.Valid params)
    (sourceFound : state.blocks[sourceId]? = some source)
    (geometric : GeometricMatchingValid state sourceId source matching)
    (matchingValid : Interface.MatchingValid params state.toInterface
      sourceId source.toInterface matching)
    (sourceIntervalGap : ℤ) :
    IsSegment
      (source.afterPassSource matching sourceIntervalGap).elements
      (after.view.attachedTopDown
        (state.passAtView after.view sourceId source matching
          sourceIntervalGap).allElements
        source.owner source.side) := by
  let passed := state.passAtView after.view sourceId source matching
    sourceIntervalGap
  have assignedPerm : passed.allElements.Perm state.allElements :=
    State.passAtView_allElements_perm_of_matching state after.view sourceId
      source matching sourceIntervalGap sourceFound matchingValid
  have assignedIff : ∀ element,
      element ∈ passed.allElements ↔ element ∈ state.allElements :=
    fun element => assignedPerm.mem_iff
  have ambientEq := after.source_attachedTopDown_eq_foldl_erase valid
    sourceFound geometric passed.allElements assignedIff
  have sourceMember : source ∈ state.blocks :=
    List.mem_of_getElem? sourceFound
  have sourceStructural := valid.2 source sourceMember
  have oldNodup :
      (state.view.attachedTopDown state.allElements
        source.owner source.side).Nodup :=
    (state.view.topDown_nodup source.owner source.side).filter _
  have losersNodup := Interface.pairingLosers_nodup geometric.2.1
  have losersInside : ∀ loser ∈ Interface.pairingLosers matching,
      loser ∈ source.elements := by
    intro loser loserMember
    obtain ⟨pairing, pairingMember, rfl⟩ :=
      List.mem_map.mp loserMember
    exact (geometric.2.2.2 pairing pairingMember).1.second_mem
  have erasedSegment := sourceStructural.isSegment.foldl_erase oldNodup
    (Interface.pairingLosers matching) losersNodup losersInside
  rw [ambientEq]
  change IsSegment (Interface.removeLosers source.elements matching) _
  rw [Interface.removeLosers_eq_foldl]
  exact erasedSegment

/-- The source keeps its original signed interval minimum across an internal
article pairing batch.  A removed loser cannot attain the old minimum: its
paired winner remains in the same source block and has strictly smaller
comparison rank, hence strictly smaller raw gap.  This is the manuscript's
local reason that an internal `Pass` needs no source rank update. -/
theorem source_afterPass_gapValid_original
    {n : ℕ} {params : Interface.Parameters}
    {state : Lazy.State n} {sourceId : Interface.BlockId}
    {source : Lazy.Block n} {matching : List (Interface.Pairing n)}
    (after : BatchReparentedView state.view matching)
    (valid : state.Valid params)
    (sourceFound : state.blocks[sourceId]? = some source)
    (geometric : GeometricMatchingValid state sourceId source matching) :
    (source.afterPassSource matching source.intervalGap).GapValid
      after.view := by
  by_cases matchingEmpty : matching = []
  · subst matching
    have rawGapEq : after.view.rawGap = state.view.rawGap := by
      funext element
      exact after.unpaired_rawGap (by simp)
    have sourceGap :=
      (valid.2 source (List.mem_of_getElem? sourceFound)).2.2
    simp only [Lazy.Block.GapValid, Lazy.Block.afterPassSource,
      geometric.1] at sourceGap ⊢
    simp only [Interface.removeLosers] at ⊢
    rw [rawGapEq]
    exact sourceGap
  · have sourceStructural :=
      valid.2 source (List.mem_of_getElem? sourceFound)
    have sourceNodup : source.elements.Nodup := by
      have sourceInterfaceFound :
          state.toInterface.block? sourceId = some source.toInterface := by
        unfold Interface.State.block? Lazy.State.toInterface
        simpa using
          congrArg (Option.map Lazy.Block.toInterface) sourceFound
      have interfaceNodup :=
        valid.1.block_elements_nodup sourceInterfaceFound
      change source.elements.Nodup at interfaceNodup
      exact interfaceNodup
    have sourceNonempty : source.elements ≠ [] := by
      obtain ⟨pairing, pairingMember⟩ :=
        List.exists_mem_of_ne_nil matching matchingEmpty
      exact List.ne_nil_of_mem (loser_mem_source geometric pairingMember)
    have sourceMinimum :
        Analysis.IsIntervalGap source.elements.toFinset state.view.rawGap
          source.intervalGap := by
      have sourceGap := sourceStructural.2.2
      simpa [Lazy.Block.GapValid, geometric.1, sourceNonempty] using sourceGap
    obtain ⟨minimizer, minimizerMember, minimizerGap⟩ := sourceMinimum.1
    have minimizerMemberList : minimizer ∈ source.elements := by
      simpa using minimizerMember
    have minimizerNotLoser :
        minimizer ∉ Interface.pairingLosers matching := by
      intro loserMember
      obtain ⟨pairing, pairingMember, loserEq⟩ :=
        List.mem_map.mp (by
          simpa only [Interface.pairingLosers] using loserMember)
      have winnerMember : pairing.winner ∈ source.elements :=
        (geometric.2.2.2 pairing pairingMember).1.first_mem
      have loserMemberSource : pairing.loser ∈ source.elements :=
        loser_mem_source geometric pairingMember
      have winnerParent := sourceStructural.parent_eq winnerMember
      have loserParent := sourceStructural.parent_eq loserMemberSource
      have rankOrderAfter := after.ordered
        (after.paired_parent pairing pairingMember)
      have rankOrderBefore :
          state.view.rank pairing.winner < state.view.rank pairing.loser := by
        simpa [after.rank_eq] using rankOrderAfter
      have rawGapOrder :
          state.view.rawGap pairing.winner <
            state.view.rawGap pairing.loser := by
        simp only [HeapView.rawGap, winnerParent, loserParent]
        omega
      have winnerLower := sourceMinimum.2 pairing.winner (by
        simpa using winnerMember)
      have loserAttains :
          state.view.rawGap pairing.loser = source.intervalGap := by
        simpa [loserEq] using minimizerGap
      omega
    have minimizerRemains :
        minimizer ∈ Interface.removeLosers source.elements matching := by
      rw [Interface.removeLosers_eq_foldl,
        List.mem_foldl_erase_iff sourceNodup]
      exact ⟨minimizerMemberList, minimizerNotLoser⟩
    have afterMinimum :
        Analysis.IsIntervalGap
          (Interface.removeLosers source.elements matching).toFinset
          after.view.rawGap source.intervalGap := by
      constructor
      · refine ⟨minimizer, by simpa using minimizerRemains, ?_⟩
        rw [after.unpaired_rawGap]
        · exact minimizerGap
        · intro pairing pairingMember equal
          apply minimizerNotLoser
          exact List.mem_map.mpr ⟨pairing, pairingMember, equal.symm⟩
      · intro element elementMember
        have elementMemberList :
            element ∈ Interface.removeLosers source.elements matching := by
          simpa using elementMember
        rw [Interface.removeLosers_eq_foldl,
          List.mem_foldl_erase_iff sourceNodup] at elementMemberList
        rw [after.unpaired_rawGap]
        · exact sourceMinimum.2 element (by
            simpa using elementMemberList.1)
        · intro pairing pairingMember equal
          apply elementMemberList.2
          exact List.mem_map.mpr ⟨pairing, pairingMember, equal.symm⟩
    have remainderNonempty :
        Interface.removeLosers source.elements matching ≠ [] :=
      List.ne_nil_of_mem minimizerRemains
    simpa [Lazy.Block.GapValid, Lazy.Block.afterPassSource,
      geometric.1, remainderNonempty] using afterMinimum

/-- For the canonical reparented batch, the exact article choice of the old
source interval gap gives rich pass preservation.  The only remaining rich
obligation is structural validity of the non-source blocks, whose nontrivial
cases are precisely the winner growing destinations. -/
theorem passAtViewPreservation_original
    {n : ℕ} {params : Interface.Parameters}
    {state : Lazy.State n} {sourceId : Interface.BlockId}
    {source : Lazy.Block n} {matching : List (Interface.Pairing n)}
    (after : BatchReparentedView state.view matching)
    (valid : state.Valid params)
    (sourceFound : state.blocks[sourceId]? = some source)
    (geometric : GeometricMatchingValid state sourceId source matching)
    (matchingValid : Interface.MatchingValid params state.toInterface
      sourceId source.toInterface matching)
    (otherValid : ∀ sourceIntervalGap,
      ∀ id : Fin
          (state.passAtView after.view sourceId source matching
            sourceIntervalGap).blocks.length,
        sourceId ≠ id.val →
          ((state.passAtView after.view sourceId source matching
            sourceIntervalGap).blocks.get id).StructurallyValid
              after.view
              (state.passAtView after.view sourceId source matching
                sourceIntervalGap).allElements) :
    PassAtViewPreservation state after.view sourceId source matching
      source.intervalGap := by
  refine ⟨?_,
    after.source_afterPass_segment valid sourceFound geometric
      matchingValid source.intervalGap,
    after.source_afterPass_gapValid_original valid sourceFound geometric,
    otherValid source.intervalGap⟩
  change
    (Lazy.Block.passBlocks state.blocks sourceId source matching
      source.intervalGap)[sourceId]? =
        some (source.afterPassSource matching source.intervalGap)
  apply Lazy.Block.passBlocks_source_getElem? state.blocks sourceId source
    matching source.intervalGap sourceFound
  intro pairing pairingMember
  exact (geometric.2.2.2 pairing pairingMember).2.1

/-- Any legal preservation witness necessarily chose the manuscript's old
source interval gap.  On a nonempty remainder this is uniqueness of the
attained minimum; on an empty remainder both valid gaps are zero. -/
theorem sourceIntervalGap_eq_original
    {n : ℕ} {params : Interface.Parameters}
    {state : Lazy.State n} {sourceId : Interface.BlockId}
    {source : Lazy.Block n} {matching : List (Interface.Pairing n)}
    (after : BatchReparentedView state.view matching)
    (valid : state.Valid params)
    (sourceFound : state.blocks[sourceId]? = some source)
    (geometric : GeometricMatchingValid state sourceId source matching)
    {sourceIntervalGap : ℤ}
    (preservation : PassAtViewPreservation state after.view sourceId source
      matching sourceIntervalGap) :
    sourceIntervalGap = source.intervalGap := by
  have original := after.source_afterPass_gapValid_original valid sourceFound
    geometric
  have chosen := preservation.sourceGapValid
  by_cases empty : Interface.removeLosers source.elements matching = []
  · have chosenZero : sourceIntervalGap = 0 := by
      simpa [Lazy.Block.GapValid, Lazy.Block.afterPassSource,
        geometric.1, empty] using chosen
    have originalZero : source.intervalGap = 0 := by
      simpa [Lazy.Block.GapValid, Lazy.Block.afterPassSource,
        geometric.1, empty] using original
    exact chosenZero.trans originalZero.symm
  · have chosenMinimum :
        Analysis.IsIntervalGap
          (Interface.removeLosers source.elements matching).toFinset
          after.view.rawGap sourceIntervalGap := by
      simpa [Lazy.Block.GapValid, Lazy.Block.afterPassSource,
        geometric.1, empty] using chosen
    have originalMinimum :
        Analysis.IsIntervalGap
          (Interface.removeLosers source.elements matching).toFinset
          after.view.rawGap source.intervalGap := by
      simpa [Lazy.Block.GapValid, Lazy.Block.afterPassSource,
        geometric.1, empty] using original
    exact chosenMinimum.unique originalMinimum

/-- Existential compatibility wrapper for callers that do not yet expose the
article's exact source-gap choice in their result type. -/
theorem exists_passAtViewPreservation
    {n : ℕ} {params : Interface.Parameters}
    {state : Lazy.State n} {sourceId : Interface.BlockId}
    {source : Lazy.Block n} {matching : List (Interface.Pairing n)}
    (after : BatchReparentedView state.view matching)
    (valid : state.Valid params)
    (sourceFound : state.blocks[sourceId]? = some source)
    (geometric : GeometricMatchingValid state sourceId source matching)
    (matchingValid : Interface.MatchingValid params state.toInterface
      sourceId source.toInterface matching)
    (otherValid : ∀ sourceIntervalGap,
      ∀ id : Fin
          (state.passAtView after.view sourceId source matching
            sourceIntervalGap).blocks.length,
        sourceId ≠ id.val →
          ((state.passAtView after.view sourceId source matching
            sourceIntervalGap).blocks.get id).StructurallyValid
              after.view
              (state.passAtView after.view sourceId source matching
                sourceIntervalGap).allElements) :
    ∃ sourceIntervalGap,
      PassAtViewPreservation state after.view sourceId source matching
        sourceIntervalGap := by
  exact ⟨source.intervalGap,
    after.passAtViewPreservation_original valid sourceFound geometric
      matchingValid otherValid⟩

/-- The article's single top-most-child geometry discharges every remaining
non-source block obligation of the rich pass.  Destinations use
`destination_inserted_structurallyValid`; all other stable IDs use exact
block separation and unchanged raw gaps. -/
theorem otherValid_of_topmost
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ} {phase : PairingPhase}
    {batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups}
    {params : Interface.Parameters} {state : Lazy.State n}
    (allocation : ArticleBatchDestinationAllocation phase batches state)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (after : BatchReparentedView state.view allocation.matching)
    (topmost : BatchTopmostGeometry after)
    (valid : state.Valid params)
    (destinationPrefixes : ∀ pairing ∈ allocation.matching,
      ∀ destination : Lazy.Block n,
        state.blocks[pairing.destination]? = some destination →
          ∃ suffix,
            state.view.attachedTopDown state.allElements
                destination.owner destination.side =
              destination.elements ++ suffix)
    (sourceFound : state.blocks[sourceId]? = some source)
    (geometric : GeometricMatchingValid state sourceId source
      allocation.matching)
    (matchingValid : Interface.MatchingValid params state.toInterface
      sourceId source.toInterface allocation.matching) :
    ∀ sourceIntervalGap,
      ∀ id : Fin
          (state.passAtView after.view sourceId source allocation.matching
            sourceIntervalGap).blocks.length,
        sourceId ≠ id.val →
          ((state.passAtView after.view sourceId source allocation.matching
            sourceIntervalGap).blocks.get id).StructurallyValid
              after.view
              (state.passAtView after.view sourceId source
                allocation.matching sourceIntervalGap).allElements := by
  intro sourceIntervalGap id sourceNeId
  let passed := state.passAtView after.view sourceId source
    allocation.matching sourceIntervalGap
  have assignedPerm : passed.allElements.Perm state.allElements :=
    State.passAtView_allElements_perm_of_matching state after.view sourceId
      source allocation.matching sourceIntervalGap sourceFound matchingValid
  have assignedIff : ∀ element,
      element ∈ passed.allElements ↔ element ∈ state.allElements :=
    fun element => assignedPerm.mem_iff
  have finalFound :
      passed.blocks[id.val]? = some (passed.blocks.get id) := by
    simp
  by_cases destinationMember :
      id.val ∈ allocation.matching.map fun pairing => pairing.destination
  · obtain ⟨pairing, pairingMember, destinationEq⟩ :=
      List.mem_map.mp destinationMember
    obtain ⟨destination, destinationFound, destinationGrowing,
        destinationOwner, destinationSide⟩ :=
      allocation.richDestinations pairing pairingMember
    have destinationNeSource : pairing.destination ≠ sourceId :=
      (geometric.2.2.2 pairing pairingMember).2.1
    have destinationLookup :
        passed.blocks[pairing.destination]? =
          some (destination.inserted pairing.loser) := by
      change
        (Block.passBlocks state.blocks sourceId source allocation.matching
          sourceIntervalGap)[pairing.destination]? = _
      exact Block.passBlocks_destination_getElem? state.blocks sourceId source
        allocation.matching sourceIntervalGap allocation.destinationsNodup
        pairing pairingMember destination destinationFound destinationNeSource
    rw [destinationEq] at destinationLookup
    have currentEq :
        passed.blocks.get id = destination.inserted pairing.loser :=
      Option.some.inj (finalFound.symm.trans destinationLookup)
    rw [currentEq]
    exact after.destination_inserted_structurallyValid topmost valid
      sourceFound geometric passed.allElements assignedIff
      pairingMember destinationFound destinationGrowing destinationOwner
      destinationSide
      (destinationPrefixes pairing pairingMember destination destinationFound)
  · have destinationsNe : ∀ pairing ∈ allocation.matching,
        pairing.destination ≠ id.val := by
      intro pairing pairingMember equal
      apply destinationMember
      exact List.mem_map.mpr ⟨pairing, pairingMember, equal⟩
    have unchangedLookup :
        passed.blocks[id.val]? = state.blocks[id.val]? := by
      change
        (Block.passBlocks state.blocks sourceId source allocation.matching
          sourceIntervalGap)[id.val]? = state.blocks[id.val]?
      exact Block.passBlocks_getElem?_of_ne state.blocks sourceId id.val source
        allocation.matching sourceIntervalGap sourceNeId.symm destinationsNe
    have oldFound :
        state.blocks[id.val]? = some (passed.blocks.get id) :=
      unchangedLookup.symm.trans finalFound
    exact after.block_structurallyValid_after_reparent topmost valid
      sourceFound oldFound sourceNeId.symm geometric passed.allElements
      assignedIff

end BatchReparentedView

/-- The simultaneous article batch has a concrete heap view obtained by
reparenting exactly its losers.  This is the structural half of the
zig-zig-to-pairings lemma: ranks and the root are retained, and every new
edge is heap ordered. -/
theorem exists_reparentedView
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
    (valid : state.Valid params)
    (rankEq : state.view.rank = snapshot.rank)
    (ordered : state.view.HeapOrdered) :
    Nonempty (BatchReparentedView state.view allocation.matching) := by
  let instructions := allocation.matching.map pairingReparentInstruction
  have loserNotRoot : ∀ instruction ∈ instructions,
      instruction.loser ≠ state.view.root := by
    intro instruction instructionMember
    obtain ⟨pairing, pairingMember, instructionEq⟩ :=
      List.mem_map.mp instructionMember
    subst instruction
    have loserInSource : pairing.loser ∈ source.elements :=
      (geometric.2.2.2 pairing pairingMember).1.second_mem
    have sourceMember : source ∈ state.blocks :=
      List.mem_of_getElem? sourceFound
    have loserAssigned : pairing.loser ∈ state.allElements :=
      State.mem_allElements_iff.mpr
        ⟨source, sourceMember, loserInSource⟩
    exact fun loserRoot =>
      valid.root_not_mem (loserRoot ▸ loserAssigned)
  have rankLt : ∀ instruction ∈ instructions,
      state.view.rank instruction.winner <
        state.view.rank instruction.loser := by
    intro instruction instructionMember
    obtain ⟨pairing, pairingMember, instructionEq⟩ :=
      List.mem_map.mp instructionMember
    subst instruction
    change state.view.rank pairing.winner < state.view.rank pairing.loser
    rw [rankEq]
    exact allocation.agreement.rank_lt pairingMember
  have sideOrder : ∀ instruction ∈ instructions,
      match instruction.side with
      | .left => instruction.loser.val < instruction.winner.val
      | .right => instruction.winner.val < instruction.loser.val := by
    intro instruction instructionMember
    obtain ⟨pairing, pairingMember, instructionEq⟩ :=
      List.mem_map.mp instructionMember
    subst instruction
    apply Splay.Lazy.Canonical.sideOf_order_of_ne
    intro equal
    have strict := rankLt (pairingReparentInstruction pairing)
      (List.mem_map.mpr ⟨pairing, pairingMember, rfl⟩)
    change state.view.rank pairing.winner <
      state.view.rank pairing.loser at strict
    rw [equal] at strict
    exact Nat.lt_irrefl _ strict
  have losersNodup :
      (instructions.map HeapView.ReparentInstruction.loser).Nodup := by
    have matchingLosersNodup :=
      Interface.pairingLosers_nodup geometric.2.1
    simpa [instructions, pairingReparentInstruction,
      Interface.pairingLosers, List.map_map, Function.comp_def] using
        matchingLosersNodup
  let afterView := state.view.reparentMany instructions ordered
    loserNotRoot rankLt sideOrder
  refine ⟨{
    view := afterView
    rank_eq := HeapView.reparentMany_rank state.view instructions ordered
      loserNotRoot rankLt sideOrder
    root_eq := HeapView.reparentMany_root state.view instructions ordered
      loserNotRoot rankLt sideOrder
    ordered := HeapView.reparentMany_heapOrdered state.view instructions ordered
      loserNotRoot rankLt sideOrder
    paired_parent := ?_
    paired_side := ?_
    unpaired_parent := ?_
    unpaired_side := ?_
  }⟩
  · intro pairing pairingMember
    have instructionMember : pairingReparentInstruction pairing ∈
        instructions :=
      List.mem_map.mpr ⟨pairing, pairingMember, rfl⟩
    exact HeapView.reparentMany_parent_of_mem state.view instructions ordered
      loserNotRoot rankLt sideOrder losersNodup
        (pairingReparentInstruction pairing) instructionMember
  · intro pairing pairingMember
    have instructionMember : pairingReparentInstruction pairing ∈
        instructions :=
      List.mem_map.mpr ⟨pairing, pairingMember, rfl⟩
    exact HeapView.reparentMany_side_of_mem state.view instructions ordered
      loserNotRoot rankLt sideOrder losersNodup
        (pairingReparentInstruction pairing) instructionMember
  · intro element notLoser
    apply HeapView.reparentMany_parent_of_not_loser state.view instructions
      ordered loserNotRoot rankLt sideOrder element
    intro instruction instructionMember
    obtain ⟨pairing, pairingMember, instructionEq⟩ :=
      List.mem_map.mp instructionMember
    subst instruction
    exact notLoser pairing pairingMember
  · intro element notLoser
    apply HeapView.reparentMany_side_of_not_loser state.view instructions
      ordered loserNotRoot rankLt sideOrder element
    intro instruction instructionMember
    obtain ⟨pairing, pairingMember, instructionEq⟩ :=
      List.mem_map.mp instructionMember
    subst instruction
    exact notLoser pairing pairingMember

/-- A shrinking source cannot be any of the allocated growing destinations. -/
theorem destinations_ne_source
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ} {phase : PairingPhase}
    {batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups}
    {state : Lazy.State n}
    (allocation : ArticleBatchDestinationAllocation phase batches state)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound :
      state.toInterface.block? sourceId = some source.toInterface)
    (sourceShrinking : source.mode = .shrinking) :
    ∀ pairing ∈ allocation.matching,
      pairing.destination ≠ sourceId ∧
        ∃ destination,
          state.toInterface.block? pairing.destination = some destination ∧
            destination.mode = .growing ∧
            destination.creator = pairing.winner := by
  intro pairing pairingMember
  obtain ⟨destination, destinationFound, destinationGrowing,
      destinationCreator⟩ :=
    allocation.destinations pairing pairingMember
  constructor
  · intro destinationEq
    rw [destinationEq, sourceFound] at destinationFound
    have blockEq : destination = source.toInterface :=
      Option.some.inj destinationFound.symm
    have sourceGrowing : source.mode = .growing := by
      change source.toInterface.mode = .growing
      rw [← blockEq]
      exact destinationGrowing
    rw [sourceShrinking] at sourceGrowing
    simp at sourceGrowing
  · exact
      ⟨destination, destinationFound, destinationGrowing,
        destinationCreator⟩

/-- An allocated batch can be reused after an unrelated preceding pass.
Stable block identifiers and all growing-placement metadata are unchanged;
only destination payloads may have acquired the preceding losers. -/
noncomputable def transport_after_passAtView
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ} {phase : PairingPhase}
    {batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups}
    {state : Lazy.State n}
    (allocation : ArticleBatchDestinationAllocation phase batches state)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    {preceding : List (Interface.Pairing n)}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceShrinking : source.mode = .shrinking)
    (precedingDestinationsNodup :
      (preceding.map fun pairing => pairing.destination).Nodup)
    (afterView : HeapView n) (sourceIntervalGap : ℤ) :
    ArticleBatchDestinationAllocation phase batches
      (state.passAtView afterView sourceId source preceding
        sourceIntervalGap) := by
  have sourceInterfaceFound :
      state.toInterface.block? sourceId = some source.toInterface := by
    unfold Interface.State.block? Lazy.State.toInterface
    simpa using congrArg (Option.map Lazy.Block.toInterface) sourceFound
  have transported : ∀ pairing ∈ allocation.matching,
      ∃ destination : Lazy.Block n,
        (state.passAtView afterView sourceId source preceding
          sourceIntervalGap).blocks[pairing.destination]? = some destination ∧
        destination.mode = .growing ∧
        destination.creator = pairing.winner ∧
        destination.owner = pairing.winner ∧
        destination.side =
          Splay.Lazy.Canonical.sideOf pairing.winner pairing.loser := by
    intro pairing pairingMember
    obtain ⟨oldBlock, oldFound, oldGrowing, oldOwner, oldSide⟩ :=
      allocation.richDestinations pairing pairingMember
    obtain ⟨interfaceBlock, interfaceFound, _interfaceGrowing,
        interfaceCreator⟩ := allocation.destinations pairing pairingMember
    have oldInterfaceFound : state.toInterface.block?
        pairing.destination = some oldBlock.toInterface := by
      unfold Interface.State.block? Lazy.State.toInterface
      simpa using congrArg (Option.map Lazy.Block.toInterface) oldFound
    have interfaceEq : interfaceBlock = oldBlock.toInterface :=
      Option.some.inj (interfaceFound.symm.trans oldInterfaceFound)
    have oldCreator : oldBlock.creator = pairing.winner := by
      change oldBlock.toInterface.creator = pairing.winner
      rw [← interfaceEq]
      exact interfaceCreator
    have destinationNeSource :=
      (allocation.destinations_ne_source sourceInterfaceFound
        sourceShrinking pairing pairingMember).1
    obtain ⟨destination, destinationFound, modeEq, creatorEq, ownerEq,
        sideEq⟩ :=
      Block.passBlocks_preserves_metadata_of_ne_source state.blocks
        sourceId pairing.destination source preceding sourceIntervalGap
        precedingDestinationsNodup oldFound destinationNeSource
    refine ⟨destination, ?_, modeEq.trans oldGrowing, creatorEq.trans oldCreator,
      ownerEq.trans oldOwner, sideEq.trans oldSide⟩
    simpa [State.passAtView, State.pass] using destinationFound
  refine {
    matching := allocation.matching
    agreement := allocation.agreement
    destinationsNodup := allocation.destinationsNodup
    destinations := ?_
    richDestinations := ?_
  }
  · intro pairing pairingMember
    obtain ⟨destination, found, growing, creator, owner, side⟩ :=
      transported pairing pairingMember
    refine ⟨destination.toInterface, ?_, growing, creator⟩
    unfold Interface.State.block?
    simpa [Lazy.State.toInterface] using
      congrArg (Option.map Lazy.Block.toInterface) found
  · intro pairing pairingMember
    obtain ⟨destination, found, growing, creator, owner, side⟩ :=
      transported pairing pairingMember
    exact ⟨destination, found, growing, owner, side⟩

/-- Every allocated article pair is either already value-valid, or is an
equal-valued good pair whose winner admits the temporary unit decrease from
the manuscript. -/
theorem valueOrder_or_equalCanDecrease
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
    (rankEq : state.view.rank = snapshot.rank) :
    ∀ pairing ∈ allocation.matching,
      state.value pairing.winner + 1 ≤ state.value pairing.loser ∨
        (state.value pairing.winner = state.value pairing.loser ∧
          1 < state.value pairing.winner) := by
  intro pairing pairingMember
  have tuple := geometric.2.2.2 pairing pairingMember
  have rankOrder :
      state.view.rank pairing.winner < state.view.rank pairing.loser := by
    rw [rankEq]
    exact allocation.agreement.rank_lt pairingMember
  exact pairingValueOrder_or_equalCanDecrease valid values
    (List.mem_of_getElem? sourceFound)
    tuple.1.first_mem tuple.1.second_mem rankOrder

/-- Decreasing exactly the good winners is a legal trace and makes every
pair in the batch satisfy the interface's value inequality simultaneously. -/
theorem prepareGoodWinners_of_dichotomy
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ} {phase : PairingPhase}
    {batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups}
    {params : Interface.Parameters} {state : Lazy.State n}
    (allocation : ArticleBatchDestinationAllocation phase batches state)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (geometric : GeometricMatchingValid state sourceId source
      allocation.matching)
    (valid : state.Valid params)
    (dichotomy : ∀ pairing ∈ allocation.matching,
      state.value pairing.winner + 1 ≤ state.value pairing.loser ∨
        (state.value pairing.winner = state.value pairing.loser ∧
          1 < state.value pairing.winner)) :
    Trace params state
        ((articleGoodWinners state allocation.matching).map fun winner =>
          .operation (.valueChange winner .decrease))
        (decreaseEach state
          (articleGoodWinners state allocation.matching)) ∧
      ∀ pairing ∈ allocation.matching,
        (decreaseEach state
              (articleGoodWinners state allocation.matching)).value
              pairing.winner + 1 ≤
          (decreaseEach state
              (articleGoodWinners state allocation.matching)).value
              pairing.loser := by
  have endpointsNodup := geometric.2.1
  have winnersNodup :=
    articleGoodWinners_nodup (state := state) endpointsNodup
  have everyWinnerCanDecrease : ∀ winner ∈
      articleGoodWinners state allocation.matching,
      1 < state.value winner := by
    intro winner winnerMember
    obtain ⟨pairing, goodMember, winnerEq⟩ :=
      List.mem_map.mp winnerMember
    subst winner
    have pairingMember : pairing ∈ allocation.matching :=
      (List.mem_filter.mp goodMember).1
    have equal :
        state.value pairing.winner = state.value pairing.loser := by
      simpa [articleGoodPairings] using
        (List.mem_filter.mp goodMember).2
    rcases dichotomy pairing pairingMember with direct | good
    · omega
    · exact good.2
  constructor
  · exact decreaseEach_trace state _ valid winnersNodup
      everyWinnerCanDecrease
  · intro pairing pairingMember
    have winnerIff := pairingWinner_mem_articleGoodWinners_iff
      (state := state) endpointsNodup pairingMember
    have loserNot := pairingLoser_not_mem_articleGoodWinners
      (state := state) endpointsNodup pairingMember
    by_cases equal :
        state.value pairing.winner = state.value pairing.loser
    · have winnerMember := winnerIff.mpr equal
      rw [decreaseEach_value_of_mem state winnersNodup winnerMember,
        decreaseEach_value_of_not_mem state _ loserNot]
      have canDecrease := everyWinnerCanDecrease pairing.winner winnerMember
      omega
    · have winnerNot :
          pairing.winner ∉ articleGoodWinners state allocation.matching :=
        winnerIff.not.mpr equal
      rw [decreaseEach_value_of_not_mem state _ winnerNot,
        decreaseEach_value_of_not_mem state _ loserNot]
      rcases dichotomy pairing pairingMember with direct | good
      · exact direct
      · exact False.elim (equal good.1)

/-- Stable gap realization supplies the dichotomy consumed by the generic
winner-preparation lemma. -/
theorem prepareGoodWinners
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
    (rankEq : state.view.rank = snapshot.rank) :
    Trace params state
        ((articleGoodWinners state allocation.matching).map fun winner =>
          .operation (.valueChange winner .decrease))
        (decreaseEach state
          (articleGoodWinners state allocation.matching)) ∧
      ∀ pairing ∈ allocation.matching,
        (decreaseEach state
              (articleGoodWinners state allocation.matching)).value
              pairing.winner + 1 ≤
          (decreaseEach state
              (articleGoodWinners state allocation.matching)).value
              pairing.loser := by
  apply allocation.prepareGoodWinners_of_dichotomy geometric valid
  exact allocation.valueOrder_or_equalCanDecrease sourceFound geometric
    valid values rankEq

/-- The geometric matching is unchanged by winner-only value preparation. -/
theorem geometric_after_prepareGoodWinners
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ} {phase : PairingPhase}
    {batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups}
    {state : Lazy.State n}
    (allocation : ArticleBatchDestinationAllocation phase batches state)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (geometric : GeometricMatchingValid state sourceId source
      allocation.matching) :
    GeometricMatchingValid
      (decreaseEach state (articleGoodWinners state allocation.matching))
      sourceId source allocation.matching := by
  refine ⟨geometric.1, geometric.2.1, geometric.2.2.1, ?_⟩
  intro pairing pairingMember
  obtain ⟨adjacent, destinationNe, destination, destinationFound,
      destinationGrowing, destinationCreator⟩ :=
    geometric.2.2.2 pairing pairingMember
  refine ⟨adjacent, destinationNe, destination, ?_, destinationGrowing,
    destinationCreator⟩
  change
    ((decreaseEach state
      (articleGoodWinners state allocation.matching)).blocks.map
        Lazy.Block.toInterface)[pairing.destination]? = some destination
  rw [decreaseEach_blocks]
  exact destinationFound

/-- Complete value-side translation of one retained article batch.

The only remaining premise for `MatchingValid` is the independent
exemption/fraction disjunction.  The returned trace contains one decrease
for every good pairing winner; its final state admits the pass immediately. -/
theorem prepared_matchingValid_of_dichotomy
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ} {phase : PairingPhase}
    {batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups}
    {params : Interface.Parameters} {state : Lazy.State n}
    (allocation : ArticleBatchDestinationAllocation phase batches state)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (geometric : GeometricMatchingValid state sourceId source
      allocation.matching)
    (valid : state.Valid params)
    (dichotomy : ∀ pairing ∈ allocation.matching,
      state.value pairing.winner + 1 ≤ state.value pairing.loser ∨
        (state.value pairing.winner = state.value pairing.loser ∧
          1 < state.value pairing.winner))
    (largeEnough :
      source.passCount < params.exemptPasses ∨
        params.matchingNumerator * source.elements.length ≤
          params.matchingDenominator * allocation.matching.length) :
    Trace params state
        ((articleGoodWinners state allocation.matching).map fun winner =>
          .operation (.valueChange winner .decrease))
        (decreaseEach state
          (articleGoodWinners state allocation.matching)) ∧
      Interface.MatchingValid params
        (decreaseEach state
          (articleGoodWinners state allocation.matching)).toInterface
        sourceId source.toInterface allocation.matching := by
  have preparation := allocation.prepareGoodWinners_of_dichotomy geometric
    valid dichotomy
  refine ⟨preparation.1, ?_⟩
  exact (allocation.geometric_after_prepareGoodWinners geometric).toInterface
    preparation.2 largeEnough

/-- Gap realization is the standard source of the generic value dichotomy. -/
theorem prepared_matchingValid
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
    (rankEq : state.view.rank = snapshot.rank)
    (largeEnough :
      source.passCount < params.exemptPasses ∨
        params.matchingNumerator * source.elements.length ≤
          params.matchingDenominator * allocation.matching.length) :
    Trace params state
        ((articleGoodWinners state allocation.matching).map fun winner =>
          .operation (.valueChange winner .decrease))
        (decreaseEach state
          (articleGoodWinners state allocation.matching)) ∧
      Interface.MatchingValid params
        (decreaseEach state
          (articleGoodWinners state allocation.matching)).toInterface
        sourceId source.toInterface allocation.matching := by
  apply allocation.prepared_matchingValid_of_dichotomy geometric valid
    (allocation.valueOrder_or_equalCanDecrease sourceFound geometric valid
      values rankEq) largeEnough

/-- The preparation followed by the article's `Pass` is now an actual legal
interface execution prefix.  The pass post-state is canonical and needs no
extra validity witness from the caller. -/
theorem prepared_passStep
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
    (rankEq : state.view.rank = snapshot.rank)
    (largeEnough :
      source.passCount < params.exemptPasses ∨
        params.matchingNumerator * source.elements.length ≤
          params.matchingDenominator * allocation.matching.length) :
    let prepared := decreaseEach state
      (articleGoodWinners state allocation.matching)
    ∃ preparation : Trace params state
          ((articleGoodWinners state allocation.matching).map fun winner =>
            .operation (.valueChange winner .decrease)) prepared,
      Interface.Step params prepared.toInterface
        (.pass sourceId allocation.matching)
        (Interface.MatchingValid.afterPass prepared.toInterface sourceId
          source.toInterface allocation.matching) := by
  dsimp only
  obtain ⟨preparation, matchingValid⟩ :=
    allocation.prepared_matchingValid sourceFound geometric valid values
      rankEq largeEnough
  refine ⟨preparation, ?_⟩
  have preparedSourceFound :
      (decreaseEach state
          (articleGoodWinners state allocation.matching)).toInterface.block?
          sourceId = some source.toInterface := by
    change
      ((decreaseEach state
        (articleGoodWinners state allocation.matching)).blocks.map
          Lazy.Block.toInterface)[sourceId]? = some source.toInterface
    rw [decreaseEach_blocks]
    simpa [Interface.State.block?, Lazy.State.toInterface] using
      congrArg (Option.map Lazy.Block.toInterface) sourceFound
  exact matchingValid.afterPass_step preparation.final_valid.toInterface
    preparedSourceFound

/-- The article batch as one genuine rich pass in its post-pairing heap view.

All value and abstract matching obligations are discharged here.  The sole
additional object is `PassAtViewPreservation`, which contains exactly the
post-pairing interval placement and signed-gap facts that must be supplied by
the splay geometry. -/
theorem prepared_richPassStep_of_dichotomy
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
    (valid : state.Valid params)
    (dichotomy : ∀ pairing ∈ allocation.matching,
      state.value pairing.winner + 1 ≤ state.value pairing.loser ∨
        (state.value pairing.winner = state.value pairing.loser ∧
          1 < state.value pairing.winner))
    (largeEnough :
      source.passCount < params.exemptPasses ∨
        params.matchingNumerator * source.elements.length ≤
          params.matchingDenominator * allocation.matching.length)
    (afterView : HeapView n) (sourceIntervalGap : ℤ)
    (preservation :
      PassAtViewPreservation
        (decreaseEach state
          (articleGoodWinners state allocation.matching))
        afterView sourceId source allocation.matching sourceIntervalGap) :
    let winners := articleGoodWinners state allocation.matching
    let prepared := decreaseEach state winners
    let passed := prepared.passAtView afterView sourceId source
      allocation.matching sourceIntervalGap
    ∃ preparation : Trace params state
          (winners.map fun winner =>
            .operation (.valueChange winner .decrease)) prepared,
      Step params prepared (.operation (.pass sourceId allocation.matching))
        passed := by
  dsimp only
  obtain ⟨preparation, matchingValid⟩ :=
    allocation.prepared_matchingValid_of_dichotomy geometric valid dichotomy
      largeEnough
  have preparedSourceFound :
      (decreaseEach state
        (articleGoodWinners state allocation.matching)).blocks[sourceId]? =
        some source := by
    simpa only [decreaseEach_blocks] using sourceFound
  refine ⟨preparation, ?_⟩
  exact preservation.step preparation.final_valid preparedSourceFound
    matchingValid

theorem prepared_richPassStep
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
    (rankEq : state.view.rank = snapshot.rank)
    (largeEnough :
      source.passCount < params.exemptPasses ∨
        params.matchingNumerator * source.elements.length ≤
          params.matchingDenominator * allocation.matching.length)
    (afterView : HeapView n) (sourceIntervalGap : ℤ)
    (preservation : PassAtViewPreservation
      (decreaseEach state (articleGoodWinners state allocation.matching))
      afterView sourceId source allocation.matching sourceIntervalGap) :
    let winners := articleGoodWinners state allocation.matching
    let prepared := decreaseEach state winners
    let passed := prepared.passAtView afterView sourceId source
      allocation.matching sourceIntervalGap
    ∃ preparation : Trace params state
          (winners.map fun winner =>
            .operation (.valueChange winner .decrease)) prepared,
      Step params prepared (.operation (.pass sourceId allocation.matching))
        passed := by
  apply allocation.prepared_richPassStep_of_dichotomy sourceFound geometric
    valid (allocation.valueOrder_or_equalCanDecrease sourceFound geometric
      valid values rankEq) largeEnough afterView sourceIntervalGap preservation

/-- Article-faithful rich macro for one retained pairing batch: decrease all
and only equal-valued winners, execute the visible pass while installing the
post-pairing heap view, and restore those winners.  The endpoint retains the
new block placement and view but has exactly the original value function. -/
theorem richPassTrace_with_goodWinnerRestoration_of_dichotomy
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
    (valid : state.Valid params)
    (dichotomy : ∀ pairing ∈ allocation.matching,
      state.value pairing.winner + 1 ≤ state.value pairing.loser ∨
        (state.value pairing.winner = state.value pairing.loser ∧
          1 < state.value pairing.winner))
    (largeEnough :
      source.passCount < params.exemptPasses ∨
        params.matchingNumerator * source.elements.length ≤
          params.matchingDenominator * allocation.matching.length)
    (afterView : HeapView n) (sourceIntervalGap : ℤ)
    (preservation :
      PassAtViewPreservation
        (decreaseEach state
          (articleGoodWinners state allocation.matching))
        afterView sourceId source allocation.matching sourceIntervalGap) :
    let winners := articleGoodWinners state allocation.matching
    let prepared := decreaseEach state winners
    let passed := prepared.passAtView afterView sourceId source
      allocation.matching sourceIntervalGap
    let restored := increaseEach passed winners
    Trace params state
        ((winners.map fun winner =>
            .operation (.valueChange winner .decrease)) ++
          [.operation (.pass sourceId allocation.matching)] ++
          (winners.map fun winner =>
            .operation (.valueChange winner .increase)))
        restored ∧
      restored.value = state.value := by
  dsimp only
  obtain ⟨preparation, passStep⟩ :=
    allocation.prepared_richPassStep_of_dichotomy sourceFound geometric valid
      dichotomy largeEnough afterView sourceIntervalGap preservation
  let winners := articleGoodWinners state allocation.matching
  let prepared := decreaseEach state winners
  let passed := prepared.passAtView afterView sourceId source
    allocation.matching sourceIntervalGap
  have endpointsNodup := geometric.2.1
  have winnersNodup : winners.Nodup := by
    exact articleGoodWinners_nodup (state := state) endpointsNodup
  have canRestore : ∀ winner ∈ winners,
      passed.value winner < params.valueBound := by
    intro winner winnerMember
    have originalBound := (valid.toInterface.2.1 winner).2
    have originalPositive := (valid.toInterface.2.1 winner).1
    change state.value winner ≤ params.valueBound at originalBound
    change 1 ≤ state.value winner at originalPositive
    change prepared.value winner < params.valueBound
    rw [decreaseEach_value_of_mem state winnersNodup winnerMember]
    omega
  have restoration : Trace params passed
      (winners.map fun winner =>
        .operation (.valueChange winner .increase))
      (increaseEach passed winners) :=
    increaseEach_trace passed winners passStep.after_valid winnersNodup
      canRestore
  have combined := preparation.append (Trace.singleton passStep)
  have complete := combined.append restoration
  constructor
  · simpa only [List.append_assoc] using complete
  · funext queried
    by_cases member : queried ∈ winners
    · rw [increaseEach_value_of_mem passed winnersNodup member]
      change prepared.value queried + 1 = state.value queried
      rw [decreaseEach_value_of_mem state winnersNodup member]
      exact Nat.sub_add_cancel (valid.toInterface.2.1 queried).1
    · rw [increaseEach_value_of_not_mem passed winners member]
      change prepared.value queried = state.value queried
      exact decreaseEach_value_of_not_mem state winners member

theorem richPassTrace_with_goodWinnerRestoration
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
    (rankEq : state.view.rank = snapshot.rank)
    (largeEnough :
      source.passCount < params.exemptPasses ∨
        params.matchingNumerator * source.elements.length ≤
          params.matchingDenominator * allocation.matching.length)
    (afterView : HeapView n) (sourceIntervalGap : ℤ)
    (preservation : PassAtViewPreservation
      (decreaseEach state (articleGoodWinners state allocation.matching))
      afterView sourceId source allocation.matching sourceIntervalGap) :
    let winners := articleGoodWinners state allocation.matching
    let prepared := decreaseEach state winners
    let passed := prepared.passAtView afterView sourceId source
      allocation.matching sourceIntervalGap
    let restored := increaseEach passed winners
    Trace params state
        ((winners.map fun winner =>
            .operation (.valueChange winner .decrease)) ++
          [.operation (.pass sourceId allocation.matching)] ++
          (winners.map fun winner =>
            .operation (.valueChange winner .increase)))
        restored ∧ restored.value = state.value := by
  apply allocation.richPassTrace_with_goodWinnerRestoration_of_dichotomy
    sourceFound geometric valid
    (allocation.valueOrder_or_equalCanDecrease sourceFound geometric valid
      values rankEq) largeEnough afterView sourceIntervalGap preservation

/-- The same rich macro specialized to the constructed reparented heap view.
The shrinking source part of `PassAtViewPreservation` is discharged
automatically; only the non-source destination/untouched block invariant is
left to the top-most-child geometry. -/
theorem richPassTrace_of_reparentedView_of_dichotomy
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
    (valid : state.Valid params)
    (dichotomy : ∀ pairing ∈ allocation.matching,
      state.value pairing.winner + 1 ≤ state.value pairing.loser ∨
        (state.value pairing.winner = state.value pairing.loser ∧
          1 < state.value pairing.winner))
    (largeEnough :
      source.passCount < params.exemptPasses ∨
        params.matchingNumerator * source.elements.length ≤
          params.matchingDenominator * allocation.matching.length)
    (after : BatchReparentedView state.view allocation.matching)
    (otherValid : ∀ sourceIntervalGap,
      ∀ id : Fin
          ((decreaseEach state
            (articleGoodWinners state allocation.matching)).passAtView
              after.view sourceId source allocation.matching
                sourceIntervalGap).blocks.length,
        sourceId ≠ id.val →
          (((decreaseEach state
            (articleGoodWinners state allocation.matching)).passAtView
              after.view sourceId source allocation.matching
                sourceIntervalGap).blocks.get id).StructurallyValid
            after.view
            ((decreaseEach state
              (articleGoodWinners state allocation.matching)).passAtView
                after.view sourceId source allocation.matching
                  sourceIntervalGap).allElements) :
    ∃ sourceIntervalGap,
      sourceIntervalGap = source.intervalGap ∧
      let winners := articleGoodWinners state allocation.matching
      let prepared := decreaseEach state winners
      let passed := prepared.passAtView after.view sourceId source
        allocation.matching sourceIntervalGap
      let restored := increaseEach passed winners
      Trace params state
          ((winners.map fun winner =>
              .operation (.valueChange winner .decrease)) ++
            [.operation (.pass sourceId allocation.matching)] ++
            (winners.map fun winner =>
              .operation (.valueChange winner .increase)))
          restored ∧
        restored.value = state.value := by
  let winners := articleGoodWinners state allocation.matching
  let prepared := decreaseEach state winners
  obtain ⟨preparation, matchingValid⟩ :=
    allocation.prepared_matchingValid_of_dichotomy geometric valid dichotomy
      largeEnough
  have preparedSourceFound : prepared.blocks[sourceId]? = some source := by
    simpa [prepared, winners] using sourceFound
  have preparedGeometric : GeometricMatchingValid prepared sourceId source
      allocation.matching := by
    simpa [prepared, winners] using
      allocation.geometric_after_prepareGoodWinners geometric
  let afterPrepared : BatchReparentedView prepared.view
      allocation.matching := {
    view := after.view
    rank_eq := by simpa [prepared, winners] using after.rank_eq
    root_eq := by simpa [prepared, winners] using after.root_eq
    ordered := after.ordered
    paired_parent := after.paired_parent
    paired_side := after.paired_side
    unpaired_parent := by
      intro element notLoser
      simpa [prepared, winners] using after.unpaired_parent element notLoser
    unpaired_side := by
      intro element notLoser
      simpa [prepared, winners] using after.unpaired_side element notLoser
  }
  have preservation :=
    afterPrepared.passAtViewPreservation_original preparation.final_valid
      preparedSourceFound preparedGeometric matchingValid (by
        intro gap id idNe
        simpa [prepared, winners] using otherValid gap id idNe)
  refine ⟨source.intervalGap, rfl, ?_⟩
  exact allocation.richPassTrace_with_goodWinnerRestoration_of_dichotomy
    sourceFound geometric valid dichotomy largeEnough after.view
    source.intervalGap (by simpa [prepared, winners] using preservation)

theorem richPassTrace_of_reparentedView
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
    (rankEq : state.view.rank = snapshot.rank)
    (largeEnough :
      source.passCount < params.exemptPasses ∨
        params.matchingNumerator * source.elements.length ≤
          params.matchingDenominator * allocation.matching.length)
    (after : BatchReparentedView state.view allocation.matching)
    (otherValid : ∀ sourceIntervalGap,
      ∀ id : Fin
          ((decreaseEach state
            (articleGoodWinners state allocation.matching)).passAtView
              after.view sourceId source allocation.matching
                sourceIntervalGap).blocks.length,
        sourceId ≠ id.val →
          (((decreaseEach state
            (articleGoodWinners state allocation.matching)).passAtView
              after.view sourceId source allocation.matching
                sourceIntervalGap).blocks.get id).StructurallyValid
            after.view
            ((decreaseEach state
              (articleGoodWinners state allocation.matching)).passAtView
                after.view sourceId source allocation.matching
                  sourceIntervalGap).allElements) :
    ∃ sourceIntervalGap,
      sourceIntervalGap = source.intervalGap ∧
      let winners := articleGoodWinners state allocation.matching
      let prepared := decreaseEach state winners
      let passed := prepared.passAtView after.view sourceId source
        allocation.matching sourceIntervalGap
      let restored := increaseEach passed winners
      Trace params state
          ((winners.map fun winner =>
              .operation (.valueChange winner .decrease)) ++
            [.operation (.pass sourceId allocation.matching)] ++
            (winners.map fun winner =>
              .operation (.valueChange winner .increase)))
          restored ∧ restored.value = state.value := by
  apply allocation.richPassTrace_of_reparentedView_of_dichotomy sourceFound
    geometric valid
    (allocation.valueOrder_or_equalCanDecrease sourceFound geometric valid
      values rankEq) largeEnough after otherValid

/-- Article-facing rich macro for one internal pairing batch.  The broad
`otherValid` premise of the lower-level theorem is now derived from exactly
the manuscript's top-most-child geometry and the stable-state
`GrowingTopmost` invariant. -/
theorem richPassTrace_of_topmostReparentedView_of_dichotomy_and_prefixes
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
    (valid : state.Valid params)
    (dichotomy : ∀ pairing ∈ allocation.matching,
      state.value pairing.winner + 1 ≤ state.value pairing.loser ∨
        (state.value pairing.winner = state.value pairing.loser ∧
          1 < state.value pairing.winner))
    (destinationPrefixes : ∀ pairing ∈ allocation.matching,
      ∀ destination : Lazy.Block n,
        state.blocks[pairing.destination]? = some destination →
          ∃ suffix,
            state.view.attachedTopDown state.allElements
                destination.owner destination.side =
              destination.elements ++ suffix)
    (largeEnough :
      source.passCount < params.exemptPasses ∨
        params.matchingNumerator * source.elements.length ≤
          params.matchingDenominator * allocation.matching.length)
    (after : BatchReparentedView state.view allocation.matching)
    (topmost : BatchTopmostGeometry after) :
    ∃ sourceIntervalGap,
      sourceIntervalGap = source.intervalGap ∧
      let winners := articleGoodWinners state allocation.matching
      let prepared := decreaseEach state winners
      let passed := prepared.passAtView after.view sourceId source
        allocation.matching sourceIntervalGap
      let restored := increaseEach passed winners
      Trace params state
          ((winners.map fun winner =>
              .operation (.valueChange winner .decrease)) ++
            [.operation (.pass sourceId allocation.matching)] ++
            (winners.map fun winner =>
              .operation (.valueChange winner .increase)))
          restored ∧
        restored.value = state.value := by
  let winners := articleGoodWinners state allocation.matching
  let prepared := decreaseEach state winners
  obtain ⟨preparation, matchingValid⟩ :=
    allocation.prepared_matchingValid_of_dichotomy geometric valid dichotomy
      largeEnough
  have preparedSourceFound : prepared.blocks[sourceId]? = some source := by
    simpa [prepared, winners] using sourceFound
  have preparedGeometric : GeometricMatchingValid prepared sourceId source
      allocation.matching := by
    simpa [prepared, winners] using
      allocation.geometric_after_prepareGoodWinners geometric
  let preparedAllocation :
      ArticleBatchDestinationAllocation phase batches prepared := {
    matching := allocation.matching
    agreement := allocation.agreement
    destinationsNodup := allocation.destinationsNodup
    destinations := by
      intro pairing pairingMember
      obtain ⟨destination, found, growing, creator⟩ :=
        allocation.destinations pairing pairingMember
      refine ⟨destination, ?_, growing, creator⟩
      simpa [Interface.State.block?, Lazy.State.toInterface, prepared,
        winners] using found
    richDestinations := by
      intro pairing pairingMember
      obtain ⟨destination, found, growing, owner, side⟩ :=
        allocation.richDestinations pairing pairingMember
      refine ⟨destination, ?_, growing, owner, side⟩
      simpa [prepared, winners] using found
  }
  let afterPrepared : BatchReparentedView prepared.view
      preparedAllocation.matching := {
    view := after.view
    rank_eq := by simpa [prepared, winners] using after.rank_eq
    root_eq := by simpa [prepared, winners] using after.root_eq
    ordered := after.ordered
    paired_parent := after.paired_parent
    paired_side := after.paired_side
    unpaired_parent := by
      intro element notLoser
      simpa [preparedAllocation, prepared, winners] using
        after.unpaired_parent element notLoser
    unpaired_side := by
      intro element notLoser
      simpa [preparedAllocation, prepared, winners] using
        after.unpaired_side element notLoser
  }
  have preparedTopmost : BatchTopmostGeometry afterPrepared := by
    simpa [BatchTopmostGeometry, afterPrepared, preparedAllocation, prepared,
      winners] using topmost
  have preparedOtherValid :=
    BatchReparentedView.otherValid_of_topmost preparedAllocation
      afterPrepared preparedTopmost preparation.final_valid
      (by
        intro pairing pairingMember destination destinationFound
        obtain ⟨expected, expectedFound, _expectedGrowing, _owner, _side⟩ :=
          allocation.richDestinations pairing pairingMember
        have preparedExpectedFound :
            prepared.blocks[pairing.destination]? = some expected := by
          simpa [prepared, winners] using expectedFound
        have destinationEq : destination = expected :=
          Option.some.inj (destinationFound.symm.trans preparedExpectedFound)
        subst destination
        obtain ⟨suffix, prefixEq⟩ :=
          destinationPrefixes pairing pairingMember expected expectedFound
        exact ⟨suffix, by
          simpa [prepared, winners, State.allElements] using prefixEq⟩)
      preparedSourceFound
      (by simpa [preparedAllocation] using preparedGeometric)
      (by simpa [preparedAllocation] using matchingValid)
  apply allocation.richPassTrace_of_reparentedView_of_dichotomy sourceFound
    geometric valid dichotomy largeEnough after
  intro sourceIntervalGap id sourceNeId
  simpa [preparedAllocation, afterPrepared, prepared, winners] using
    preparedOtherValid sourceIntervalGap id sourceNeId

/-- Stable states provide the local destination prefixes required by the
article-facing batch macro. -/
theorem richPassTrace_of_topmostReparentedView_of_dichotomy
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
    (valid : state.Valid params)
    (dichotomy : ∀ pairing ∈ allocation.matching,
      state.value pairing.winner + 1 ≤ state.value pairing.loser ∨
        (state.value pairing.winner = state.value pairing.loser ∧
          1 < state.value pairing.winner))
    (growingTopmost : state.GrowingTopmost)
    (largeEnough :
      source.passCount < params.exemptPasses ∨
        params.matchingNumerator * source.elements.length ≤
          params.matchingDenominator * allocation.matching.length)
    (after : BatchReparentedView state.view allocation.matching)
    (topmost : BatchTopmostGeometry after) :
    ∃ sourceIntervalGap,
      sourceIntervalGap = source.intervalGap ∧
      let winners := articleGoodWinners state allocation.matching
      let prepared := decreaseEach state winners
      let passed := prepared.passAtView after.view sourceId source
        allocation.matching sourceIntervalGap
      let restored := increaseEach passed winners
      Trace params state
          ((winners.map fun winner =>
              .operation (.valueChange winner .decrease)) ++
            [.operation (.pass sourceId allocation.matching)] ++
            (winners.map fun winner =>
              .operation (.valueChange winner .increase)))
          restored ∧
        restored.value = state.value := by
  apply allocation.richPassTrace_of_topmostReparentedView_of_dichotomy_and_prefixes
    sourceFound geometric valid dichotomy
  · intro pairing pairingMember destination destinationFound
    obtain ⟨expected, expectedFound, expectedGrowing, _owner, _side⟩ :=
      allocation.richDestinations pairing pairingMember
    have destinationEq : destination = expected :=
      Option.some.inj (destinationFound.symm.trans expectedFound)
    subst destination
    exact BatchReparentedView.growing_attached_prefix
      growingTopmost expectedFound expectedGrowing
  · exact largeEnough
  · exact topmost

theorem richPassTrace_of_topmostReparentedView
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
      sourceIntervalGap = source.intervalGap ∧
      let winners := articleGoodWinners state allocation.matching
      let prepared := decreaseEach state winners
      let passed := prepared.passAtView after.view sourceId source
        allocation.matching sourceIntervalGap
      let restored := increaseEach passed winners
      Trace params state
          ((winners.map fun winner =>
              .operation (.valueChange winner .decrease)) ++
            [.operation (.pass sourceId allocation.matching)] ++
            (winners.map fun winner =>
              .operation (.valueChange winner .increase)))
          restored ∧ restored.value = state.value := by
  apply allocation.richPassTrace_of_topmostReparentedView_of_dichotomy
    sourceFound geometric valid
    (allocation.valueOrder_or_equalCanDecrease sourceFound geometric valid
      values rankEq) growingTopmost largeEnough after topmost

/-- Equivalent article-facing form with only the local symmetric-order
inequality.  The exact top-down update is reconstructed from endpoint
disjointness and the reparented-view laws. -/
theorem richPassTrace_of_outermostReparentedView
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
    (outermost : BatchOutermostOrder state.view allocation.matching) :
    ∃ sourceIntervalGap,
      sourceIntervalGap = source.intervalGap ∧
      let winners := articleGoodWinners state allocation.matching
      let prepared := decreaseEach state winners
      let passed := prepared.passAtView after.view sourceId source
        allocation.matching sourceIntervalGap
      let restored := increaseEach passed winners
      Trace params state
          ((winners.map fun winner =>
              .operation (.valueChange winner .decrease)) ++
            [.operation (.pass sourceId allocation.matching)] ++
            (winners.map fun winner =>
              .operation (.valueChange winner .increase)))
          restored ∧
        restored.value = state.value := by
  apply allocation.richPassTrace_of_topmostReparentedView sourceFound
    geometric valid values growingTopmost rankEq largeEnough after
  exact after.topmostGeometry_of_outermostOrder valid sourceFound geometric
    outermost

/-- The same completed batch macro stated with the standard laminar
BST-to-heap invariant.  This isolates the remaining canonical-geometry lemma
from every lazy-interval and interface concern. -/
theorem richPassTrace_of_nestedChildOrderReparentedView
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
    (nested : state.view.NestedChildOrder) :
    ∃ sourceIntervalGap,
      sourceIntervalGap = source.intervalGap ∧
      let winners := articleGoodWinners state allocation.matching
      let prepared := decreaseEach state winners
      let passed := prepared.passAtView after.view sourceId source
        allocation.matching sourceIntervalGap
      let restored := increaseEach passed winners
      Trace params state
          ((winners.map fun winner =>
              .operation (.valueChange winner .decrease)) ++
            [.operation (.pass sourceId allocation.matching)] ++
            (winners.map fun winner =>
              .operation (.valueChange winner .increase)))
          restored ∧
        restored.value = state.value := by
  apply allocation.richPassTrace_of_outermostReparentedView sourceFound
    geometric valid values growingTopmost rankEq largeEnough after
  exact outermostOrder_of_nestedChildOrder valid sourceFound geometric nested

/-- In the actual pre-splay state, the canonical representation supplies all
structural and geometric premises of the article batch macro. -/
theorem richPassTrace_of_representedReparentedView
    {n key : ℕ} {snapshot : Snapshot n}
    {before : BST 0 n} {eligibleGroups : List ℕ}
    {phase : PairingPhase}
    {batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key eligibleGroups}
    {params : Interface.Parameters} {state : Lazy.State n}
    (allocation : ArticleBatchDestinationAllocation phase batches state)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (geometric : GeometricMatchingValid state sourceId source
      allocation.matching)
    (represents : state.Represents params snapshot before)
    (largeEnough :
      source.passCount < params.exemptPasses ∨
        params.matchingNumerator * source.elements.length ≤
          params.matchingDenominator * allocation.matching.length)
    (after : BatchReparentedView state.view allocation.matching) :
    ∃ sourceIntervalGap,
      sourceIntervalGap = source.intervalGap ∧
      let winners := articleGoodWinners state allocation.matching
      let prepared := decreaseEach state winners
      let passed := prepared.passAtView after.view sourceId source
        allocation.matching sourceIntervalGap
      let restored := increaseEach passed winners
      Trace params state
          ((winners.map fun winner =>
              .operation (.valueChange winner .decrease)) ++
            [.operation (.pass sourceId allocation.matching)] ++
            (winners.map fun winner =>
              .operation (.valueChange winner .increase)))
          restored ∧
        restored.value = state.value := by
  exact allocation.richPassTrace_of_nestedChildOrderReparentedView
    sourceFound geometric represents.valid represents.valuesRealizeGaps
    represents.growingTopmost represents.view_rank_eq largeEnough after
    represents.nestedChildOrder

/-- Article-faithful interface macro for one retained pairing batch:
decrease all and only equal-valued winners, execute one `Pass`, and restore
those winners.  The final value function is exactly the original one; only
the pass block rearrangement remains visible in the state. -/
theorem passTrace_with_goodWinnerRestoration
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
    (rankEq : state.view.rank = snapshot.rank)
    (largeEnough :
      source.passCount < params.exemptPasses ∨
        params.matchingNumerator * source.elements.length ≤
          params.matchingDenominator * allocation.matching.length) :
    let winners := articleGoodWinners state allocation.matching
    let prepared := decreaseEach state winners
    let passed := Interface.MatchingValid.afterPass prepared.toInterface
      sourceId source.toInterface allocation.matching
    let restored := interfaceIncreaseEach passed winners
    Interface.Trace params state.toInterface
        ((winners.map fun winner =>
            .valueChange winner .decrease) ++
          [.pass sourceId allocation.matching] ++
          (winners.map fun winner =>
            .valueChange winner .increase))
        restored ∧
      restored.value = state.value := by
  dsimp only
  obtain ⟨preparation, passStep⟩ :=
    allocation.prepared_passStep sourceFound geometric valid values rankEq
      largeEnough
  have endpointsNodup := geometric.2.1
  have winnersNodup :=
    articleGoodWinners_nodup (state := state) endpointsNodup
  let prepared := decreaseEach state
    (articleGoodWinners state allocation.matching)
  let passed := Interface.MatchingValid.afterPass prepared.toInterface
    sourceId source.toInterface allocation.matching
  have canRestore : ∀ winner ∈
      articleGoodWinners state allocation.matching,
      passed.value winner < params.valueBound := by
    intro winner winnerMember
    have originalBound := (valid.toInterface.2.1 winner).2
    have originalPositive := (valid.toInterface.2.1 winner).1
    change state.value winner ≤ params.valueBound at originalBound
    change 1 ≤ state.value winner at originalPositive
    change prepared.value winner < params.valueBound
    rw [decreaseEach_value_of_mem state winnersNodup winnerMember]
    omega
  have restoration := interfaceIncreaseEach_trace passed
    (articleGoodWinners state allocation.matching)
    passStep.2.2 winnersNodup canRestore
  have preparationInterface : Interface.Trace params state.toInterface
      ((articleGoodWinners state allocation.matching).map fun winner =>
        .valueChange winner .decrease)
      prepared.toInterface := by
    have erased : Lazy.eraseOperations
        ((articleGoodWinners state allocation.matching).map fun winner =>
          Lazy.Event.operation
            (.valueChange winner .decrease)) =
        (articleGoodWinners state allocation.matching).map fun winner =>
          .valueChange winner .decrease := by
      induction articleGoodWinners state allocation.matching with
      | nil => rfl
      | cons winner winners ih =>
          change
            Interface.Operation.valueChange winner .decrease ::
                Lazy.eraseOperations
                  (winners.map fun later => Lazy.Event.operation
                    (.valueChange later .decrease)) =
              Interface.Operation.valueChange winner .decrease ::
                (winners.map fun later => .valueChange later .decrease)
          rw [ih]
    rw [← erased]
    simpa [prepared] using preparation.toInterface
  have passTrace : Interface.Trace params prepared.toInterface
      [.pass sourceId allocation.matching] passed :=
    .cons passStep (.nil passStep.2.2)
  constructor
  · simpa [prepared, passed, List.append_assoc] using
      interfaceTrace_append preparationInterface
        (interfaceTrace_append passTrace restoration)
  · funext queried
    by_cases member :
        queried ∈ articleGoodWinners state allocation.matching
    · rw [interfaceIncreaseEach_value_of_mem passed winnersNodup member]
      change prepared.value queried + 1 = state.value queried
      rw [decreaseEach_value_of_mem state winnersNodup member]
      have positive := (valid.toInterface.2.1 queried).1
      change 1 ≤ state.value queried at positive
      omega
    · rw [interfaceIncreaseEach_value_of_not_mem passed _ member]
      change prepared.value queried = state.value queried
      exact decreaseEach_value_of_not_mem state _ member

end ArticleBatchDestinationAllocation

open ArticleBatchDestinationAllocation

/-- The rich source payload after the first concrete pass is exactly the
ambient order used by the second article batch. -/
theorem ArticleBatchEndpointAgreement.afterPassSource_elements_eq
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ}
    {batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups}
    {source : Lazy.Block n} {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement .first batches matching)
    (intervalGap : ℤ) :
    (source.afterPassSource matching intervalGap).elements =
      batches.firstLosers.foldl List.erase source.elements := by
  change Interface.removeLosers source.elements matching = _
  rw [Interface.removeLosers_eq_foldl]
  rw [← agreement.firstLosers_eq_pairingLosers]

/-- The source of the second article phase is no longer than the lazy
interval immediately before the splay. -/
theorem ArticleBatchEndpointAgreement.afterPassSource_length_le
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ}
    {batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups}
    {source : Lazy.Block n} {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement .first batches matching)
    {elements : List (Interface.Element n)}
    (sourceElements : source.elements = elements)
    (intervalGap : ℤ) :
  (source.afterPassSource matching intervalGap).elements.length ≤
      elements.length := by
  rw [agreement.afterPassSource_elements_eq]
  exact
    (Interface.length_foldl_erase_le source.elements batches.firstLosers).trans_eq
      (congrArg List.length sourceElements)

/-- Supplying only the destination-block facts turns the first retained
endpoint batch into a geometrically valid interface matching. -/
theorem ArticleInternalPairingFractionCertificate.first_geometricMatching
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {state : Lazy.State n} {sourceId : Interface.BlockId}
    {source : Lazy.Block n} {matching : List (Interface.Pairing n)}
    (sourceElements : source.elements = elements)
    (sourceShrinking : source.mode = .shrinking)
    (agreement : ArticleBatchEndpointAgreement .first batches matching)
    (destinationsNodup :
      (matching.map fun pairing => pairing.destination).Nodup)
    (destinations : ∀ pairing ∈ matching,
      pairing.destination ≠ sourceId ∧
        ∃ destination,
          state.toInterface.block? pairing.destination = some destination ∧
            destination.mode = .growing ∧
            destination.creator = pairing.winner) :
    GeometricMatchingValid state sourceId source matching := by
  refine ⟨sourceShrinking, ?_, destinationsNodup, ?_⟩
  · rw [agreement.matchingEndpoints_eq_rows]
    simpa [articleRowSelection] using batches.firstEndpoints_nodup
  · intro pairing pairingMember
    obtain ⟨row, rowMember, endpointAgreement⟩ :=
      agreement.exists_row_of_mem pairingMember
    obtain ⟨winner, loser, rowEq, adjacent⟩ :=
      certificate.retainedFirstBatch_adjacent batches row rowMember
    have pairEq : [winner, loser] =
        [pairing.winner, pairing.loser] := by
      exact rowEq.symm.trans endpointAgreement
    have endpointEq : winner = pairing.winner ∧
        loser = pairing.loser := by simpa using pairEq
    have adjacentConcrete :
        Interface.Adjacent elements pairing.winner pairing.loser := by
      simpa [endpointEq.1, endpointEq.2] using adjacent
    have destinationFacts := destinations pairing pairingMember
    exact ⟨by simpa [sourceElements] using adjacentConcrete,
      destinationFacts.1, destinationFacts.2⟩

/--
The first article batch is geometrically valid after using the canonical
growing-block allocation.  In particular, neither destination identifiers
nor their duplicate-freeness remain caller obligations.
-/
theorem ArticleInternalPairingFractionCertificate.first_geometricMatching_of_allocation
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {state : Lazy.State n} {sourceId : Interface.BlockId}
    {source : Lazy.Block n}
    (allocation :
      ArticleBatchDestinationAllocation .first batches state)
    (sourceFound :
      state.toInterface.block? sourceId = some source.toInterface)
    (sourceElements : source.elements = elements)
    (sourceShrinking : source.mode = .shrinking) :
    GeometricMatchingValid state sourceId source allocation.matching := by
  exact certificate.first_geometricMatching batches sourceElements
    sourceShrinking allocation.agreement allocation.destinationsNodup
    (allocation.destinations_ne_source sourceFound sourceShrinking)

/-- For a nonempty first-phase batch, the manuscript's one-tenth constant
discharges the abstract interface fraction premise. -/
theorem ArticleInternalPairingFractionCertificate.first_matchingFraction_of_nonempty
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {state : Lazy.State n} {source : Lazy.Block n}
    (allocation :
      ArticleBatchDestinationAllocation .first batches state)
    {params : Interface.Parameters}
    (article_fraction :
      10 * params.matchingNumerator ≤ params.matchingDenominator)
    (sourceElements : source.elements = elements)
    (matching_nonempty : allocation.matching ≠ []) :
    params.matchingNumerator * source.elements.length ≤
      params.matchingDenominator * allocation.matching.length := by
  apply certificate.matchingFraction_of_nonempty batches
    allocation.agreement article_fraction
  · simpa [sourceElements]
  · exact matching_nonempty

/-- Supplying the destination-block facts for the state after phase one turns
the second retained endpoint batch into a geometrically valid matching. -/
theorem ArticleInternalPairingFractionCertificate.second_geometricMatching
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {state : Lazy.State n} {sourceId : Interface.BlockId}
    {source : Lazy.Block n} {matching : List (Interface.Pairing n)}
    (sourceElements : source.elements =
      batches.firstLosers.foldl List.erase elements)
    (sourceShrinking : source.mode = .shrinking)
    (agreement : ArticleBatchEndpointAgreement .second batches matching)
    (destinationsNodup :
      (matching.map fun pairing => pairing.destination).Nodup)
    (destinations : ∀ pairing ∈ matching,
      pairing.destination ≠ sourceId ∧
        ∃ destination,
          state.toInterface.block? pairing.destination = some destination ∧
            destination.mode = .growing ∧
            destination.creator = pairing.winner) :
    GeometricMatchingValid state sourceId source matching := by
  refine ⟨sourceShrinking, ?_, destinationsNodup, ?_⟩
  · rw [agreement.matchingEndpoints_eq_rows]
    simpa [articleRowSelection] using batches.secondEndpoints_nodup
  · intro pairing pairingMember
    obtain ⟨row, rowMember, endpointAgreement⟩ :=
      agreement.exists_row_of_mem pairingMember
    obtain ⟨winner, loser, rowEq, adjacent⟩ :=
      certificate.retainedSecondBatch_adjacent batches row rowMember
    have pairEq : [winner, loser] =
        [pairing.winner, pairing.loser] := by
      exact rowEq.symm.trans endpointAgreement
    have endpointEq : winner = pairing.winner ∧
        loser = pairing.loser := by simpa using pairEq
    have adjacentConcrete : Interface.Adjacent
        (batches.firstLosers.foldl List.erase elements)
        pairing.winner pairing.loser := by
      simpa [endpointEq.1, endpointEq.2] using adjacent
    have destinationFacts := destinations pairing pairingMember
    exact ⟨by simpa [sourceElements] using adjacentConcrete,
      destinationFacts.1, destinationFacts.2⟩

/-- Canonically allocated form of the second article batch. -/
theorem ArticleInternalPairingFractionCertificate.second_geometricMatching_of_allocation
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {state : Lazy.State n} {sourceId : Interface.BlockId}
    {source : Lazy.Block n}
    (allocation :
      ArticleBatchDestinationAllocation .second batches state)
    (sourceFound :
      state.toInterface.block? sourceId = some source.toInterface)
    (sourceElements : source.elements =
      batches.firstLosers.foldl List.erase elements)
    (sourceShrinking : source.mode = .shrinking) :
    GeometricMatchingValid state sourceId source allocation.matching := by
  exact certificate.second_geometricMatching batches sourceElements
    sourceShrinking allocation.agreement allocation.destinationsNodup
    (allocation.destinations_ne_source sourceFound sourceShrinking)

/-- The value dichotomy for the second sequential pair is already determined
in the original source interval.  Adjacency is only needed later for the
second pass; here membership of both retained endpoints and their comparison
rank order suffice. -/
theorem ArticleInternalPairingFractionCertificate.second_valueOrder_or_equalCanDecrease
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
    (allocation :
      ArticleBatchDestinationAllocation .second batches state)
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    (rankEq : state.view.rank = snapshot.rank) :
    ∀ pairing ∈ allocation.matching,
      state.value pairing.winner + 1 ≤ state.value pairing.loser ∨
        (state.value pairing.winner = state.value pairing.loser ∧
          1 < state.value pairing.winner) := by
  intro pairing pairingMember
  obtain ⟨row, rowMember, selectedEq⟩ :=
    allocation.agreement.exists_row_of_mem pairingMember
  obtain ⟨winner, firstLoser, secondLoser, candidates, firstEq,
      secondEq, firstAdjacent, secondAdjacent, losersNe, candidatePerm,
      candidateChunk, candidateSegment, firstInBlock, secondInBlock,
      winnerInside, firstInside, secondInside⟩ :=
    certificate.retainedRow_inside batches rowMember
  have pairEq : [winner, secondLoser] =
      [pairing.winner, pairing.loser] :=
    secondEq.symm.trans selectedEq
  have endpointEq : winner = pairing.winner ∧
      secondLoser = pairing.loser := by
    simpa using pairEq
  apply pairingValueOrder_or_equalCanDecrease valid values
    (List.mem_of_getElem? sourceFound)
  · simpa [sourceElements, endpointEq.1] using winnerInside
  · simpa [sourceElements, endpointEq.2] using secondInside
  · rw [rankEq]
    exact allocation.agreement.rank_lt pairingMember

/-- Phase one only erases losers, so the same one-tenth certificate also
discharges the fraction premise for a nonempty second-phase batch. -/
theorem ArticleInternalPairingFractionCertificate.second_matchingFraction_of_nonempty
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {state : Lazy.State n} {source : Lazy.Block n}
    (allocation :
      ArticleBatchDestinationAllocation .second batches state)
    {params : Interface.Parameters}
    (article_fraction :
      10 * params.matchingNumerator ≤ params.matchingDenominator)
    (sourceElements : source.elements =
      batches.firstLosers.foldl List.erase elements)
    (matching_nonempty : allocation.matching ≠ []) :
    params.matchingNumerator * source.elements.length ≤
      params.matchingDenominator * allocation.matching.length := by
  apply certificate.matchingFraction_of_nonempty batches
    allocation.agreement article_fraction
  · rw [sourceElements]
    exact Interface.length_foldl_erase_le elements batches.firstLosers
  · exact matching_nonempty

/-- Source-order form, also applicable to exempt passes. -/
theorem ArticleSourcePairings.first_geometricMatching
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ}
    {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches)
    {state : Lazy.State n} {sourceId : Interface.BlockId}
    {source : Lazy.Block n} {matching : List (Interface.Pairing n)}
    (sourceElements : source.elements = elements)
    (sourceShrinking : source.mode = .shrinking)
    (agreement : ArticleBatchEndpointAgreement .first batches matching)
    (destinationsNodup :
      (matching.map fun pairing => pairing.destination).Nodup)
    (destinations : ∀ pairing ∈ matching,
      pairing.destination ≠ sourceId ∧
        ∃ destination,
          state.toInterface.block? pairing.destination = some destination ∧
            destination.mode = .growing ∧
            destination.creator = pairing.winner) :
    GeometricMatchingValid state sourceId source matching := by
  refine ⟨sourceShrinking, ?_, destinationsNodup, ?_⟩
  · rw [agreement.matchingEndpoints_eq_rows]
    simpa [articleRowSelection] using batches.firstEndpoints_nodup
  · intro pairing pairingMember
    obtain ⟨row, rowMember, endpointAgreement⟩ :=
      agreement.exists_row_of_mem pairingMember
    obtain ⟨winner, loser, rowEq, adjacent⟩ :=
      plan.retainedFirstBatch_adjacent row rowMember
    have pairEq : [winner, loser] =
        [pairing.winner, pairing.loser] := by
      exact rowEq.symm.trans endpointAgreement
    have endpointEq : winner = pairing.winner ∧
        loser = pairing.loser := by simpa using pairEq
    have adjacentConcrete :
        Interface.Adjacent elements pairing.winner pairing.loser := by
      simpa [endpointEq.1, endpointEq.2] using adjacent
    have destinationFacts := destinations pairing pairingMember
    exact ⟨by simpa [sourceElements] using adjacentConcrete,
      destinationFacts.1, destinationFacts.2⟩


/-- Source-order form, also applicable to exempt passes. -/
theorem ArticleSourcePairings.first_geometricMatching_of_allocation
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ}
    {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches)
    {state : Lazy.State n} {sourceId : Interface.BlockId}
    {source : Lazy.Block n}
    (allocation :
      ArticleBatchDestinationAllocation .first batches state)
    (sourceFound :
      state.toInterface.block? sourceId = some source.toInterface)
    (sourceElements : source.elements = elements)
    (sourceShrinking : source.mode = .shrinking) :
    GeometricMatchingValid state sourceId source allocation.matching := by
  exact plan.first_geometricMatching sourceElements
    sourceShrinking allocation.agreement allocation.destinationsNodup
    (allocation.destinations_ne_source sourceFound sourceShrinking)


/-- Source-order form, also applicable to exempt passes. -/
theorem ArticleSourcePairings.second_geometricMatching
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ}
    {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches)
    {state : Lazy.State n} {sourceId : Interface.BlockId}
    {source : Lazy.Block n} {matching : List (Interface.Pairing n)}
    (sourceElements : source.elements =
      batches.firstLosers.foldl List.erase elements)
    (sourceShrinking : source.mode = .shrinking)
    (agreement : ArticleBatchEndpointAgreement .second batches matching)
    (destinationsNodup :
      (matching.map fun pairing => pairing.destination).Nodup)
    (destinations : ∀ pairing ∈ matching,
      pairing.destination ≠ sourceId ∧
        ∃ destination,
          state.toInterface.block? pairing.destination = some destination ∧
            destination.mode = .growing ∧
            destination.creator = pairing.winner) :
    GeometricMatchingValid state sourceId source matching := by
  refine ⟨sourceShrinking, ?_, destinationsNodup, ?_⟩
  · rw [agreement.matchingEndpoints_eq_rows]
    simpa [articleRowSelection] using batches.secondEndpoints_nodup
  · intro pairing pairingMember
    obtain ⟨row, rowMember, endpointAgreement⟩ :=
      agreement.exists_row_of_mem pairingMember
    obtain ⟨winner, loser, rowEq, adjacent⟩ :=
      plan.retainedSecondBatch_adjacent row rowMember
    have pairEq : [winner, loser] =
        [pairing.winner, pairing.loser] := by
      exact rowEq.symm.trans endpointAgreement
    have endpointEq : winner = pairing.winner ∧
        loser = pairing.loser := by simpa using pairEq
    have adjacentConcrete : Interface.Adjacent
        (batches.firstLosers.foldl List.erase elements)
        pairing.winner pairing.loser := by
      simpa [endpointEq.1, endpointEq.2] using adjacent
    have destinationFacts := destinations pairing pairingMember
    exact ⟨by simpa [sourceElements] using adjacentConcrete,
      destinationFacts.1, destinationFacts.2⟩


/-- Source-order form, also applicable to exempt passes. -/
theorem ArticleSourcePairings.second_geometricMatching_of_allocation
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ}
    {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches)
    {state : Lazy.State n} {sourceId : Interface.BlockId}
    {source : Lazy.Block n}
    (allocation :
      ArticleBatchDestinationAllocation .second batches state)
    (sourceFound :
      state.toInterface.block? sourceId = some source.toInterface)
    (sourceElements : source.elements =
      batches.firstLosers.foldl List.erase elements)
    (sourceShrinking : source.mode = .shrinking) :
    GeometricMatchingValid state sourceId source allocation.matching := by
  exact plan.second_geometricMatching sourceElements
    sourceShrinking allocation.agreement allocation.destinationsNodup
    (allocation.destinations_ne_source sourceFound sourceShrinking)


/-- Source-order form, also applicable to exempt passes. -/
theorem ArticleSourcePairings.second_valueOrder_or_equalCanDecrease
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ}
    {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches)
    {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (allocation :
      ArticleBatchDestinationAllocation .second batches state)
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    (rankEq : state.view.rank = snapshot.rank) :
    ∀ pairing ∈ allocation.matching,
      state.value pairing.winner + 1 ≤ state.value pairing.loser ∨
        (state.value pairing.winner = state.value pairing.loser ∧
          1 < state.value pairing.winner) := by
  intro pairing pairingMember
  obtain ⟨row, rowMember, selectedEq⟩ :=
    allocation.agreement.exists_row_of_mem pairingMember
  obtain ⟨winner, firstLoser, secondLoser, candidates, firstEq,
      secondEq, firstAdjacent, secondAdjacent, losersNe, candidatePerm,
      candidateChunk, candidateSegment, firstInBlock, secondInBlock,
      winnerInside, firstInside, secondInside⟩ :=
    plan.row_inside rowMember
  have pairEq : [winner, secondLoser] =
      [pairing.winner, pairing.loser] :=
    secondEq.symm.trans selectedEq
  have endpointEq : winner = pairing.winner ∧
      secondLoser = pairing.loser := by
    simpa using pairEq
  apply pairingValueOrder_or_equalCanDecrease valid values
    (List.mem_of_getElem? sourceFound)
  · simpa [sourceElements, endpointEq.1] using winnerInside
  · simpa [sourceElements, endpointEq.2] using secondInside
  · rw [rankEq]
    exact allocation.agreement.rank_lt pairingMember


theorem ArticleSourcePairings.exists_twoPhaseRichPassTrace_of_allocations_and_outermost
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ}
    {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches)
    {params : Interface.Parameters} {state : Lazy.State n}
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (sourceShrinking : source.mode = .shrinking)
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    (complete : state.Complete)
    (oneGrowing : state.OneGrowingPerSide)
    (growingTopmost : state.GrowingTopmost)
    (rankEq : state.view.rank = snapshot.rank)
    (ordered : state.view.HeapOrdered)
    (firstAllocation :
      ArticleBatchDestinationAllocation .first batches state)
    (originalSecondAllocation :
      ArticleBatchDestinationAllocation .second batches state)
    (admissible : source.passCount + 1 < params.exemptPasses ∨
      params.matchingNumerator * source.elements.length ≤
        params.matchingDenominator * firstAllocation.matching.length)
    (firstOutermost :
      BatchOutermostOrder state.view firstAllocation.matching)
    (originalSecondOutermost :
      BatchOutermostOrder state.view originalSecondAllocation.matching) :
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
                sourceId secondSource secondAllocation.matching
                  secondIntervalGap
              let final := increaseEach secondPassed secondWinners
              Trace params state
                  (articlePairingPassEvents state sourceId
                      firstAllocation.matching ++
                    articlePairingPassEvents middle sourceId
                      secondAllocation.matching)
                  final ∧
                final.Complete ∧
                final.OneGrowingPerSide ∧
                final.GrowingTopmost ∧
                final.view.HeapOrdered ∧
                final.value = state.value := by
  have sourceInterfaceFound : state.toInterface.block? sourceId =
      some source.toInterface := by
    unfold Interface.State.block? Lazy.State.toInterface
    simpa using congrArg (Option.map Lazy.Block.toInterface) sourceFound
  have firstGeometric :=
    plan.first_geometricMatching_of_allocation firstAllocation
      sourceInterfaceFound sourceElements sourceShrinking
  obtain ⟨afterFirst⟩ := firstAllocation.exists_reparentedView sourceFound
    firstGeometric valid rankEq ordered
  have firstTopmost := afterFirst.topmostGeometry_of_outermostOrder valid
    sourceFound firstGeometric firstOutermost
  have firstAdmissible : source.passCount < params.exemptPasses ∨
      params.matchingNumerator * source.elements.length ≤
        params.matchingDenominator * firstAllocation.matching.length := by
    rcases admissible with exempt | fraction
    · exact Or.inl (by omega)
    · exact Or.inr fraction
  obtain ⟨firstIntervalGap, firstIntervalGapEq, firstTrace,
      firstValueEq⟩ :=
    firstAllocation.richPassTrace_of_topmostReparentedView sourceFound
      firstGeometric valid values growingTopmost rankEq firstAdmissible
      afterFirst firstTopmost
  refine ⟨afterFirst, firstIntervalGap, firstIntervalGapEq, ?_⟩
  dsimp only
  let firstWinners := articleGoodWinners state firstAllocation.matching
  let firstPrepared := decreaseEach state firstWinners
  let firstPassed := firstPrepared.passAtView afterFirst.view sourceId source
    firstAllocation.matching firstIntervalGap
  let middle := increaseEach firstPassed firstWinners
  let secondSource := source.afterPassSource firstAllocation.matching
    firstIntervalGap
  have firstDichotomy := firstAllocation.valueOrder_or_equalCanDecrease
    sourceFound firstGeometric valid values rankEq
  obtain ⟨firstPreparation, firstMatchingValid⟩ :=
    firstAllocation.prepared_matchingValid_of_dichotomy firstGeometric valid
      firstDichotomy firstAdmissible
  have firstPreparedSourceFound :
      firstPrepared.blocks[sourceId]? = some source := by
    simpa [firstPrepared, firstWinners] using sourceFound
  have firstPreparedGeometric : GeometricMatchingValid firstPrepared sourceId
      source firstAllocation.matching := by
    simpa [firstPrepared, firstWinners] using
      firstAllocation.geometric_after_prepareGoodWinners firstGeometric
  let firstPreparedAllocation :
      ArticleBatchDestinationAllocation .first batches firstPrepared :=
    firstAllocation.transport_blocks_eq (by
      simp [firstPrepared, firstWinners])
  let secondPreparedAllocation :
      ArticleBatchDestinationAllocation .second batches firstPrepared :=
    originalSecondAllocation.transport_blocks_eq (by
      simp [firstPrepared, firstWinners])
  let afterFirstPrepared : BatchReparentedView firstPrepared.view
      firstPreparedAllocation.matching := {
    view := afterFirst.view
    rank_eq := by
      simpa [firstPreparedAllocation, firstPrepared, firstWinners] using
        afterFirst.rank_eq
    root_eq := by
      simpa [firstPreparedAllocation, firstPrepared, firstWinners] using
        afterFirst.root_eq
    ordered := afterFirst.ordered
    paired_parent := afterFirst.paired_parent
    paired_side := afterFirst.paired_side
    unpaired_parent := by
      intro element notLoser
      simpa [firstPreparedAllocation, firstPrepared, firstWinners] using
        afterFirst.unpaired_parent element notLoser
    unpaired_side := by
      intro element notLoser
      simpa [firstPreparedAllocation, firstPrepared, firstWinners] using
        afterFirst.unpaired_side element notLoser
  }
  have firstPreparedTopmost : BatchTopmostGeometry afterFirstPrepared := by
    unfold BatchTopmostGeometry
    intro pairing pairingMember
    change pairing ∈ firstAllocation.matching at pairingMember
    have topmostEq := firstTopmost pairing pairingMember
    simpa [afterFirstPrepared, firstPrepared, firstWinners] using topmostEq
  have firstPreparedOneGrowing : firstPrepared.OneGrowingPerSide := by
    rw [State.OneGrowingPerSide, decreaseEach_blocks]
    exact oneGrowing
  have firstPreparedComplete : firstPrepared.Complete := by
    rw [State.Complete]
    simpa only [State.Complete, firstPrepared, State.allElements,
      decreaseEach_blocks, decreaseEach_view] using complete
  have firstPreparedGrowingTopmost : firstPrepared.GrowingTopmost := by
    rw [State.GrowingTopmost, decreaseEach_blocks, decreaseEach_view]
    exact growingTopmost
  have firstPassedComplete : firstPassed.Complete := by
    apply afterFirstPrepared.complete_after_pass firstPreparedComplete
      firstPreparedSourceFound
    · change Interface.MatchingValid params firstPrepared.toInterface
        sourceId source.toInterface firstAllocation.matching
      exact firstMatchingValid
  have firstPassedOneGrowing : firstPassed.OneGrowingPerSide := by
    exact State.OneGrowingPerSide.passAtView firstPreparedOneGrowing
      afterFirst.view sourceId source firstAllocation.matching firstIntervalGap
      firstPreparedSourceFound
  have firstPassedGrowingTopmost : firstPassed.GrowingTopmost := by
    apply afterFirstPrepared.growingTopmost_after_topmostPass
      firstPreparedAllocation firstPreparedSourceFound sourceShrinking
      firstPreparation.final_valid firstPreparedComplete
      firstPreparedOneGrowing firstPreparedGrowingTopmost
    · change GeometricMatchingValid firstPrepared sourceId source
        firstAllocation.matching
      exact firstPreparedGeometric
    · exact firstPreparedTopmost
    · change Interface.MatchingValid params firstPrepared.toInterface
        sourceId source.toInterface firstAllocation.matching
      exact firstMatchingValid
  have middleComplete : middle.Complete := by
    rw [State.Complete]
    simpa only [State.Complete, middle, State.allElements,
      increaseEach_blocks, increaseEach_view] using firstPassedComplete
  have middleOneGrowing : middle.OneGrowingPerSide := by
    rw [State.OneGrowingPerSide, increaseEach_blocks]
    exact firstPassedOneGrowing
  have middleGrowingTopmost : middle.GrowingTopmost := by
    rw [State.GrowingTopmost, increaseEach_blocks, increaseEach_view]
    exact firstPassedGrowingTopmost
  let secondPassedAllocation :=
    secondPreparedAllocation.transport_after_passAtView
      firstPreparedSourceFound sourceShrinking
      firstAllocation.destinationsNodup afterFirst.view firstIntervalGap
  let secondAllocation :
      ArticleBatchDestinationAllocation .second batches middle :=
    secondPassedAllocation.transport_blocks_eq (by
      simp [middle, firstPassed, firstWinners])
  have middleSourceFound : middle.blocks[sourceId]? = some secondSource := by
    change (increaseEach firstPassed firstWinners).blocks[sourceId]? = _
    rw [increaseEach_blocks]
    change (Block.passBlocks firstPrepared.blocks sourceId source
      firstAllocation.matching firstIntervalGap)[sourceId]? = _
    apply Block.passBlocks_source_getElem?
    · exact firstPreparedSourceFound
    · intro pairing pairingMember
      exact (firstPreparedGeometric.2.2.2 pairing pairingMember).2.1
  have secondSourceElements : secondSource.elements =
      batches.firstLosers.foldl List.erase elements := by
    simpa [secondSource, sourceElements] using
      firstAllocation.agreement.afterPassSource_elements_eq
        (source := source) firstIntervalGap
  have middleSourceInterfaceFound : middle.toInterface.block? sourceId =
      some secondSource.toInterface := by
    unfold Interface.State.block? Lazy.State.toInterface
    simpa using congrArg (Option.map Lazy.Block.toInterface) middleSourceFound
  have secondGeometric :=
    plan.second_geometricMatching_of_allocation
      secondAllocation middleSourceInterfaceFound secondSourceElements
      (by
        change source.mode = .shrinking
        exact sourceShrinking)
  have middleValid : middle.Valid params := firstTrace.final_valid
  have middleRankEq : middle.view.rank = snapshot.rank := by
    calc
      middle.view.rank = afterFirst.view.rank := by
        simp [middle, firstPassed, firstPrepared, firstWinners]
      _ = state.view.rank := afterFirst.rank_eq
      _ = snapshot.rank := rankEq
  have middleOrdered : middle.view.HeapOrdered := by
    have middleViewEq : middle.view = afterFirst.view := by
      simp [middle, firstPassed, firstPrepared, firstWinners]
    rw [middleViewEq]
    intro element owner parentEq
    exact afterFirst.ordered parentEq
  obtain ⟨afterSecond⟩ := secondAllocation.exists_reparentedView
    middleSourceFound secondGeometric middleValid middleRankEq middleOrdered
  have secondBaseOutermost :
      BatchOutermostOrder state.view secondAllocation.matching := by
    change BatchOutermostOrder state.view
      originalSecondAllocation.matching
    exact originalSecondOutermost
  have secondOutermost := afterFirst.secondOutermostOrder_after_first
    plan sourceFound sourceElements valid firstAllocation
      firstGeometric secondAllocation secondBaseOutermost
  have secondOutermostMiddle :
      BatchOutermostOrder middle.view secondAllocation.matching := by
    have middleViewEq : middle.view = afterFirst.view := by
      simp [middle, firstPassed, firstPrepared, firstWinners]
    rw [middleViewEq]
    exact secondOutermost
  have secondTopmost := afterSecond.topmostGeometry_of_outermostOrder
    middleValid middleSourceFound secondGeometric secondOutermostMiddle
  have originalSecondDichotomy :=
    plan.second_valueOrder_or_equalCanDecrease
      originalSecondAllocation sourceFound sourceElements valid values rankEq
  have secondDichotomy : ∀ pairing ∈ secondAllocation.matching,
      middle.value pairing.winner + 1 ≤ middle.value pairing.loser ∨
        (middle.value pairing.winner = middle.value pairing.loser ∧
          1 < middle.value pairing.winner) := by
    intro pairing pairingMember
    have originalMember : pairing ∈ originalSecondAllocation.matching := by
      change pairing ∈ originalSecondAllocation.matching at pairingMember ⊢
      exact pairingMember
    rw [firstValueEq]
    exact originalSecondDichotomy pairing originalMember
  have passedDestinationPrefixes :=
    afterFirstPrepared.destinationPrefixes_after_topmostPass
      firstPreparedAllocation secondPreparedAllocation
      firstPreparedSourceFound firstPreparation.final_valid
      firstPreparedOneGrowing firstPreparedGrowingTopmost
      (by
        change GeometricMatchingValid firstPrepared sourceId source
          firstAllocation.matching
        exact firstPreparedGeometric)
      firstPreparedTopmost
      (by
        change Interface.MatchingValid params firstPrepared.toInterface
          sourceId source.toInterface firstAllocation.matching
        exact firstMatchingValid)
      firstIntervalGap
  have secondDestinationPrefixes : ∀ pairing ∈ secondAllocation.matching,
      ∀ destination : Lazy.Block n,
        middle.blocks[pairing.destination]? = some destination →
          ∃ suffix,
            middle.view.attachedTopDown middle.allElements
                destination.owner destination.side =
              destination.elements ++ suffix := by
    intro pairing pairingMember destination destinationFound
    have preparedMember : pairing ∈ secondPreparedAllocation.matching := by
      change pairing ∈ originalSecondAllocation.matching at pairingMember ⊢
      exact pairingMember
    have passedFound : firstPassed.blocks[pairing.destination]? =
        some destination := by
      simpa [middle, firstWinners] using destinationFound
    obtain ⟨suffix, prefixEq⟩ := passedDestinationPrefixes pairing
      preparedMember destination passedFound
    change firstPassed.view.attachedTopDown firstPassed.allElements
        destination.owner destination.side =
      destination.elements ++ suffix at prefixEq
    exact ⟨suffix, by
      simpa [middle, firstWinners, State.allElements] using prefixEq⟩
  have secondAdmissible : secondSource.passCount < params.exemptPasses ∨
      params.matchingNumerator * secondSource.elements.length ≤
        params.matchingDenominator * secondAllocation.matching.length := by
    rcases admissible with exempt | fraction
    · exact Or.inl exempt
    · apply Or.inr
      have lengthLe := firstAllocation.agreement.afterPassSource_length_le (source := source) rfl firstIntervalGap
      have matchingLength : secondAllocation.matching.length = firstAllocation.matching.length := by
        rw [secondAllocation.agreement.matching_length_eq_eligibleGroups_length,
          firstAllocation.agreement.matching_length_eq_eligibleGroups_length]
      rw [matchingLength]
      exact (Nat.mul_le_mul_left params.matchingNumerator lengthLe).trans fraction
  obtain ⟨secondPreparation, secondMatchingValid⟩ :=
    secondAllocation.prepared_matchingValid_of_dichotomy secondGeometric
      middleValid secondDichotomy secondAdmissible
  let secondWinners := articleGoodWinners middle secondAllocation.matching
  let secondPrepared := decreaseEach middle secondWinners
  have secondPreparedSourceFound :
      secondPrepared.blocks[sourceId]? = some secondSource := by
    simpa [secondPrepared, secondWinners] using middleSourceFound
  have secondPreparedGeometric : GeometricMatchingValid secondPrepared
      sourceId secondSource secondAllocation.matching := by
    simpa [secondPrepared, secondWinners] using
      secondAllocation.geometric_after_prepareGoodWinners secondGeometric
  let secondPreparedAllocation :
      ArticleBatchDestinationAllocation .second batches secondPrepared :=
    secondAllocation.transport_blocks_eq (by
      simp [secondPrepared, secondWinners])
  let afterSecondPrepared : BatchReparentedView secondPrepared.view
      secondPreparedAllocation.matching := {
    view := afterSecond.view
    rank_eq := by
      simpa [secondPreparedAllocation, secondPrepared, secondWinners] using
        afterSecond.rank_eq
    root_eq := by
      simpa [secondPreparedAllocation, secondPrepared, secondWinners] using
        afterSecond.root_eq
    ordered := afterSecond.ordered
    paired_parent := afterSecond.paired_parent
    paired_side := afterSecond.paired_side
    unpaired_parent := by
      intro element notLoser
      simpa [secondPreparedAllocation, secondPrepared, secondWinners] using
        afterSecond.unpaired_parent element notLoser
    unpaired_side := by
      intro element notLoser
      simpa [secondPreparedAllocation, secondPrepared, secondWinners] using
        afterSecond.unpaired_side element notLoser
  }
  have secondPreparedTopmost : BatchTopmostGeometry afterSecondPrepared := by
    unfold BatchTopmostGeometry
    intro pairing pairingMember
    change pairing ∈ secondAllocation.matching at pairingMember
    have topmostEq := secondTopmost pairing pairingMember
    simpa [afterSecondPrepared, secondPrepared, secondWinners] using topmostEq
  have secondPreparedComplete : secondPrepared.Complete := by
    rw [State.Complete]
    simpa only [State.Complete, secondPrepared, State.allElements,
      decreaseEach_blocks, decreaseEach_view] using middleComplete
  have secondPreparedOneGrowing : secondPrepared.OneGrowingPerSide := by
    rw [State.OneGrowingPerSide, decreaseEach_blocks]
    exact middleOneGrowing
  have secondPreparedGrowingTopmost : secondPrepared.GrowingTopmost := by
    rw [State.GrowingTopmost, decreaseEach_blocks, decreaseEach_view]
    exact middleGrowingTopmost
  obtain ⟨secondIntervalGap, secondIntervalGapEq, secondTrace,
      secondValueEq⟩ :=
    secondAllocation.richPassTrace_of_topmostReparentedView_of_dichotomy_and_prefixes
      middleSourceFound secondGeometric middleValid secondDichotomy
      secondDestinationPrefixes secondAdmissible afterSecond
      secondTopmost
  let secondPassed := secondPrepared.passAtView afterSecond.view sourceId
    secondSource secondAllocation.matching secondIntervalGap
  let final := increaseEach secondPassed secondWinners
  have secondPassedComplete : secondPassed.Complete := by
    apply afterSecondPrepared.complete_after_pass secondPreparedComplete
      secondPreparedSourceFound
    · change Interface.MatchingValid params secondPrepared.toInterface
        sourceId secondSource.toInterface secondAllocation.matching
      exact secondMatchingValid
  have secondPassedOneGrowing : secondPassed.OneGrowingPerSide := by
    exact State.OneGrowingPerSide.passAtView secondPreparedOneGrowing
      afterSecond.view sourceId secondSource secondAllocation.matching
      secondIntervalGap secondPreparedSourceFound
  have secondPassedGrowingTopmost : secondPassed.GrowingTopmost := by
    apply afterSecondPrepared.growingTopmost_after_topmostPass
      secondPreparedAllocation secondPreparedSourceFound
    · change source.mode = .shrinking
      exact sourceShrinking
    · exact secondPreparation.final_valid
    · exact secondPreparedComplete
    · exact secondPreparedOneGrowing
    · exact secondPreparedGrowingTopmost
    · change GeometricMatchingValid secondPrepared sourceId secondSource
        secondAllocation.matching
      exact secondPreparedGeometric
    · exact secondPreparedTopmost
    · change Interface.MatchingValid params secondPrepared.toInterface
        sourceId secondSource.toInterface secondAllocation.matching
      exact secondMatchingValid
  have finalComplete : final.Complete := by
    rw [State.Complete]
    simpa only [State.Complete, final, State.allElements,
      increaseEach_blocks, increaseEach_view] using secondPassedComplete
  have finalOneGrowing : final.OneGrowingPerSide := by
    rw [State.OneGrowingPerSide, increaseEach_blocks]
    exact secondPassedOneGrowing
  have finalGrowingTopmost : final.GrowingTopmost := by
    rw [State.GrowingTopmost, increaseEach_blocks, increaseEach_view]
    exact secondPassedGrowingTopmost
  have finalOrdered : final.view.HeapOrdered := by
    have viewEq : final.view = afterSecond.view := by
      simp [final, secondPassed]
    rw [viewEq]
    intro element owner parentEq
    exact afterSecond.ordered parentEq
  have secondIntervalGapEqSource :
      secondIntervalGap = source.intervalGap := by
    exact secondIntervalGapEq.trans (by
      change firstIntervalGap = source.intervalGap
      exact firstIntervalGapEq)
  refine ⟨firstTrace.final_valid, firstValueEq, secondAllocation, afterSecond,
    secondIntervalGap,
    secondIntervalGapEqSource, ?_⟩
  refine ⟨?_, finalComplete, finalOneGrowing, finalGrowingTopmost,
    finalOrdered, ?_⟩
  · simpa [articlePairingPassEvents, List.append_assoc, final, secondPassed,
      secondPrepared, secondWinners] using
      firstTrace.append secondTrace
  · exact secondValueEq.trans firstValueEq


/-- The original unbroken-source API supplies the admissibility proof from
its quantitative fraction certificate. -/
theorem ArticleInternalPairingFractionCertificate.exists_twoPhaseRichPassTrace_of_allocations_and_outermost
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
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    (complete : state.Complete)
    (oneGrowing : state.OneGrowingPerSide)
    (growingTopmost : state.GrowingTopmost)
    (rankEq : state.view.rank = snapshot.rank)
    (ordered : state.view.HeapOrdered)
    (articleFraction :
      10 * params.matchingNumerator ≤ params.matchingDenominator)
    (groupsNonempty : certificate.fraction.groups ≠ [])
    (firstAllocation :
      ArticleBatchDestinationAllocation .first batches state)
    (originalSecondAllocation :
      ArticleBatchDestinationAllocation .second batches state)
    (firstOutermost :
      BatchOutermostOrder state.view firstAllocation.matching)
    (originalSecondOutermost :
      BatchOutermostOrder state.view originalSecondAllocation.matching) :
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
                sourceId secondSource secondAllocation.matching
                  secondIntervalGap
              let final := increaseEach secondPassed secondWinners
              Trace params state
                  (articlePairingPassEvents state sourceId
                      firstAllocation.matching ++
                    articlePairingPassEvents middle sourceId
                      secondAllocation.matching)
                  final ∧
                final.Complete ∧
                final.OneGrowingPerSide ∧
                final.GrowingTopmost ∧
                final.view.HeapOrdered ∧
                final.value = state.value := by
  have firstNonempty : firstAllocation.matching ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [firstAllocation.agreement.matching_length_eq_eligibleGroups_length]
    exact Nat.pos_of_ne_zero (by simpa using groupsNonempty)
  have fraction := certificate.first_matchingFraction_of_nonempty batches firstAllocation
    articleFraction sourceElements firstNonempty
  exact (certificate.sourcePairings batches).exists_twoPhaseRichPassTrace_of_allocations_and_outermost
    sourceFound sourceElements sourceShrinking valid values complete oneGrowing growingTopmost
    rankEq ordered firstAllocation originalSecondAllocation (Or.inr fraction)
    firstOutermost originalSecondOutermost

/-- Public proposition exposing the complete two-phase article macro while
hiding the auxiliary pre-pass allocation used to construct its persistent
destination identifiers. -/
def ArticleRetainedPairingBatches.TwoPhaseRichPassTrace
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
            let final := increaseEach secondPassed secondWinners
            Trace params state
                (articlePairingPassEvents state sourceId
                    firstAllocation.matching ++
                  articlePairingPassEvents middle sourceId
                    secondAllocation.matching)
                final ∧
              final.Complete ∧
              final.OneGrowingPerSide ∧
              final.GrowingTopmost ∧
              final.view.HeapOrdered ∧
              final.value = state.value

/- The fraction-certificate specialization has the same trace proposition. -/
def ArticleInternalPairingFractionCertificate.TwoPhaseRichPassTrace
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
            let final := increaseEach secondPassed secondWinners
            Trace params state
                (articlePairingPassEvents state sourceId
                    firstAllocation.matching ++
                  articlePairingPassEvents middle sourceId
                    secondAllocation.matching)
                final ∧
              final.Complete ∧
              final.OneGrowingPerSide ∧
              final.GrowingTopmost ∧
              final.view.HeapOrdered ∧
              final.value = state.value

/-- A represented stable state automatically supplies both growing-block
allocations and every canonical heap invariant required by the two sequential
article pairings. -/
theorem ArticleInternalPairingFractionCertificate.exists_twoPhaseRichPassTrace
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {params : Interface.Parameters} {state : Lazy.State n}
    (represents : state.Represents params snapshot before)
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceElements : source.elements = elements)
    (sourceShrinking : source.mode = .shrinking)
    (articleFraction :
      10 * params.matchingNumerator ≤ params.matchingDenominator)
    (groupsNonempty : certificate.fraction.groups ≠ []) :
    ∃ firstAllocation :
        ArticleBatchDestinationAllocation .first batches state,
      certificate.TwoPhaseRichPassTrace batches params state sourceId source
        firstAllocation := by
  obtain ⟨firstAllocation⟩ := batches.exists_destinationAllocation .first
    state represents.valid represents.oneGrowingPerSide
  obtain ⟨secondAllocation⟩ := batches.exists_destinationAllocation .second
    state represents.valid represents.oneGrowingPerSide
  have firstGeometric :=
    certificate.first_geometricMatching_of_allocation batches firstAllocation
      (by
        unfold Interface.State.block? Lazy.State.toInterface
        simpa using congrArg (Option.map Lazy.Block.toInterface) sourceFound)
      sourceElements sourceShrinking
  have firstOutermost := outermostOrder_of_nestedChildOrder represents.valid
    sourceFound firstGeometric represents.nestedChildOrder
  have secondOutermost :=
    articleSecondOutermostOrder_of_nestedChildOrder certificate batches
      sourceFound sourceElements represents.valid represents.nestedChildOrder
      secondAllocation
  refine ⟨firstAllocation, ?_⟩
  unfold TwoPhaseRichPassTrace
  exact certificate.exists_twoPhaseRichPassTrace_of_allocations_and_outermost
    batches
    sourceFound sourceElements sourceShrinking represents.valid
    represents.valuesRealizeGaps represents.complete represents.oneGrowingPerSide
    represents.growingTopmost represents.view_rank_eq represents.heapOrdered
    articleFraction groupsNonempty firstAllocation secondAllocation
    firstOutermost secondOutermost

end Splay.Accounting
