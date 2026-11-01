import Splay.Interface.History
import Mathlib.Algebra.Order.Ring.Pow
import Lean.Elab.Tactic.Omega

namespace Splay.Interface

/-- The loser selected by each pairing, in matching order. -/
def pairingLosers {n : ℕ} (matching : List (Pairing n)) :
    List (Element n) :=
  matching.map Pairing.loser

/-- Pairing losers form a sublist of the matching's flattened element list. -/
theorem pairingLosers_sublist {n : ℕ} (matching : List (Pairing n)) :
    (pairingLosers matching).Sublist
      (matching.flatMap fun pairing => [pairing.winner, pairing.loser]) := by
  induction matching with
  | nil =>
      exact .slnil
  | cons pairing matching ih =>
      exact (ih.cons_cons pairing.loser).cons pairing.winner

/-- Disjoint matching elements imply, in particular, distinct losers. -/
theorem pairingLosers_nodup {n : ℕ} {matching : List (Pairing n)}
    (matchingNodup :
      (matching.flatMap fun pairing =>
        [pairing.winner, pairing.loser]).Nodup) :
    (pairingLosers matching).Nodup :=
  (pairingLosers_sublist matching).nodup matchingNodup

namespace Adjacent

/-- The first endpoint of an adjacent pair belongs to the block. -/
theorem first_mem {α : Type*} {elements : List α} {first second : α}
    (adjacent : Adjacent elements first second) :
    first ∈ elements := by
  obtain ⟨front, back, ordered | reversed⟩ := adjacent
  · rw [ordered]
    simp
  · rw [reversed]
    simp

/-- The second endpoint of an adjacent pair belongs to the block. -/
theorem second_mem {α : Type*} {elements : List α} {first second : α}
    (adjacent : Adjacent elements first second) :
    second ∈ elements := by
  obtain ⟨front, back, ordered | reversed⟩ := adjacent
  · rw [ordered]
    simp
  · rw [reversed]
    simp

end Adjacent

/-- Repeated erasure can only shorten a list.  Unlike the exact balance
lemma below, this monotone form needs neither distinctness nor membership of
the requested removals. -/
theorem length_foldl_erase_le {α : Type*} [BEq α]
    (elements removals : List α) :
    (removals.foldl (fun remaining element =>
      remaining.erase element) elements).length ≤ elements.length := by
  induction removals generalizing elements with
  | nil => simp
  | cons removal removals ih =>
      simp only [List.foldl_cons]
      exact (ih (elements.erase removal)).trans
        List.erase_sublist.length_le

/--
Erasing a list of distinct elements already present in a sequence removes
exactly one position per element.
-/
theorem length_foldl_erase_add {α : Type*} [BEq α] [LawfulBEq α]
    (elements removals : List α)
    (removalsNodup : removals.Nodup)
    (removalsPresent : ∀ element ∈ removals, element ∈ elements) :
    (removals.foldl (fun remaining element =>
        remaining.erase element) elements).length +
        removals.length =
      elements.length := by
  induction removals generalizing elements with
  | nil =>
      simp
  | cons removal removals ih =>
      have head_not_mem : removal ∉ removals :=
        (List.nodup_cons.mp removalsNodup).1
      have tail_nodup : removals.Nodup :=
        (List.nodup_cons.mp removalsNodup).2
      have removal_mem : removal ∈ elements :=
        removalsPresent removal (by simp)
      have tail_present :
          ∀ element ∈ removals, element ∈ elements.erase removal := by
        intro element element_mem
        have element_ne : element ≠ removal := by
          intro element_eq
          subst element
          exact head_not_mem element_mem
        exact (List.mem_erase_of_ne element_ne).2
          (removalsPresent element (by simp [element_mem]))
      have tail_balance :=
        ih (elements.erase removal) tail_nodup tail_present
      simp only [List.foldl_cons, List.length_cons]
      rw [List.length_erase_of_mem removal_mem] at tail_balance
      calc
        (removals.foldl
              (fun remaining element => remaining.erase element)
              (elements.erase removal)).length +
              (removals.length + 1) =
            ((removals.foldl
                (fun remaining element => remaining.erase element)
                (elements.erase removal)).length +
              removals.length) + 1 := by omega
        _ = (elements.length - 1) + 1 := by rw [tail_balance]
        _ = elements.length := Nat.sub_add_cancel (by
          exact Nat.succ_le_iff.mpr (List.length_pos_of_mem removal_mem))

/-- `removeLosers` is erasure of the loser projection of the matching. -/
theorem removeLosers_eq_foldl {n : ℕ} (elements : List (Element n))
    (matching : List (Pairing n)) :
    removeLosers elements matching =
      (pairingLosers matching).foldl
        (fun remaining element => remaining.erase element) elements := by
  induction matching generalizing elements with
  | nil =>
      rfl
  | cons pairing matching ih =>
      simpa [removeLosers, pairingLosers] using
        ih (elements.erase pairing.loser)

namespace MatchingValid

/-- Every matching loser is present in the shrinking source before the pass. -/
theorem loser_mem {n : ℕ} {params : Parameters} {state : State n}
    {sourceId : BlockId} {source : Block n}
    {matching : List (Pairing n)}
    (valid : MatchingValid params state sourceId source matching)
    {pairing : Pairing n} (pairing_mem : pairing ∈ matching) :
    pairing.loser ∈ source.elements :=
  (valid.2.2.2.1 pairing pairing_mem).1.second_mem

private theorem reverse_append_foldl_erase_perm
    {α : Type*} [BEq α] [LawfulBEq α]
    (elements removals : List α)
    (removalsNodup : removals.Nodup)
    (removalsPresent : ∀ element ∈ removals, element ∈ elements) :
    List.Perm
      (removals.reverse ++
        removals.foldl (fun remaining element => remaining.erase element)
          elements)
      elements := by
  induction removals generalizing elements with
  | nil => simp
  | cons removal removals ih =>
      have parts := List.nodup_cons.mp removalsNodup
      have removalPresent := removalsPresent removal (by simp)
      have tailPresent : ∀ element ∈ removals,
          element ∈ elements.erase removal := by
        intro element elementMember
        have different : element ≠ removal := by
          intro equal
          subst element
          exact parts.1 elementMember
        exact (List.mem_erase_of_ne different).2
          (removalsPresent element (by simp [elementMember]))
      have tailPerm := ih (elements.erase removal) parts.2 tailPresent
      have commute : List.Perm
          (removals.reverse ++ [removal] ++
              removals.foldl
                (fun remaining element => remaining.erase element)
                (elements.erase removal))
            (removal ::
              (removals.reverse ++
                removals.foldl
                  (fun remaining element => remaining.erase element)
                  (elements.erase removal))) := by
        simpa [List.append_assoc] using
          (List.perm_append_comm.trans
            (List.Perm.refl (removals.reverse ++ [removal]))).append_right
              (removals.foldl
                (fun remaining element => remaining.erase element)
                (elements.erase removal))
      simpa [List.foldl_cons, List.reverse_cons, List.append_assoc] using
        commute.trans
          ((tailPerm.cons removal).trans
            (List.perm_cons_erase removalPresent).symm)

private theorem sourceUpdate_recovered_perm
    {n : ℕ} (blocks : List (Block n)) (sourceId : BlockId)
    (source : Block n) (matching : List (Pairing n))
    (found : blocks[sourceId]? = some source)
    (losersPresent : ∀ loser ∈ pairingLosers matching,
      loser ∈ source.elements)
    (losersNodup : (pairingLosers matching).Nodup) :
    List.Perm ((pairingLosers matching).reverse ++
        ((blocks.modify sourceId fun _ =>
            { source with
              passCount := source.passCount + 1
              elements := removeLosers source.elements matching }).flatMap
          fun block => block.elements))
      (blocks.flatMap fun block => block.elements) := by
  induction blocks generalizing sourceId source with
  | nil => simp at found
  | cons head blocks ih =>
      cases sourceId with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst source
          rw [List.modify_zero_cons]
          simp only [List.flatMap_cons]
          have restored := reverse_append_foldl_erase_perm
            head.elements (pairingLosers matching) losersNodup losersPresent
          rw [← removeLosers_eq_foldl] at restored
          simpa [List.append_assoc] using
            restored.append_right
              (blocks.flatMap fun block => block.elements)
      | succ sourceId =>
          simp only [List.getElem?_cons_succ] at found
          rw [List.modify_succ_cons]
          simp only [List.flatMap_cons]
          have tail := ih sourceId source found losersPresent
          have commute : List.Perm
              ((pairingLosers matching).reverse ++ head.elements ++
                    ((blocks.modify sourceId fun _ =>
                      { source with
                        passCount := source.passCount + 1
                        elements := removeLosers source.elements matching
                      }).flatMap fun block => block.elements))
                (head.elements ++ (pairingLosers matching).reverse ++
                    ((blocks.modify sourceId fun _ =>
                      { source with
                        passCount := source.passCount + 1
                        elements := removeLosers source.elements matching
                      }).flatMap fun block => block.elements)) := by
            simpa [List.append_assoc] using
              (List.perm_append_comm
                (l₁ := (pairingLosers matching).reverse)
                (l₂ := head.elements)).append_right
                  ((blocks.modify sourceId fun _ =>
                    { source with
                      passCount := source.passCount + 1
                      elements := removeLosers source.elements matching
                    }).flatMap fun block => block.elements)
          simpa [List.append_assoc] using commute.trans (by
            simpa [List.append_assoc] using tail.append_left head.elements)

private theorem prependAt_allElements_perm
    {n : ℕ} (blocks : List (Block n)) (index : BlockId)
    (element : Element n) (indexLt : index < blocks.length) :
    List.Perm ((blocks.modify index fun block =>
        { block with elements := element :: block.elements }).flatMap
      fun block => block.elements)
      (element :: (blocks.flatMap fun block => block.elements)) := by
  induction blocks generalizing index with
  | nil => simp at indexLt
  | cons head blocks ih =>
      cases index with
      | zero =>
          rw [List.modify_zero_cons]
          simp
      | succ index =>
          rw [List.modify_succ_cons]
          simp only [List.flatMap_cons, List.length_cons,
            Nat.succ_lt_succ_iff] at indexLt ⊢
          exact (ih index indexLt).append_left head.elements |>.trans
            List.perm_middle

private theorem insertAtDestinations_allElements_perm
    {n : ℕ} (blocks : List (Block n))
    (matching : List (Pairing n))
    (destinationsLt : ∀ pairing ∈ matching,
      pairing.destination < blocks.length) :
    List.Perm
      ((insertAtDestinations blocks matching).flatMap
        (fun block => block.elements))
      ((pairingLosers matching).reverse ++
        blocks.flatMap fun block => block.elements) := by
  induction matching generalizing blocks with
  | nil => rfl
  | cons pairing matching ih =>
      let updated := blocks.modify pairing.destination fun block =>
        { block with elements := pairing.loser :: block.elements }
      have destinationLt := destinationsLt pairing (by simp)
      have tailLt : ∀ later ∈ matching,
          later.destination < updated.length := by
        intro later laterMember
        simpa [updated] using destinationsLt later (by simp [laterMember])
      have tail := ih updated tailLt
      have prepended :=
        prependAt_allElements_perm blocks pairing.destination pairing.loser
          destinationLt
      exact tail.trans (by
        simpa [updated, pairingLosers, List.append_assoc] using
          prepended.append_left (pairingLosers matching).reverse)

/-- A valid pass merely permutes the global assigned-element list. -/
theorem passBlocks_allElements_perm
    {n : ℕ} {params : Parameters} {state : State n}
    {sourceId : BlockId} {source : Block n}
    {matching : List (Pairing n)}
    (found : state.block? sourceId = some source)
    (valid : MatchingValid params state sourceId source matching) :
    List.Perm
      ((passBlocks state.blocks sourceId source matching).flatMap
        (fun block => block.elements))
      state.allElements := by
  have losersNodup := pairingLosers_nodup valid.2.1
  have losersPresent : ∀ loser ∈ pairingLosers matching,
      loser ∈ source.elements := by
    intro loser loserMember
    obtain ⟨pairing, pairingMember, rfl⟩ :=
      List.mem_map.mp loserMember
    exact valid.loser_mem pairingMember
  let sourceUpdated := state.blocks.modify sourceId fun _ =>
    { source with
      passCount := source.passCount + 1
      elements := removeLosers source.elements matching }
  have sourceRecovered : List.Perm
      ((pairingLosers matching).reverse ++
          (sourceUpdated.flatMap fun block => block.elements))
        state.allElements := by
    exact sourceUpdate_recovered_perm state.blocks sourceId source matching
      found losersPresent losersNodup
  have destinationLt : ∀ pairing ∈ matching,
      pairing.destination < sourceUpdated.length := by
    intro pairing pairingMember
    obtain ⟨destination, destinationFound, _growing, _creator⟩ :=
      (valid.2.2.2.1 pairing pairingMember).2.2.2
    have destinationOriginalLt : pairing.destination < state.blocks.length :=
      (List.getElem?_eq_some_iff.mp destinationFound).1
    simpa [sourceUpdated] using destinationOriginalLt
  unfold passBlocks
  exact (insertAtDestinations_allElements_perm sourceUpdated matching
    destinationLt).trans sourceRecovered

private theorem filter_length_modify_eq_of_preserves
    {α : Type*} (values : List α) (index : ℕ) (update : α → α)
    (select : α → Bool) (preserves : ∀ value,
      select (update value) = select value) :
    ((values.modify index update).filter select).length =
      (values.filter select).length := by
  induction values generalizing index with
  | nil => cases index <;> rfl
  | cons head values ih =>
      cases index with
      | zero =>
          rw [List.modify_zero_cons, List.filter_cons, List.filter_cons,
            preserves head]
          split <;> simp
      | succ index =>
          rw [List.modify_succ_cons]
          simp only [List.filter_cons]
          split <;> simp_all

private theorem filter_length_modify_const_eq_of_found
    {α : Type*} (values : List α) (index : ℕ) (oldValue newValue : α)
    (select : α → Bool) (found : values[index]? = some oldValue)
    (preserves : select newValue = select oldValue) :
    ((values.modify index fun _ => newValue).filter select).length =
      (values.filter select).length := by
  induction values generalizing index oldValue with
  | nil => simp at found
  | cons head values ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst oldValue
          rw [List.modify_zero_cons, List.filter_cons, List.filter_cons,
            preserves]
          split <;> simp
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          rw [List.modify_succ_cons, List.filter_cons, List.filter_cons]
          split <;> simp_all

private theorem filter_length_insertAtDestinations_eq
    {n : ℕ} (blocks : List (Block n)) (matching : List (Pairing n))
    (select : Block n → Bool)
    (insertPreserves : ∀ block element,
      select { block with elements := element :: block.elements } =
        select block) :
    ((insertAtDestinations blocks matching).filter select).length =
      (blocks.filter select).length := by
  unfold insertAtDestinations
  induction matching generalizing blocks with
  | nil => rfl
  | cons pairing matching ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact filter_length_modify_eq_of_preserves blocks pairing.destination
        (fun block =>
          { block with elements := pairing.loser :: block.elements })
        select (fun block => insertPreserves block pairing.loser)

/-- Passes preserve every creator's number of growing blocks. -/
theorem passBlocks_growingCount_eq
    {n : ℕ} (blocks : List (Block n)) (sourceId : BlockId)
    (source : Block n) (matching : List (Pairing n))
    (creator : Element n) (found : blocks[sourceId]? = some source) :
    ((passBlocks blocks sourceId source matching).filter fun block =>
        decide (block.mode = .growing ∧ block.creator = creator)).length =
      (blocks.filter fun block =>
        decide (block.mode = .growing ∧ block.creator = creator)).length := by
  let select : Block n → Bool := fun block =>
    decide (block.mode = .growing ∧ block.creator = creator)
  let sourceAfter : Block n :=
    { source with
      passCount := source.passCount + 1
      elements := removeLosers source.elements matching }
  let sourceUpdated := blocks.modify sourceId fun _ => sourceAfter
  have insertEq := filter_length_insertAtDestinations_eq
    sourceUpdated matching select (by
      intro block element
      rfl)
  have sourceEq := filter_length_modify_const_eq_of_found blocks sourceId
    source sourceAfter select found (by rfl)
  unfold passBlocks
  exact insertEq.trans sourceEq

/-- Canonical abstract state after a pass. -/
def afterPass {n : ℕ} (state : State n) (sourceId : BlockId)
    (source : Block n) (matching : List (Pairing n)) : State n :=
  { state with blocks := passBlocks state.blocks sourceId source matching }

/-- The canonical after-pass state is valid whenever the source lookup and
matching are valid. -/
theorem afterPass_valid
    {n : ℕ} {params : Parameters} {state : State n}
    {sourceId : BlockId} {source : Block n}
    {matching : List (Pairing n)}
    (stateValid : state.Valid params)
    (found : state.block? sourceId = some source)
    (valid : MatchingValid params state sourceId source matching) :
    (afterPass state sourceId source matching).Valid params := by
  refine ⟨?_, stateValid.2.1, ?_⟩
  · exact (passBlocks_allElements_perm found valid).symm.nodup
      stateValid.1
  · intro creator
    change
      ((passBlocks state.blocks sourceId source matching).filter fun block =>
        decide (block.mode = .growing ∧ block.creator = creator)).length ≤
        params.growingLimit
    rw [passBlocks_growingCount_eq _ _ _ _ _ found]
    exact stateValid.2.2 creator

/-- A valid matching therefore determines an actual legal pass step without
any caller-supplied post-state validity proof. -/
theorem afterPass_step
    {n : ℕ} {params : Parameters} {state : State n}
    {sourceId : BlockId} {source : Block n}
    {matching : List (Pairing n)}
    (stateValid : state.Valid params)
    (found : state.block? sourceId = some source)
    (valid : MatchingValid params state sourceId source matching) :
    Step params state (.pass sourceId matching)
      (afterPass state sourceId source matching) := by
  refine ⟨stateValid, ?_, valid.afterPass_valid stateValid found⟩
  exact .pass found valid rfl rfl

/-- A valid pass removes exactly one source element for every pairing. -/
theorem removeLosers_length_add {n : ℕ} {params : Parameters}
    {state : State n} {sourceId : BlockId} {source : Block n}
    {matching : List (Pairing n)}
    (valid : MatchingValid params state sourceId source matching) :
    (removeLosers source.elements matching).length + matching.length =
      source.elements.length := by
  rw [removeLosers_eq_foldl]
  simpa [pairingLosers] using
    length_foldl_erase_add source.elements (pairingLosers matching)
      (pairingLosers_nodup valid.2.1)
      (by
        intro loser loser_mem
        obtain ⟨pairing, pairing_mem, loser_eq⟩ :=
          List.mem_map.mp loser_mem
        subst loser
        exact valid.loser_mem pairing_mem)

/-- The number of pairings cannot exceed the pre-pass source size. -/
theorem matching_length_le {n : ℕ} {params : Parameters}
    {state : State n} {sourceId : BlockId} {source : Block n}
    {matching : List (Pairing n)}
    (valid : MatchingValid params state sourceId source matching) :
    matching.length ≤ source.elements.length := by
  have balance := valid.removeLosers_length_add
  omega

/--
Once the source pass counter reaches the exemption threshold, the matching
fraction condition is mandatory.
-/
theorem fraction_bound {n : ℕ} {params : Parameters} {state : State n}
    {sourceId : BlockId} {source : Block n}
    {matching : List (Pairing n)}
    (valid : MatchingValid params state sourceId source matching)
    (nonexempt : params.exemptPasses ≤ source.passCount) :
    params.matchingNumerator * source.elements.length ≤
      params.matchingDenominator * matching.length := by
  rcases valid.2.2.2.2 with exempt | fraction
  · omega
  · exact fraction

/--
Division-free one-step contraction inequality for every nonexempt pass.

Writing `a/d` for the required matching fraction, this is exactly
`d · |after| + a · |before| ≤ d · |before|`.
-/
theorem weighted_decay {n : ℕ} {params : Parameters} {state : State n}
    {sourceId : BlockId} {source : Block n}
    {matching : List (Pairing n)}
    (valid : MatchingValid params state sourceId source matching)
    (nonexempt : params.exemptPasses ≤ source.passCount) :
    params.matchingDenominator *
          (removeLosers source.elements matching).length +
        params.matchingNumerator * source.elements.length ≤
      params.matchingDenominator * source.elements.length := by
  have fraction := valid.fraction_bound nonexempt
  have balance := valid.removeLosers_length_add
  calc
    params.matchingDenominator *
          (removeLosers source.elements matching).length +
        params.matchingNumerator * source.elements.length ≤
        params.matchingDenominator *
            (removeLosers source.elements matching).length +
          params.matchingDenominator * matching.length :=
      Nat.add_le_add_left fraction _
    _ = params.matchingDenominator *
          ((removeLosers source.elements matching).length +
            matching.length) := by
      rw [Nat.mul_add]
    _ = params.matchingDenominator * source.elements.length := by
      rw [balance]

end MatchingValid

/--
One valid pass preserves an exact source-size balance and increments the
counter inherited by all future split descendants.
-/
theorem Effect.pass_decay {n : ℕ} {params : Parameters}
    {before after : State n} {sourceId : BlockId}
    {matching : List (Pairing n)}
    (effect : Effect params before (.pass sourceId matching) after) :
    ∃ source afterSource,
      before.block? sourceId = some source ∧
        after.block? sourceId = some afterSource ∧
        afterSource.creator = source.creator ∧
        afterSource.passCount = source.passCount + 1 ∧
        afterSource.mode = source.mode ∧
        afterSource.elements.length + matching.length =
          source.elements.length := by
  cases effect with
  | pass found valid_matching blocks_eq values_eq =>
      rename_i source
      let afterSource : Block n :=
        { source with
          passCount := source.passCount + 1
          elements := removeLosers source.elements matching }
      have source_after :
          after.block? sourceId = some afterSource := by
        have pass_effect :
            Effect params before (.pass sourceId matching) after :=
          .pass found valid_matching blocks_eq values_eq
        obtain ⟨source', source_found', source_after'⟩ :=
          pass_effect.pass_source?
        have source_eq : source' = source := by
          rw [found] at source_found'
          exact (Option.some.inj source_found').symm
        subst source'
        simpa [afterSource] using source_after'
      refine
        ⟨source, afterSource, found, source_after, rfl, rfl, rfl, ?_⟩
      exact valid_matching.removeLosers_length_add

/--
The weighted decay inequality packaged with the exact post-pass source lookup.
-/
theorem Effect.pass_weighted_decay {n : ℕ} {params : Parameters}
    {before after : State n} {sourceId : BlockId}
    {matching : List (Pairing n)}
    (effect : Effect params before (.pass sourceId matching) after)
    {source : Block n} (source_found : before.block? sourceId = some source)
    (nonexempt : params.exemptPasses ≤ source.passCount) :
    ∃ afterSource,
      after.block? sourceId = some afterSource ∧
        afterSource.creator = source.creator ∧
        afterSource.passCount = source.passCount + 1 ∧
        afterSource.mode = source.mode ∧
        params.matchingDenominator * afterSource.elements.length +
            params.matchingNumerator * source.elements.length ≤
          params.matchingDenominator * source.elements.length := by
  cases effect with
  | pass found valid_matching blocks_eq values_eq =>
      rename_i actualSource
      have source_eq : actualSource = source := by
        rw [source_found] at found
        exact (Option.some.inj found).symm
      subst actualSource
      let afterSource : Block n :=
        { source with
          passCount := source.passCount + 1
          elements := removeLosers source.elements matching }
      have source_after :
          after.block? sourceId = some afterSource := by
        have pass_effect :
            Effect params before (.pass sourceId matching) after :=
          .pass source_found valid_matching blocks_eq values_eq
        obtain ⟨source', source_found', source_after'⟩ :=
          pass_effect.pass_source?
        have source'_eq : source' = source := by
          rw [source_found] at source_found'
          exact (Option.some.inj source_found').symm
        subst source'
        simpa [afterSource] using source_after'
      refine ⟨afterSource, source_after, rfl, rfl, rfl, ?_⟩
      simpa [afterSource] using valid_matching.weighted_decay nonexempt

/--
Abstract iteration of the division-free decay inequality.

If every transition satisfies
`denominator * next + numerator * current ≤ denominator * current`,
then after `steps` transitions the remaining size is bounded by the
corresponding powers.  This form deliberately stays in `ℕ`: no division or
rounding convention is hidden in the statement.
-/
theorem weighted_decay_iterate
    {denominator numerator steps : ℕ} {size : ℕ → ℕ}
    (numerator_le : numerator ≤ denominator)
    (decay :
      ∀ index < steps,
        denominator * size (index + 1) + numerator * size index ≤
          denominator * size index) :
    denominator ^ steps * size steps ≤
      (denominator - numerator) ^ steps * size 0 := by
  induction steps with
  | zero =>
      simp
  | succ steps ih =>
      have prefixDecay :
          ∀ index < steps,
            denominator * size (index + 1) + numerator * size index ≤
              denominator * size index := by
        intro index index_lt
        exact decay index (by omega)
      have ih' := ih prefixDecay
      have lastDecay := decay steps (by omega)
      have denominator_split :
          denominator =
            (denominator - numerator) + numerator := by
        omega
      have right_split :
          denominator * size steps =
            (denominator - numerator) * size steps +
              numerator * size steps := by
        calc
          denominator * size steps =
              ((denominator - numerator) + numerator) * size steps := by
                rw [← denominator_split]
          _ = (denominator - numerator) * size steps +
                numerator * size steps := Nat.add_mul _ _ _
      have lastWeighted :
          denominator * size (steps + 1) ≤
            (denominator - numerator) * size steps := by
        rw [right_split] at lastDecay
        omega
      calc
        denominator ^ (steps + 1) * size (steps + 1) =
            denominator ^ steps *
              (denominator * size (steps + 1)) := by
                simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm,
                  Nat.mul_comm]
        _ ≤ denominator ^ steps *
              ((denominator - numerator) * size steps) :=
            Nat.mul_le_mul_left _ lastWeighted
        _ = (denominator - numerator) *
              (denominator ^ steps * size steps) := by
                simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ ≤ (denominator - numerator) *
              ((denominator - numerator) ^ steps * size 0) :=
            Nat.mul_le_mul_left _ ih'
        _ = (denominator - numerator) ^ (steps + 1) * size 0 := by
                rw [Nat.pow_succ]
                ac_rfl

/--
One block of `matchingDenominator` nonexempt passes cuts the weighted
remaining-factor power by at least two.

This is the division-free Bernoulli step behind the logarithmic threshold.
-/
theorem Parameters.two_mul_remaining_pow_le_denominator_pow
    (params : Parameters) :
    2 *
        (params.matchingDenominator - params.matchingNumerator) ^
          params.matchingDenominator ≤
      params.matchingDenominator ^ params.matchingDenominator := by
  let denominator := params.matchingDenominator
  let numerator := params.matchingNumerator
  let remaining := denominator - numerator
  have numerator_pos : 0 < numerator :=
    params.matchingNumerator_pos
  have fraction_half : 2 * numerator ≤ denominator :=
    params.matchingFraction_le_half
  have numerator_le : numerator ≤ denominator := by
    omega
  have denominator_pos : 0 < denominator := by
    omega
  have remaining_add : remaining + numerator = denominator := by
    exact Nat.sub_add_cancel numerator_le
  have remaining_le_denominator_mul :
      remaining ≤ denominator * numerator := by
    have remaining_le : remaining ≤ denominator :=
      Nat.sub_le _ _
    have denominator_le :
        denominator ≤ denominator * numerator := by
      have scaled :=
        Nat.mul_le_mul_left denominator
          (Nat.succ_le_iff.mpr numerator_pos)
      simpa using scaled
    exact remaining_le.trans denominator_le
  have pow_factor :
      remaining ^ denominator =
        remaining ^ (denominator - 1) * remaining := by
    calc
      remaining ^ denominator =
          remaining ^ ((denominator - 1) + 1) := by
            rw [Nat.sub_add_cancel
              (Nat.succ_le_iff.mpr denominator_pos)]
      _ = remaining ^ (denominator - 1) * remaining := by
            rw [Nat.pow_succ]
  have first_le_linear :
      remaining ^ denominator ≤
        denominator * remaining ^ (denominator - 1) * numerator := by
    calc
      remaining ^ denominator =
          remaining ^ (denominator - 1) * remaining :=
            pow_factor
      _ ≤ remaining ^ (denominator - 1) *
            (denominator * numerator) :=
          Nat.mul_le_mul_left _ remaining_le_denominator_mul
      _ = denominator * remaining ^ (denominator - 1) * numerator := by
          ac_rfl
  have bernoulli :
      remaining ^ denominator +
          denominator * remaining ^ (denominator - 1) * numerator ≤
        (remaining + numerator) ^ denominator := by
    exact pow_add_mul_le_add_pow (R := ℕ) (a := remaining)
      (b := numerator) (by omega) (by omega) denominator
  change 2 * remaining ^ denominator ≤ denominator ^ denominator
  calc
    2 * remaining ^ denominator =
        remaining ^ denominator + remaining ^ denominator := by
          omega
    _ ≤ remaining ^ denominator +
          denominator * remaining ^ (denominator - 1) * numerator :=
        Nat.add_le_add_left first_le_linear _
    _ ≤ (remaining + numerator) ^ denominator :=
        bernoulli
    _ = denominator ^ denominator := by
        rw [remaining_add]

/-- Iteration of the denominator-sized halving block. -/
theorem Parameters.pow_two_mul_remaining_pow_blocks_le
    (params : Parameters) (blocks : ℕ) :
    2 ^ blocks *
        (params.matchingDenominator - params.matchingNumerator) ^
          (params.matchingDenominator * blocks) ≤
      params.matchingDenominator ^
        (params.matchingDenominator * blocks) := by
  have powered :=
    Nat.pow_le_pow_left
      params.two_mul_remaining_pow_le_denominator_pow blocks
  calc
    2 ^ blocks *
          (params.matchingDenominator - params.matchingNumerator) ^
            (params.matchingDenominator * blocks) =
        (2 *
            (params.matchingDenominator - params.matchingNumerator) ^
              params.matchingDenominator) ^ blocks := by
          rw [Nat.mul_pow, Nat.pow_mul]
    _ ≤
        (params.matchingDenominator ^
          params.matchingDenominator) ^ blocks :=
      powered
    _ =
        params.matchingDenominator ^
          (params.matchingDenominator * blocks) := by
      rw [Nat.pow_mul]

/--
A contiguous run of passes on one stable source identifier.

Other blocks may be changed as destinations of the matchings, but the source
identifier is fixed.  This small trace fragment is the basic unit used when
passes are later grouped by ghost lineage.
-/
inductive PassRun {n : ℕ} (params : Parameters) (sourceId : BlockId) :
    State n → List (List (Pairing n)) → State n → Prop
  | nil {state : State n} (valid : state.Valid params) :
      PassRun params sourceId state [] state
  | cons {before middle after : State n}
      {matching : List (Pairing n)}
      {matchings : List (List (Pairing n))}
      (head : Step params before (.pass sourceId matching) middle)
      (tail : PassRun params sourceId middle matchings after) :
      PassRun params sourceId before (matching :: matchings) after

/-- Total matching activity in a run of passes. -/
def passRunActivity {n : ℕ} (matchings : List (List (Pairing n))) : ℕ :=
  (matchings.map List.length).sum

/--
Length of the potentially exempt prefix of a run whose inherited pre-pass
counter is `passCount`.
-/
def exemptPrefixLength (params : Parameters) (passCount steps : ℕ) : ℕ :=
  min steps (params.exemptPasses - passCount)

namespace exemptPrefixLength

theorem le_steps (params : Parameters) (passCount steps : ℕ) :
    exemptPrefixLength params passCount steps ≤ steps :=
  Nat.min_le_left _ _

theorem le_exemptPasses (params : Parameters) (passCount steps : ℕ) :
    exemptPrefixLength params passCount steps ≤ params.exemptPasses := by
  unfold exemptPrefixLength
  have min_le :
      min steps (params.exemptPasses - passCount) ≤
        params.exemptPasses - passCount :=
    Nat.min_le_right _ _
  omega

/--
Every actual pass after the computed prefix is nonexempt.  The strict
`index < steps` premise rules out the case where the whole run is exempt.
-/
theorem nonexempt_after (params : Parameters) (passCount steps index : ℕ)
    (after_prefix : exemptPrefixLength params passCount steps ≤ index)
    (in_run : index < steps) :
    params.exemptPasses ≤ passCount + index := by
  unfold exemptPrefixLength at after_prefix
  by_cases already_nonexempt : params.exemptPasses ≤ passCount
  · omega
  · have passCount_lt : passCount < params.exemptPasses := by
      omega
    by_cases whole_run :
        steps ≤ params.exemptPasses - passCount
    · have prefix_eq :
          min steps (params.exemptPasses - passCount) = steps :=
        Nat.min_eq_left whole_run
      rw [prefix_eq] at after_prefix
      omega
    · have threshold_le :
          params.exemptPasses - passCount ≤ steps :=
        Nat.le_of_lt (Nat.lt_of_not_ge whole_run)
      have prefix_eq :
          min steps (params.exemptPasses - passCount) =
            params.exemptPasses - passCount :=
        Nat.min_eq_right threshold_le
      rw [prefix_eq] at after_prefix
      omega

end exemptPrefixLength

namespace PassRun

/-- The initial endpoint of a pass run is valid. -/
theorem initial_valid {n : ℕ} {params : Parameters} {sourceId : BlockId}
    {initial final : State n}
    {matchings : List (List (Pairing n))}
    (run : PassRun params sourceId initial matchings final) :
    initial.Valid params := by
  cases run with
  | nil valid =>
      exact valid
  | cons head tail =>
      exact head.1

/-- A pass run is an ordinary interface trace with only pass operations. -/
theorem toTrace {n : ℕ} {params : Parameters} {sourceId : BlockId}
    {initial final : State n}
    {matchings : List (List (Pairing n))}
    (run : PassRun params sourceId initial matchings final) :
    Trace params initial
      (matchings.map fun matching => Operation.pass sourceId matching)
      final := by
  induction run with
  | nil valid =>
      exact .nil valid
  | cons head tail ih =>
      exact .cons head ih

/-- A pass run can be cut after any number of its pass operations. -/
theorem split {n : ℕ} {params : Parameters} {sourceId : BlockId}
    {initial final : State n}
    {matchings : List (List (Pairing n))}
    (run : PassRun params sourceId initial matchings final)
    (prefixLength : ℕ) (prefix_le : prefixLength ≤ matchings.length) :
    ∃ middle,
      PassRun params sourceId initial
          (matchings.take prefixLength) middle ∧
        PassRun params sourceId middle
          (matchings.drop prefixLength) final := by
  induction prefixLength generalizing initial matchings with
  | zero =>
      refine ⟨initial, ?_, ?_⟩
      · simpa using PassRun.nil (sourceId := sourceId) run.initial_valid
      · simpa using run
  | succ prefixLength ih =>
      cases run with
      | nil valid =>
          simp at prefix_le
      | @cons before middle after matching matchings head tail =>
          have tail_prefix_le : prefixLength ≤ matchings.length := by
            simpa using prefix_le
          obtain ⟨cut, prefixRun, suffixRun⟩ :=
            ih tail tail_prefix_le
          refine ⟨cut, ?_, ?_⟩
          · simpa using PassRun.cons head prefixRun
          · simpa using suffixRun

/--
Exact telescoping law for one fixed source block.

The creator and mode do not change, the pass counter rises by the number of
passes, and total matching activity is exactly the number of elements removed
from the source.
-/
theorem source_evolution {n : ℕ} {params : Parameters}
    {sourceId : BlockId} {initial final : State n}
    {matchings : List (List (Pairing n))}
    (run : PassRun params sourceId initial matchings final)
    {source : Block n} (source_found : initial.block? sourceId = some source) :
    ∃ finalSource,
      final.block? sourceId = some finalSource ∧
        finalSource.creator = source.creator ∧
        finalSource.passCount = source.passCount + matchings.length ∧
        finalSource.mode = source.mode ∧
        finalSource.elements.length + passRunActivity matchings =
          source.elements.length := by
  induction run generalizing source with
  | nil valid =>
      refine ⟨source, source_found, rfl, ?_, rfl, ?_⟩
      · simp
      · simp [passRunActivity]
  | @cons before middle after matching matchings head tail ih =>
      obtain
        ⟨headSource, middleSource, head_found, middle_found,
          creator_eq, count_eq, mode_eq, size_eq⟩ :=
        head.2.1.pass_decay
      have headSource_eq : headSource = source := by
        rw [source_found] at head_found
        exact (Option.some.inj head_found).symm
      subst headSource
      obtain
        ⟨finalSource, final_found, tail_creator, tail_count,
          tail_mode, tail_size⟩ :=
        ih middle_found
      refine
        ⟨finalSource, final_found, ?_, ?_, ?_, ?_⟩
      · exact tail_creator.trans creator_eq
      · simp only [List.length_cons]
        omega
      · exact tail_mode.trans mode_eq
      · simp only [passRunActivity, List.map_cons, List.sum_cons] at tail_size ⊢
        omega

/--
Geometric decay over an arbitrary nonexempt run on one source identifier.

The inherited counter premise is enough for every pass in the run: each pass
increments the counter, so no later transition can return to the exempt
prefix.  The conclusion is the exact division-free power inequality.
-/
theorem weighted_source_decay {n : ℕ} {params : Parameters}
    {sourceId : BlockId} {initial final : State n}
    {matchings : List (List (Pairing n))}
    (run : PassRun params sourceId initial matchings final)
    {source : Block n} (source_found : initial.block? sourceId = some source)
    (nonexempt : params.exemptPasses ≤ source.passCount) :
    ∃ finalSource,
      final.block? sourceId = some finalSource ∧
        finalSource.creator = source.creator ∧
        finalSource.passCount = source.passCount + matchings.length ∧
        finalSource.mode = source.mode ∧
        params.matchingDenominator ^ matchings.length *
            finalSource.elements.length ≤
          (params.matchingDenominator - params.matchingNumerator) ^
              matchings.length *
            source.elements.length := by
  induction run generalizing source with
  | nil valid =>
      refine ⟨source, source_found, rfl, ?_, rfl, ?_⟩
      · simp
      · simp
  | @cons before middle after matching matchings head tail ih =>
      obtain
        ⟨middleSource, middle_found, head_creator, head_count,
          head_mode, head_decay⟩ :=
        head.2.1.pass_weighted_decay source_found nonexempt
      have middle_nonexempt :
          params.exemptPasses ≤ middleSource.passCount := by
        omega
      obtain
        ⟨finalSource, final_found, tail_creator, tail_count,
          tail_mode, tail_decay⟩ :=
        ih middle_found middle_nonexempt
      have numerator_le :
          params.matchingNumerator ≤ params.matchingDenominator := by
        have fraction_half := params.matchingFraction_le_half
        omega
      have denominator_split :
          params.matchingDenominator =
            (params.matchingDenominator - params.matchingNumerator) +
              params.matchingNumerator := by
        omega
      have source_right_split :
          params.matchingDenominator * source.elements.length =
            (params.matchingDenominator - params.matchingNumerator) *
                source.elements.length +
              params.matchingNumerator * source.elements.length := by
        calc
          params.matchingDenominator * source.elements.length =
              ((params.matchingDenominator -
                    params.matchingNumerator) +
                  params.matchingNumerator) *
                source.elements.length := by
                  rw [← denominator_split]
          _ = (params.matchingDenominator -
                  params.matchingNumerator) *
                source.elements.length +
              params.matchingNumerator * source.elements.length :=
                Nat.add_mul _ _ _
      have head_weighted :
          params.matchingDenominator * middleSource.elements.length ≤
            (params.matchingDenominator - params.matchingNumerator) *
              source.elements.length := by
        rw [source_right_split] at head_decay
        omega
      refine
        ⟨finalSource, final_found, tail_creator.trans head_creator, ?_,
          tail_mode.trans head_mode, ?_⟩
      · simp only [List.length_cons]
        omega
      · simp only [List.length_cons]
        calc
          params.matchingDenominator ^ (matchings.length + 1) *
                finalSource.elements.length =
              params.matchingDenominator *
                (params.matchingDenominator ^ matchings.length *
                  finalSource.elements.length) := by
                    rw [Nat.pow_succ]
                    ac_rfl
          _ ≤ params.matchingDenominator *
                ((params.matchingDenominator -
                    params.matchingNumerator) ^ matchings.length *
                  middleSource.elements.length) :=
              Nat.mul_le_mul_left _ tail_decay
          _ = (params.matchingDenominator -
                  params.matchingNumerator) ^ matchings.length *
                (params.matchingDenominator *
                  middleSource.elements.length) := by
                    ac_rfl
          _ ≤ (params.matchingDenominator -
                  params.matchingNumerator) ^ matchings.length *
                ((params.matchingDenominator -
                    params.matchingNumerator) *
                  source.elements.length) :=
              Nat.mul_le_mul_left _ head_weighted
          _ = (params.matchingDenominator -
                  params.matchingNumerator) ^ (matchings.length + 1) *
                source.elements.length := by
                    rw [Nat.pow_succ]
                    ac_rfl

/--
Canonical decomposition at the exemption threshold.

When the run reaches beyond its potentially exempt prefix, the prefix
activity telescopes exactly against the source size and the entire remaining
suffix satisfies geometric weighted decay.  This is the multi-step form
needed before grouping pass runs by ghost lineage.
-/
theorem weighted_decay_after_exempt_prefix
    {n : ℕ} {params : Parameters}
    {sourceId : BlockId} {initial final : State n}
    {matchings : List (List (Pairing n))}
    (run : PassRun params sourceId initial matchings final)
    {source : Block n} (source_found : initial.block? sourceId = some source)
    (reaches_nonexempt :
      exemptPrefixLength params source.passCount matchings.length <
        matchings.length) :
    ∃ (middle : State n) (middleSource finalSource : Block n),
      middle.block? sourceId = some middleSource ∧
        final.block? sourceId = some finalSource ∧
        middleSource.creator = source.creator ∧
        middleSource.mode = source.mode ∧
        middleSource.passCount =
          source.passCount +
            exemptPrefixLength params source.passCount matchings.length ∧
        middleSource.elements.length +
            passRunActivity
              (matchings.take
                (exemptPrefixLength params source.passCount
                  matchings.length)) =
          source.elements.length ∧
        params.matchingDenominator ^
              (matchings.length -
                exemptPrefixLength params source.passCount
                  matchings.length) *
              finalSource.elements.length ≤
          (params.matchingDenominator - params.matchingNumerator) ^
              (matchings.length -
                exemptPrefixLength params source.passCount
                  matchings.length) *
            middleSource.elements.length := by
  let prefixLength :=
    exemptPrefixLength params source.passCount matchings.length
  have prefix_le : prefixLength ≤ matchings.length := by
    exact exemptPrefixLength.le_steps _ _ _
  obtain ⟨middle, prefixRun, suffixRun⟩ :=
    run.split prefixLength prefix_le
  obtain
    ⟨middleSource, middle_found, middle_creator, middle_count,
      middle_mode, prefix_balance⟩ :=
    prefixRun.source_evolution source_found
  have take_length :
      (matchings.take prefixLength).length = prefixLength := by
    simp [List.length_take, prefix_le]
  rw [take_length] at middle_count
  have middle_nonexempt :
      params.exemptPasses ≤ middleSource.passCount := by
    rw [middle_count]
    exact exemptPrefixLength.nonexempt_after params source.passCount
      matchings.length prefixLength (by rfl) reaches_nonexempt
  obtain
    ⟨finalSource, final_found, _final_creator, _final_count,
      _final_mode, suffix_decay⟩ :=
    suffixRun.weighted_source_decay middle_found middle_nonexempt
  refine
    ⟨middle, middleSource, finalSource, middle_found, final_found,
      middle_creator, middle_mode, ?_, prefix_balance, ?_⟩
  · exact middle_count
  · simpa [prefixLength] using suffix_decay

/--
Only the first `exemptPasses` passes of a source can be exempt.  The statement
uses the inherited pre-run counter, so after a split it applies unchanged to
either child.
-/
theorem exempt_prefix_length_le {n : ℕ} {params : Parameters}
    {sourceId : BlockId} {initial final : State n}
    {matchings : List (List (Pairing n))}
    (run : PassRun params sourceId initial matchings final)
    {source : Block n} (source_found : initial.block? sourceId = some source)
    (all_exempt : source.passCount + matchings.length ≤ params.exemptPasses) :
    matchings.length ≤ params.exemptPasses := by
  have _evolution := run.source_evolution source_found
  omega

end PassRun

end Splay.Interface
