import Splay.Accounting.BoundaryBlockCredit

namespace Splay.Interface

private theorem sum_map_modify_balance {α : Type*} (weight : α → ℕ) (values : List α)
    (id : ℕ) (value : α) (update : α → α) (found : values[id]? = some value) :
    ((values.modify id update).map weight).sum + weight value =
      (values.map weight).sum + weight (update value) := by
  induction values generalizing id with
  | nil => simp at found
  | cons head tail ih =>
    cases id with
    | zero =>
      have equal : head = value := Option.some.inj found
      subst value
      simp
      omega
    | succ id =>
      have tailFound : tail[id]? = some value := found
      have result := ih id tailFound
      change weight head + ((tail.modify id update).map weight).sum + weight value =
        weight head + (tail.map weight).sum + weight (update value)
      omega

private theorem insertAtDestinations_credit_sum {n : ℕ} (cutoff : ℕ) (blocks : List (Block n))
    (matching : List (Pairing n))
    (destinations : ∀ pairing ∈ matching, ∃ block : Block n,
      blocks[pairing.destination]? = some block ∧ block.mode = .growing) :
    ((insertAtDestinations blocks matching).map (boundaryBlockCredit cutoff)).sum =
      (blocks.map (boundaryBlockCredit cutoff)).sum := by
  induction matching generalizing blocks with
  | nil => rfl
  | cons pairing matching ih =>
    obtain ⟨destination, found, growing⟩ := destinations pairing (by simp)
    let updated := blocks.modify pairing.destination (fun block => {block with elements := pairing.loser :: block.elements})
    have tailDestinations : ∀ later ∈ matching, ∃ block : Block n,
        updated[later.destination]? = some block ∧ block.mode = .growing := by
      intro later member
      obtain ⟨block, blockFound, blockGrowing⟩ := destinations later (by simp [member])
      by_cases equal : pairing.destination = later.destination
      · refine ⟨{block with elements := pairing.loser :: block.elements}, ?_, blockGrowing⟩
        simp [updated, List.getElem?_modify, equal, blockFound]
      · exact ⟨block, by simp [updated, List.getElem?_modify, equal, blockFound], blockGrowing⟩
    change ((insertAtDestinations updated matching).map (boundaryBlockCredit cutoff)).sum = _
    rw [ih updated tailDestinations]
    have balance := sum_map_modify_balance (boundaryBlockCredit cutoff) blocks pairing.destination destination
      (fun block => {block with elements := pairing.loser :: block.elements}) found
    have same : boundaryBlockCredit cutoff {destination with elements := pairing.loser :: destination.elements} =
        boundaryBlockCredit cutoff destination := by simp [boundaryBlockCredit, growing]
    rw [same] at balance
    exact Nat.add_right_cancel balance

/-- Only the source's credit changes in a pass. Every destination remains
growing and retains its constant reserved credit. -/
theorem passBlocks_boundaryCredit_balance {n : ℕ} {params : Parameters} {before : State n}
    {id : BlockId} {source : Block n} {matching : List (Pairing n)} (cutoff : ℕ)
    (found : before.block? id = some source) (valid : MatchingValid params before id source matching) :
    ((passBlocks before.blocks id source matching).map (boundaryBlockCredit cutoff)).sum + boundaryBlockCredit cutoff source =
      boundaryCredit cutoff before + boundaryBlockCredit cutoff
        {source with passCount := source.passCount + 1, elements := removeLosers source.elements matching} := by
  let next := {source with passCount := source.passCount + 1, elements := removeLosers source.elements matching}
  let updated := before.blocks.modify id (fun _ => next)
  have destinations : ∀ pairing ∈ matching, ∃ block : Block n,
      updated[pairing.destination]? = some block ∧ block.mode = .growing := by
    intro pairing member
    have facts := valid.2.2.2.1 pairing member
    obtain ⟨block, blockFound, growing, _⟩ := facts.2.2.2
    refine ⟨block, ?_, growing⟩
    change before.blocks[pairing.destination]? = some block at blockFound
    simp [updated, List.getElem?_modify, facts.2.2.1.symm, blockFound]
  change ((insertAtDestinations updated matching).map (boundaryBlockCredit cutoff)).sum + _ = _
  rw [insertAtDestinations_credit_sum cutoff updated matching destinations]
  exact sum_map_modify_balance (boundaryBlockCredit cutoff) before.blocks id source (fun _ => next) found

/-- Every actual interface operation pays its designated boundary charge.
The sole permitted increase is the fixed credit of newly created physical IDs. -/
theorem Effect.boundaryCredit_bound {n : ℕ} {params : Parameters} {before after : State n}
    {operation : Operation n} (effect : Effect params before operation after) (cutoff : ℕ) :
    boundaryCredit cutoff after + boundaryOperationCharge cutoff before operation ≤
      boundaryCredit cutoff before + boundaryCreditCapacity cutoff * operation.blockGrowth := by
  cases effect with
  | @convert after id block found growing blocksEq valuesEq =>
    have balance := sum_map_modify_balance (boundaryBlockCredit cutoff) before.blocks id block
      (fun current => {current with mode := .shrinking}) found
    have nextBound := boundaryBlockCredit_le cutoff {block with mode := .shrinking}
    have oldCredit : boundaryBlockCredit cutoff block = boundaryCreditCapacity cutoff := by simp [boundaryBlockCredit, growing]
    simp only [boundaryCredit, blocksEq, boundaryOperationCharge, Operation.blockGrowth, Nat.mul_zero, Nat.add_zero]
    unfold boundaryCredit at balance
    rw [oldCredit] at balance
    omega
  | @create after creator room blocksEq valuesEq =>
    simp [boundaryCredit, blocksEq, boundaryOperationCharge, Operation.blockGrowth, boundaryBlockCredit]
  | @insert after id block element found growing unassigned order blocksEq valuesEq =>
    have balance := sum_map_modify_balance (boundaryBlockCredit cutoff) before.blocks id block
      (fun current => {current with elements := element :: current.elements}) found
    have same : boundaryBlockCredit cutoff {block with elements := element :: block.elements} = boundaryBlockCredit cutoff block := by
      simp [boundaryBlockCredit, growing]
    rw [same] at balance
    simp only [boundaryCredit, blocksEq, boundaryOperationCharge, Operation.blockGrowth, Nat.mul_zero, Nat.add_zero]
    omega
  | @delete after id block element found shrinking present blocksEq valuesEq =>
    have balance := sum_map_modify_balance (boundaryBlockCredit cutoff) before.blocks id block
      (fun current => {current with elements := current.elements.erase element}) found
    have paid := boundaryBlockCredit_delete cutoff block element shrinking present
    simp only [boundaryOperationCharge, found, Operation.blockGrowth, Nat.mul_zero, Nat.add_zero]
    simp only [boundaryCredit, blocksEq]
    omega
  | @pass after id source matching found valid blocksEq valuesEq =>
    have balance := passBlocks_boundaryCredit_balance cutoff found valid
    have paid := boundaryBlockCredit_pass cutoff valid
    simp only [boundaryOperationCharge, found, Operation.blockGrowth, Nat.mul_zero, Nat.add_zero]
    simp only [boundaryCredit, blocksEq] at balance ⊢
    omega
  | @split after id source prefixLength found shrinking prefixLe blocksEq valuesEq =>
    have balance := sum_map_modify_balance (boundaryBlockCredit cutoff) before.blocks id source
      (fun current => {current with elements := []}) found
    have emptyLe := boundaryBlockCredit_mono_shrinking cutoff (before := source) (after := {source with elements := []}) shrinking shrinking
      (show ([] : List (Element n)).length ≤ source.elements.length by simp) (Nat.le_refl source.passCount)
    have prefixBound := boundaryBlockCredit_le cutoff {source with elements := source.elements.take prefixLength}
    have suffixBound := boundaryBlockCredit_le cutoff {source with elements := source.elements.drop prefixLength}
    simp only [boundaryCredit, blocksEq, splitBlocks, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      boundaryOperationCharge, Operation.blockGrowth]
    omega
  | decrease _ blocksEq _ => simp [boundaryCredit, blocksEq, boundaryOperationCharge, Operation.blockGrowth]
  | increase _ blocksEq _ => simp [boundaryCredit, blocksEq, boundaryOperationCharge, Operation.blockGrowth]

end Splay.Interface
