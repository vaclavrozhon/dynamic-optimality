import Splay.Accounting.BoundaryCreditEffects

namespace Splay.Interface

/-- Exact chronological charges, computed at each real interface pre-state. -/
inductive BoundaryCreditHistory {n : ℕ} (cutoff : ℕ) (params : Parameters) :
    State n → List (Operation n) → State n → ℕ → Prop
  | nil {state : State n} (valid : state.Valid params) :
      BoundaryCreditHistory cutoff params state [] state 0
  | cons {before middle after : State n} {operation : Operation n} {operations : List (Operation n)}
      {tailCharge : ℕ} (head : Step params before operation middle)
      (tail : BoundaryCreditHistory cutoff params middle operations after tailCharge) :
      BoundaryCreditHistory cutoff params before (operation :: operations) after
        (boundaryOperationCharge cutoff before operation + tailCharge)

namespace BoundaryCreditHistory

theorem erase {n cutoff : ℕ} {params : Parameters} {before after : State n} {operations : List (Operation n)}
    {charge : ℕ} (history : BoundaryCreditHistory cutoff params before operations after charge) :
    Trace params before operations after := by
  induction history with
  | nil valid => exact .nil valid
  | cons head tail ih => exact .cons head ih

theorem lift {n : ℕ} {params : Parameters} {before after : State n} {operations : List (Operation n)}
    (trace : Trace params before operations after) (cutoff : ℕ) :
    ∃ charge, BoundaryCreditHistory cutoff params before operations after charge := by
  induction trace with
  | nil valid => exact ⟨0, .nil valid⟩
  | cons head tail ih =>
    obtain ⟨charge, history⟩ := ih
    exact ⟨_, .cons head history⟩

theorem append {n cutoff : ℕ} {params : Parameters} {before middle after : State n}
    {first second : List (Operation n)} {firstCharge secondCharge : ℕ}
    (left : BoundaryCreditHistory cutoff params before first middle firstCharge)
    (right : BoundaryCreditHistory cutoff params middle second after secondCharge) :
    BoundaryCreditHistory cutoff params before (first ++ second) after (firstCharge + secondCharge) := by
  induction left with
  | nil => simpa using right
  | cons head tail ih =>
    simpa only [List.cons_append, Nat.add_assoc] using BoundaryCreditHistory.cons head (ih right)

/-- The complete chronological boundary credit is paid solely by the
initial reserve and the historical number of created physical blocks. -/
theorem credit_bound {n cutoff : ℕ} {params : Parameters} {before after : State n}
    {operations : List (Operation n)} {charge : ℕ}
    (history : BoundaryCreditHistory cutoff params before operations after charge) :
    boundaryCredit cutoff after + charge ≤ boundaryCredit cutoff before +
      boundaryCreditCapacity cutoff * totalBlockGrowth operations := by
  induction history with
  | nil => simp [totalBlockGrowth]
  | @cons before middle after operation operations tailCharge head tail ih =>
    have localBound := head.2.1.boundaryCredit_bound cutoff
    simp only [totalBlockGrowth, List.map_cons, List.sum_cons, Nat.mul_add]
    simp only [totalBlockGrowth] at ih
    omega

theorem charge_le_created_credit {n cutoff : ℕ} {params : Parameters} {before after : State n}
    {operations : List (Operation n)} {charge : ℕ}
    (history : BoundaryCreditHistory cutoff params before operations after charge) (initial : before.Initial params) :
    charge ≤ boundaryCreditCapacity cutoff * totalBlockGrowth operations := by
  have bound := history.credit_bound
  simp only [boundaryCredit, initial.2, List.map_nil, List.sum_nil, Nat.zero_add] at bound
  omega

/-- Winner preparation changes no block, so the ensuing first pass is
charged against exactly the source present before that preparation. -/
theorem initialPass_charge_le {n cutoff : ℕ} {params : Parameters}
    {before after : State n} {sourceId : BlockId} {source : Block n}
    {matching : List (Pairing n)} {suffix : List (Operation n)}
    {winners : List (Element n)} {charge : ℕ}
    (found : before.block? sourceId = some source)
    (history : BoundaryCreditHistory cutoff params before
      ((winners.map fun winner => Operation.valueChange winner .decrease) ++
        .pass sourceId matching :: suffix) after charge) :
    boundaryPassCharge cutoff source matching ≤ charge := by
  induction winners generalizing before charge with
  | nil =>
    cases history with
    | cons head tail =>
      simp only [boundaryOperationCharge, found]
      omega
  | cons winner winners ih =>
    cases history with
    | @cons before middle after operation operations tailCharge head tail =>
      have blocksEq : middle.blocks = before.blocks := by
        cases head.2.1 with
        | decrease _ equal _ => exact equal
      have nextFound : middle.block? sourceId = some source := by
        simpa only [State.block?, blocksEq] using found
      simpa only [boundaryOperationCharge, Nat.zero_add] using ih nextFound tail

end BoundaryCreditHistory

theorem Trace.boundaryCredit_bound {n cutoff : ℕ} {params : Parameters}
    {before after : State n} {operations : List (Operation n)}
    (trace : Trace params before operations after) :
    boundaryCredit cutoff after ≤ boundaryCredit cutoff before +
      boundaryCreditCapacity cutoff * totalBlockGrowth operations := by
  obtain ⟨charge, history⟩ := BoundaryCreditHistory.lift trace cutoff
  exact (Nat.le_add_right _ _).trans history.credit_bound

theorem boundaryCreditCapacity_bound (cutoff : ℕ) :
    boundaryCreditCapacity cutoff ≤ 16 * Nat.clog 2 cutoff + 14 := by
  have bound := Splay.Accounting.boundarySizeCredit_bound cutoff cutoff
  rw [Splay.Accounting.boundarySizeCredit_of_le (Nat.le_refl cutoff)] at bound
  unfold boundaryCreditCapacity
  omega

/-- A uniform logarithmic lifetime bound for every actual interface trace,
including empty first passes, splitting, conversion, and boundary deletion. -/
theorem BoundaryCreditHistory.charge_le_log_created {n cutoff : ℕ} {params : Parameters} {before after : State n}
    {operations : List (Operation n)} {charge : ℕ}
    (history : BoundaryCreditHistory cutoff params before operations after charge) (initial : before.Initial params) :
    charge ≤ (16 * Nat.clog 2 cutoff + 14) * totalBlockGrowth operations :=
  (history.charge_le_created_credit initial).trans (Nat.mul_le_mul_right _ (boundaryCreditCapacity_bound cutoff))

end Splay.Interface
