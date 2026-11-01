import Splay.Accounting.BoundarySizeCredit
import Splay.Interface.BlockCount

namespace Splay.Interface

open Splay.Accounting

/-- Credit assigned once to each physical block at creation. -/
def boundaryCreditCapacity (cutoff : ℕ) : ℕ := Nat.clog 2 (cutoff ^ 16 + 1) + 13

/-- Growing blocks reserve their entire future budget. Shrinking blocks
spend it on fractional passes, their first pass, and their last twelve elements. -/
def boundaryBlockCredit {n : ℕ} (cutoff : ℕ) (block : Block n) : ℕ :=
  match block.mode with
  | .growing => boundaryCreditCapacity cutoff
  | .shrinking => boundarySizeCredit cutoff block.elements.length +
      (if block.passCount = 0 then 1 else 0) + min 12 block.elements.length

def boundaryCredit {n : ℕ} (cutoff : ℕ) (state : State n) : ℕ :=
  (state.blocks.map (boundaryBlockCredit cutoff)).sum

/-- A counted pass is either the first pass or a positive, sufficiently
fractional pass of a source below the size cutoff. -/
def boundaryPassCharge {n : ℕ} (cutoff : ℕ) (source : Block n) (matching : List (Pairing n)) : ℕ :=
  if source.passCount = 0 then 1 else
    if 0 < source.elements.length ∧ source.elements.length ≤ cutoff ∧ source.elements.length ≤ 8 * matching.length then 1 else 0

def boundaryOperationCharge {n : ℕ} (cutoff : ℕ) (before : State n) : Operation n → ℕ
  | .pass id matching => match before.block? id with
    | some source => boundaryPassCharge cutoff source matching
    | none => 0
  | .delete id _ => match before.block? id with
    | some source => if source.elements.length ≤ 12 then 1 else 0
    | none => 0
  | _ => 0

theorem boundaryBlockCredit_le {n : ℕ} (cutoff : ℕ) (block : Block n) :
    boundaryBlockCredit cutoff block ≤ boundaryCreditCapacity cutoff := by
  cases mode : block.mode with
  | growing => simp [boundaryBlockCredit, mode]
  | shrinking =>
    have sizeBound : boundarySizeCredit cutoff block.elements.length ≤ Nat.clog 2 (cutoff ^ 16 + 1) := min_le_left _ _
    have smallBound := min_le_left 12 block.elements.length
    simp only [boundaryBlockCredit, mode, boundaryCreditCapacity]
    split <;> omega

theorem boundaryBlockCredit_mono_shrinking {n : ℕ} (cutoff : ℕ) {before after : Block n}
    (beforeShrinking : before.mode = .shrinking) (afterShrinking : after.mode = .shrinking)
    (size : after.elements.length ≤ before.elements.length) (count : before.passCount ≤ after.passCount) :
    boundaryBlockCredit cutoff after ≤ boundaryBlockCredit cutoff before := by
  have sizeCredit := boundarySizeCredit_mono cutoff size
  have smallCredit := min_le_min_left 12 size
  simp only [boundaryBlockCredit, beforeShrinking, afterShrinking]
  split <;> split <;> omega

/-- A valid pass spends the designated credit at its actual source. -/
theorem boundaryBlockCredit_pass {n : ℕ} {params : Parameters} {before : State n}
    {id : BlockId} {source : Block n} {matching : List (Pairing n)} (cutoff : ℕ)
    (valid : MatchingValid params before id source matching) :
    boundaryBlockCredit cutoff { source with passCount := source.passCount + 1, elements := removeLosers source.elements matching } +
      boundaryPassCharge cutoff source matching ≤ boundaryBlockCredit cutoff source := by
  have count := valid.removeLosers_length_add
  have sizeLe : (removeLosers source.elements matching).length ≤ source.elements.length := by omega
  have sizeCredit := boundarySizeCredit_mono cutoff sizeLe
  have smallCredit := min_le_min_left 12 sizeLe
  simp only [boundaryBlockCredit, valid.1, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
    Nat.add_zero, boundaryPassCharge]
  by_cases first : source.passCount = 0
  · simp only [first, if_pos, Nat.zero_add]
    omega
  · simp only [first, if_false, Nat.add_zero]
    split
    next qualifying =>
      have decay : 8 * (removeLosers source.elements matching).length ≤ 7 * source.elements.length := by omega
      have paid := boundarySizeCredit_decay qualifying.1 qualifying.2.1 decay
      omega
    next => omega

/-- Deleting one of the last twelve elements spends one unit of the
small-source reserve. All other deletion effects are nonincreasing. -/
theorem boundaryBlockCredit_delete {n : ℕ} (cutoff : ℕ) (source : Block n) (element : Element n)
    (shrinking : source.mode = .shrinking) (present : element ∈ source.elements) :
    boundaryBlockCredit cutoff {source with elements := source.elements.erase element} +
      (if source.elements.length ≤ 12 then 1 else 0) ≤ boundaryBlockCredit cutoff source := by
  have length := List.length_erase_of_mem present
  have positive : 0 < source.elements.length := List.length_pos_of_mem present
  have sizeLe : (source.elements.erase element).length ≤ source.elements.length := by omega
  have sizeCredit := boundarySizeCredit_mono cutoff sizeLe
  have smallCredit := min_le_min_left 12 sizeLe
  simp only [boundaryBlockCredit, shrinking]
  by_cases small : source.elements.length ≤ 12
  · rw [if_pos small, min_eq_right small, min_eq_right (sizeLe.trans small)]
    omega
  · rw [if_neg small]
    omega

end Splay.Interface
