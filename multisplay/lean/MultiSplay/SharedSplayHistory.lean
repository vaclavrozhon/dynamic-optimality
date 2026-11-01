import MultiSplay.FramedBoundaryCredit
import MultiSplay.RichBoundaryInvariants

/-!
# Chronological splay accounting with changing components

A `Segment` is either an actual article macro executed in a passive frame, or
a strict interface trace of maintenance operations. Maintenance is charged its
literal operation count; common splits and joins each use at most eight.

`History` concatenates these segments in one fixed interface universe. Local
macros may have different component sizes. Every estimate below telescopes on
the actual shared state, including old records which are no longer active.
-/

noncomputable section

namespace MultiSplay.SharedSplay

open Splay.Interface
open Splay.Accounting (ArticleCheckpoint ArticleMacro PassedBlocksUnbroken)
open Splay.Rank (Snapshot)

variable {m : Nat} {params : Parameters}

theorem inserts_le_length {n : Nat} (word : List (Operation n)) : totalInserts word ≤ word.length := by
  induction word with
  | nil => simp [totalInserts]
  | cons head tail ih => cases head <;> simp_all [totalInserts, Operation.insertCount] <;> omega

theorem increases_le_length {n : Nat} (word : List (Operation n)) : totalIncreases word ≤ word.length := by
  induction word with
  | nil => simp [totalIncreases]
  | cons head tail ih =>
      have bound : head.increaseCount ≤ 1 := by
        cases head <;> simp [Operation.increaseCount]
        split <;> decide
      simp only [totalIncreases, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

theorem growth_le_length {n : Nat} (word : List (Operation n)) : totalBlockGrowth word ≤ 2 * word.length := by
  induction word with
  | nil => simp [totalBlockGrowth]
  | cons head tail ih => cases head <;> simp_all [totalBlockGrowth, Operation.blockGrowth] <;> omega

inductive Segment (params : Parameters) : State m → State m → Type
  | article {n : Nat} {before after : ArticleCheckpoint n} {whole : State m}
      (step : ArticleMacro params before after)
      (unbroken : PassedBlocksUnbroken (Snapshot.ofTree before.comparison).withTruePriority before.splay before.state)
      (framed : InterfaceFramedTrace.Framed params before.state.toInterface whole)
      (run : FramedSplay.Realization step whole framed) : Segment params whole run.final
  | maintenance {before after : State m} {word : List (Operation m)}
      (execution : Trace params before word after) : Segment params before after

namespace Segment

variable {before after : State m}

def operations : Segment params before after → List (Operation m)
  | .article _ _ _ run => run.operations
  | .maintenance (word := word) _ => word

def good : Segment params before after → Nat
  | .article step _ _ _ => step.goodCount
  | .maintenance _ => 0

def boundary : Segment params before after → Nat
  | .article step _ _ _ => step.boundaryCount
  | .maintenance _ => 0

def rotations : Segment params before after → Nat
  | .article step _ _ _ => step.rotationCount
  | .maintenance _ => 0

def births : Segment params before after → Nat
  | .article step _ _ _ => step.birthBudget
  | .maintenance _ => 0

def maintenanceCost : Segment params before after → Nat
  | .article _ _ _ _ => 0
  | .maintenance (word := word) _ => word.length

def zigZigs : Segment params before after → Nat
  | .article step _ _ _ => step.kinds.count .zigZig
  | .maintenance _ => 0

theorem trace (segment : Segment params before after) : Trace params before segment.operations after := by
  cases segment with
  | article step unbroken framed run => exact run.trace
  | maintenance execution => exact execution

theorem inserts (segment : Segment params before after) :
    totalInserts segment.operations ≤ segment.rotations + 2 * segment.boundary + segment.maintenanceCost := by
  cases segment with
  | article step unbroken framed run => simpa [operations, rotations, boundary, maintenanceCost] using run.inserts
  | maintenance execution => simpa [operations, rotations, boundary, maintenanceCost] using inserts_le_length (operations (.maintenance execution))

theorem increases (segment : Segment params before after) :
    totalIncreases segment.operations ≤ segment.good + 8 * params.valueBound * segment.boundary +
      3 * params.valueBound * segment.rotations + segment.maintenanceCost := by
  cases segment with
  | article step unbroken framed run => simpa [operations, good, boundary, rotations, maintenanceCost] using run.increases
  | maintenance execution => simpa [operations, good, boundary, rotations, maintenanceCost] using increases_le_length _

theorem good_charge (segment : Segment params before after) (valid : before.Valid params) :
    InterfaceForest.excess after + segment.good ≤ InterfaceForest.excess before +
      8 * params.valueBound * segment.boundary + 3 * params.valueBound * segment.rotations + segment.maintenanceCost := by
  cases segment with
  | article step unbroken framed run => simpa [good, boundary, rotations, maintenanceCost] using run.good_charge
  | maintenance execution =>
      have balance := InterfaceForest.excess_balance valid execution
      have increase := increases_le_length (Segment.operations (.maintenance execution))
      dsimp only [operations] at increase
      simp only [good, boundary, rotations, maintenanceCost, Nat.mul_zero, Nat.add_zero]
      omega

theorem boundary_credit (segment : Segment params before after) (cutoff : Nat)
    (exempt : params.exemptPasses = 2) (numerator : params.matchingNumerator = 1) (denominator : params.matchingDenominator = 8) :
    cutoff * (2 * segment.boundary) + 4 * cutoff * boundaryCredit cutoff after ≤
      4 * cutoff * boundaryCredit cutoff before +
        4 * cutoff * boundaryCreditCapacity cutoff * (segment.births + 2 * segment.maintenanceCost) +
        16 * totalActivity segment.operations := by
  cases segment with
  | article step unbroken framed run =>
      simpa [boundary, births, maintenanceCost, operations] using run.boundary_credit exempt numerator denominator unbroken (cutoff := cutoff)
  | maintenance execution =>
      have paid := execution.boundaryCredit_bound (cutoff := cutoff)
      have growth := growth_le_length (Segment.operations (.maintenance execution))
      dsimp only [operations] at growth
      have enlarged := paid.trans (Nat.add_le_add_left (Nat.mul_le_mul_left (boundaryCreditCapacity cutoff) growth) _)
      have weighted := Nat.mul_le_mul_left (4 * cutoff) enlarged
      simp only [boundary, births, maintenanceCost, operations, Nat.mul_zero, Nat.zero_add]
      nlinarith

theorem zigZigs_paid (segment : Segment params before after) :
    2 * segment.zigZigs ≤ totalActivity segment.operations + totalInserts segment.operations := by
  cases segment with
  | article step unbroken framed run => exact run.zigZigs
  | maintenance execution => exact Nat.zero_le _

end Segment

inductive History (params : Parameters) : State m → State m → Type
  | done (state : State m) : History params state state
  | next {first middle last : State m} (head : Segment params first middle)
      (tail : History params middle last) : History params first last

namespace History

variable {first last : State m}

def operations : {first last : State m} → History params first last → List (Operation m)
  | _, _, .done _ => []
  | _, _, .next head tail => head.operations ++ tail.operations

def sum (charge : {a b : State m} → Segment params a b → Nat) : {first last : State m} → History params first last → Nat
  | _, _, .done _ => 0
  | _, _, .next head tail => charge head + tail.sum charge

abbrev good (history : History params first last) := history.sum Segment.good
abbrev boundary (history : History params first last) := history.sum Segment.boundary
abbrev rotations (history : History params first last) := history.sum Segment.rotations
abbrev births (history : History params first last) := history.sum Segment.births
abbrev maintenanceCost (history : History params first last) := history.sum Segment.maintenanceCost
abbrev zigZigs (history : History params first last) := history.sum Segment.zigZigs

theorem trace (history : History params first last) (valid : first.Valid params) :
    Trace params first history.operations last := by
  induction history with
  | done state => exact .nil valid
  | next head tail ih => exact InterfaceForest.trace_append head.trace (ih (InterfaceForest.trace_final_valid head.trace))

theorem inserts (history : History params first last) :
    totalInserts history.operations ≤ history.rotations + 2 * history.boundary + history.maintenanceCost := by
  induction history with
  | done state => simp [operations, sum, totalInserts]
  | next head tail ih =>
      have paid := head.inserts
      dsimp only [rotations, boundary, maintenanceCost] at ih
      simp only [operations, totalInserts_append, rotations, boundary, maintenanceCost, sum]
      omega

theorem increases (history : History params first last) :
    totalIncreases history.operations ≤ history.good + 8 * params.valueBound * history.boundary +
      3 * params.valueBound * history.rotations + history.maintenanceCost := by
  induction history with
  | done state => simp [operations, sum, totalIncreases]
  | next head tail ih =>
      have paid := head.increases
      simp only [operations, totalIncreases_append, good, boundary, rotations, maintenanceCost, sum]
      dsimp only [good, boundary, rotations, maintenanceCost] at ih
      nlinarith

theorem good_charge (history : History params first last) (valid : first.Valid params) :
    InterfaceForest.excess last + history.good ≤ InterfaceForest.excess first +
      8 * params.valueBound * history.boundary + 3 * params.valueBound * history.rotations + history.maintenanceCost := by
  induction history with
  | done state => simp [sum]
  | next head tail ih =>
      have paid := head.good_charge valid
      have rest := ih (InterfaceForest.trace_final_valid head.trace)
      simp only [good, boundary, rotations, maintenanceCost, sum]
      dsimp only [good, boundary, rotations, maintenanceCost] at rest
      nlinarith

theorem boundary_credit (history : History params first last) (cutoff : Nat)
    (exempt : params.exemptPasses = 2) (numerator : params.matchingNumerator = 1) (denominator : params.matchingDenominator = 8) :
    cutoff * (2 * history.boundary) + 4 * cutoff * boundaryCredit cutoff last ≤
      4 * cutoff * boundaryCredit cutoff first +
        4 * cutoff * boundaryCreditCapacity cutoff * (history.births + 2 * history.maintenanceCost) +
        16 * totalActivity history.operations := by
  induction history with
  | done state => simp [operations, sum, totalActivity]
  | next head tail ih =>
      have paid := head.boundary_credit cutoff exempt numerator denominator
      simp only [operations, totalActivity_append, boundary, births, maintenanceCost, sum]
      dsimp only [boundary, births, maintenanceCost] at ih
      nlinarith

theorem zigZigs_paid (history : History params first last) :
    2 * history.zigZigs ≤ totalActivity history.operations + totalInserts history.operations := by
  induction history with
  | done state => simp [operations, sum, totalActivity, totalInserts]
  | next head tail ih =>
      have paid := head.zigZigs_paid
      dsimp only [zigZigs] at ih
      simp only [operations, totalActivity_append, totalInserts_append, zigZigs, sum]
      omega

end History
end MultiSplay.SharedSplay
