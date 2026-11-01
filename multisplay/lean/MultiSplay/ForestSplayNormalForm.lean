import MultiSplay.ForestSplayTheorem
import MultiSplay.PackedBoundedPreparation

/-!
# Public splay-side theorem for the bounded common-forest normal form

`comparisonCost` charges a comparison rotation at depth d by d+1, and a
search, common split, or common join by one. `mass` is twice the initial key
count plus the initial component count. The actual bounded normalizer supplies
neighbor slack 20 and rotation depth at most one; `boundedRequest` and
`prepare` below translate exactly those local guarantees into physical moves.
-/

namespace MultiSplay.Unlocated

open Splay.Interface (Parameters)
open Splay.Accounting
open Splay.Tree.BST

variable {params : Parameters} {slack depth : Nat} {before after : List Trees}

def Move.comparisonCost : Move params slack depth before after → Nat
  | .rotation (actualDepth := actualDepth) .. => actualDepth+1
  | .request .. | .split .. | .join .. => 1
  | .reorder .. => 0

abbrev Program.comparisonCost (program : Program params slack depth before after) := program.sum Move.comparisonCost

theorem Move.volume_le_comparisonCost (move : Move params slack depth before after) :
    move.requests + move.rotations + move.boundaries ≤ move.comparisonCost := by
  cases move <;> simp [Move.requests, Move.rotations, Move.boundaries, Move.comparisonCost]

theorem Program.volume_le_comparisonCost (program : Program params slack depth before after) :
    program.requests + program.rotations + program.boundaries ≤ program.comparisonCost := by
  induction program with
  | done => exact Nat.le_refl _
  | next move tail ih =>
      have paid := move.volume_le_comparisonCost
      change (move.requests+tail.requests)+(move.rotations+tail.rotations)+(move.boundaries+tail.boundaries) ≤
        move.comparisonCost+tail.comparisonCost
      omega

theorem mass_eq (forest : List Trees) : mass forest = 2*(forest.map Trees.size).sum + forest.length := by
  induction forest with
  | nil => rfl
  | cons head tail ih =>
      simp only [mass, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      omega

/-- Uniform common-forest splay bound with the original iterated-log factor.
The theorem constructs the complete global accounting execution internally. -/
theorem forest_splay_bound :
    ∃ constant : Nat, 0 < constant ∧ ∀ (capacity : Nat) {before after : List Trees}
      (program : Program (articleParameters (Layered.Bounded.height capacity)) 20 1 before after),
      (∀ trees ∈ before, trees.comparison.height ≤ Layered.Bounded.height capacity) →
      program.splayCost + program.boundaries ≤
        constant * (2*(before.map Trees.size).sum + before.length + program.comparisonCost) *
          Splay.Analysis.targetFactor capacity := by
  obtain ⟨constant, positive, bound⟩ := normalized_splay_bound 20 1
  refine ⟨constant, positive, ?_⟩
  intro capacity before after program bounded
  have volume : program.volume ≤ mass before + program.comparisonCost := by
    have paid := program.volume_le_comparisonCost
    unfold Program.volume
    omega
  rw [mass_eq] at volume
  exact (bound capacity program bounded).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left constant volume))

def boundedRequest {n : Nat} (height slack depth : Nat) (comparison before after : Splay.Tree.BST 0 n)
    (key : Fin n) (tail : List Trees) (root : comparison.HasRoot key.val)
    (execution : SplayExecution key.val before after) (bounded : comparison.height ≤ height)
    (ribs : OfflineNormalForm.HasBoundedMinorRibs comparison slack) :
    Move (articleParameters height) slack depth (⟨n, comparison, before⟩ :: tail) (⟨n, comparison, after⟩ :: tail) :=
  .request comparison before after key tail root execution
    (Splay.Analysis.contractedGap_mono (by change 2*comparison.height+1 ≤ 2*height+1; omega))
    ((OfflineNormalForm.hasBoundedMinorRibs_iff_relevantNeighborDepth comparison).mp ribs).toRankBound

theorem prepare {n height slack count : Nat} {before after : Splay.Tree.BST 0 n}
    (path : BoundedMacros.Path height slack before after count) (splay : Splay.Tree.BST 0 n)
    (tail : List Trees) (params : Parameters) :
    ∃ program : Program params slack 1 (⟨n, before, splay⟩ :: tail) (⟨n, after, splay⟩ :: tail),
      program.rotations = count ∧ program.requests = 0 ∧ program.boundaries = 0 ∧ program.splayCost = 0 ∧
        program.comparisonCost ≤ 2*count := by
  induction path with
  | nil source bounded ribs => exact ⟨.done _, rfl, rfl, rfl, rfl, Nat.le_refl 0⟩
  | cons rotation shallow bounded ribs rest ih =>
      obtain ⟨later, rotations, requests, boundaries, cost, work⟩ := ih
      refine ⟨.next (.rotation _ _ splay tail rotation shallow) later, ?_, ?_, ?_, ?_, ?_⟩
      · change 1+later.rotations = _
        omega
      · simpa [Program.requests, Program.sum, Move.requests] using requests
      · simpa [Program.boundaries, Program.sum, Move.boundaries] using boundaries
      · simpa [Program.splayCost, Program.sum, Move.splayCost] using cost
      · change _+1+later.comparisonCost ≤ _
        omega

end MultiSplay.Unlocated
