import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Lean.Elab.Tactic.Omega

/-!
Exact five-port algebra for an ordinary refinement rotation at fixed ranks.
Ports in inorder are A*, a, B*, b, C*. Only the roots of the three fringe
subtrees occur here; their internal edges remain outside this local model.

Before rotation, ports 0,1,2 are grouped first. Afterwards, ports 2,3,4 are
grouped first. This file proves that at most two port parent identities
change for arbitrary ranks with a unique global minimum and valid local
minima. The finite shape lemma uses kernel `decide`, not a native oracle.
-/

namespace GreedyMerge.RotationPorts

abbrev Port := Fin 5

def BeforeParent (leftWinner global : Port) (child : Port) : Option Port :=
  if child = global then none
  else if child.val < 3 ∧ child ≠ leftWinner then some leftWinner
  else some global

def AfterParent (rightWinner global : Port) (child : Port) : Option Port :=
  if child = global then none
  else if 2 ≤ child.val ∧ child ≠ rightWinner then some rightWinner
  else some global

def Changed (leftWinner rightWinner global : Port) : Finset Port :=
  Finset.univ.filter fun child =>
    BeforeParent leftWinner global child ≠ AfterParent rightWinner global child

/-- Five global-minimum locations and three possible local minima on each
side suffice. Equal nonminimum ranks impose no additional condition. -/
theorem changed_card_le_two_finite :
    ∀ leftWinner rightWinner global : Port,
      leftWinner.val < 3 → 2 ≤ rightWinner.val →
      (global.val < 3 → leftWinner = global) →
      (2 ≤ global.val → rightWinner = global) →
      (Changed leftWinner rightWinner global).card ≤ 2 := by
  decide

def UniqueGlobalMinimum (rank : Port → ℕ) (global : Port) : Prop :=
  ∀ child, child ≠ global → rank global < rank child

def LeftMinimum (rank : Port → ℕ) (winner : Port) : Prop :=
  winner.val < 3 ∧ ∀ child, child.val < 3 → rank winner ≤ rank child

def RightMinimum (rank : Port → ℕ) (winner : Port) : Prop :=
  2 ≤ winner.val ∧ ∀ child, 2 ≤ child.val → rank winner ≤ rank child

theorem leftMinimum_eq_global {rank : Port → ℕ} {winner global : Port}
    (hglobal : UniqueGlobalMinimum rank global) (hleft : LeftMinimum rank winner)
    (inside : global.val < 3) : winner = global := by
  by_contra hne
  have hl := hleft.2 global inside
  have hg := hglobal winner hne
  omega

theorem rightMinimum_eq_global {rank : Port → ℕ} {winner global : Port}
    (hglobal : UniqueGlobalMinimum rank global) (hright : RightMinimum rank winner)
    (inside : 2 ≤ global.val) : winner = global := by
  by_contra hne
  have hl := hright.2 global inside
  have hg := hglobal winner hne
  omega

/-- Under actual minimum-rank choices, no more than two port attachments
change when the binary refinement rotates. -/
theorem changed_card_le_two {rank : Port → ℕ} {leftWinner rightWinner global : Port}
    (hglobal : UniqueGlobalMinimum rank global)
    (hleft : LeftMinimum rank leftWinner) (hright : RightMinimum rank rightWinner) :
    (Changed leftWinner rightWinner global).card ≤ 2 := by
  exact changed_card_le_two_finite leftWinner rightWinner global hleft.1 hright.1
    (leftMinimum_eq_global hglobal hleft) (rightMinimum_eq_global hglobal hright)

theorem middle_global_no_change :
    ∀ child : Port, BeforeParent 2 2 child = AfterParent 2 2 child := by
  decide

end GreedyMerge.RotationPorts

#print axioms GreedyMerge.RotationPorts.changed_card_le_two
