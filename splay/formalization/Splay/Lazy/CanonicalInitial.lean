import Splay.Lazy.CanonicalValues
import Splay.Lazy.Model

namespace Splay.Lazy.Canonical

open Splay.Rank

/--
The empty-block interface starting point associated with a canonical heap
view.  It carries the eventual canonical values but has not yet created or
populated any lazy blocks.
-/
noncomputable def emptyCanonicalState {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) : State n where
  view := canonicalHeapView snapshot tree
  blocks := []
  value := canonicalValue snapshot tree

@[simp]
theorem emptyCanonicalState_view {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (emptyCanonicalState snapshot tree).view =
      canonicalHeapView snapshot tree :=
  rfl

@[simp]
theorem emptyCanonicalState_blocks {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (emptyCanonicalState snapshot tree).blocks = [] :=
  rfl

@[simp]
theorem emptyCanonicalState_value {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (emptyCanonicalState snapshot tree).value =
      canonicalValue snapshot tree :=
  rfl

/-- Its abstract projection is a genuine initial interface state. -/
theorem emptyCanonicalState_toInterface_initial {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    (emptyCanonicalState snapshot tree).toInterface.Initial params := by
  constructor
  · constructor
    · simp [emptyCanonicalState, State.toInterface,
        Interface.State.allElements]
    · constructor
      · intro element
        constructor
        · exact canonicalValue_pos snapshot tree element
        · exact
            (canonicalValue_le_contractedGap_maxRank
              snapshot tree element).trans valueBound
      · intro creator
        simp [emptyCanonicalState, State.toInterface,
          Interface.State.growingCount]
  · rfl

/--
The rich empty-block state is transient-valid; local block obligations are
vacuous.  It is intentionally not stable, because all non-root heap paths are
still detached.
-/
theorem emptyCanonicalState_valid {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    (emptyCanonicalState snapshot tree).Valid params := by
  constructor
  · exact
      (emptyCanonicalState_toInterface_initial
        snapshot tree params valueBound).1
  · intro block member
    simp [emptyCanonicalState] at member

end Splay.Lazy.Canonical
