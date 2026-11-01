import Greedy.RunClosedFamilies
import Greedy.FamilyCutState

/-! Once all fragments of a closed family avoid a cut, they avoid it forever. -/

namespace Greedy.ClosedFamilies

open Splay.Rank GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.FrozenHistory GreedyForest

def AvoidsCut (cut : ℕ) (block : Frozen) : Prop :=
  ¬ GreedyForest.Straddles (fun joined => decide (cut ≤ joined)) (joins block)

theorem avoidsCut_hereditary (cut : ℕ) : Hereditary (AvoidsCut cut) := by
  intro before after descendant avoids crossing
  exact avoids (straddles_of_subset _ _ _ (descends_joins descendant) crossing)

theorem Closed.with_property {Slot : Type*} {family : ℕ} {firstProperty : Frozen → Prop}
    {states : Slot → SideState} (closed : Closed family firstProperty states) (property : Frozen → Prop)
    (holds : ∀ slot block, block ∈ (states slot).shrinking → block.family = family → property block) : Closed family property states :=
  ⟨closed.growing, holds⟩

theorem closed_of_separated {n family : ℕ} {oldProperty : Frozen → Prop} {states : HeapSides n}
    (closed : HeapClosed family oldProperty states) (cut : ℕ)
    (separated : CutSeparated (fun joined => decide (cut ≤ joined))
      (familyView family (FamilyOrder.allFrozen (table states)))) : HeapClosed family (AvoidsCut cut) states := by
  apply closed.with_property (AvoidsCut cut)
  intro slot block member same
  exact separated (joins block) (mem_familyView.mpr ⟨block, FamilyOrder.mem_allFrozen (table states) slot block member, same, rfl⟩)

theorem coefficient_zero {n family time : ℕ} {states : HeapSides n}
    (closed : HeapClosed family (AvoidsCut (time+1)) states) (owner : External n) (side : Bool)
    (block : Frozen) (member : block ∈ (states owner side).shrinking) (same : block.family = family)
    (winner loser : Entry) (winnerMem : winner ∈ block.members) (loserMem : loser ∈ block.members) :
    joinCoefficient winner.joined loser.joined time = 0 := by
  have avoids := closed.frozen (encode n (owner, side)) block (by simpa [table] using member) same
  by_contra nonzero
  exact avoids (FamilyOrder.coefficient_straddles block winner loser time winnerMem loserMem nonzero)

theorem no_future_crossings {n family time : ℕ} {K : ℤ}
    {first last : Greedy.Execution.State n} {requests : List (Fin n)}
    (execution : Greedy.Execution.Run K first last requests)
    (closed : HeapClosed family (AvoidsCut (time+1)) first.blocks) (past : family < first.next) :
    AllSourcesClosed (family := family) (AvoidsCut (time+1)) execution :=
  all_sources_closed execution closed (avoidsCut_hereditary (time+1)) past

end Greedy.ClosedFamilies
