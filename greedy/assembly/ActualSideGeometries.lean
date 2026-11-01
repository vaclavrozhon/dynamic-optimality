import StoredSourceHistory

/-! Instantiate the local accounting geometries from the exact data of
an actual access. Cartesian shape, local owners, interval uniqueness,
record monotonicity and immutable source chronology are derived from
that same factory witness and concrete state invariants. -/
namespace GreedyMerge.AccessSourceAccounting

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.PathPlateau GreedyMerge.PlateauBridge GreedyMerge.AccessConsolidation
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open GreedyForest.Phase

theorem atom_owner_monotone_on_tree {n access lo hi : ℕ} (comparator oldTree : BST 0 n)
    (p : Decomposition oldTree access) (gapOwner : ℕ→ℕ)
    (minima : ∀ i, i ≤ p.count → GreedyMerge.IntervalRootOracle.UniqueMin comparator.externalDepth
      (2*GreedyMerge.ExpansionRotations.GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (tree : BST lo hi) (upper : hi ≤ p.count) :
    ∀ first∈atoms tree, ∀ second∈atoms tree, first ≤ second →
      AtomOwner p.separator gapOwner first ≤ AtomOwner p.separator gapOwner second := by
  intro first firstMem second secondMem less
  rcases lt_or_eq_of_le less with strict | rfl
  · have firstBound := (atoms_mem_iff tree first).mp firstMem
    have secondBound := (atoms_mem_iff tree second).mp secondMem
    exact Nat.le_of_lt ((GreedyMerge.MappedConsolidation.atom_owner_lt_iff comparator p gapOwner minima
      (by omega) (by omega)).mpr strict)
  · exact le_refl _

theorem left_winner_geometry {n access : ℕ} (comparator oldTree newTree : BST 0 n)
    (p : Decomposition oldTree access) (data : AccessScheduleData comparator oldTree newTree p)
    (initial : ℕ→ℤ) (state : SideState)
    (view : SideView comparator.externalDepth initial (AtomOwner p.separator data.gapOwner) data.left state)
    (winner : ℕ) :
    Nonempty (GreedyForest.Execution.WinnerPhaseGeometry
      (actualBadWins (comparator.externalDepth ∘ AtomOwner p.separator data.gapOwner)
        (initial ∘ AtomOwner p.separator data.gapOwner) (schedule data.owner data.left)
        view.partition.block winner).card) := by
  have upper := data.right.lower_le_upper
  apply actual_winner_geometry _ data.owner data.left
    (canonical_cartesian _ data.left data.canonical.2.1)
  · intro q lower bound
    exact data.localOwners q lower (by omega)
  · intro lo hi first second lower bound
    exact atom_intervals_unique comparator p data.gapOwner data.minima lo hi first second lower (by omega)

theorem right_winner_geometry {n access : ℕ} (comparator oldTree newTree : BST 0 n)
    (p : Decomposition oldTree access) (data : AccessScheduleData comparator oldTree newTree p)
    (initial : ℕ→ℤ) (state : SideState)
    (view : SideView comparator.externalDepth initial (AtomOwner p.separator data.gapOwner) data.right state)
    (winner : ℕ) :
    Nonempty (GreedyForest.Execution.WinnerPhaseGeometry
      (actualBadWins (comparator.externalDepth ∘ AtomOwner p.separator data.gapOwner)
        (initial ∘ AtomOwner p.separator data.gapOwner) (schedule data.owner data.right)
        view.partition.block winner).card) := by
  apply actual_winner_geometry _ data.owner data.right
    (canonical_cartesian _ data.right data.canonical.2.2)
  · intro q lower bound
    exact data.localOwners q (Nat.zero_le _) bound
  · intro lo hi first second lower bound
    exact atom_intervals_unique comparator p data.gapOwner data.minima lo hi first second (Nat.zero_le _) bound

/-- The generic subtree version is instantiated with either factory
side; both chronological and physical-key order come from concrete state. -/
theorem actual_creator_cut_geometry {n access lo hi : ℕ} (comparator oldTree : BST 0 n)
    (p : Decomposition oldTree access) (gapOwner : ℕ→ℕ)
    (minima : ∀ i, i ≤ p.count → GreedyMerge.IntervalRootOracle.UniqueMin comparator.externalDepth
      (2*GreedyMerge.ExpansionRotations.GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (tree : BST lo hi) (upper : hi ≤ p.count) (owner : ℕ→ℕ)
    (projection : Projection (comparator.externalDepth ∘ AtomOwner p.separator gapOwner) owner tree)
    (localOwners : LocalOwners (comparator.externalDepth ∘ AtomOwner p.separator gapOwner) owner lo hi)
    (states : States n) (ready : Ready comparator oldTree states) (histories : Histories states)
    (source : External n) (side : Bool) (K : ℤ)
    (view : SideView comparator.externalDepth (StateLabels.label comparator.externalDepth K states)
      (AtomOwner p.separator gapOwner) tree (states source side))
    (block : Frozen) (blockMem : block∈(states source side).shrinking) (time H : ℕ)
    (bound : ∀ atom, 2*lo ≤ atom → atom ≤ 2*hi → comparator.externalDepth (AtomOwner p.separator gapOwner atom) ≤ H) :
    Nonempty (GreedyForest.Execution.CutPhaseGeometry (contractedGap H)
      (blockBadCrossings (comparator.externalDepth ∘ AtomOwner p.separator gapOwner)
        (StateLabels.label comparator.externalDepth K states ∘ AtomOwner p.separator gapOwner)
        (schedule owner tree) view.partition.block (storedJoin (states source side) ∘ AtomOwner p.separator gapOwner)
        block.id time).card) := by
  exact view.creator_cut_geometry source.val side (ready.valid source side)
    (atom_owner_monotone_on_tree comparator oldTree p gapOwner minima tree upper)
    owner projection localOwners block blockMem ((histories source side).1 block blockMem) time H bound

end GreedyMerge.AccessSourceAccounting

#print axioms GreedyMerge.AccessSourceAccounting.left_winner_geometry
#print axioms GreedyMerge.AccessSourceAccounting.right_winner_geometry
#print axioms GreedyMerge.AccessSourceAccounting.actual_creator_cut_geometry
