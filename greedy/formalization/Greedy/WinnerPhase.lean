import Greedy.WinnerTickets

/-! Membership win counts in the two literal sides of an access. -/

namespace Greedy.WinnerTickets

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.PlateauBridge
open GreedyMerge.AccessSourceAccounting GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.FrozenHistory

theorem record_injective {n access lo hi : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (tree : BST lo hi) (upper : hi ≤ p.count) :
    Set.InjOn (AtomOwner p.separator data.gapOwner) {key | key ∈ atoms tree} := by
  intro first firstMem second secondMem same
  have firstBound := (atoms_mem_iff tree first).mp firstMem
  have secondBound := (atoms_mem_iff tree second).mp secondMem
  exact (GreedyMerge.MappedConsolidation.atom_owner_eq_iff comparator p data.gapOwner data.minima (by omega) (by omega)).mp same

noncomputable def part {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (side : Bool) (block : Frozen) (joined : ℕ) : ℕ :=
  if side then (wins (states source side) block (AtomOwner p.separator data.gapOwner) data.owner data.left joined).card
  else (wins (states source side) block (AtomOwner p.separator data.gapOwner) data.owner data.right joined).card

theorem nonempty_contains {lo hi : ℕ} (state : SideState) (block : Frozen) (record owner : ℕ → ℕ)
    (tree : BST lo hi) (joined source : ℕ) (side : Bool) (valid : Valid source side state)
    (blockMem : block ∈ state.shrinking) (nonzero : (wins state block record owner tree joined).card ≠ 0) : joined ∈ joins block := by
  obtain ⟨edge, member⟩ := Finset.card_ne_zero.mp nonzero
  obtain ⟨winner, _, winnerMem, _, _, _, winnerTime⟩ := witnesses state block record owner tree joined source side valid blockMem edge member
  exact winnerTime ▸ GreedyMerge.HistoryProcess.entry_join_mem winnerMem

theorem part_nonzero_contains {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (side : Bool) (block : Frozen) (joined : ℕ)
    (valid : Valid source.val side (states source side)) (member : block ∈ (states source side).shrinking)
    (nonzero : part data states source side block joined ≠ 0) : joined ∈ joins block := by
  cases side <;> exact nonempty_contains _ _ _ _ _ _ _ _ valid member nonzero

theorem part_bound {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (side : Bool) (block : Frozen) (joined : ℕ)
    (valid : Valid source.val side (states source side)) (member : block ∈ (states source side).shrinking)
    (history : ∃ orientation, HistMonotone orientation block.members) : part data states source side block joined ≤ 4 := by
  have upper := data.right.lower_le_upper
  cases side with
  | false =>
      apply count_le_four _ data.owner data.right data.projection.2.2 _ _ block _ joined source.val false valid member history
        (record_injective data data.right (le_refl _))
      intro q lower bound
      exact data.localOwners q (by omega) bound
  | true =>
      apply count_le_four _ data.owner data.left data.projection.2.1 _ _ block _ joined source.val true valid member history
        (record_injective data data.left (by omega))
      intro q lower bound
      exact data.localOwners q lower (by omega)

theorem part_zero_of_isolated {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (side : Bool) (block : Frozen) (joined : ℕ)
    (valid : Valid source.val side (states source side)) (member : block ∈ (states source side).shrinking)
    (history : ∃ orientation, HistMonotone orientation block.members) (isolated : ClosedFamilies.Isolated joined block) :
    part data states source side block joined = 0 := by
  have upper := data.right.lower_le_upper
  cases side with
  | false =>
      have zero := isolated_no_wins _ data.owner data.right data.projection.2.2
        (fun q lower bound => data.localOwners q (by omega) bound) _ block _ joined source.val false valid member history
        (record_injective data data.right (le_refl _)) isolated
      simp only [part, Bool.false_eq_true, if_false, zero, Finset.card_empty]
  | true =>
      have zero := isolated_no_wins _ data.owner data.left data.projection.2.1
        (fun q lower bound => data.localOwners q lower (by omega)) _ block _ joined source.val true valid member history
        (record_injective data data.left (by omega)) isolated
      simp only [part, if_true, zero, Finset.card_empty]

end Greedy.WinnerTickets
