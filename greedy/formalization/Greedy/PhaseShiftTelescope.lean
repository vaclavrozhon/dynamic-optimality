import Greedy.StoredCreatorLabels
import Greedy.HistoryPairing
import Greedy.FamilyPhaseSum

/-! Stored creator shifts in one actual access equal its sparse pairing. -/

namespace Greedy.CreatorPhase

open Splay.Tree Splay.Rank GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.ActualLinks
open GreedyMerge.AccessSourceAccounting GreedyMerge.PathPlateau GreedyMerge.PlateauBridge
open scoped BigOperators

noncomputable def shiftCoefficient {lo hi : ℕ} (state : SideState) (block : Frozen)
    (record owner : ℕ → ℕ) (tree : BST lo hi) : ℤ :=
  ∑ edge ∈ (schedule owner tree).toFinset, shiftWeight state block record edge

theorem shiftCoefficient_telescope {n lo hi : ℕ} (history : LabelHistory.History (External n))
    (state : SideState) (block : Frozen) (record owner : ℕ → ℕ) (tree : BST lo hi) (source : ℕ) (side : Bool)
    (valid : Valid source side state) (member : block ∈ state.shrinking)
    (snapshots : ∀ entry ∈ block.members, LabelSnapshots.Snapshot history block.creator entry) :
    shiftCoefficient state block record owner tree = LabelHistory.pairing history (fun creator time =>
      if block.creator = creator.val then coefficient state block record owner tree time else 0) := by
  classical
  unfold shiftCoefficient
  have one (edge : ℕ × ℕ) : shiftWeight state block record edge = LabelHistory.pairing history
      (fun creator time => if block.creator = creator.val then weight state block record time edge else 0) := by
    simpa only [LabelHistory.pairing, ite_mul, zero_mul] using
      shiftWeight_telescope history state block record source side valid member snapshots edge
  rw [Finset.sum_congr rfl (fun edge _ => one edge), ← LabelHistory.pairing_sum]
  congr 1
  funext creator time
  by_cases equal : block.creator = creator.val <;> simp [equal, coefficient]

noncomputable def shiftPart {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (side : Bool) (block : Frozen) : ℤ :=
  if side then shiftCoefficient (states source side) block (AtomOwner p.separator data.gapOwner) data.owner data.left
  else shiftCoefficient (states source side) block (AtomOwner p.separator data.gapOwner) data.owner data.right

theorem shiftPart_telescope {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (history : LabelHistory.History (External n)) (states : HeapSides n) (source : External n)
    (side : Bool) (block : Frozen) (valid : Valid source.val side (states source side))
    (member : block ∈ (states source side).shrinking) (snapshots : LabelSnapshots.HeapSnapshots history states) :
    shiftPart data states source side block = LabelHistory.pairing history
      (fun creator time => if block.creator = creator.val then part data states source side block time else 0) := by
  have stored : ∀ entry ∈ block.members, LabelSnapshots.Snapshot history block.creator entry :=
    fun entry entryMem => snapshots source side entry block.creator
      (LabelSnapshots.tagged_frozen _ block member entry entryMem)
  cases side <;> exact shiftCoefficient_telescope history _ block _ _ _ source.val _ valid member stored

noncomputable def shiftPhase {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) : ℤ :=
  ∑ piece ∈ pieces states source, shiftPart data states source piece.1 piece.2

theorem shiftPhase_telescope {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (history : LabelHistory.History (External n)) (states : HeapSides n) (source : External n)
    (valid : ∀ side, Valid source.val side (states source side)) (snapshots : LabelSnapshots.HeapSnapshots history states)
    (names : Finset ℕ) (covers : ∀ side block, block ∈ (states source side).shrinking → block.family ∈ names) :
    shiftPhase data states source = LabelHistory.pairing history
      (fun creator time => ∑ family ∈ names, familyCoefficient data states source creator.val family time) := by
  classical
  have one (piece : Bool × Frozen) (member : piece ∈ pieces states source) :
      shiftPart data states source piece.1 piece.2 = LabelHistory.pairing history
        (fun creator time => if piece.2.creator = creator.val then part data states source piece.1 piece.2 time else 0) :=
    shiftPart_telescope data history states source piece.1 piece.2 (valid piece.1) ((mem_pieces ..).mp member) snapshots
  unfold shiftPhase
  rw [Finset.sum_congr rfl one, ← LabelHistory.pairing_sum]
  congr 1
  funext creator time
  unfold familyCoefficient
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro piece member
  have familyMem := covers piece.1 piece.2 ((mem_pieces ..).mp member)
  by_cases created : piece.2.creator = creator.val
  · simp [created, familyMem]
  · simp [created]

end Greedy.CreatorPhase
