import AccessSourceAccounting

/-!
Read immutable joined timestamps from the actual source Entry records.
The source block's inherited chronological orientation and the stored
spatial ordering imply the monotone/antitone key-cut hypothesis used by
the creator charge. Neither a join-label lookup nor a cut-edge projection
is supplied independently.
-/
namespace GreedyMerge.AccessSourceAccounting

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.PathPlateau GreedyMerge.PlateauBridge GreedyMerge.AccessFrontier
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.ActualBlockPartition
open GreedyForest.Phase

noncomputable def storedJoin (state : SideState) (key : ℕ) : ℕ := by
  classical
  exact if present : ∃ entry∈entries state, entry.key=key then present.choose.joined else 0

theorem storedJoin_of_member (state : SideState) (owner : ℕ) (side : Bool)
    (valid : Valid owner side state) (entry : Entry) (member : entry∈entries state) :
    storedJoin state entry.key=entry.joined := by
  have present : ∃ actual∈entries state, actual.key=entry.key := ⟨entry,member,rfl⟩
  simp only [storedJoin,dif_pos present]
  have same := List.inj_on_of_nodup_map (StateLabels.entries_key_nodup owner side state valid)
    present.choose_spec.1 member present.choose_spec.2
  exact congrArg Entry.joined same

theorem storedJoin_of_frozen (state : SideState) (owner : ℕ) (side : Bool)
    (valid : Valid owner side state) (block : Frozen) (blockMem : block∈state.shrinking)
    (entry : Entry) (member : entry∈block.members) : storedJoin state entry.key=entry.joined := by
  apply storedJoin_of_member state owner side valid entry
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨block,blockMem,member⟩

theorem frozen_spatial_order (state : SideState) (owner : ℕ) (side : Bool)
    (valid : Valid owner side state) (block : Frozen) (blockMem : block∈state.shrinking) :
    block.members.Pairwise (OrderedBlocks.outward side) := by
  have flat := (List.pairwise_append.mp valid.1).1
  exact (List.pairwise_flatMap.mp flat).1 block blockMem

/-- Convert strict list chronology to the weak comparison of any two
records in ascending physical-key order. Equal records are allowed. -/
theorem increasing_history_compare (members : List Entry) (orientation : Bool)
    (ordered : members.Pairwise (fun first second => first.key<second.key))
    (history : HistMonotone orientation members)
    (first second : Entry) (firstMem : first∈members) (secondMem : second∈members)
    (keyOrder : first.key ≤ second.key) :
    if orientation then first.joined ≤ second.joined else second.joined ≤ first.joined := by
  induction members generalizing first second with
  | nil => simp at firstMem
  | cons head tail ih =>
      have spatial := List.pairwise_cons.mp ordered
      have times := List.pairwise_cons.mp history
      rcases List.mem_cons.mp firstMem with rfl | firstTail
      · rcases List.mem_cons.mp secondMem with rfl | secondTail
        · cases orientation <;> exact le_refl _
        · have less := times.1 second secondTail
          cases orientation <;> exact Nat.le_of_lt less
      · rcases List.mem_cons.mp secondMem with rfl | secondTail
        · have backwards := spatial.1 first firstTail
          omega
        · exact ih spatial.2 times.2 first second firstTail secondTail keyOrder

def increasingMembers (side : Bool) (block : Frozen) : List Entry :=
  if side then block.members.reverse else block.members

@[simp] theorem increasingMembers_mem (side : Bool) (block : Frozen) (entry : Entry) :
    entry∈increasingMembers side block ↔ entry∈block.members := by
  cases side <;> simp [increasingMembers]

theorem increasingMembers_order (state : SideState) (owner : ℕ) (side : Bool)
    (valid : Valid owner side state) (block : Frozen) (blockMem : block∈state.shrinking) :
    (increasingMembers side block).Pairwise (fun first second => first.key<second.key) := by
  have order := frozen_spatial_order state owner side valid block blockMem
  cases side with
  | false => exact order
  | true =>
      change block.members.reverse.Pairwise (fun first second => first.key<second.key)
      exact List.pairwise_reverse.mpr order

theorem increasingMembers_history (side : Bool) (block : Frozen)
    (history : ∃ orientation, HistMonotone orientation block.members) :
    ∃ orientation, HistMonotone orientation (increasingMembers side block) := by
  obtain ⟨orientation,history⟩ := history
  cases side with
  | false => exact ⟨orientation,history⟩
  | true =>
      refine ⟨!orientation,?_⟩
      cases orientation <;> simpa only [increasingMembers,HistMonotone,if_true,if_false,
        Bool.false_eq_true,Bool.not_false,Bool.not_true,List.pairwise_reverse] using history

/-- The creator-cut monotonicity hypothesis is derived from the actual
Entry list, including leftward sides whose spatial order is reversed. -/
theorem SideView.storedJoin_order {lo hi : ℕ} {rank : ℕ→ℕ} {initial : ℕ→ℤ} {record : ℕ→ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (source : ℕ) (side : Bool) (valid : Valid source side state)
    (recordMono : ∀ first∈atoms tree, ∀ second∈atoms tree,
      first ≤ second → record first ≤ record second)
    (block : Frozen) (blockMem : block∈state.shrinking)
    (history : ∃ orientation, HistMonotone orientation block.members) :
    (∀ first∈blockMembers tree view.partition.block block.id,
      ∀ second∈blockMembers tree view.partition.block block.id, first ≤ second →
      storedJoin state (record first) ≤ storedJoin state (record second)) ∨
    (∀ first∈blockMembers tree view.partition.block block.id,
      ∀ second∈blockMembers tree view.partition.block block.id, first ≤ second →
      storedJoin state (record second) ≤ storedJoin state (record first)) := by
  obtain ⟨orientation,orientedHistory⟩ := increasingMembers_history side block history
  have orientedOrder := increasingMembers_order state source side valid block blockMem
  have compare : ∀ first∈blockMembers tree view.partition.block block.id,
      ∀ second∈blockMembers tree view.partition.block block.id, first ≤ second →
      if orientation then storedJoin state (record first) ≤ storedJoin state (record second)
      else storedJoin state (record second) ≤ storedJoin state (record first) := by
    intro first firstMem second secondMem less
    obtain ⟨firstAtom,firstBlock⟩ := Finset.mem_filter.mp firstMem
    obtain ⟨secondAtom,secondBlock⟩ := Finset.mem_filter.mp secondMem
    have firstBounds := (atoms_mem_iff tree first).mp (List.mem_toFinset.mp firstAtom)
    have secondBounds := (atoms_mem_iff tree second).mp (List.mem_toFinset.mp secondAtom)
    obtain ⟨firstEntry,firstEntryMem,firstKey⟩ := List.mem_map.mp
      ((view.matching first firstBounds.1 firstBounds.2 block blockMem).mp firstBlock)
    obtain ⟨secondEntry,secondEntryMem,secondKey⟩ := List.mem_map.mp
      ((view.matching second secondBounds.1 secondBounds.2 block blockMem).mp secondBlock)
    have entryOrder : firstEntry.key ≤ secondEntry.key := by
      rw [firstKey,secondKey]
      exact recordMono first (List.mem_toFinset.mp firstAtom) second (List.mem_toFinset.mp secondAtom) less
    have compared := increasing_history_compare (increasingMembers side block) orientation orientedOrder
      orientedHistory firstEntry secondEntry ((increasingMembers_mem side block firstEntry).mpr firstEntryMem)
      ((increasingMembers_mem side block secondEntry).mpr secondEntryMem) entryOrder
    rw [←firstKey,←secondKey,
      storedJoin_of_frozen state source side valid block blockMem firstEntry firstEntryMem,
      storedJoin_of_frozen state source side valid block blockMem secondEntry secondEntryMem]
    exact compared
  cases orientation with
  | false => exact Or.inr (by simpa only [Bool.false_eq_true,if_false] using compare)
  | true => exact Or.inl (by simpa only [if_true] using compare)

/-- The literal block's creator-cut geometry uses its actual immutable
join snapshots. The geometric cut is constructed by the existing local
cut theorem after the stored-history monotonicity is discharged. -/
theorem SideView.creator_cut_geometry {lo hi : ℕ} {rank : ℕ→ℕ} {initial : ℕ→ℤ} {record : ℕ→ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (source : ℕ) (side : Bool) (valid : Valid source side state)
    (recordMono : ∀ first∈atoms tree, ∀ second∈atoms tree,
      first ≤ second → record first ≤ record second)
    (owner : ℕ→ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi)
    (block : Frozen) (blockMem : block∈state.shrinking)
    (history : ∃ orientation, HistMonotone orientation block.members) (time H : ℕ)
    (bound : ∀ atom, 2*lo ≤ atom → atom ≤ 2*hi → rank (record atom) ≤ H) :
    Nonempty (GreedyForest.Execution.CutPhaseGeometry (contractedGap H)
      (blockBadCrossings (rank ∘ record) (initial ∘ record) (schedule owner tree)
        view.partition.block (storedJoin state ∘ record) block.id time).card) := by
  exact block_creator_cut_geometry _ owner tree projection localOwners _ view.partition _ block.id time H
    (view.storedJoin_order source side valid recordMono block blockMem history) bound

end GreedyMerge.AccessSourceAccounting

#print axioms GreedyMerge.AccessSourceAccounting.storedJoin_of_frozen
#print axioms GreedyMerge.AccessSourceAccounting.SideView.storedJoin_order
#print axioms GreedyMerge.AccessSourceAccounting.SideView.creator_cut_geometry
