import ActualBlockPartition

/-!
Orient the literal persistent side-block state into increasing search order
and derive its accounting partition. The list cover is reconstructed from
the actual state's orderedness and record coverage, rather than supplied
as block interval endpoints or an independently chosen ID map.
-/
namespace GreedyMerge.SourceSideStates
open Splay.Tree Splay.Tree.BST Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open GreedyMerge.ActualBlockPartition
open GreedyMerge.PathPlateau GreedyMerge.IntervalRootOracle GreedyMerge.ExpansionRotations
open GreedyMerge.PlateauBridge
open GreedyForest.Phase

def orientBlock (goLeft : Bool) (block : Frozen) : Frozen :=
  if goLeft then { block with members := block.members.reverse } else block

def orientBlocks (goLeft : Bool) (blocks : List Frozen) : List Frozen :=
  if goLeft then blocks.reverse.map (orientBlock true) else blocks

@[simp] theorem orientBlock_id (goLeft : Bool) (block : Frozen) :
    (orientBlock goLeft block).id = block.id := by cases goLeft <;> rfl

@[simp] theorem orientBlock_base (goLeft : Bool) (block : Frozen) :
    (orientBlock goLeft block).base = block.base := by cases goLeft <;> rfl

@[simp] theorem orientBlock_mem (goLeft : Bool) (block : Frozen) (entry : Entry) :
    entry ∈ (orientBlock goLeft block).members ↔ entry ∈ block.members := by
  cases goLeft <;> simp [orientBlock]

@[simp] theorem orientBlock_keys (goLeft : Bool) (block : Frozen) (key : ℕ) :
    key ∈ blockKeys (orientBlock goLeft block) ↔ key ∈ blockKeys block := by
  simp only [blockKeys,List.mem_map,orientBlock_mem]

theorem orientBlocks_mem (goLeft : Bool) (blocks : List Frozen) (block : Frozen) :
    block ∈ orientBlocks goLeft blocks ↔ ∃ old ∈ blocks, orientBlock goLeft old=block := by
  cases goLeft <;> simp [orientBlocks,orientBlock]

theorem orientBlocks_ids (goLeft : Bool) (blocks : List Frozen) :
    (orientBlocks goLeft blocks).map Frozen.id =
      if goLeft then (blocks.map Frozen.id).reverse else blocks.map Frozen.id := by
  cases goLeft <;> simp [orientBlocks,List.map_map,List.map_reverse,Function.comp_def]

theorem orientBlocks_entries (goLeft : Bool) (blocks : List Frozen) :
    frozenEntries (orientBlocks goLeft blocks) =
      if goLeft then (frozenEntries blocks).reverse else frozenEntries blocks := by
  cases goLeft
  · rfl
  · simp only [orientBlocks,↓reduceIte,frozenEntries,List.flatMap_map,
      orientBlock,List.reverse_flatMap]
    rfl

def increasingKeys (goLeft : Bool) (state : SideState) : List ℕ :=
  if goLeft then ((entries state).map Entry.key).reverse else (entries state).map Entry.key

theorem keys_orientBlocks (goLeft : Bool) (state : SideState)
    (emptyGrower : growerEntries state.grower = []) :
    keys (orientBlocks goLeft state.shrinking)=increasingKeys goLeft state := by
  rw [keys_eq_entries,orientBlocks_entries]
  cases goLeft <;> simp [increasingKeys,entries,emptyGrower,List.map_reverse]

theorem increasingKeys_sorted {owner : ℕ} {goLeft : Bool} {state : SideState}
    (valid : Valid owner goLeft state) :
    (increasingKeys goLeft state).Pairwise (fun a b => a<b) := by
  cases goLeft
  · have order : (entries state).Pairwise (fun a b => a.key < b.key) := valid.1
    simpa [increasingKeys,List.pairwise_map] using order
  · have order : (entries state).Pairwise (fun a b => b.key < a.key) := valid.1
    simpa [increasingKeys,List.pairwise_reverse,List.pairwise_map] using order

theorem increasingKeys_membership (goLeft : Bool) (state : SideState) (key : ℕ) :
    key ∈ increasingKeys goLeft state ↔ key ∈ (entries state).map Entry.key := by
  cases goLeft <;> simp [increasingKeys]

theorem atoms_eq_range' {lo hi : ℕ} (tree : BST lo hi) :
    atoms tree = List.range' (2*lo) (2*hi+1-2*lo) := by
  have order := tree.lower_le_upper
  apply List.Pairwise.eq_of_mem_iff (atoms_pairwise tree) (List.pairwise_lt_range' (step := 1))
  intro value
  rw [atoms_mem_iff,mem_range_iff]
  omega

/-- A phase side's literal ordered child state determines the accounting
partition. The coverage hypothesis is ordinary heap-state correctness;
source identities and interval coordinates are constructed internally. -/
theorem source_partition_of_side {n access lo hi ownerKey : ℕ}
    (comparator : BST 0 n) {oldTree : BST 0 n}
    (p : Decomposition oldTree access) (gapOwner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (tree : BST lo hi) (upper : hi ≤ p.count)
    (initial : ℕ → ℤ) (goLeft : Bool) (state : SideState)
    (valid : Valid ownerKey goLeft state)
    (emptyGrower : growerEntries state.grower = [])
    (ids : (state.shrinking.map Frozen.id).Nodup)
    (coverage : ∀ key, key ∈ (entries state).map Entry.key ↔
      key ∈ (atoms tree).map (AtomOwner p.separator gapOwner))
    (buckets : ∀ b ∈ state.shrinking, ∀ e ∈ b.members,
      initial e.key = baseLabel comparator.externalDepth b.base e.key)
    (floors : ∀ b ∈ state.shrinking, ∀ e ∈ b.members,
      b.base ≤ comparator.externalDepth e.key) :
    ∃ s : SourcePartition
        (comparator.externalDepth ∘ AtomOwner p.separator gapOwner)
        (initial ∘ AtomOwner p.separator gapOwner) lo hi,
      (∀ v, 2*lo ≤ v → v ≤ 2*hi → ∀ b ∈ state.shrinking,
        s.block v=b.id ↔ AtomOwner p.separator gapOwner v ∈ blockKeys b) ∧
      (∀ b ∈ state.shrinking, s.base b.id=b.base) := by
  let f := AtomOwner p.separator gapOwner
  have increasing : ((atoms tree).map f).Pairwise (fun a b => a<b) := by
    rw [List.pairwise_map]
    apply (atoms_pairwise tree).imp_of_mem
    intro a b ha hb hab
    have ba := (atoms_mem_iff tree a).mp ha
    have bb := (atoms_mem_iff tree b).mp hb
    exact (GreedyMerge.MappedConsolidation.atom_owner_lt_iff comparator p gapOwner minima
      (by omega) (by omega)).mpr hab
  have orderedCover : keys (orientBlocks goLeft state.shrinking) = (atoms tree).map f := by
    rw [keys_orientBlocks goLeft state emptyGrower]
    apply List.Pairwise.eq_of_mem_iff (increasingKeys_sorted valid) increasing
    intro key
    exact (increasingKeys_membership goLeft state key).trans (coverage key)
  have orientedIds : ((orientBlocks goLeft state.shrinking).map Frozen.id).Nodup := by
    rw [orientBlocks_ids]
    cases goLeft <;> simpa using ids
  obtain ⟨s,matching,bases⟩ := source_partition_of_blocks f comparator.externalDepth initial lo hi
    tree.lower_le_upper (orientBlocks goLeft state.shrinking) orientedIds
    (by simpa only [atoms_eq_range'] using orderedCover)
    (by intro a ha haz b hb hbz heq
        exact (GreedyMerge.MappedConsolidation.atom_owner_eq_iff comparator p gapOwner minima
          (by omega) (by omega)).mp heq)
    (by intro b hb e he
        obtain ⟨old,hold,rfl⟩ := (orientBlocks_mem goLeft state.shrinking b).mp hb
        simpa only [orientBlock_base] using buckets old hold e ((orientBlock_mem _ _ _).mp he))
    (by intro b hb e he
        obtain ⟨old,hold,rfl⟩ := (orientBlocks_mem goLeft state.shrinking b).mp hb
        simpa only [orientBlock_base] using floors old hold e ((orientBlock_mem _ _ _).mp he))
  refine ⟨s,?_,?_⟩
  · intro v hv hz b hb
    have member := (orientBlocks_mem goLeft state.shrinking (orientBlock goLeft b)).mpr
      ⟨b,hb,rfl⟩
    simpa only [orientBlock_id,orientBlock_keys] using matching v hv hz _ member
  · intro b hb
    have member := (orientBlocks_mem goLeft state.shrinking (orientBlock goLeft b)).mpr
      ⟨b,hb,rfl⟩
    simpa only [orientBlock_id,orientBlock_base] using bases _ member

end GreedyMerge.SourceSideStates

#print axioms GreedyMerge.SourceSideStates.source_partition_of_side
