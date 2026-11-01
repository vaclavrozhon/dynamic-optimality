import MultiSplay.RichSplitRecordPartition
import MultiSplay.ListPartition

/-! # Repacking the exact split history, including every retired root record -/

namespace MultiSplay.RichSplit

open Splay.Tree (BST)
open Splay.Rank (Snapshot)
open Splay.Lazy (State Block Element)
open Splay.Lazy.Canonical

variable {l r : Nat} {params : Splay.Interface.Parameters}

noncomputable def archive {n : Nat} (source : State n) (pivot : Element n) : Splay.Interface.State n where
  blocks := (source.blocks.filter (fun block => decide (block.owner = pivot))).map (retiredRecord pivot)
  value := fun _ => 1

theorem archive_closed {n : Nat} (source : State n) (pivot : Element n)
    (block : Splay.Interface.Block n) (member : block ∈ (archive source pivot).blocks) :
    block.mode = .shrinking ∧ block.elements = [] := by
  obtain ⟨original, selected, rfl⟩ := List.mem_map.mp member
  have owner := of_decide_eq_true (List.mem_filter.mp selected).2
  simp [retiredRecord, owner]

theorem archive_passive {n k : Nat} (source : State n) (pivot : Element n) (embedding : Element k → Element n) :
    InterfacePrefix.Passive embedding (archive source pivot) := by
  constructor
  · intro x member
    obtain ⟨block, blockMem, present⟩ := List.mem_flatMap.mp member
    rw [(archive_closed source pivot block blockMem).2] at present
    exact False.elim (List.not_mem_nil present)
  · intro block member growing
    have mode := (archive_closed source pivot block member).1
    rw [mode] at growing
    cases growing

theorem archive_valid {n : Nat} (source : State n) (pivot : Element n) : (archive source pivot).Valid params := by
  have empty : (archive source pivot).allElements = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x member
    exact (archive_passive source pivot id).elements x member x rfl
  refine ⟨by rw [empty]; exact List.nodup_nil, ?_, ?_⟩
  · intro x
    have cap := params.valueBound_ge_two
    change 1 ≤ 1 ∧ 1 ≤ params.valueBound
    omega
  · intro creator
    change ((archive source pivot).blocks.filter _).length ≤ params.growingLimit
    rw [List.filter_eq_nil_iff.mpr ?_]
    · exact Nat.zero_le _
    · intro block member
      have mode := (archive_closed source pivot block member).1
      simp [mode]

theorem owner_partition (source : State (0+l+1+r)) :
    ((source.blocks.filter (fun block => decide (block.owner = JoinRanks.pivot l r))) ++
      (source.blocks.filter (fun block => decide (block.owner ∈ Set.range (JoinIntervals.rightEmbedding l r)))) ++
      (source.blocks.filter (fun block => decide (block.owner ∈ Set.range (JoinIntervals.leftEmbedding l r))))).Perm source.blocks := by
  classical
  apply ListPartition.three
  · intro block right same
    obtain ⟨x, eq⟩ := right
    exact JoinIntervals.right_ne_pivot l r x (eq.trans same)
  · intro block
    constructor
    · rintro ⟨x, eq⟩
      refine ⟨?_, ?_⟩
      · rintro ⟨y, yeq⟩
        exact JoinIntervals.disjoint l r x y (eq.trans yeq.symm)
      · intro same
        exact JoinIntervals.left_ne_pivot l r x (eq.trans same)
    · rintro ⟨notRight, notPivot⟩
      rcases JoinIntervals.cases_element l r block.owner with left | equal | right
      · exact left
      · exact False.elim (notPivot equal)
      · exact False.elim (notRight right)

noncomputable def leftComponent (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)) :
    InterfacePacking.Component (0+l+1+r) where
  size := l
  source := (leftState left right sl sr source represented).toInterface
  element := JoinIntervals.leftEmbedding l r
  injective := RankEmbedding.external_injective _ _

noncomputable def rightComponent (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (source : State (0+l+1+r))
    (represented : source.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)) :
    InterfacePacking.Component (0+l+1+r) where
  size := r
  source := (rightState left right sl sr source represented).toInterface
  element := JoinIntervals.rightEmbedding l r
  injective := RankEmbedding.external_injective _ _

end MultiSplay.RichSplit
