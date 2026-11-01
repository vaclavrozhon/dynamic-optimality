import ActualLinkClasses

/-!
One concrete source-block partition identifies the schedule's block-ID
event filters with the interval and historical-cut filters used by the
geometric lemmas. Thus their capacities apply to the same literal events.
-/
namespace GreedyForest.Phase

open Splay.Tree Splay.Tree.BST
open Splay.Analysis
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open HistoricalCuts

/-- A phase-start partition of the ordered old-root atoms. Empty block
IDs are allowed. Frozen bases and initial labels are properties of this
one partition; they are not chosen separately for each charged event. -/
structure SourcePartition (rank : ℕ → ℕ) (initial : ℕ → ℤ) (lo hi : ℕ) where
  block : ℕ → ℕ
  base : ℕ → ℕ
  first : ℕ → ℕ
  finish : ℕ → ℕ
  intervalBounds : ∀ b, 2*lo ≤ first b ∧ finish b ≤ 2*hi+1
  intervalExact : ∀ v, 2*lo ≤ v → v ≤ 2*hi → ∀ b,
    block v = b ↔ first b ≤ v ∧ v < finish b
  initialBucket : ∀ v, 2*lo ≤ v → v ≤ 2*hi → initial v = baseLabel rank (base (block v)) v
  baseFloor : ∀ v, 2*lo ≤ v → v ≤ 2*hi → base (block v) ≤ rank v

namespace SourcePartition

variable {rank : ℕ → ℕ} {initial : ℕ → ℤ} {lo hi : ℕ}

theorem interval_bucket (s : SourcePartition rank initial lo hi) (b v : ℕ)
    (hf : s.first b ≤ v) (hz : v < s.finish b) : initial v = baseLabel rank (s.base b) v := by
  have hbounds := s.intervalBounds b
  have hlo : 2*lo ≤ v := by omega
  have hhi : v ≤ 2*hi := by omega
  have heq := (s.intervalExact v hlo hhi b).mpr ⟨hf,hz⟩
  simpa only [heq] using s.initialBucket v hlo hhi

theorem interval_floor (s : SourcePartition rank initial lo hi) (b v : ℕ)
    (hf : s.first b ≤ v) (hz : v < s.finish b) : s.base b ≤ rank v := by
  have hbounds := s.intervalBounds b
  have hlo : 2*lo ≤ v := by omega
  have hhi : v ≤ 2*hi := by omega
  have heq := (s.intervalExact v hlo hhi b).mpr ⟨hf,hz⟩
  simpa only [heq] using s.baseFloor v hlo hhi

end SourcePartition

noncomputable def blockPositive (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (events : List (ℕ × ℕ)) (block : ℕ → ℕ) (b : ℕ) : Finset (Fin events.length) := by
  classical
  exact Finset.univ.filter (fun i => block (events.get i).2 = b ∧
    labelsAt rank initial events i (events.get i).2 <
      labelsAt rank initial events (i.val+1) (events.get i).2)

noncomputable def blockBoundaryNondrops (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (events : List (ℕ × ℕ)) (block : ℕ → ℕ) (b : ℕ) : Finset (Fin events.length) := by
  classical
  exact Finset.univ.filter (fun i => block (events.get i).2 = b ∧
    block (events.get i).1 ≠ b ∧
    labelsAt rank initial events i (events.get i).2 ≤
      labelsAt rank initial events (i.val+1) (events.get i).2)

theorem block_positive_eq_interval {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hp : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi)
    (initial : ℕ → ℤ) (s : SourcePartition rank initial lo hi) (b : ℕ) :
    blockPositive rank initial (schedule owner tree) s.block b =
      actualPositiveDepartures rank initial (schedule owner tree) (s.first b) (s.finish b) := by
  classical
  ext i
  have hm := (schedule_run rank owner tree hp hloc).event_members
    ((schedule owner tree).get i) (List.get_mem _ i)
  have hv := (atoms_mem_iff tree _).mp hm.2
  have heq := s.intervalExact _ hv.1 hv.2 b
  simp only [blockPositive,actualPositiveDepartures,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [heq]
  tauto

theorem block_boundary_eq_interval {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hp : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi)
    (initial : ℕ → ℤ) (s : SourcePartition rank initial lo hi) (b : ℕ) :
    blockBoundaryNondrops rank initial (schedule owner tree) s.block b =
      actualBoundaryNondrops rank initial (schedule owner tree) (s.first b) (s.finish b) := by
  classical
  ext i
  have hm := (schedule_run rank owner tree hp hloc).event_members
    ((schedule owner tree).get i) (List.get_mem _ i)
  have hv := (atoms_mem_iff tree _).mp hm.2
  have hw := (atoms_mem_iff tree _).mp hm.1
  have heqv := s.intervalExact _ hv.1 hv.2 b
  have heqw := s.intervalExact _ hw.1 hw.2 b
  simp only [blockBoundaryNondrops,actualBoundaryNondrops,Finset.mem_filter,
    Finset.mem_univ,true_and]
  simp only [ne_eq,heqv,heqw]
  tauto

theorem block_positive_geometry {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hp : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi)
    (initial : ℕ → ℤ) (s : SourcePartition rank initial lo hi) (b : ℕ) :
    Nonempty (Execution.HarmfulPhaseGeometry
      (blockPositive rank initial (schedule owner tree) s.block b).card) := by
  rw [block_positive_eq_interval rank owner tree hp hloc initial s b]
  exact actual_positive_geometry rank owner tree hp hloc initial (s.first b) (s.finish b)
    (s.base b) (s.interval_bucket b) (s.interval_floor b)

theorem block_boundary_geometry {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hp : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi)
    (initial : ℕ → ℤ) (s : SourcePartition rank initial lo hi) (b H : ℕ)
    (hrank : ∀ v, 2*lo ≤ v → v ≤ 2*hi → rank v ≤ H) :
    Nonempty (Execution.BoundaryPhaseGeometry (contractedGap H)
      (blockBoundaryNondrops rank initial (schedule owner tree) s.block b).card) := by
  rw [block_boundary_eq_interval rank owner tree hp hloc initial s b]
  exact actual_boundary_geometry rank owner tree hp hloc initial (s.first b) (s.finish b)
    (s.base b) H (s.interval_bucket b) (s.interval_floor b) hrank

noncomputable def blockMembers {lo hi : ℕ} (tree : BST lo hi) (block : ℕ → ℕ) (b : ℕ) :
    Finset ℕ := by
  classical
  exact (atoms tree).toFinset.filter (fun v => block v=b)

noncomputable def blockBadCrossings (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (events : List (ℕ × ℕ)) (block join : ℕ → ℕ) (b time : ℕ) :
    Finset (Fin events.length) := by
  classical
  exact (actualInternalBad rank initial events block).filter (fun i =>
    block (events.get i).1 = b ∧ TimeCrosses time (join (events.get i).1) (join (events.get i).2))

theorem block_bad_crossings_eq_members {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hp : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi)
    (initial : ℕ → ℤ) (block join : ℕ → ℕ) (b time : ℕ) :
    blockBadCrossings rank initial (schedule owner tree) block join b time =
      actualBadCrossings rank initial (schedule owner tree) (blockMembers tree block b) join time := by
  classical
  ext i
  have hm := (schedule_run rank owner tree hp hloc).event_members
    ((schedule owner tree).get i) (List.get_mem _ i)
  simp only [blockBadCrossings,actualInternalBad,actualBadCrossings,blockMembers,
    Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset]
  simp only [hm.1,hm.2,true_and]
  constructor
  · rintro ⟨⟨hblock,hbad⟩,hparent,htime⟩
    exact ⟨hparent,hblock.symm.trans hparent,hbad,htime⟩
  · rintro ⟨hparent,hchild,hbad,htime⟩
    exact ⟨⟨hparent.trans hchild.symm,hbad⟩,hparent,htime⟩

theorem block_creator_cut_geometry {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hp : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi)
    (initial : ℕ → ℤ) (s : SourcePartition rank initial lo hi) (join : ℕ → ℕ) (b time H : ℕ)
    (horder :
      (∀ a ∈ blockMembers tree s.block b, ∀ v ∈ blockMembers tree s.block b,
        a ≤ v → join a ≤ join v) ∨
      (∀ a ∈ blockMembers tree s.block b, ∀ v ∈ blockMembers tree s.block b,
        a ≤ v → join v ≤ join a))
    (hrank : ∀ v, 2*lo ≤ v → v ≤ 2*hi → rank v ≤ H) :
    Nonempty (Execution.CutPhaseGeometry (contractedGap H)
      (blockBadCrossings rank initial (schedule owner tree) s.block join b time).card) := by
  rw [block_bad_crossings_eq_members rank owner tree hp hloc initial s.block join b time]
  apply actual_bad_crossing_geometry rank owner tree hp hloc initial _ (s.base b)
    join time H ?_ horder hrank
  intro v hv
  have hm := Finset.mem_filter.mp hv
  have hb := (atoms_mem_iff tree v).mp (List.mem_toFinset.mp hm.1)
  have heq : s.block v = b := hm.2
  simpa only [heq] using s.initialBucket v hb.1 hb.2

end GreedyForest.Phase

#print axioms GreedyForest.Phase.block_positive_geometry
#print axioms GreedyForest.Phase.block_boundary_geometry
#print axioms GreedyForest.Phase.block_creator_cut_geometry
