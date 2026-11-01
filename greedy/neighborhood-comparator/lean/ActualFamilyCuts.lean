import ActualSourceBlocks

/-!
Identify a family's entire phase census with its unique crossing source
block. One historical key cut is constructed for the whole family, and
the literal interval partition implies that every crossing block is the
block containing that key cut. No unique-straddler/event-map premise is
supplied for the phase.
-/
namespace GreedyForest.Phase

open Splay.Tree Splay.Tree.BST
open Splay.Analysis
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open HistoricalCuts

theorem SourcePartition.crossing_block_contains_cut {rank : ℕ → ℕ} {initial : ℕ → ℤ}
    {lo hi : ℕ} (s : SourcePartition rank initial lo hi) (a b cut : ℕ)
    (ha : 2*lo ≤ a ∧ a ≤ 2*hi) (hb : 2*lo ≤ b ∧ b ≤ 2*hi)
    (hsame : s.block a = s.block b) (hcross : KeyCrosses cut a b) :
    s.block cut = s.block a := by
  have hia := (s.intervalExact a ha.1 ha.2 (s.block a)).mp rfl
  have hib := (s.intervalExact b hb.1 hb.2 (s.block a)).mp hsame.symm
  have hbounds := s.intervalBounds (s.block a)
  unfold KeyCrosses at hcross
  have hfirst : s.first (s.block a) ≤ cut := by omega
  have hfinish : cut < s.finish (s.block a) := by omega
  exact (s.intervalExact cut (by omega) (by omega) (s.block a)).mpr ⟨hfirst,hfinish⟩

noncomputable def familyMembers {lo hi : ℕ} (tree : BST lo hi)
    (block family : ℕ → ℕ) (f : ℕ) : Finset ℕ := by
  classical
  exact (atoms tree).toFinset.filter (fun v => family (block v) = f)

noncomputable def familyBadCrossings (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (events : List (ℕ × ℕ)) (block family join : ℕ → ℕ) (f time : ℕ) :
    Finset (Fin events.length) := by
  classical
  exact (actualInternalBad rank initial events block).filter (fun i =>
    family (block (events.get i).1) = f ∧
    TimeCrosses time (join (events.get i).1) (join (events.get i).2))

/-- The literal family-stage event set is either empty or exactly the
literal event set of one source block belonging to that family. -/
theorem family_bad_crossings_single_source {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hp : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi)
    (initial : ℕ → ℤ) (s : SourcePartition rank initial lo hi)
    (family join : ℕ → ℕ) (f time : ℕ)
    (horder :
      (∀ a ∈ familyMembers tree s.block family f, ∀ b ∈ familyMembers tree s.block family f,
        a ≤ b → join a ≤ join b) ∨
      (∀ a ∈ familyMembers tree s.block family f, ∀ b ∈ familyMembers tree s.block family f,
        a ≤ b → join b ≤ join a)) :
    familyBadCrossings rank initial (schedule owner tree) s.block family join f time = ∅ ∨
    ∃ b, family b = f ∧
      familyBadCrossings rank initial (schedule owner tree) s.block family join f time =
        blockBadCrossings rank initial (schedule owner tree) s.block join b time := by
  classical
  let events := schedule owner tree
  let crossings := familyBadCrossings rank initial events s.block family join f time
  by_cases hempty : crossings = ∅
  · exact Or.inl hempty
  have hnonempty : crossings.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨cut,hcut⟩ := ordered_join_crossings_have_one_key_cut
    (familyMembers tree s.block family f) join time horder
  have htarget : ∀ i ∈ crossings, s.block (events.get i).1 = s.block cut := by
    intro i hi
    obtain ⟨hiBad,hiFamily,hiTime⟩ := Finset.mem_filter.mp hi
    have hsame := (Finset.mem_filter.mp hiBad).2.1
    have hm := (schedule_run rank owner tree hp hloc).event_members (events.get i) (List.get_mem events i)
    have hparent : (events.get i).1 ∈ familyMembers tree s.block family f :=
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm.1,hiFamily⟩
    have hchild : (events.get i).2 ∈ familyMembers tree s.block family f := by
      apply Finset.mem_filter.mpr
      refine ⟨List.mem_toFinset.mpr hm.2,?_⟩
      rw [←hsame]
      exact hiFamily
    have hcross := (hcut _ hparent _ hchild).mp hiTime
    exact (s.crossing_block_contains_cut _ _ cut ((atoms_mem_iff tree _).mp hm.1)
      ((atoms_mem_iff tree _).mp hm.2) hsame hcross).symm
  obtain ⟨first,hfirst⟩ := hnonempty
  have hfamily : family (s.block cut) = f := by
    have hf := (Finset.mem_filter.mp hfirst).2.1
    rw [htarget first hfirst] at hf
    exact hf
  refine Or.inr ⟨s.block cut,hfamily,?_⟩
  ext i
  simp only [familyBadCrossings,blockBadCrossings,Finset.mem_filter]
  constructor
  · intro hi
    have hic : i ∈ crossings := by
      simpa only [crossings,familyBadCrossings,Finset.mem_filter] using hi
    obtain ⟨hiBad,hiFamily,hiTime⟩ := hi
    exact ⟨hiBad,htarget i hic,hiTime⟩
  · rintro ⟨hiBad,hiBlock,hiTime⟩
    refine ⟨hiBad,?_,hiTime⟩
    simpa only [hiBlock] using hfamily

/-- Actual source geometry for the entire family's phase census. The
global lifetime proof may now use this without supplying a per-phase
unique-straddler map or an event projection into its active cut tree. -/
theorem actual_family_cut_geometry {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hp : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi)
    (initial : ℕ → ℤ) (s : SourcePartition rank initial lo hi)
    (family join : ℕ → ℕ) (f time H : ℕ)
    (horder :
      (∀ a ∈ familyMembers tree s.block family f, ∀ b ∈ familyMembers tree s.block family f,
        a ≤ b → join a ≤ join b) ∨
      (∀ a ∈ familyMembers tree s.block family f, ∀ b ∈ familyMembers tree s.block family f,
        a ≤ b → join b ≤ join a))
    (hrank : ∀ v, 2*lo ≤ v → v ≤ 2*hi → rank v ≤ H) :
    Nonempty (Execution.CutPhaseGeometry (contractedGap H)
      (familyBadCrossings rank initial (schedule owner tree) s.block family join f time).card) := by
  classical
  rcases family_bad_crossings_single_source rank owner tree hp hloc initial s family join f time horder
    with hempty | ⟨b,hfamily,heq⟩
  · rw [hempty,Finset.card_empty]
    refine ⟨⟨.empty,trivial,trivial,Fin.elim0,?_⟩⟩
    intro i; exact Fin.elim0 i
  · rw [heq]
    apply block_creator_cut_geometry rank owner tree hp hloc initial s join b time H ?_ hrank
    have hsubset : blockMembers tree s.block b ⊆ familyMembers tree s.block family f := by
      intro v hv
      obtain ⟨hm,hb⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨hm,by simpa only [hb] using hfamily⟩
    rcases horder with hm | ha
    · exact Or.inl (fun a hma v hmv hav => hm a (hsubset hma) v (hsubset hmv) hav)
    · exact Or.inr (fun a hma v hmv hav => ha a (hsubset hma) v (hsubset hmv) hav)

end GreedyForest.Phase

#print axioms GreedyForest.Phase.family_bad_crossings_single_source
#print axioms GreedyForest.Phase.actual_family_cut_geometry
