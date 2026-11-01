import TypedAccessSchedule
import ActualRunLabels

/-! Return of the literal block/parent execution to the new canonical heap.
Inherited old gap edges, every scheduled new edge, and the surviving root
children are the three exhaustive parent sources of the executed run. -/
namespace GreedyMerge.ActualLinks
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.AccessFrontier
open GreedyMerge.ExpandedFringe GreedyMerge.InheritedGapEdges GreedyMerge.AccessSurvivors
open GreedyMerge.PathPlateau GreedyMerge.Primitives GreedyMerge.OrderedBlocks

theorem hasPair_iff_canonicalParent {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (owner child : External n) :
    HasPair snapshot tree (Nat.le_refl n) 0 owner.val child.val ↔
      canonicalParent snapshot tree child=some owner := by
  constructor
  · rintro ⟨edge,member,parentEq,childEq⟩
    have fact := Splay.Accounting.canonicalParent_eq_some_of_mem_fullEdges snapshot tree edge
      (by simpa only [fullEdges] using member)
    have ownerSame : edge.owner=owner := Fin.ext parentEq
    have childSame : edge.child=child := Fin.ext childEq
    simpa only [ownerSame,childSame] using fact
  · exact canonical_parent_pair snapshot tree owner child

/-- The complete literal execution's final parent map is the new canonical
parent map. All nonsource inherited edges are proved to survive internally;
the event-edge and final-root facts are exactly the checked expansion and
survivor theorems, rather than a supplied global parent-map equality. -/
theorem runParents_eq_canonical {n access : ℕ} (snapshot : Snapshot n)
    (oldTree : BST 0 n) (p : Decomposition oldTree access) (skeleton : BST 0 p.count)
    (source : External n) (real : source.val=2*access+1) (zero : snapshot.rank source=0)
    (accessBound : access<n) (rank : ℕ → ℕ) (events : List (External n × External n))
    (roots finalRoots : List ℕ) (unique : roots.Nodup)
    (run : Run rank (events.map eventKeys) roots finalRoots)
    (actualChildren : ∀ child, HasChild snapshot oldTree (Nat.le_refl n) 0 source child ↔ child ∈ roots)
    (eventEdges : ∀ event ∈ events,
      HasPair snapshot (p.expand skeleton) (Nat.le_refl n) 0 event.1.val event.2.val)
    (finalChildren : ∀ child,
      HasPair snapshot (p.expand skeleton) (Nat.le_refl n) 0 source.val child ↔ child ∈ finalRoots) :
    runParents (canonicalParent snapshot oldTree) events = canonicalParent snapshot (p.expand skeleton) := by
  have oldRoot : canonicalRoot snapshot oldTree=source :=
    owner_eq_of_zero snapshot oldTree (Nat.le_refl n) source zero (by omega)
  have newRoot : canonicalRoot snapshot (p.expand skeleton)=source :=
    owner_eq_of_zero snapshot (p.expand skeleton) (Nat.le_refl n) source zero (by omega)
  have rootParent : ∀ child : External n,
      canonicalParent snapshot oldTree child=some source ↔ child.val∈roots := by
    intro child
    rw [←hasPair_iff_canonicalParent snapshot oldTree source child,
      ←hasChild_iff_hasPair snapshot oldTree (Nat.le_refl n) 0 source child.val]
    exact actualChildren child.val
  have neverWins : ∀ event∈events, event.1≠source := by
    intro event member same
    have rootMem := (run.event_members _ (List.mem_map.mpr ⟨event,member,rfl⟩)).1
    have ne := hasChild_ne_owner snapshot oldTree source event.1.val ((actualChildren _).mpr rootMem)
    exact ne (congrArg Fin.val same)
  funext child
  cases finalParent : runParents (canonicalParent snapshot oldTree) events child with
  | none =>
      have oldNone := runParents_none _ events child finalParent
      have atSource : child=source :=
        ((canonicalParent_eq_none_iff snapshot oldTree child).mp oldNone).trans oldRoot
      exact ((canonicalParent_eq_none_iff snapshot (p.expand skeleton) child).mpr
        (atSource.trans newRoot.symm)).symm
  | some owner =>
      have finalEdge : HasPair snapshot (p.expand skeleton) (Nat.le_refl n) 0 owner.val child.val := by
        rcases runParents_provenance _ events child owner finalParent with inherited | attached
        · by_cases isSource : owner=source
          · subst owner
            apply (finalChildren child.val).mpr
            exact (runParents_source_survivor _ events source child rank roots finalRoots run unique
              (rootParent child) neverWins).mp finalParent
          · exact inherited_edge_survives snapshot oldTree p skeleton source real zero accessBound
              (fun equal => isSource (Fin.ext equal))
              ((hasPair_iff_canonicalParent snapshot oldTree owner child).mpr inherited)
        · obtain ⟨event,member,loser,winner⟩ := attached
          simpa only [loser,winner] using eventEdges event member
      exact ((hasPair_iff_canonicalParent snapshot (p.expand skeleton) owner child).mp finalEdge).symm

/-- Actual ordered-prefix facts are derived from the same whole schedule's
spatial arrival order; callers do not supply them to the numerical run. -/
theorem runLinks_ordered_prefixes {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (source : External n) (sourceSide : External n × External n → Bool) (states : States n)
    (sound : SoundFor (canonicalParent snapshot tree) states)
    (ordered : Ordered states) (persistent : Persistent states)
    (emptySource : ∀ side, growerEntries (states source side).grower=[])
    (rank : ℕ → ℕ) (events : List (External n × External n)) (roots finalRoots : List ℕ)
    (run : Run rank (events.map eventKeys) roots finalRoots)
    (actualChildren : ∀ child, HasChild snapshot tree (Nat.le_refl n) 0 source child ↔ child ∈ roots)
    (reader : ℕ → States n → ℕ → ℤ) (time : ℕ)
    (arrivalOrders : ∀ event ∈ events,
      (arrivals (targetSide event) event.1.val (events.map eventKeys)).Pairwise
        (arrivalOrder (targetSide event))) :
    ∀ first second, events=first++second →
      Ordered (runLinks source sourceSide reader time states first) := by
  intro first second split
  obtain ⟨middle,prefixRun,suffixRun⟩ := GreedyForest.Phase.run_take_split run first.length
    (by simp only [split,List.length_map,List.length_append]; omega)
  have prefixKeys : (events.map eventKeys).take first.length=first.map eventKeys := by
    simp [split,List.take_append]
  rw [prefixKeys] at prefixRun
  apply runLinks_ordered snapshot tree source sourceSide states sound ordered persistent emptySource
    rank first roots middle prefixRun actualChildren reader time
  intro event member
  have order := arrivalOrders event (by rw [split]; exact List.mem_append_left _ member)
  rw [split,List.map_append,arrivals_append] at order
  exact (List.pairwise_append.mp order).1

end GreedyMerge.ActualLinks

#print axioms GreedyMerge.ActualLinks.runParents_eq_canonical
#print axioms GreedyMerge.ActualLinks.runLinks_ordered_prefixes
