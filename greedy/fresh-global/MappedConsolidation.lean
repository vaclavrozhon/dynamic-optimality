import ExpandedFringe

namespace GreedyMerge.MappedConsolidation
open Splay.Tree Splay.Tree.BST
open Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.PathPlateau GreedyMerge.AccessFrontier GreedyMerge.AccessConsolidation
open GreedyMerge.IntervalRootOracle GreedyMerge.PlateauBridge GreedyMerge.ExpansionRotations
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule

def mapEvents (map : ℕ → ℕ) (events : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  events.map fun event => (map event.1,map event.2)

theorem atom_owner_eq_iff {n access first second : ℕ} (comparator : BST 0 n)
    {oldTree : BST 0 n} (p : Decomposition oldTree access) (gapOwner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (firstBound : first ≤ 2*p.count) (secondBound : second ≤ 2*p.count) :
    AtomOwner p.separator gapOwner first = AtomOwner p.separator gapOwner second ↔ first = second := by
  constructor
  · intro equal
    by_contra different
    rcases lt_or_gt_of_ne different with less | greater
    · have strict := atom_owners_strict p.gaps minima less (by omega)
      omega
    · have strict := atom_owners_strict p.gaps minima greater (by omega)
      omega
  · rintro rfl
    rfl

theorem atom_owner_lt_iff {n access first second : ℕ} (comparator : BST 0 n)
    {oldTree : BST 0 n} (p : Decomposition oldTree access) (gapOwner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (firstBound : first ≤ 2*p.count) (secondBound : second ≤ 2*p.count) :
    AtomOwner p.separator gapOwner first < AtomOwner p.separator gapOwner second ↔ first < second := by
  constructor
  · intro less
    by_contra notLess
    rcases eq_or_lt_of_le (Nat.le_of_not_gt notLess) with equal | greater
    · subst first
      exact Nat.lt_irrefl _ less
    · have strict := atom_owners_strict p.gaps minima greater (by omega)
      omega
  · intro less
    exact atom_owners_strict p.gaps minima less (by omega)

theorem schedule_event_bounds {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (projection : Projection rank owner tree) (localOwners : LocalOwners rank owner lo hi)
    (event : ℕ × ℕ) (member : event ∈ schedule owner tree) :
    2*lo ≤ event.1 ∧ event.1 ≤ 2*hi ∧ 2*lo ≤ event.2 ∧ event.2 ≤ 2*hi := by
  have edge := (schedule_perm_edges rank owner tree projection localOwners).mem_iff.mp member
  have spec := edge_strict_rank_and_bounds rank owner tree event.1 event.2 projection edge
  exact ⟨spec.1,spec.2.1,spec.2.2.1,spec.2.2.2.1⟩

/-- Degree four holds for actual record identities, not only for the
abstract atom names of the projection. -/
theorem mapped_schedule_wins_le_four {n access : ℕ} (comparator : BST 0 n)
    {oldTree : BST 0 n} (p : Decomposition oldTree access) (gapOwner owner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (skeleton : BST 0 p.count)
    (projection : Projection
      (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) owner skeleton)
    (localOwners : LocalOwners
      (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) owner 0 p.count)
    (record : ℕ) :
    (mapEvents (AtomOwner p.separator gapOwner) (schedule owner skeleton)).countP
      (fun event => event.1 == record) ≤ 4 := by
  classical
  let f := AtomOwner p.separator gapOwner
  by_cases represented : ∃ atom, atom ≤ 2*p.count ∧ f atom = record
  · obtain ⟨atom, atomBound, rfl⟩ := represented
    have countEq : (mapEvents f (schedule owner skeleton)).countP (fun event => event.1 == f atom) =
        (schedule owner skeleton).countP (fun event => event.1 == atom) := by
      rw [mapEvents, List.countP_map]
      apply List.countP_congr
      intro event member
      have bounds := schedule_event_bounds _ owner skeleton projection localOwners event member
      simpa only [Function.comp_apply, beq_iff_eq] using
        atom_owner_eq_iff comparator p gapOwner minima bounds.2.1 atomBound
    rw [countEq]
    exact schedule_winner_count_le_four _ owner skeleton atom projection localOwners
  · have zero : (mapEvents f (schedule owner skeleton)).countP (fun event => event.1 == record) = 0 := by
      apply List.countP_eq_zero.mpr
      intro event member equal
      obtain ⟨source, sourceMember, mapped⟩ := List.mem_map.mp member
      have bounds := schedule_event_bounds _ owner skeleton projection localOwners source sourceMember
      apply represented
      exact ⟨source.1,bounds.2.1,(congrArg Prod.fst mapped).trans (of_decide_eq_true equal)⟩
    rw [zero]
    omega

theorem mapped_two_sided_wins_le_four {n access root : ℕ} (comparator : BST 0 n)
    {oldTree : BST 0 n} (p : Decomposition oldTree access) (gapOwner owner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (left : BST 0 root) (right : BST (root+1) p.count)
    (projection : Projection
      (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) owner (.node left right))
    (localOwners : LocalOwners
      (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) owner 0 p.count)
    (record : ℕ) :
    (mapEvents (AtomOwner p.separator gapOwner) (schedule owner left ++ schedule owner right)).countP
      (fun event => event.1 == record) ≤ 4 := by
  have full := mapped_schedule_wins_le_four comparator p gapOwner owner minima
    (.node left right) projection localOwners record
  simp only [mapEvents, schedule, List.map_append, List.countP_append] at full ⊢
  omega

theorem mapped_arrivals_eq {n access : ℕ} (comparator : BST 0 n)
    {oldTree : BST 0 n} (p : Decomposition oldTree access) (gapOwner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (events : List (ℕ × ℕ)) (bounds : ∀ event ∈ events, event.1 ≤ 2*p.count ∧ event.2 ≤ 2*p.count)
    (side : Bool) (parent : ℕ) (parentBound : parent ≤ 2*p.count) :
    arrivals side (AtomOwner p.separator gapOwner parent)
        (mapEvents (AtomOwner p.separator gapOwner) events) =
      (arrivals side parent events).map (AtomOwner p.separator gapOwner) := by
  induction events with
  | nil => simp [mapEvents,arrivals]
  | cons event rest ih =>
      have headBounds := bounds event (by simp)
      have tailBounds : ∀ e ∈ rest, e.1 ≤ 2*p.count ∧ e.2 ≤ 2*p.count := by
        intro e member
        exact bounds e (List.mem_cons_of_mem _ member)
      have eqTest := atom_owner_eq_iff comparator p gapOwner minima headBounds.1 parentBound
      have leftTest := atom_owner_lt_iff comparator p gapOwner minima headBounds.2 parentBound
      have rightTest := atom_owner_lt_iff comparator p gapOwner minima parentBound headBounds.2
      have tailEq := ih tailBounds
      cases side <;>
        simp only [arrivals, mapEvents, List.map_cons, List.filterMap_cons, Bool.false_eq_true,
          ↓reduceIte, eqTest, leftTest, rightTest] at tailEq ⊢ <;>
        split_ifs <;> simp only [List.map_cons, tailEq]

theorem arrival_mem_event {events : List (ℕ × ℕ)} {side : Bool} {parent child : ℕ}
    (member : child ∈ arrivals side parent events) :
    ∃ event ∈ events, event.2 = child := by
  obtain ⟨event, eventMember, output⟩ := List.mem_filterMap.mp member
  unfold arrivals at *
  split_ifs at output <;> exact ⟨event,eventMember,Option.some.inj output⟩

/-- The checked inner-to-outer schedule order survives the literal
embedding of atoms into their actual external-record positions. -/
theorem mapped_schedule_arrivals {n access : ℕ} (comparator : BST 0 n)
    {oldTree : BST 0 n} (p : Decomposition oldTree access) (gapOwner owner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (skeleton : BST 0 p.count)
    (projection : Projection
      (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) owner skeleton)
    (localOwners : LocalOwners
      (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) owner 0 p.count)
    (side : Bool) (parent : ℕ) (parentBound : parent ≤ 2*p.count) :
    (arrivals side (AtomOwner p.separator gapOwner parent)
      (mapEvents (AtomOwner p.separator gapOwner) (schedule owner skeleton))).Pairwise (arrivalOrder side) := by
  have bounds : ∀ event ∈ schedule owner skeleton, event.1 ≤ 2*p.count ∧ event.2 ≤ 2*p.count := by
    intro event member
    have h := schedule_event_bounds _ owner skeleton projection localOwners event member
    exact ⟨h.2.1,h.2.2.2⟩
  rw [mapped_arrivals_eq comparator p gapOwner minima _ bounds side parent parentBound,
    List.pairwise_map]
  apply List.Pairwise.imp_of_mem _
    (schedule_arrivals_inner_to_outer _ owner skeleton side parent projection localOwners)
  intro first second firstMem secondMem order
  obtain ⟨firstEvent, firstEventMem, firstEq⟩ := arrival_mem_event firstMem
  obtain ⟨secondEvent, secondEventMem, secondEq⟩ := arrival_mem_event secondMem
  have firstBound : first ≤ 2*p.count := by simpa only [firstEq] using (bounds _ firstEventMem).2
  have secondBound : second ≤ 2*p.count := by simpa only [secondEq] using (bounds _ secondEventMem).2
  cases side <;> simp only [arrivalOrder, Bool.false_eq_true, ↓reduceIte] at order ⊢
  · exact (atom_owner_lt_iff comparator p gapOwner minima firstBound secondBound).2 order
  · exact (atom_owner_lt_iff comparator p gapOwner minima secondBound firstBound).2 order

theorem mapped_two_sided_arrivals {n access root : ℕ} (comparator : BST 0 n)
    {oldTree : BST 0 n} (p : Decomposition oldTree access) (gapOwner owner : ℕ → ℕ)
    (minima : ∀ i, i ≤ p.count → UniqueMin comparator.externalDepth
      (2*GapLower 0 p.separator i) (2*p.separator i) (gapOwner i))
    (left : BST 0 root) (right : BST (root+1) p.count)
    (projection : Projection
      (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) owner (.node left right))
    (localOwners : LocalOwners
      (fun atom => comparator.externalDepth (AtomOwner p.separator gapOwner atom)) owner 0 p.count)
    (side : Bool) (parent : ℕ) (parentBound : parent ≤ 2*p.count) :
    (arrivals side (AtomOwner p.separator gapOwner parent)
      (mapEvents (AtomOwner p.separator gapOwner) (schedule owner left ++ schedule owner right))).Pairwise
        (arrivalOrder side) := by
  have full := mapped_schedule_arrivals comparator p gapOwner owner minima
    (.node left right) projection localOwners side parent parentBound
  simp only [schedule, mapEvents, List.map_append, arrivals, List.filterMap_append] at full ⊢
  exact (List.pairwise_append.mp full).1

theorem run_event_rank_lt {rank : ℕ → ℕ} {events : List (ℕ × ℕ)} {before after : List ℕ}
    (run : Run rank events before after) (event : ℕ × ℕ) (member : event ∈ events) :
    rank event.1 < rank event.2 := by
  induction run with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with equal | tail
      · subst event
        cases first <;> assumption
      · exact ih tail

/-- A link between distinct old siblings is farther outward than every
preexisting child of its winner. This is concrete ordered-tree geometry,
not an assumption about a heap interface or an arrival trace. -/
theorem old_sibling_link_is_outer {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (root : External n) (winner loser oldChild : ℕ)
    (winnerMember : HasChild snapshot tree (Nat.le_refl n) 0 root winner)
    (loserMember : HasChild snapshot tree (Nat.le_refl n) 0 root loser)
    (oldMember : GreedyMerge.ExpandedFringe.HasPair snapshot tree (Nat.le_refl n) 0 winner oldChild)
    (different : winner ≠ loser) :
    if loser < winner then loser < oldChild else oldChild < loser := by
  obtain ⟨winnerEdge, winnerEdgeMem, winnerOwner, winnerValue⟩ := winnerMember
  obtain ⟨loserEdge, loserEdgeMem, loserOwner, loserValue⟩ := loserMember
  obtain ⟨childEdge, childEdgeMem, childOwner, childValue⟩ := oldMember
  have sameOwner : winnerEdge.owner = loserEdge.owner := winnerOwner.trans loserOwner.symm
  have childOwnerEq : childEdge.owner = winnerEdge.child :=
    Fin.ext (childOwner.trans winnerValue.symm)
  have differentRecords : winnerEdge.child ≠ loserEdge.child := by
    intro equal
    exact different (winnerValue.symm.trans ((congrArg Fin.val equal).trans loserValue))
  have geometry := mem_treeEdges_nested_children snapshot tree (Nat.le_refl n)
    winnerEdgeMem loserEdgeMem childEdgeMem sameOwner childOwnerEq differentRecords
  simpa only [winnerValue, loserValue, childValue] using geometry

/-- Every event of a literal run on the actual old root-child list is
outside all of its winner's preexisting children. Together with the mapped
inner-to-outer arrival theorem, this justifies appending arrivals to the
winner's geometric grower order across phases. -/
theorem scheduled_arrival_outside_old_children {n : ℕ} (snapshot : Snapshot n)
    (tree : BST 0 n) (root : External n) (rank : ℕ → ℕ)
    (events : List (ℕ × ℕ)) (before after : List ℕ)
    (run : Run rank events before after)
    (actualChildren : ∀ child, HasChild snapshot tree (Nat.le_refl n) 0 root child ↔ child ∈ before)
    (event : ℕ × ℕ) (member : event ∈ events) (oldChild : ℕ)
    (oldMember : GreedyMerge.ExpandedFringe.HasPair snapshot tree (Nat.le_refl n) 0 event.1 oldChild) :
    if event.2 < event.1 then event.2 < oldChild else oldChild < event.2 := by
  have members := run.event_members event member
  have strict := run_event_rank_lt run event member
  have different : event.1 ≠ event.2 := by
    intro equal
    rw [equal] at strict
    exact Nat.lt_irrefl _ strict
  exact old_sibling_link_is_outer snapshot tree root event.1 event.2 oldChild
    ((actualChildren event.1).2 members.1) ((actualChildren event.2).2 members.2)
    oldMember different

end GreedyMerge.MappedConsolidation

#print axioms GreedyMerge.MappedConsolidation.mapped_two_sided_wins_le_four
#print axioms GreedyMerge.MappedConsolidation.mapped_schedule_arrivals
#print axioms GreedyMerge.MappedConsolidation.mapped_two_sided_arrivals
#print axioms GreedyMerge.MappedConsolidation.scheduled_arrival_outside_old_children
