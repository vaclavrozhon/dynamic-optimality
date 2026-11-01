import ActualLinkState

/-! Literal execution of link-state updates and its exact arrival lists.
These facts connect the checked spatial schedule to persistent grower
append operations, including children already present before this access. -/
namespace GreedyMerge.ActualLinks
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open GreedyMerge.MappedConsolidation GreedyMerge.AccessFrontier GreedyMerge.ExpandedFringe

def eventKeys {n : ℕ} (event : External n × External n) : ℕ × ℕ :=
  (event.1.val,event.2.val)

def targetSide {n : ℕ} (event : External n × External n) : Bool :=
  decide (event.2.val<event.1.val)

def runLinks {n : ℕ} (source : External n) (sourceSide : External n × External n → Bool)
    (labels : ℕ → States n → ℕ → ℤ) : ℕ → States n → List (External n × External n) → States n
  | _, states, [] => states
  | time, states, event::rest =>
      runLinks source sourceSide labels (time+1)
        (linkState states source event.1 event.2 (sourceSide event) (targetSide event)
          (arrivalEntry (labels time states) event.1 event.2 time)) rest

theorem singleton_arrivals {n : ℕ} (event : External n × External n)
    (different : event.1 ≠ event.2) (owner : External n) (side : Bool) :
    arrivals side owner.val [eventKeys event] =
      if owner=event.1 ∧ side=targetSide event then [event.2.val] else [] := by
  have values : event.1.val ≠ event.2.val := fun h => different (Fin.ext h)
  by_cases sameOwner : owner=event.1
  · subst owner
    by_cases less : event.2.val<event.1.val
    · have notRight : ¬event.1.val<event.2.val := by omega
      cases side <;> simp [arrivals,eventKeys,targetSide,less,notRight]
    · have right : event.1.val<event.2.val := by omega
      cases side <;> simp [arrivals,eventKeys,targetSide,less,right]
  · have valueNe : event.1.val ≠ owner.val := fun h => sameOwner (Fin.ext h.symm)
    simp [arrivals,eventKeys,valueNe,sameOwner]

theorem linkState_keys_nonroot {n : ℕ} (states : States n) (source : External n)
    (sourceSide : Bool) (event : External n × External n) (time : ℕ) (labels : ℕ → ℤ)
    (persistent : Persistent states) (different : event.1 ≠ event.2)
    (owner : External n) (side : Bool) (notSource : owner ≠ source) :
    (entries (linkState states source event.1 event.2 sourceSide (targetSide event)
      (arrivalEntry labels event.1 event.2 time) owner side)).map Entry.key =
      (entries (states owner side)).map Entry.key ++ arrivals side owner.val [eventKeys event] := by
  rw [singleton_arrivals event different owner side]
  unfold linkState
  simp only [notSource,false_and,↓reduceIte]
  split_ifs with selected
  · obtain ⟨rfl,rfl⟩ := selected
    rw [appendGrower_entries _ _ (persistent _ _),List.map_append]
    rfl
  · simp only [List.append_nil]

theorem runLinks_persistent {n : ℕ} (source : External n) (sourceSide : External n × External n → Bool)
    (labels : ℕ → States n → ℕ → ℤ) (time : ℕ) (states : States n)
    (events : List (External n × External n)) (persistent : Persistent states) :
    Persistent (runLinks source sourceSide labels time states events) := by
  induction events generalizing time states with
  | nil => exact persistent
  | cons event rest ih =>
      exact ih (time+1) _ (linkState_persistent states source event.1 event.2 (sourceSide event) _ _ persistent)

/-- The actual state's nonroot child list consists exactly of its old
children followed by precisely the earlier arrivals of the literal run. -/
theorem runLinks_keys_nonroot {n : ℕ} (source : External n) (sourceSide : External n × External n → Bool)
    (labels : ℕ → States n → ℕ → ℤ) (time : ℕ) (states : States n)
    (events : List (External n × External n)) (persistent : Persistent states)
    (different : ∀ event ∈ events, event.1 ≠ event.2)
    (owner : External n) (side : Bool) (notSource : owner ≠ source) :
    (entries (runLinks source sourceSide labels time states events owner side)).map Entry.key =
      (entries (states owner side)).map Entry.key ++
        arrivals side owner.val (events.map eventKeys) := by
  induction events generalizing time states with
  | nil => simp [runLinks,arrivals]
  | cons event rest ih =>
      change (entries (runLinks source sourceSide labels (time+1)
        (linkState states source event.1 event.2 (sourceSide event) (targetSide event)
          (arrivalEntry (labels time states) event.1 event.2 time)) rest owner side)).map Entry.key = _
      rw [ih (time+1) _ (linkState_persistent _ _ _ _ _ _ _ persistent)
        (by intro e he; exact different e (List.mem_cons_of_mem _ he))]
      rw [linkState_keys_nonroot _ source (sourceSide event) event time _ persistent
        (different event (by simp)) owner side notSource]
      rw [List.append_assoc]
      congr 1
      simpa only [List.map_cons,List.singleton_append] using
        (arrivals_append side owner.val [eventKeys event] (rest.map eventKeys)).symm

theorem run_event_distinct {n : ℕ} (rank : ℕ → ℕ)
    (events : List (External n × External n)) (before after : List ℕ)
    (run : Run rank (events.map eventKeys) before after) :
    ∀ event ∈ events, event.1 ≠ event.2 := by
  intro event member same
  have bound := run_event_rank_lt run (eventKeys event) (List.mem_map.mpr ⟨event,member,rfl⟩)
  simpa only [eventKeys,same,lt_self_iff_false] using bound

theorem canonical_parent_pair {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (owner child : External n) (parent : canonicalParent snapshot tree child=some owner) :
    HasPair snapshot tree (Nat.le_refl n) 0 owner.val child.val := by
  simp only [canonicalParent,Option.map_eq_some_iff] at parent
  obtain ⟨edge,lookup,equal⟩ := parent
  have spec := incomingEdge?_some_mem snapshot tree lookup
  exact ⟨edge,by simpa only [fullEdges] using spec.1,
    congrArg Fin.val equal,congrArg Fin.val spec.2⟩

theorem arrivals_before_event {before after : List (ℕ × ℕ)} {event : ℕ × ℕ}
    (side : Bool)
    (correctSide : if side then event.2<event.1 else event.1<event.2)
    (ordered : (arrivals side event.1 (before++event::after)).Pairwise (arrivalOrder side)) :
    ∀ old ∈ arrivals side event.1 before, arrivalOrder side old event.2 := by
  rw [arrivals_append] at ordered
  have cross := (List.pairwise_append.mp ordered).2.2
  intro old member
  apply cross old member event.2
  simp [arrivals,correctSide]

/-- The spatial append condition at an arbitrary actual prefix is derived
from canonical old-child geometry and the whole schedule's arrival order.
Its current child list is computed by `runLinks`, not assumed separately. -/
theorem actual_prefix_append_outer {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (source : External n) (sourceSide : External n × External n → Bool) (states : States n)
    (sound : SoundFor (canonicalParent snapshot tree) states)
    (persistent : Persistent states) (rank : ℕ → ℕ)
    (before after : List (External n × External n)) (event : External n × External n)
    (roots finalRoots : List ℕ)
    (run : Run rank ((before++event::after).map eventKeys) roots finalRoots)
    (actualChildren : ∀ child, HasChild snapshot tree (Nat.le_refl n) 0 source child ↔ child ∈ roots)
    (notSource : event.1 ≠ source)
    (labels : ℕ → States n → ℕ → ℤ) (time : ℕ)
    (arrivalOrderProof :
      (arrivals (targetSide event) event.1.val ((before++event::after).map eventKeys)).Pairwise
        (arrivalOrder (targetSide event))) :
    ∀ old ∈ entries
      (runLinks source sourceSide labels time states before event.1 (targetSide event)),
      outward (targetSide event) old
        (arrivalEntry (labels (time+before.length) (runLinks source sourceSide labels time states before)) event.1 event.2 (time+before.length)) := by
  have allDistinct := run_event_distinct rank _ roots finalRoots run
  have different := allDistinct event (by simp)
  have valueDifferent : event.1.val ≠ event.2.val := fun h => different (Fin.ext h)
  have sideOrder : if targetSide event then event.2.val<event.1.val else event.1.val<event.2.val := by
    unfold targetSide
    split_ifs <;> simp_all <;> omega
  have prior := arrivals_before_event (before := before.map eventKeys) (after := after.map eventKeys)
    (event := eventKeys event) (targetSide event) sideOrder
    (by simpa only [List.map_append,List.map_cons,eventKeys] using arrivalOrderProof)
  intro old member
  have keyMem : old.key ∈ (entries
      (runLinks source sourceSide labels time states before event.1 (targetSide event))).map Entry.key :=
    List.mem_map.mpr ⟨old,member,rfl⟩
  rw [runLinks_keys_nonroot source sourceSide labels time states before persistent
    (by intro e he; exact allDistinct e (List.mem_append_left _ he)) _ _ notSource] at keyMem
  rcases List.mem_append.mp keyMem with oldMem | arrived
  · obtain ⟨original,originalMem,sameKey⟩ := List.mem_map.mp oldMem
    obtain ⟨child,childKey,parent⟩ := sound event.1 (targetSide event) original originalMem
    have geometry := scheduled_arrival_outside_old_children snapshot tree source rank _ roots finalRoots run
      actualChildren (eventKeys event) (List.mem_map.mpr ⟨event,by simp,rfl⟩) child.val
      (canonical_parent_pair snapshot tree event.1 child parent)
    change (if targetSide event then event.2.val<old.key else old.key<event.2.val)
    simpa only [eventKeys,targetSide,decide_eq_true_eq,childKey,sameKey] using geometry
  · exact prior old.key arrived

@[simp] theorem runLinks_append {n : ℕ} (source : External n) (sourceSide : External n × External n → Bool)
    (labels : ℕ → States n → ℕ → ℤ) (time : ℕ) (states : States n)
    (first second : List (External n × External n)) :
    runLinks source sourceSide labels time states (first++second) =
      runLinks source sourceSide labels (time+first.length)
        (runLinks source sourceSide labels time states first) second := by
  induction first generalizing time states with
  | nil => simp [runLinks]
  | cons event rest ih =>
      simp only [List.cons_append,runLinks,ih,List.length_cons]
      congr 1
      omega

theorem runLinks_source_grower {n : ℕ} (source : External n) (sourceSide : External n × External n → Bool)
    (labels : ℕ → States n → ℕ → ℤ) (time : ℕ) (states : States n)
    (events : List (External n × External n))
    (notWinner : ∀ event ∈ events, event.1 ≠ source) (side : Bool) :
    (runLinks source sourceSide labels time states events source side).grower =
      (states source side).grower := by
  induction events generalizing time states with
  | nil => rfl
  | cons event rest ih =>
      rw [runLinks,ih (time+1) _ (by intro e he; exact notWinner e (List.mem_cons_of_mem _ he))]
      have ne := (notWinner event (by simp)).symm
      simp only [linkState,ne,false_and,↓reduceIte]
      split_ifs <;> rfl

theorem hasChild_ne_owner {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (owner : External n) (child : ℕ)
    (member : HasChild snapshot tree (Nat.le_refl n) 0 owner child) : child ≠ owner.val := by
  obtain ⟨edge,edgeMem,parentEq,childEq⟩ := member
  have strict := mem_treeEdges_rank_lt snapshot tree (Nat.le_refl n) edgeMem
  rw [parentEq] at strict
  intro same
  have eq : edge.child=owner := Fin.ext (childEq.trans same)
  rw [eq] at strict
  exact Nat.lt_irrefl _ strict

/-- Full ordered-state preservation for a concrete legal schedule. The
only schedule-specific geometry input is the already proved inner-to-outer
order of its literal mapped arrivals. The harder preexisting-child part
is discharged inside the theorem from the canonical old heap. -/
theorem runLinks_ordered {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (source : External n) (sourceSide : External n × External n → Bool) (states : States n)
    (sound : SoundFor (canonicalParent snapshot tree) states)
    (ordered : Ordered states) (persistent : Persistent states)
    (emptySource : ∀ side, growerEntries (states source side).grower=[])
    (rank : ℕ → ℕ) (events : List (External n × External n)) (roots finalRoots : List ℕ)
    (run : Run rank (events.map eventKeys) roots finalRoots)
    (actualChildren : ∀ child, HasChild snapshot tree (Nat.le_refl n) 0 source child ↔ child ∈ roots)
    (labels : ℕ → States n → ℕ → ℤ) (time : ℕ)
    (arrivalOrders : ∀ event ∈ events,
      (arrivals (targetSide event) event.1.val (events.map eventKeys)).Pairwise
        (arrivalOrder (targetSide event))) :
    Ordered (runLinks source sourceSide labels time states events) := by
  have different := run_event_distinct rank events roots finalRoots run
  have notWinner : ∀ event ∈ events, event.1 ≠ source := by
    intro event member same
    have rootsMember := (run.event_members _ (List.mem_map.mpr ⟨event,member,rfl⟩)).1
    have ne := hasChild_ne_owner snapshot tree source event.1.val ((actualChildren _).mpr rootsMember)
    exact ne (congrArg Fin.val same)
  have aux : ∀ rest before : List (External n × External n), events=before++rest →
      Ordered (runLinks source sourceSide labels time states before) →
      Ordered (runLinks source sourceSide labels time states events) := by
    intro rest
    induction rest with
    | nil =>
        intro before split orderBefore
        have same : events=before := by simpa only [List.append_nil] using split
        simpa only [same] using orderBefore
    | cons event rest ih =>
        intro before split orderBefore
        have member : event ∈ events := by rw [split]; simp
        let current := runLinks source sourceSide labels time states before
        let now := time+before.length
        let fresh := arrivalEntry (labels now current) event.1 event.2 now
        have currentPersistent : Persistent current := runLinks_persistent _ _ _ _ _ _ persistent
        have currentEmpty : growerEntries (current source (sourceSide event)).grower=[] := by
          rw [runLinks_source_grower source sourceSide labels time states before
            (by intro e he; exact notWinner e (by rw [split]; exact List.mem_append_left _ he))]
          exact emptySource (sourceSide event)
        have onCorrectSide : onSide event.1.val (targetSide event) fresh := by
          have ne : event.1.val ≠ event.2.val := fun h => different event member (Fin.ext h)
          change if targetSide event then event.2.val<event.1.val else event.1.val<event.2.val
          unfold targetSide
          split_ifs <;> simp_all <;> omega
        have outer : ∀ old ∈ entries (current event.1 (targetSide event)),
            outward (targetSide event) old fresh :=
          actual_prefix_append_outer snapshot tree source sourceSide states sound persistent rank
            before rest event roots finalRoots (by simpa only [split] using run) actualChildren
            (notWinner event member) labels time (by simpa only [split] using arrivalOrders event member)
        have nextOrder := linkState_ordered current source event.1 event.2 (sourceSide event)
          (targetSide event) fresh orderBefore currentPersistent currentEmpty onCorrectSide outer
        apply ih (before++[event])
        · simpa only [List.append_assoc,List.singleton_append] using split
        · simpa only [runLinks_append,runLinks,List.length_singleton] using nextOrder
  exact aux events [] rfl (by simpa only [runLinks] using ordered)

/-- The actual access appends memberships in strict chronological order,
retains every inherited frozen orientation, and advances the global entry
clock by exactly the number of executed links. -/
theorem runLinks_histories {n : ℕ} (source : External n)
    (sourceSide : External n × External n → Bool) (reader : ℕ → States n → ℕ → ℤ)
    (clock : ℕ) (states : States n) (events : List (External n × External n))
    (persistent : Persistent states) (histories : Histories states) (beforeTime : BeforeTime clock states)
    (emptySource : ∀ side, growerEntries (states source side).grower=[])
    (neverWins : ∀ event∈events, event.1≠source) :
    Histories (runLinks source sourceSide reader clock states events) ∧
    BeforeTime (clock+events.length) (runLinks source sourceSide reader clock states events) := by
  induction events generalizing clock states with
  | nil => simpa only [runLinks,List.length_nil,Nat.add_zero] using And.intro histories beforeTime
  | cons event rest ih =>
      let fresh := arrivalEntry (reader clock states) event.1 event.2 clock
      let next := linkState states source event.1 event.2 (sourceSide event) (targetSide event) fresh
      have nextPersistent : Persistent next := linkState_persistent _ _ _ _ _ _ _ persistent
      have nextHistories : Histories next := linkState_histories _ _ _ _ _ _ _ histories beforeTime
      have nextTime : BeforeTime (clock+1) next :=
        linkState_beforeTime _ _ _ _ _ _ _ persistent (emptySource _) beforeTime
      have nextEmpty : ∀ side, growerEntries (next source side).grower=[] := by
        intro side
        have ne := (neverWins event (by simp)).symm
        dsimp only [next,linkState]
        simp only [ne,false_and,↓reduceIte]
        split_ifs <;> exact emptySource side
      have result := ih (clock+1) next nextPersistent nextHistories nextTime nextEmpty
        (fun e he => neverWins e (List.mem_cons_of_mem _ he))
      simpa only [runLinks,List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using result

end GreedyMerge.ActualLinks

#print axioms GreedyMerge.ActualLinks.runLinks_keys_nonroot
#print axioms GreedyMerge.ActualLinks.actual_prefix_append_outer

#print axioms GreedyMerge.ActualLinks.runLinks_ordered

#print axioms GreedyMerge.ActualLinks.runLinks_histories
