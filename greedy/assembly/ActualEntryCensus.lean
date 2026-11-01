import ActualLinkClasses
import ExecutionTrace

/-!
One consistent origin assignment for all actual membership occurrences.
Initial entries, ordinary administrative entries, and link arrivals are
separate occurrence types. A link is classified from its two actual source
IDs and pre-update labels. Its bad-arrival origin and the exceptional-entry
injection are computed from that same classification, so no independent
bad-edge census or exceptional-slot injection is assumed.
-/
namespace GreedyMerge.EntryCensus

open GreedyForest GreedyForest.Execution

inductive LinkKind where
  | good | bad | boundary
  deriving DecidableEq

def classify (winnerBlock loserBlock : ℕ) (winnerLabel loserLabel : ℤ) : LinkKind :=
  if winnerBlock=loserBlock then
    if winnerLabel=loserLabel then .good else .bad
  else .boundary

def actualKind (rank : ℕ → ℕ) (labels : ℕ → ℤ) (events : List (ℕ × ℕ))
    (block : ℕ → ℕ) (event : Fin events.length) : LinkKind :=
  classify (block (events.get event).1) (block (events.get event).2)
    (Phase.labelsAt rank labels events event (events.get event).1)
    (Phase.labelsAt rank labels events event (events.get event).2)

theorem classify_bad_iff (winnerBlock loserBlock : ℕ) (winnerLabel loserLabel : ℤ) :
    classify winnerBlock loserBlock winnerLabel loserLabel=.bad ↔
      winnerBlock=loserBlock ∧ winnerLabel≠loserLabel := by
  unfold classify
  split_ifs <;> simp_all

theorem classify_good_iff (winnerBlock loserBlock : ℕ) (winnerLabel loserLabel : ℤ) :
    classify winnerBlock loserBlock winnerLabel loserLabel=.good ↔
      winnerBlock=loserBlock ∧ winnerLabel=loserLabel := by
  unfold classify
  split_ifs <;> simp_all

theorem classify_boundary_iff (winnerBlock loserBlock : ℕ) (winnerLabel loserLabel : ℤ) :
    classify winnerBlock loserBlock winnerLabel loserLabel=.boundary ↔
      winnerBlock≠loserBlock := by
  unfold classify
  split_ifs <;> simp_all

theorem actualKind_bad_iff (rank : ℕ → ℕ) (labels : ℕ → ℤ) (events : List (ℕ × ℕ))
    (block : ℕ → ℕ) (event : Fin events.length) :
    actualKind rank labels events block event=.bad ↔
      event∈Phase.actualInternalBad rank labels events block := by
  simp only [actualKind,classify_bad_iff,Phase.actualInternalBad,Finset.mem_filter,Finset.mem_univ,true_and]

theorem actualKind_good_iff (rank : ℕ → ℕ) (labels : ℕ → ℤ) (events : List (ℕ × ℕ))
    (block : ℕ → ℕ) (event : Fin events.length) :
    actualKind rank labels events block event=.good ↔
      event∈Phase.actualInternalGood rank labels events block := by
  simp only [actualKind,classify_good_iff,Phase.actualInternalGood,Finset.mem_filter,Finset.mem_univ,true_and]

variable {Initial Ordinary Link Record : Type*}

abbrev Member (Initial Ordinary Link : Type*) := Sum Initial (Sum Ordinary Link)
abbrev Bad (kind : Link → LinkKind) := {event : Link // kind event=.bad}
abbrev Good (kind : Link → LinkKind) := {event : Link // kind event=.good}
abbrev Boundary (kind : Link → LinkKind) := {event : Link // kind event=.boundary}

def origin (kind : Link → LinkKind) : Member Initial Ordinary Link → Option (Bad kind)
  | .inl _ => none
  | .inr (.inl _) => none
  | .inr (.inr event) => if h : kind event=.bad then some ⟨event,h⟩ else none

theorem origin_some_iff (kind : Link → LinkKind) (member : Member Initial Ordinary Link)
    (event : Bad kind) : origin kind member=some event ↔ member=Sum.inr (Sum.inr event.val) := by
  rcases member with initial | ordinary | link
  · simp [origin]
  · simp [origin]
  · by_cases bad : kind link=.bad
    · simp only [origin,dif_pos bad,Option.some.injEq,Sum.inr.injEq]
      exact Subtype.ext_iff
    · have different : link≠event.val := by
        intro same
        exact bad (same ▸ event.property)
      simp [origin,bad,different]

abbrev Exceptional (kind : Link → LinkKind) :=
  {member : Member Initial Ordinary Link // (origin kind member).isNone}

def exceptionalIndex (kind : Link → LinkKind) (occurrence : Exceptional (Initial:=Initial) (Ordinary:=Ordinary) kind) :
    Sum Initial (Sum Ordinary (Sum (Good kind) (Boundary kind))) := by
  rcases occurrence with ⟨member,exceptional⟩
  rcases member with initial | ordinary | event
  · exact .inl initial
  · exact .inr (.inl ordinary)
  · by_cases good : kind event=.good
    · exact .inr (.inr (.inl ⟨event,good⟩))
    · have boundary : kind event=.boundary := by
        cases hk : kind event <;> simp_all [origin]
      exact .inr (.inr (.inr ⟨event,boundary⟩))

def recoverIndex (kind : Link → LinkKind) :
    Sum Initial (Sum Ordinary (Sum (Good kind) (Boundary kind))) → Member Initial Ordinary Link
  | .inl initial => .inl initial
  | .inr (.inl ordinary) => .inr (.inl ordinary)
  | .inr (.inr (.inl event)) => .inr (.inr event.val)
  | .inr (.inr (.inr event)) => .inr (.inr event.val)

theorem recover_exceptionalIndex (kind : Link → LinkKind)
    (occurrence : Exceptional (Initial:=Initial) (Ordinary:=Ordinary) kind) :
    recoverIndex kind (exceptionalIndex kind occurrence)=occurrence.val := by
  rcases occurrence with ⟨member,exceptional⟩
  rcases member with initial | ordinary | event
  · rfl
  · rfl
  · cases hk : kind event with
    | good => simp [exceptionalIndex,recoverIndex,hk]
    | boundary => simp [exceptionalIndex,recoverIndex,hk]
    | bad => simp [origin,hk] at exceptional

theorem exceptionalIndex_injective (kind : Link → LinkKind) :
    Function.Injective (exceptionalIndex (Initial:=Initial) (Ordinary:=Ordinary) kind) := by
  intro first second equal
  apply Subtype.ext
  simpa only [recover_exceptionalIndex] using congrArg (recoverIndex kind) equal

/-- Initial slots charge their actual record; ordinary, good and boundary
occurrences charge themselves. This is exactly the finite trace's sum of
exception classes, with ordinary entries excluding initialization. -/
def exceptionalOrigin (initialRecord : Initial → Record) (kind : Link → LinkKind) :
    Exceptional (Initial:=Initial) (Ordinary:=Ordinary) kind →
      Sum Record (Sum Ordinary (Sum (Good kind) (Boundary kind))) :=
  Sum.map initialRecord id ∘ exceptionalIndex kind

theorem exceptionalOrigin_injective (initialRecord : Initial → Record)
    (initialUnique : Function.Injective initialRecord) (kind : Link → LinkKind) :
    Function.Injective (exceptionalOrigin (Ordinary:=Ordinary) initialRecord kind) :=
  ((Sum.map_injective.mpr ⟨initialUnique,Function.injective_id⟩).comp (exceptionalIndex_injective kind))

theorem entryBadEdges_eq_filterMap (kind : Link → LinkKind)
    (record : Member Initial Ordinary Link → Record) (creatorLabel : Member Initial Ordinary Link → ℤ)
    (order : List (Member Initial Ordinary Link)) :
    entryBadEdges (order.map (fun member => EntryEvent.mk (record member) (creatorLabel member) (origin kind member))) =
      order.filterMap (origin kind) := by
  induction order with
  | nil => rfl
  | cons member rest ih =>
      simp only [List.map_cons,entryBadEdges,ih,List.filterMap_cons]
      cases origin kind member <;> simp

/-- Every bad edge is the origin of exactly its own link-arrival member.
An injective enumeration of member occurrences therefore gives the exact
badNodup and badComplete fields required by AccountingTrace. -/
theorem bad_census (kind : Link → LinkKind)
    (record : Member Initial Ordinary Link → Record) (creatorLabel : Member Initial Ordinary Link → ℤ)
    (order : List (Member Initial Ordinary Link)) (unique : order.Nodup)
    (complete : ∀ member, member∈order) :
    (entryBadEdges (order.map (fun member => EntryEvent.mk (record member) (creatorLabel member) (origin kind member)))).Nodup ∧
    ∀ event : Bad kind, event∈entryBadEdges (order.map (fun member =>
      EntryEvent.mk (record member) (creatorLabel member) (origin kind member))) := by
  rw [entryBadEdges_eq_filterMap]
  constructor
  · apply List.Nodup.filterMap _ unique
    intro first second event firstMem secondMem
    have firstEq := (origin_some_iff kind first event).mp firstMem
    have secondEq := (origin_some_iff kind second event).mp secondMem
    exact firstEq.trans secondEq.symm
  · intro event
    apply List.mem_filterMap.mpr
    exact ⟨.inr (.inr event.val),complete _,(origin_some_iff kind _ event).mpr rfl⟩


theorem link_census [Fintype Link] (kind : Link → LinkKind) :
    Fintype.card Link=Fintype.card (Good kind)+Fintype.card (Bad kind)+Fintype.card (Boundary kind) := by
  classical
  have point : ∀ event : Link,
      (if kind event=.good then 1 else 0) + (if kind event=.bad then 1 else 0) +
        (if kind event=.boundary then 1 else 0) = (1 : ℕ) := by
    intro event
    cases kind event <;> simp
  have counts := congrArg (fun f : Link → ℕ => ∑ event, f event) (funext point)
  simp only [Finset.sum_add_distrib,Finset.sum_boole,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] at counts
  simpa [Fintype.card_subtype,Good,Bad,Boundary] using counts.symm

end GreedyMerge.EntryCensus

#print axioms GreedyMerge.EntryCensus.actualKind_bad_iff
#print axioms GreedyMerge.EntryCensus.exceptionalOrigin_injective
#print axioms GreedyMerge.EntryCensus.bad_census

#print axioms GreedyMerge.EntryCensus.link_census
