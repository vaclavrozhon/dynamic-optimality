import MultiSplay.ClassicalSwitchStart
import MultiSplay.SecondaryEmissionWords
import MultiSplay.ComparatorSuffixAccounting

/-!
# Persistent genuine writes in the actual switch chronology

Each emitted switch uses its current preferred-component start. A genuine
write retains the original interval and primary owner; a structural boundary
record writes nothing. Thus each persistent row sees a literal subsequence
of the already bounded actual emission word, with the same initial bit.
-/

namespace MultiSplay.ComparatorHistory

open TangoSquared (DepthTree DepthSplit edgeChange changesFrom)
open TangoSquared.Primary (Key level mem_level)
open EndpointEncoding (State actualEmissions nodeStep)
open ClassicalSwitch (schedule startDepth)
open Secondary (Row rows project actualRow actualLedger)

/-- A genuine row write depends only on the current switch state and owner. -/
def write (row : Row) (entry : State × Key) : Option Bool :=
  if startDepth entry.1 entry.2 ≤ row.1.lo then project row entry.2 entry.2 else none

theorem take_eq_of_prefix {owner address : Key} (isPrefix : owner.IsPrefix address)
    {depth : Nat} (inside : depth ≤ owner.length) :
    owner.take depth = address.take depth := by
  obtain ⟨rest,rfl⟩ := isPrefix
  exact (List.take_append_of_le_length inside).symm

theorem project_prefix (row : Row) {owner address : Key} (isPrefix : owner.IsPrefix address) :
    project row owner owner = project row address owner := by
  by_cases inside : row.1.lo ≤ owner.length ∧ owner.length ≤ row.1.hi
  · simp only [project,if_pos inside,take_eq_of_prefix isPrefix inside.1]
  · simp only [project,if_neg inside,ite_self]

theorem actual_prefix {state : State} {address owner : Key}
    (emitted : owner ∈ actualEmissions state address) : owner.IsPrefix address :=
  EndpointEncoding.ascendingEmissions_prefix
    ((EndpointEncoding.actualEmissions_perm state address).mem_iff.mp emitted)

theorem schedule_write_sublist (row : Row) (state : State) (address : Key)
    (owners : List Key) (prefixes : ∀ owner ∈ owners, owner.IsPrefix address) :
    ((schedule state owners).filterMap (write row)).Sublist
      (owners.filterMap (project row address)) := by
  induction owners generalizing state with
  | nil => exact .refl _
  | cons owner rest ih =>
      have tail := ih (fun other member => prefixes other (by simp [member]))
        (state := EndpointEncoding.toggle state owner)
      have ownerPrefix := prefixes owner (by simp)
      simp only [schedule,List.filterMap_cons]
      by_cases retained : startDepth state owner ≤ row.1.lo
      · have same : write row (state,owner) = project row address owner := by
          simpa only [write,if_pos retained] using project_prefix row ownerPrefix
        rw [same]
        cases project row address owner with
        | none => exact tail
        | some bit => exact tail.cons_cons bit
      · have absent : write row (state,owner) = none := by simp only [write,if_neg retained]
        rw [absent]
        cases project row address owner with
        | none => exact tail
        | some bit => exact tail.cons bit

def history (state : State) : List Key → List (State × Key)
  | [] => []
  | address :: rest => schedule state (actualEmissions state address) ++
      history (nodeStep state address) rest

def rowWord (row : Row) (state : State) (addresses : List Key) : List Bool :=
  (history state addresses).filterMap (write row)

theorem rowWord_sublist (row : Row) (state : State) (addresses : List Key) :
    (rowWord row state addresses).Sublist (actualRow row state addresses) := by
  induction addresses generalizing state with
  | nil => exact .refl _
  | cons address rest ih =>
      simp only [rowWord,history,List.filterMap_append,actualRow]
      exact (schedule_write_sublist row state address (actualEmissions state address)
        (fun _ emitted => actual_prefix emitted)).append (ih (nodeStep state address))

def ledger {a b : Nat} (reference : DepthTree a b) (initial : Row → Bool)
    (state : State) (addresses : List Key) : Nat :=
  ∑ row ∈ rows reference, changesFrom (initial row) (rowWord row state addresses)

/-- No new initialization charge or row reset appears when components split. -/
theorem ledger_le_actual {a b : Nat} (reference : DepthTree a b) (initial : Row → Bool)
    (state : State) (addresses : List Key) :
    ledger reference initial state addresses ≤ actualLedger reference initial state addresses := by
  apply Finset.sum_le_sum
  intro row _
  exact TangoSquared.changesFrom_sublist (rowWord_sublist row state addresses) (initial row)

def update (entry : State × Key) (memory : Row → Bool) : Row → Bool :=
  fun row => (write row entry).getD (memory row)

/-- Reading along any continuation of the emitted node gives the local
genuine-memory update. The unchanged tail keeps its old owner records. -/
theorem update_local (entry : State × Key) (memory : Row → Bool) (path : Key)
    (continuation : entry.2.IsPrefix path) (split : DepthSplit) :
    update entry memory ⟨split,path.take split.lo⟩ =
      ComparatorSuffix.writeGenuine (startDepth entry.1 entry.2) entry.2.length
        (fun interval => memory ⟨interval,path.take interval.lo⟩) split := by
  by_cases inside : split.lo ≤ entry.2.length ∧ entry.2.length ≤ split.hi
  · have same := take_eq_of_prefix continuation inside.1
    simp only [update,write,project,ComparatorSuffix.writeGenuine,
      TangoSquared.Paper20261030.Secondary.intervalUpdate,if_pos inside,same,ite_true]
    split <;> rfl
  · simp only [update,write,project,ComparatorSuffix.writeGenuine,
      TangoSquared.Paper20261030.Secondary.intervalUpdate,if_neg inside,ite_self]
    rfl

theorem update_other_owner (entry : State × Key) (memory : Row → Bool)
    (row : Row) (different : row.2 ≠ entry.2.take row.1.lo) :
    update entry memory row = memory row := by
  simp [update,write,project,different]

def eventCost {a b : Nat} (reference : DepthTree a b) (memory : Row → Bool)
    (entry : State × Key) : Nat :=
  ∑ row ∈ rows reference, edgeChange (memory row) (update entry memory row)

/-- The global row cost is exactly the local genuine cost, for every actual
continuation of the emitted node. Off-path owner records remain untouched. -/
theorem eventCost_eq_genuine {a b : Nat} (reference : DepthTree a b)
    (memory : Row → Bool) (entry : State × Key) (path : Key)
    (continuation : entry.2.IsPrefix path) :
    eventCost reference memory entry =
      ComparatorSuffix.genuineCost reference (startDepth entry.1 entry.2) entry.2.length
        (fun split => memory ⟨split,path.take split.lo⟩) := by
  rw [eventCost,rows,Finset.sum_sigma,ComparatorSuffix.genuineCost]
  apply Finset.sum_congr rfl
  intro split _
  by_cases lower : split.lo ≤ entry.2.length
  · rw [Finset.sum_eq_single (entry.2.take split.lo)]
    · rw [take_eq_of_prefix continuation lower,update_local entry memory path continuation split]
    · intro owner _ different
      rw [update_other_owner entry memory ⟨split,owner⟩ different, TangoSquared.edgeChange_self]
    · intro absent
      exact False.elim (absent ((mem_level _ _).mpr (List.length_take_of_le lower)))
  · have inactive (owner : Key) : update entry memory ⟨split,owner⟩ = memory ⟨split,owner⟩ := by
      simp [update,write,project,lower]
    simp only [inactive,TangoSquared.edgeChange_self,Finset.sum_const_zero]
    simp [ComparatorSuffix.writeGenuine,TangoSquared.Paper20261030.Secondary.intervalUpdate,lower]

def runCost {a b : Nat} (reference : DepthTree a b) (memory : Row → Bool) :
    List (State × Key) → Nat
  | [] => 0
  | entry :: rest => eventCost reference memory entry +
      runCost reference (update entry memory) rest

theorem runCost_eq {a b : Nat} (reference : DepthTree a b) (memory : Row → Bool)
    (entries : List (State × Key)) :
    runCost reference memory entries =
      ∑ row ∈ rows reference, changesFrom (memory row) (entries.filterMap (write row)) := by
  induction entries generalizing memory with
  | nil => simp [runCost]
  | cons entry rest ih =>
      rw [runCost,ih,eventCost,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro row _
      simp only [List.filterMap_cons,update]
      cases write row entry <;> simp

theorem runCost_history_eq {a b : Nat} (reference : DepthTree a b) (memory : Row → Bool)
    (state : State) (addresses : List Key) :
    runCost reference memory (history state addresses) = ledger reference memory state addresses :=
  runCost_eq reference memory (history state addresses)

theorem runCost_history_le_actual {a b : Nat} (reference : DepthTree a b) (memory : Row → Bool)
    (state : State) (addresses : List Key) :
    runCost reference memory (history state addresses) ≤ actualLedger reference memory state addresses := by
  rw [runCost_history_eq]
  exact ledger_le_actual reference memory state addresses

end MultiSplay.ComparatorHistory
