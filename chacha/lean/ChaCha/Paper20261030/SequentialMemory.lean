import ChaCha.Paper20261030.PersistentMemory
import ChaCha.Paper20261030.HeadSwitchOwners

/-!
# Secondary memory updates in actual exit-depth order

The earlier bit-history accounting groups writes by memory. Here the same
execution is performed one exit depth at a time, preserving all other
bits at each step. Both the final state and the exact flip count agree
with the grouped implementation.
-/

namespace ChaCha.Paper20261030.Secondary

open PreferredProjection

variable {α : Type*} [DecidableEq α]

def depthWrite (primary : PrefRouter α) (x : α) (d : Nat) (key : MemoryKey) : Option Bool :=
  if key.2.IsPrefix (primary.searchPath x) ∧ key.1.lo ≤ d ∧ d ≤ key.1.hi then
    some (decide (key.1.cut < d)) else none

def depthHistory (primary : PrefRouter α) (x : α) (key : MemoryKey) : List Nat → List Bool
  | [] => []
  | d :: ds => (depthWrite primary x d key).toList ++ depthHistory primary x key ds

def advanceDepth (primary : PrefRouter α) (x : α) (d : Nat) (preference : MemoryKey → Bool) :
    MemoryKey → Bool := fun key => (depthWrite primary x d key).getD (preference key)

def runDepths (primary : PrefRouter α) (x : α) : List Nat → (MemoryKey → Bool) → (MemoryKey → Bool)
  | [],preference => preference
  | d :: ds,preference => runDepths primary x ds (advanceDepth primary x d preference)

def depthCost (keys : Finset MemoryKey) (primary : PrefRouter α) (x : α) :
    List Nat → (MemoryKey → Bool) → Nat
  | [],_ => 0
  | d :: ds,preference =>
      (∑ key ∈ keys, changesFrom (preference key) (depthWrite primary x d key).toList) +
        depthCost keys primary x ds (advanceDepth primary x d preference)

theorem depthHistory_word (primary : PrefRouter α) (x : α) (key : MemoryKey) (ds : List Nat) :
    depthHistory primary x key ds =
      if key.2.IsPrefix (primary.searchPath x) then writeWord key.1.cut (intervalDepths key.1 ds) else [] := by
  induction ds with
  | nil => by_cases ho : key.2.IsPrefix (primary.searchPath x) <;> simp [depthHistory,intervalDepths,writeWord,ho]
  | cons d ds ih =>
    by_cases ho : key.2.IsPrefix (primary.searchPath x)
    · by_cases hd : key.1.lo ≤ d ∧ d ≤ key.1.hi
      · simp [depthHistory,depthWrite,ho,hd,ih,intervalDepths,writeWord]
      · simp [depthHistory,depthWrite,ho,hd,ih,intervalDepths,writeWord]
    · simp [depthHistory,depthWrite,ho,ih]

theorem depthHistory_request (primary : PrefRouter α) (x : α) (key : MemoryKey) :
    depthHistory primary x key (primary.exitDepths x) = requestWrites primary x key :=
  depthHistory_word primary x key _

theorem option_last (bit : Option Bool) (initial : Bool) : bit.toList.getLastD initial = bit.getD initial := by
  cases bit <;> rfl

theorem runDepths_last (primary : PrefRouter α) (x : α) (ds : List Nat)
    (preference : MemoryKey → Bool) (key : MemoryKey) :
    runDepths primary x ds preference key = (depthHistory primary x key ds).getLastD (preference key) := by
  induction ds generalizing preference with
  | nil => rfl
  | cons d ds ih =>
    rw [runDepths,ih,depthHistory,last_append,option_last]
    rfl

theorem depthCost_histories (keys : Finset MemoryKey) (primary : PrefRouter α) (x : α)
    (ds : List Nat) (preference : MemoryKey → Bool) :
    depthCost keys primary x ds preference =
      ∑ key ∈ keys, changesFrom (preference key) (depthHistory primary x key ds) := by
  induction ds generalizing preference with
  | nil => simp [depthCost,depthHistory]
  | cons d ds ih =>
    simp only [depthCost,ih,depthHistory,changes_append,option_last,advanceDepth,Finset.sum_add_distrib]

def sequentialRequest (s : MemoryState α) (x : α) : MemoryState α :=
  ⟨s.primary.access x,runDepths s.primary x (s.primary.exitDepths x) s.preference⟩

theorem sequentialRequest_eq_advance (s : MemoryState α) (x : α) :
    sequentialRequest s x = s.advance x := by
  have hp : runDepths s.primary x (s.primary.exitDepths x) s.preference =
      fun key => (requestWrites s.primary x key).getLastD (s.preference key) := by
    funext key
    rw [runDepths_last,depthHistory_request]
  exact congrArg (MemoryState.mk (s.primary.access x)) hp

theorem sequentialRequest_cost (keys : Finset MemoryKey) (s : MemoryState α) (x : α) :
    depthCost keys s.primary x (s.primary.exitDepths x) s.preference = memoryCost keys s [x] := by
  rw [depthCost_histories]
  simp only [depthHistory_request,memoryCost,Nat.add_zero]

theorem depthWrite_path_congr {t u : PrefRouter α} {x : α}
    (h : t.searchPath x = u.searchPath x) (d : Nat) (key : MemoryKey) :
    depthWrite t x d key = depthWrite u x d key := by simp only [depthWrite,h]

theorem runDepths_path_congr {t u : PrefRouter α} {x : α}
    (h : t.searchPath x = u.searchPath x) (ds : List Nat) (preference : MemoryKey → Bool) :
    runDepths t x ds preference = runDepths u x ds preference := by
  have ha : ∀ d pref, advanceDepth t x d pref = advanceDepth u x d pref := by
    intro d pref
    funext key
    simp only [advanceDepth,depthWrite_path_congr h]
  induction ds generalizing preference with
  | nil => rfl
  | cons d ds ih => simp only [runDepths,ha,ih]

inductive SequentialHeadTrace (x : α) : MemoryState α → List Nat → MemoryState α → Prop
  | nil (s : MemoryState α) : SequentialHeadTrace x s [] s
  | cons {t u : PrefRouter α} {preference : MemoryKey → Bool} {final : MemoryState α}
      {d : Nat} {ds : List Nat} (step : PrefRouter.HeadStep x d t u)
      (rest : SequentialHeadTrace x ⟨u,advanceDepth t x d preference⟩ ds final) :
      SequentialHeadTrace x ⟨t,preference⟩ (d :: ds) final

theorem lift_headTrace {x : α} {t u : PrefRouter α} {ds : List Nat}
    (h : PrefRouter.HeadTrace x t ds u) (preference : MemoryKey → Bool) :
    SequentialHeadTrace x ⟨t,preference⟩ ds ⟨u,runDepths t x ds preference⟩ := by
  induction h generalizing preference with
  | nil t => exact .nil _
  | @cons t u v d ds step rest ih =>
    apply SequentialHeadTrace.cons step
    have ht := ih (advanceDepth t x d preference)
    simpa only [runDepths,runDepths_path_congr (step.searchPath x)] using ht

/-- The concrete loop writes the exit bits, performs that head switch,
and retains its resulting memory for the next iteration. Its final state
is exactly the state used in the proved global counting bound. -/
theorem access_sequential_headTrace (s : MemoryState α) (x : α) :
    SequentialHeadTrace x s (s.primary.exitDepths x) (s.advance x) := by
  rw [← sequentialRequest_eq_advance]
  exact lift_headTrace (s.primary.access_headTrace x) s.preference

theorem head_depthWrite_owner {x : α} {d : Nat} {t u : PrefRouter α}
    (h : PrefRouter.HeadStep x d t u) (hn : t.leaves.Nodup) (key : MemoryKey)
    (hlen : key.2.length = key.1.lo) :
    depthWrite t x d key =
      if key.2.IsPrefix (t.searchPath t.terminal) ∧ key.1.lo ≤ d ∧ d ≤ key.1.hi then
        some (decide (key.1.cut < d)) else none := by
  by_cases hd : key.1.lo ≤ d ∧ d ≤ key.1.hi
  · have hp := h.memory_owner hn hd.1
    have he : key.2.IsPrefix (t.searchPath x) ↔ key.2.IsPrefix (t.searchPath t.terminal) := by
      simp only [List.prefix_iff_eq_take,hlen,hp]
    simp only [depthWrite,he]
  · simp [depthWrite,hd]

/-- On every actual memory key, selecting an owner from the request agrees
with selecting it from the active preferred endpoint before the switch. -/
theorem head_depthWrite_memory_owner {x : α} {d a b : Nat} {t u : PrefRouter α}
    (h : PrefRouter.HeadStep x d t u) (hn : t.leaves.Nodup) (reference : DepthTree a b)
    (key : MemoryKey) (hk : key ∈ memoryKeys t reference) :
    depthWrite t x d key =
      if key.2.IsPrefix (t.searchPath t.terminal) ∧ key.1.lo ≤ d ∧ d ≤ key.1.hi then
        some (decide (key.1.cut < d)) else none := by
  have hm := (mem_memoryKeys t reference key.1 key.2).mp hk
  exact head_depthWrite_owner h hn key (PrefRouter.mem_ownerPaths.mp hm.2).1

end ChaCha.Paper20261030.Secondary
