import TangoSquared.Paper20261030.MemoryKeys
import TangoSquared.Paper20261030.SecondaryWords

/-!
# Concrete persistent secondary-memory execution

Each bit is indexed by its fixed primary owner and secondary interval.
For one request, `requestWrites` lists exactly the writes at its increasing
exit depths. Grouping writes by bit is legitimate because different bits
are independent; `memoryCost_eq_histories` proves the exact accumulated
cost. A bit's final value is the last write in its actual history.

The completion root is treated separately: it starts and finishes each
request pointing at the completion leaf. Physical BST realization and
global LCA charging are separate obligations.
-/

namespace TangoSquared.Paper20261030.Secondary

open PreferredProjection
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

def intervalDepths (s : DepthSplit) (ds : List Nat) : List Nat :=
  ds.filter (fun d => decide (s.lo ≤ d ∧ d ≤ s.hi))

def requestWrites (primary : PrefRouter α) (x : α) (key : MemoryKey) : List Bool :=
  if key.2.IsPrefix (primary.searchPath x) then
    writeWord key.1.cut (intervalDepths key.1 (primary.exitDepths x))
  else []

structure MemoryState (α : Type*) where
  primary : PrefRouter α
  preference : MemoryKey → Bool

def MemoryState.initial (primary : PrefRouter α) : MemoryState α := ⟨primary,fun _ => true⟩

def MemoryState.advance (s : MemoryState α) (x : α) : MemoryState α :=
  ⟨s.primary.access x,fun key => (requestWrites s.primary x key).getLastD (s.preference key)⟩

def bitHistory (primary : PrefRouter α) (key : MemoryKey) : List α → List Bool
  | [] => []
  | x :: xs => requestWrites primary x key ++ bitHistory (primary.access x) key xs

def runMemory (s : MemoryState α) : List α → MemoryState α
  | [] => s
  | x :: xs => runMemory (s.advance x) xs

def memoryCost (keys : Finset MemoryKey) (s : MemoryState α) : List α → Nat
  | [] => 0
  | x :: xs =>
      (∑ key ∈ keys, changesFrom (s.preference key) (requestWrites s.primary x key)) +
        memoryCost keys (s.advance x) xs

theorem last_append (initial : Bool) (xs ys : List Bool) :
    (xs ++ ys).getLastD initial = ys.getLastD (xs.getLastD initial) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih => rw [List.cons_append,List.getLastD_cons,List.getLastD_cons,ih]

theorem runMemory_primary (s : MemoryState α) (xs : List α) :
    (runMemory s xs).primary = s.primary.run xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simpa only [runMemory,MemoryState.advance,PrefRouter.run] using ih (s.advance x)

/-- No reset or reinitialization occurs when the primary path changes. -/
theorem runMemory_preference (s : MemoryState α) (xs : List α) (key : MemoryKey) :
    (runMemory s xs).preference key = (bitHistory s.primary key xs).getLastD (s.preference key) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [runMemory,ih,bitHistory,last_append]
    rfl

/-- Exact cost decomposition, including the initialized preferences. -/
theorem memoryCost_eq_histories (keys : Finset MemoryKey) (s : MemoryState α) (xs : List α) :
    memoryCost keys s xs =
      ∑ key ∈ keys, changesFrom (s.preference key) (bitHistory s.primary key xs) := by
  induction xs generalizing s with
  | nil => simp [memoryCost,bitHistory]
  | cons x xs ih =>
    simp only [memoryCost,ih,bitHistory,changes_append,Finset.sum_add_distrib,MemoryState.advance]

theorem memoryKeys_runMemory (s : MemoryState α) {a b : Nat}
    (reference : DepthTree a b) (xs : List α) :
    memoryKeys (runMemory s xs).primary reference = memoryKeys s.primary reference := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => rw [runMemory,ih]; exact memoryKeys_access _ reference x

theorem requestWrites_changes_le_two (primary : PrefRouter α) (x : α) (key : MemoryKey)
    (initial : Bool) : changesFrom initial (requestWrites primary x key) ≤ 2 := by
  unfold requestWrites
  split_ifs
  · exact writeWord_changes_le_two _ _ ((primary.exitDepths_increasing x).filter _) initial
  · simp

def completionWord (ds : List Nat) : List Bool := ds.map (fun _ => false) ++ [true]

theorem completionWord_last (ds : List Nat) (initial : Bool) :
    (completionWord ds).getLastD initial = true := by
  rw [completionWord,last_append]
  rfl

theorem completionWord_cost (ds : List Nat) :
    changesFrom true (completionWord ds) = if ds = [] then 0 else 2 := by
  have hm : ds.map (fun _ => false) = List.replicate ds.length false := by
    induction ds with
    | nil => rfl
    | cons d ds ih => simp [ih,List.replicate_succ]
  unfold completionWord
  rw [hm]
  cases ds with
  | nil => decide +kernel
  | cons d ds => simp [changes_replicate_prefix,edgeChange]

def completionCost (primary : PrefRouter α) : List α → Nat
  | [] => 0
  | x :: xs => changesFrom true (completionWord (primary.exitDepths x)) +
      completionCost (primary.access x) xs

/-- The bit-array implementation's full secondary flip count. The memory
set is computed from the actual references and is invariant during the run. -/
def secondaryCost {a b : Nat} (reference : DepthTree a b) (s : MemoryState α)
    (xs : List α) : Nat :=
  memoryCost (memoryKeys s.primary reference) s xs + completionCost s.primary xs

end TangoSquared.Paper20261030.Secondary
