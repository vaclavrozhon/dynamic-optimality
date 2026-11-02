import MultiSplay.ComparatorGenuineHistory
import MultiSplay.ComparatorStableRestoration

/-!
# Global owner memory through a classical preferred-path switch

A component reads a global row at the prefix of its external completion
address ending at the row's lower depth. Two completions with the same
component start therefore share every row that this component can write.
The main component receives the prepared old prefix and incoming suffix;
the parked suffix and all other components retain their genuine rows.
Structural rows are masked by `ComparatorStableSuffix.bits`, not reset in
global memory.
-/

namespace MultiSplay.ClassicalSwitch

open ChaCha.Primary (Key)
open EndpointEncoding (State below)

/-- Once the entire nonpreferred prefix has been included, taking a longer
prefix does not change the start of the current preferred component. -/
theorem startDepth_take (state : State) (address : Key) (depth : Nat)
    (included : startDepth state address ≤ depth) :
    startDepth state (address.take depth) = startDepth state address := by
  induction address generalizing state depth with
  | nil => simp [startDepth]
  | cons edge rest ih =>
      cases depth with
      | zero =>
          have zero : startDepth state (edge :: rest) = 0 := by omega
          change 0 = startDepth state (edge :: rest)
          exact zero.symm
      | succ depth =>
          have lower : startDepth (below state edge) rest ≤ depth := by
            simp only [startDepth] at included
            split at included <;> omega
          simp only [List.take_succ_cons, startDepth, ih (below state edge) depth lower]

/-- The original reference address of the current component root. -/
def componentStart (state : State) (address : Key) : Key :=
  address.take (startDepth state address)

theorem componentStart_eq_of_take_eq (state : State) (first second : Key) (depth : Nat)
    (same : first.take depth = second.take depth)
    (firstStart : startDepth state first ≤ depth)
    (secondStart : startDepth state second ≤ depth) :
    componentStart state first = componentStart state second := by
  have starts : startDepth state first = startDepth state second := by
    rw [← startDepth_take state first depth firstStart,
      ← startDepth_take state second depth secondStart, same]
  have prefixes := congrArg (List.take (startDepth state first)) same
  simpa only [List.take_take, Nat.min_eq_left firstStart, componentStart, ← starts] using prefixes

end MultiSplay.ClassicalSwitch

namespace MultiSplay.ComparatorHistory

open ChaCha (DepthSplit)
open ChaCha.Primary (Key)
open EndpointEncoding (State)
open ClassicalSwitch (startDepth componentStart)
open Secondary (Row)
open ChaCha.Paper20261030.Secondary (intervalUpdate spliceBits)
open ComparatorSuffix (writeGenuine)
open ComparatorStableSuffix (bits)

/-- Local genuine memory read from the immutable original row and owner. -/
def localBits (memory : Row → Bool) (path : Key) (split : DepthSplit) : Bool :=
  memory ⟨split, path.take split.lo⟩

theorem localBits_eq_of_prefix (memory : Row → Bool) {pivot first second : Key}
    (firstPrefix : pivot.IsPrefix first) (secondPrefix : pivot.IsPrefix second)
    (split : DepthSplit) (lower : split.lo ≤ pivot.length) :
    localBits memory first split = localBits memory second split := by
  unfold localBits
  rw [← take_eq_of_prefix firstPrefix lower, ← take_eq_of_prefix secondPrefix lower]

/-- A write at the pivot depth never reaches a strictly deeper owner row. -/
theorem update_after_depth (entry : State × Key) (memory : Row → Bool)
    (row : Row) (later : entry.2.length < row.1.lo) :
    update entry memory row = memory row := by
  simp [update, write, Secondary.project, show ¬row.1.lo ≤ entry.2.length by omega]

/-- Exact global-to-local memory splice. Both paths are literal reference
completions extending the pivot; no memory equality is assumed. -/
theorem update_main (entry : State × Key) (memory : Row → Bool) (oldPath newPath : Key)
    (oldPrefix : entry.2.IsPrefix oldPath) (newPrefix : entry.2.IsPrefix newPath) :
    localBits (update entry memory) newPath =
      spliceBits entry.2.length
        (writeGenuine (startDepth entry.1 entry.2) entry.2.length (localBits memory oldPath))
        (localBits memory newPath) := by
  funext split
  by_cases lower : split.lo ≤ entry.2.length
  · simp only [spliceBits, if_pos lower]
    have updated := update_local entry memory newPath newPrefix split
    change localBits (update entry memory) newPath split =
      writeGenuine (startDepth entry.1 entry.2) entry.2.length (localBits memory newPath) split at updated
    have same := localBits_eq_of_prefix memory newPrefix oldPrefix split lower
    rw [updated]
    simp only [writeGenuine, intervalUpdate, same]
  · simp only [spliceBits, if_neg lower]
    exact update_after_depth entry memory ⟨split, newPath.take split.lo⟩
      (by change entry.2.length < split.lo; omega)

/-- The parked suffix keeps its old local memory at every genuine interval.
The same statement applies to any deeper component, including an empty tail. -/
theorem bits_update_after (entry : State × Key) (memory : Row → Bool)
    (path : Key) (start : Nat) (later : entry.2.length < start) :
    bits start (localBits (update entry memory) path) = bits start (localBits memory path) := by
  funext split
  by_cases structural : split.lo < start
  · simp only [bits, if_pos structural]
  · simp only [bits, if_neg structural]
    exact update_after_depth entry memory ⟨split, path.take split.lo⟩
      (by change entry.2.length < split.lo; omega)

theorem bits_update_parked (entry : State × Key) (memory : Row → Bool) (oldPath : Key) :
    bits (entry.2.length + 1) (localBits (update entry memory) oldPath) =
      bits (entry.2.length + 1) (localBits memory oldPath) :=
  bits_update_after entry memory oldPath _ (by omega)

/-- Distinct current component roots cannot share a row that is genuine
for the other component and writable by this pivot. -/
theorem update_other_component (state : State) (pivot path : Key) (memory : Row → Bool)
    (different : componentStart state path ≠ componentStart state pivot)
    (split : DepthSplit) (genuine : startDepth state path ≤ split.lo) :
    localBits (update (state, pivot) memory) path split = localBits memory path split := by
  by_cases retained : startDepth state pivot ≤ split.lo
  · apply update_other_owner
    intro same
    exact different (ClassicalSwitch.componentStart_eq_of_take_eq state path pivot split.lo
      same genuine retained)
  · simp only [localBits, update, write, if_neg retained, Option.getD_none]

/-- Full stable-source memory frame for every other preferred component. -/
theorem bits_update_other_component (state : State) (pivot path : Key) (memory : Row → Bool)
    (different : componentStart state path ≠ componentStart state pivot) :
    bits (startDepth state path) (localBits (update (state, pivot) memory) path) =
      bits (startDepth state path) (localBits memory path) := by
  funext split
  by_cases structural : split.lo < startDepth state path
  · simp only [bits, if_pos structural]
  · simp only [bits, if_neg structural]
    exact update_other_component state pivot path memory different split (by omega)

end MultiSplay.ComparatorHistory
