import DynamicOptimality.Basic
import Mathlib.Data.Finset.Sort

/-! # A finite alphabet for the actually observed colored keys

An event is `(color,key)`. Encoding only observed pairs avoids charging
the unused universe; encoding only observed colors avoids an unused-finger
startup charge. A monotone decoder later coalesces copies of the same
original key. This interface is discharged by `ShuffleEncoding`.
-/

namespace DynamicOptimality.ColoredWalks

structure Encoding {n k : Nat} (events : List (Fin k × Fin n)) where
  size : Nat
  count : Nat
  size_pos : 0 < size
  count_pos : 0 < count
  size_le_length : size ≤ events.length
  count_le_length : count ≤ events.length
  count_le_colors : count ≤ k
  encode : Fin k × Fin n → Fin size
  decode : Fin size → Fin k × Fin n
  color : Fin k → Fin count
  decode_mem : ∀ rank, decode rank ∈ events
  decode_encode : ∀ event ∈ events, decode (encode event) = event
  encode_decode : ∀ rank, encode (decode rank) = rank
  monotone_key : Monotone (fun rank => (decode rank).2)
  same_color : ∀ first last, color (decode first).1 = color (decode last).1 ↔
    (decode first).1 = (decode last).1
  order_same_color : ∀ first last, (decode first).1 = (decode last).1 →
    (first < last ↔ (decode first).2 < (decode last).2)

namespace Encoding

variable {n k : Nat} {events : List (Fin k × Fin n)}

def label (encoding : Encoding events) (rank : Fin encoding.size) : Fin encoding.count :=
  encoding.color (encoding.decode rank).1

theorem color_injective_on_events (encoding : Encoding events)
    {first last : Fin k × Fin n} (firstMem : first ∈ events) (lastMem : last ∈ events)
    (same : encoding.color first.1 = encoding.color last.1) : first.1 = last.1 := by
  have answer := (encoding.same_color (encoding.encode first) (encoding.encode last)).mp
    (by simpa only [encoding.decode_encode first firstMem,encoding.decode_encode last lastMem] using same)
  simpa only [encoding.decode_encode first firstMem,encoding.decode_encode last lastMem] using answer

end Encoding
end DynamicOptimality.ColoredWalks
