import TangoSquared.Paper20261030.ComponentMarkers

/-! Inserting an extreme separator preserves marked hanging ports, opens
only the preferred component, and marks the resulting auxiliary root. -/

namespace TangoSquared.Paper20261030.BoundaryObservations

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent

variable {α κ : Type*} {β : κ → Type*} [Ord κ]

theorem clean_prepend (key : κ) (value : Tagged β key) (hv : value.2 = false)
    (sibling : Source α (Record (β := β))) (c : AuxiliaryComponent α κ (Tagged β)) (hc : Clean c.core) :
    Clean (prepend key value sibling c).core := by
  rw [clean_iff_word,prepend_word]
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact hv
  · exact (clean_iff_word _).mp hc e he

theorem clean_append (c : AuxiliaryComponent α κ (Tagged β)) (hc : Clean c.core)
    (key : κ) (value : Tagged β key) (hv : value.2 = false) (sibling : Source α (Record (β := β))) :
    Clean (append c key value sibling).core := by
  rw [clean_iff_word,append_word]
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact (clean_iff_word _).mp hc e he
  · have heq := List.mem_singleton.mp he
    cases heq
    exact hv

theorem marked_prepend (key : κ) (value : Tagged β key)
    (sibling : Source α (Record (β := β))) (hs : entry sibling.rootRecord = true)
    (c : AuxiliaryComponent α κ (Tagged β)) (hc : MarkedPorts c) : MarkedPorts (prepend key value sibling c) := by
  intro i hi
  rw [prepend_size] at hi
  by_cases he : i = 0
  · simpa only [prepend,if_pos he] using hs
  · simpa only [prepend,if_neg he] using hc (i - 1) (by omega)

theorem marked_append (c : AuxiliaryComponent α κ (Tagged β)) (hc : MarkedPorts c)
    (key : κ) (value : Tagged β key) (sibling : Source α (Record (β := β)))
    (hs : entry sibling.rootRecord = true) : MarkedPorts (append c key value sibling) := by
  intro i hi
  by_cases he : i ≤ c.core.size
  · simpa only [append,if_pos he] using hc i he
  · simpa only [append,if_neg he] using hs

theorem prependMarked_charged (key : κ) (value : Tagged β key)
    (sibling : Source α (Record (β := β))) (c : AuxiliaryComponent α κ (Tagged β))
    (hc : Clean c.core) (hp : MarkedPorts c) (old : Nat) :
    SourcePointer.Rearranges (.fork (old,⟨key,value⟩) sibling (closed c))
      (closed (prepend key value sibling c)) (495 * Nat.clog 2 (c.core.size + 1) + 82) := by
  have opened := (open_charged c hc hp).right (l := sibling) (record := (old,⟨key,value⟩))
  have inserted := prepend_charged key value sibling c old
  have finished := close_charged (prepend key value sibling c)
  apply ((opened.trans inserted).trans finished).mono
  omega

theorem appendMarked_charged (c : AuxiliaryComponent α κ (Tagged β)) (hc : Clean c.core)
    (hp : MarkedPorts c) (key : κ) (value : Tagged β key) (sibling : Source α (Record (β := β))) (old : Nat) :
    SourcePointer.Rearranges (.fork (old,⟨key,value⟩) (closed c) sibling)
      (closed (append c key value sibling)) (495 * Nat.clog 2 (c.core.size + 1) + 82) := by
  have opened := (open_charged c hc hp).left (r := sibling) (record := (old,⟨key,value⟩))
  have inserted := append_charged c key value sibling old
  have finished := close_charged (append c key value sibling)
  apply ((opened.trans inserted).trans finished).mono
  omega

end TangoSquared.Paper20261030.BoundaryObservations
