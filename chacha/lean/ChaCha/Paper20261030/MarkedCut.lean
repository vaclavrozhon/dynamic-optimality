import ChaCha.Paper20261030.ComponentMarkers
import ChaCha.Paper20261030.ComponentCut

/-!
# A cut that maintains physical component-entry markers

Open the original component, expose the cut separator, mark the new
suffix while its root is the reached right child, rebalance the prefix,
and mark its new root. The resulting two cores are clean and every port
entry remains marked. The operation adds eight charged operations to
the unmarked cut bound.
-/

namespace ChaCha.Paper20261030.BoundaryObservations

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent

variable {α κ : Type*} {β : κ → Type*} [Ord κ] [LawfulEqOrd κ]

theorem clean_split (c : AuxiliaryComponent α κ (Tagged β)) (hc : Clean c.core)
    (key : κ) (found : searchResult key c.core = true) :
    (splitAt key c.core c.balanced found).value.2 = false ∧
      Clean (cutLeft c key found).core ∧ Clean (cutRight c key found).core := by
  have h := clean_of_word hc (splitAt_toList key c.core c.balanced found)
  exact h

theorem marked_cutLeft (c : AuxiliaryComponent α κ (Tagged β)) (hp : MarkedPorts c)
    (key : κ) (found : searchResult key c.core = true) : MarkedPorts (cutLeft c key found) := by
  intro i hi
  have hs := splitAt_size key c.core c.balanced found
  apply hp i
  change i ≤ (splitAt key c.core c.balanced found).left.size at hi
  omega

theorem marked_cutRight (c : AuxiliaryComponent α κ (Tagged β)) (hp : MarkedPorts c)
    (key : κ) (found : searchResult key c.core = true) : MarkedPorts (cutRight c key found) := by
  intro i hi
  have hs := splitAt_size key c.core c.balanced found
  apply hp
  change i ≤ (splitAt key c.core c.balanced found).right.size at hi
  omega

def cutMarked (c : AuxiliaryComponent α κ (Tagged β)) (key : κ) (found : searchResult key c.core = true) :
    AuxiliaryComponent α κ (Tagged β) :=
  (cutLeft c key found).append key (splitAt key c.core c.balanced found).value (closed (cutRight c key found))

theorem clean_cutMarked (c : AuxiliaryComponent α κ (Tagged β)) (hc : Clean c.core)
    (key : κ) (found : searchResult key c.core = true) : Clean (cutMarked c key found).core := by
  obtain ⟨hp,hl,hr⟩ := clean_split c hc key found
  rw [clean_iff_word]
  simp only [cutMarked,append_word,List.mem_append,List.mem_singleton]
  intro e he
  rcases he with he | he
  · exact (clean_iff_word _).mp hl e he
  · cases he; exact hp

theorem marked_cutMarked (c : AuxiliaryComponent α κ (Tagged β)) (hp : MarkedPorts c)
    (key : κ) (found : searchResult key c.core = true) : MarkedPorts (cutMarked c key found) := by
  intro i hi
  by_cases hleft : i ≤ (cutLeft c key found).core.size
  · simpa only [cutMarked,append,if_pos hleft] using marked_cutLeft c hp key found i hleft
  · simpa only [cutMarked,append,if_neg hleft] using closed_entry (cutRight c key found)

theorem cutMarked_charged (c : AuxiliaryComponent α κ (Tagged β)) (hc : Clean c.core)
    (hp : MarkedPorts c) (key : κ) (found : searchResult key c.core = true) :
    SourcePointer.Rearranges (closed c) (closed (cutMarked c key found))
      (6225 * Nat.clog 2 (c.core.size + 1) + 84) := by
  have opened := open_charged c hc hp
  have exposed := expose_charged c key found
  have suffixClosed := (close_charged (cutRight c key found)).right
    (l := (cutLeft c key found).tree) (record := (c.core.size,⟨key,(splitAt key c.core c.balanced found).value⟩))
  have joined := append_charged (cutLeft c key found) key
    (splitAt key c.core c.balanced found).value (closed (cutRight c key found)) c.core.size
  have finished := close_charged (cutMarked c key found)
  have full := (((opened.trans exposed).trans suffixClosed).trans joined).trans finished
  apply full.mono
  have hs := splitAt_size key c.core c.balanced found
  have hm := Nat.clog_monotone 2
    (show (cutLeft c key found).core.size + 1 ≤ c.core.size + 1 by
      change (splitAt key c.core c.balanced found).left.size + 1 ≤ _
      omega)
  omega

end ChaCha.Paper20261030.BoundaryObservations
