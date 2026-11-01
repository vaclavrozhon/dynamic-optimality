import TangoSquared.Paper20261030.MarkedCut

/-! Expose the existing separator with both exact split fragments closed. -/

namespace TangoSquared.Paper20261030.BoundaryObservations

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent

variable {α κ : Type*} {β : κ → Type*} [Ord κ] [LawfulEqOrd κ]

theorem expose_closed_fragments (c : AuxiliaryComponent α κ (Tagged β))
    (clean : Clean c.core) (marked : MarkedPorts c) (key : κ)
    (found : searchResult key c.core = true) :
    SourcePointer.Rearranges (closed c)
      (.fork (c.core.size,⟨key,(splitAt key c.core c.balanced found).value⟩)
        (closed (cutLeft c key found)) (closed (cutRight c key found)))
      (5730 * Nat.clog 2 (c.core.size+1) + 10) := by
  have opened := open_charged c clean marked
  have split := expose_charged c key found
  have left := (close_charged (cutLeft c key found)).left
    (r := (cutRight c key found).tree)
    (record := (c.core.size,⟨key,(splitAt key c.core c.balanced found).value⟩))
  have right := (close_charged (cutRight c key found)).right
    (l := closed (cutLeft c key found))
    (record := (c.core.size,⟨key,(splitAt key c.core c.balanced found).value⟩))
  exact (((opened.trans split).trans left).trans right).mono (by omega)

end TangoSquared.Paper20261030.BoundaryObservations
