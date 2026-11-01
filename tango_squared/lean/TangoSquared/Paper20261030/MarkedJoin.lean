import TangoSquared.Paper20261030.ComponentMarkers
import TangoSquared.Paper20261030.ComponentJoin

/-! A physical join opens its reached child components, joins their clean
cores at the existing unmarked separator, then marks the resulting root.
All hanging port roots remain marked throughout. -/

namespace TangoSquared.Paper20261030.BoundaryObservations

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent

variable {α κ : Type*} {β : κ → Type*} [Ord κ]

theorem clean_join (key : κ) (value : Tagged β key) (hv : value.2 = false)
    (l r : AuxiliaryComponent α κ (Tagged β)) (hl : Clean l.core) (hr : Clean r.core) :
    Clean (join key value l r).core := by
  rw [clean_iff_word,join_word]
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact (clean_iff_word _).mp hl e he
  · rcases List.mem_cons.mp he with rfl | he
    · exact hv
    · exact (clean_iff_word _).mp hr e he

theorem marked_join (key : κ) (value : Tagged β key) (l r : AuxiliaryComponent α κ (Tagged β))
    (hl : MarkedPorts l) (hr : MarkedPorts r) : MarkedPorts (join key value l r) := by
  intro i hi
  rw [join_size] at hi
  by_cases hs : i ≤ l.core.size
  · simpa only [join,if_pos hs] using hl i hs
  · have hb : i - (l.core.size + 1) ≤ r.core.size := by omega
    simpa only [join,if_neg hs] using hr (i - (l.core.size + 1)) hb

theorem joinMarked_charged (key : κ) (value : Tagged β key)
    (l r : AuxiliaryComponent α κ (Tagged β)) (hl : Clean l.core) (hr : Clean r.core)
    (hpl : MarkedPorts l) (hpr : MarkedPorts r) (old : Nat) :
    SourcePointer.Rearranges (.fork (old,⟨key,value⟩) (closed l) (closed r))
      (closed (join key value l r))
      (495 * (Nat.clog 2 (l.core.size + 1) + Nat.clog 2 (r.core.size + 1)) + 86) := by
  have openedLeft := (open_charged l hl hpl).left (r := closed r) (record := (old,⟨key,value⟩))
  have openedRight := (open_charged r hr hpr).right (l := l.tree) (record := (old,⟨key,value⟩))
  have joined := join_charged key value l r old
  have finished := close_charged (join key value l r)
  have full := ((openedLeft.trans openedRight).trans joined).trans finished
  apply full.mono
  omega

end TangoSquared.Paper20261030.BoundaryObservations
