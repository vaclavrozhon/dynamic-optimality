import TangoSquared.Paper20261030.ComponentMeld
import TangoSquared.Paper20261030.MarkedCut
import TangoSquared.Paper20261030.MarkedJoin

/-! Melding an actual marked extreme port into its parent component.
Only the two component-entry markers are opened. The resulting balanced
core is clean, its remaining ports stay marked, and its new root is
closed. Every marker update is charged at the reached record. -/

namespace TangoSquared.Paper20261030.BoundaryObservations

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent

variable {α κ : Type*} {β : κ → Type*} [Ord κ] [LawfulEqOrd κ]

theorem clean_meldLast (outer incoming : AuxiliaryComponent α κ (Tagged β))
    (ho : Clean outer.core) (hi : Clean incoming.core) (key : κ)
    (found : searchResult key outer.core = true) :
    Clean (meldLast outer incoming key found).core := by
  obtain ⟨hv,hl,_⟩ := clean_split outer ho key found
  exact clean_join _ _ hv _ _ hl hi

theorem clean_meldFirst (incoming outer : AuxiliaryComponent α κ (Tagged β))
    (hi : Clean incoming.core) (ho : Clean outer.core) (key : κ)
    (found : searchResult key outer.core = true) :
    Clean (meldFirst incoming outer key found).core := by
  obtain ⟨hv,_,hr⟩ := clean_split outer ho key found
  exact clean_join _ _ hv _ _ hi hr

theorem marked_meldLast (outer incoming : AuxiliaryComponent α κ (Tagged β))
    (ho : MarkedPorts outer) (hi : MarkedPorts incoming) (key : κ)
    (found : searchResult key outer.core = true) :
    MarkedPorts (meldLast outer incoming key found) :=
  marked_join _ _ _ _ (marked_cutLeft outer ho key found) hi

theorem marked_meldFirst (incoming outer : AuxiliaryComponent α κ (Tagged β))
    (hi : MarkedPorts incoming) (ho : MarkedPorts outer) (key : κ)
    (found : searchResult key outer.core = true) :
    MarkedPorts (meldFirst incoming outer key found) :=
  marked_join _ _ _ _ hi (marked_cutRight outer ho key found)

theorem meldLastMarked_charged (outer incoming : AuxiliaryComponent α κ (Tagged β))
    (ho : Clean outer.core) (hi : Clean incoming.core)
    (hpo : MarkedPorts outer) (hpi : MarkedPorts incoming) (key : κ)
    (found : searchResult key outer.core = true)
    (empty : (splitAt key outer.core outer.balanced found).right = .leaf)
    (attached : outer.ports outer.core.size = closed incoming) :
    SourcePointer.Rearranges (closed outer) (closed (meldLast outer incoming key found))
      (6225 * Nat.clog 2 (outer.core.size + 1) +
        495 * Nat.clog 2 (incoming.core.size + 1) + 84) := by
  have exposed := expose_charged outer key found
  rw [cutRight_empty_tree outer key found empty,attached] at exposed
  have opened := (open_charged incoming hi hpi).right
    (l := (cutLeft outer key found).tree)
    (record := (outer.core.size,⟨key,(splitAt key outer.core outer.balanced found).value⟩))
  have joined := join_charged key (splitAt key outer.core outer.balanced found).value
    (cutLeft outer key found) incoming outer.core.size
  have full := ((((open_charged outer ho hpo).trans exposed).trans opened).trans joined).trans
    (close_charged (meldLast outer incoming key found))
  apply full.mono
  have hs := splitAt_size key outer.core outer.balanced found
  have hm := Nat.clog_monotone 2
    (show (cutLeft outer key found).core.size + 1 ≤ outer.core.size + 1 by
      change (splitAt key outer.core outer.balanced found).left.size + 1 ≤ _
      omega)
  omega

theorem meldFirstMarked_charged (incoming outer : AuxiliaryComponent α κ (Tagged β))
    (hi : Clean incoming.core) (ho : Clean outer.core)
    (hpi : MarkedPorts incoming) (hpo : MarkedPorts outer) (key : κ)
    (found : searchResult key outer.core = true)
    (empty : (splitAt key outer.core outer.balanced found).left = .leaf)
    (attached : outer.ports 0 = closed incoming) :
    SourcePointer.Rearranges (closed outer) (closed (meldFirst incoming outer key found))
      (6225 * Nat.clog 2 (outer.core.size + 1) +
        495 * Nat.clog 2 (incoming.core.size + 1) + 84) := by
  have exposed := expose_charged outer key found
  rw [cutLeft_empty_tree outer key found empty,attached] at exposed
  have opened := (open_charged incoming hi hpi).left
    (r := (cutRight outer key found).tree)
    (record := (outer.core.size,⟨key,(splitAt key outer.core outer.balanced found).value⟩))
  have joined := join_charged key (splitAt key outer.core outer.balanced found).value
    incoming (cutRight outer key found) outer.core.size
  have full := ((((open_charged outer ho hpo).trans exposed).trans opened).trans joined).trans
    (close_charged (meldFirst incoming outer key found))
  apply full.mono
  have hs := splitAt_size key outer.core outer.balanced found
  have hm := Nat.clog_monotone 2
    (show (cutRight outer key found).core.size + 1 ≤ outer.core.size + 1 by
      change (splitAt key outer.core outer.balanced found).right.size + 1 ≤ _
      omega)
  omega

end TangoSquared.Paper20261030.BoundaryObservations
