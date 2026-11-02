import ChaCha.Paper20261030.MarkedMeld
import ChaCha.Paper20261030.MarkedInsertion

/-!
# Changing the preferred child at a component's reference head

The head record is the maximum separator when its old preferred child
is left, and the minimum when its old preferred child is right. Expose
that existing record, close the detached old continuation, update the
head payload, and insert the head into the incoming path. Its old
continuation becomes an actual marked port of the new component.

The operation starts and ends at the component root and uses one cursor.
An interior departure first needs the separate interval-extraction step;
this theorem does not assume that step is free.
-/

namespace ChaCha.Paper20261030.BoundaryObservations

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent

variable {α κ : Type*} {β : κ → Type*} [Ord κ] [LawfulEqOrd κ]

def preferRight (outer incoming : AuxiliaryComponent α κ (Tagged β)) (key : κ)
    (found : searchResult key outer.core = true) (fresh : Tagged β key) :
    AuxiliaryComponent α κ (Tagged β) :=
  prepend key fresh (closed (cutLeft outer key found)) incoming

def preferLeft (incoming outer : AuxiliaryComponent α κ (Tagged β)) (key : κ)
    (found : searchResult key outer.core = true) (fresh : Tagged β key) :
    AuxiliaryComponent α κ (Tagged β) :=
  append incoming key fresh (closed (cutRight outer key found))

theorem preferRight_invariant (outer incoming : AuxiliaryComponent α κ (Tagged β))
    (hi : Clean incoming.core) (hpi : MarkedPorts incoming) (key : κ)
    (found : searchResult key outer.core = true) (fresh : Tagged β key) (hf : fresh.2 = false) :
    Clean (preferRight outer incoming key found fresh).core ∧
      MarkedPorts (preferRight outer incoming key found fresh) :=
  ⟨clean_prepend _ _ hf _ _ hi,marked_prepend _ _ _ (closed_entry _) _ hpi⟩

theorem preferLeft_invariant (incoming outer : AuxiliaryComponent α κ (Tagged β))
    (hi : Clean incoming.core) (hpi : MarkedPorts incoming) (key : κ)
    (found : searchResult key outer.core = true) (fresh : Tagged β key) (hf : fresh.2 = false) :
    Clean (preferLeft incoming outer key found fresh).core ∧
      MarkedPorts (preferLeft incoming outer key found fresh) :=
  ⟨clean_append _ hi _ _ hf _,marked_append _ hpi _ _ _ (closed_entry _)⟩

theorem preferRight_word (outer incoming : AuxiliaryComponent α κ (Tagged β)) (key : κ)
    (found : searchResult key outer.core = true) (fresh : Tagged β key) :
    (preferRight outer incoming key found fresh).core.toListModel =
      ⟨key,fresh⟩ :: incoming.core.toListModel := prepend_word _ _ _ _

theorem preferLeft_word (incoming outer : AuxiliaryComponent α κ (Tagged β)) (key : κ)
    (found : searchResult key outer.core = true) (fresh : Tagged β key) :
    (preferLeft incoming outer key found fresh).core.toListModel =
      incoming.core.toListModel ++ [⟨key,fresh⟩] := append_word _ _ _ _

theorem preferRight_charged (outer incoming : AuxiliaryComponent α κ (Tagged β))
    (ho : Clean outer.core) (hi : Clean incoming.core)
    (hpo : MarkedPorts outer) (hpi : MarkedPorts incoming) (key : κ)
    (found : searchResult key outer.core = true)
    (empty : (splitAt key outer.core outer.balanced found).right = .leaf)
    (attached : outer.ports outer.core.size = closed incoming) (fresh : Tagged β key) :
    SourcePointer.Rearranges (closed outer) (closed (preferRight outer incoming key found fresh))
      (5730 * Nat.clog 2 (outer.core.size + 1) +
        495 * Nat.clog 2 (incoming.core.size + 1) + 90) := by
  have exposed := expose_charged outer key found
  rw [cutRight_empty_tree outer key found empty,attached] at exposed
  have detached := (close_charged (cutLeft outer key found)).left
    (r := closed incoming)
    (record := (outer.core.size,⟨key,(splitAt key outer.core outer.balanced found).value⟩))
  have updated := SourcePointer.replace_root
    (.fork (outer.core.size,⟨key,(splitAt key outer.core outer.balanced found).value⟩)
      (closed (cutLeft outer key found)) (closed incoming)) (outer.core.size,⟨key,fresh⟩)
  have joined := prependMarked_charged key fresh (closed (cutLeft outer key found))
    incoming hi hpi outer.core.size
  have full := ((((open_charged outer ho hpo).trans exposed).trans detached).trans updated).trans joined
  apply full.mono
  omega

theorem preferLeft_charged (incoming outer : AuxiliaryComponent α κ (Tagged β))
    (hi : Clean incoming.core) (ho : Clean outer.core)
    (hpi : MarkedPorts incoming) (hpo : MarkedPorts outer) (key : κ)
    (found : searchResult key outer.core = true)
    (empty : (splitAt key outer.core outer.balanced found).left = .leaf)
    (attached : outer.ports 0 = closed incoming) (fresh : Tagged β key) :
    SourcePointer.Rearranges (closed outer) (closed (preferLeft incoming outer key found fresh))
      (5730 * Nat.clog 2 (outer.core.size + 1) +
        495 * Nat.clog 2 (incoming.core.size + 1) + 90) := by
  have exposed := expose_charged outer key found
  rw [cutLeft_empty_tree outer key found empty,attached] at exposed
  have detached := (close_charged (cutRight outer key found)).right
    (l := closed incoming)
    (record := (outer.core.size,⟨key,(splitAt key outer.core outer.balanced found).value⟩))
  have updated := SourcePointer.replace_root
    (.fork (outer.core.size,⟨key,(splitAt key outer.core outer.balanced found).value⟩)
      (closed incoming) (closed (cutRight outer key found))) (outer.core.size,⟨key,fresh⟩)
  have joined := appendMarked_charged incoming hi hpi key fresh
    (closed (cutRight outer key found)) outer.core.size
  have full := ((((open_charged outer ho hpo).trans exposed).trans detached).trans updated).trans joined
  apply full.mono
  omega

end ChaCha.Paper20261030.BoundaryObservations
