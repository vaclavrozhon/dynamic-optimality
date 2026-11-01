import TangoSquared.Paper20261030.IntervalReplacement

/-! The one-boundary cases of interval replacement. A repaired prefix
or suffix is reincorporated at the exposed existing boundary separator.
The physical proof charges opening, closing, the nested repair, and join. -/

namespace TangoSquared.Paper20261030.BoundaryObservations

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent

variable {α κ : Type*} {β : κ → Type*} [Ord κ] [LawfulEqOrd κ]

def replacePrefix (c : AuxiliaryComponent α κ (Tagged β)) (key : κ)
    (found : searchResult key c.core = true) (fresh : AuxiliaryComponent α κ (Tagged β)) :=
  join key (splitAt key c.core c.balanced found).value fresh (cutRight c key found)

def replaceSuffix (c : AuxiliaryComponent α κ (Tagged β)) (key : κ)
    (found : searchResult key c.core = true) (fresh : AuxiliaryComponent α κ (Tagged β)) :=
  join key (splitAt key c.core c.balanced found).value (cutLeft c key found) fresh

theorem replacePrefix_invariant (c : AuxiliaryComponent α κ (Tagged β))
    (hc : Clean c.core) (hp : MarkedPorts c) (key : κ)
    (found : searchResult key c.core = true)
    (fresh : AuxiliaryComponent α κ (Tagged β)) (hfc : Clean fresh.core) (hfp : MarkedPorts fresh) :
    Clean (replacePrefix c key found fresh).core ∧ MarkedPorts (replacePrefix c key found fresh) :=
  ⟨clean_join _ _ (clean_split c hc key found).1 _ _ hfc (clean_split c hc key found).2.2,
    marked_join _ _ _ _ hfp (marked_cutRight c hp key found)⟩

theorem replaceSuffix_invariant (c : AuxiliaryComponent α κ (Tagged β))
    (hc : Clean c.core) (hp : MarkedPorts c) (key : κ)
    (found : searchResult key c.core = true)
    (fresh : AuxiliaryComponent α κ (Tagged β)) (hfc : Clean fresh.core) (hfp : MarkedPorts fresh) :
    Clean (replaceSuffix c key found fresh).core ∧ MarkedPorts (replaceSuffix c key found fresh) :=
  ⟨clean_join _ _ (clean_split c hc key found).1 _ _ (clean_split c hc key found).2.1 hfc,
    marked_join _ _ _ _ (marked_cutLeft c hp key found) hfp⟩

theorem replacePrefix_charged (c : AuxiliaryComponent α κ (Tagged β))
    (hc : Clean c.core) (hp : MarkedPorts c) (key : κ)
    (found : searchResult key c.core = true)
    (fresh : AuxiliaryComponent α κ (Tagged β)) (hfc : Clean fresh.core) (hfp : MarkedPorts fresh)
    (cost : Nat) (repair : SourcePointer.Rearranges (closed (cutLeft c key found)) (closed fresh) cost)
    (K : Nat) (hold : c.core.size ≤ K) (hnew : (replacePrefix c key found fresh).core.size ≤ K) :
    SourcePointer.Rearranges (closed c) (closed (replacePrefix c key found fresh))
      (cost + 6720 * Nat.clog 2 (K + 1) + 90) := by
  let r := cutRight c key found
  let record : Record (β := β) := (c.core.size,⟨key,(splitAt key c.core c.balanced found).value⟩)
  have exposed := expose_charged c key found
  have mark := (close_charged (cutLeft c key found)).left (r := r.tree) (record := record)
  have repaired := repair.left (r := r.tree) (record := record)
  have reopened := (open_charged fresh hfc hfp).left (r := r.tree) (record := record)
  have joined := join_charged key (splitAt key c.core c.balanced found).value fresh r c.core.size
  have full := (((((open_charged c hc hp).trans exposed).trans mark).trans repaired).trans reopened).trans joined
  apply (full.trans (close_charged (replacePrefix c key found fresh))).mono
  have hs : (replacePrefix c key found fresh).core.size = fresh.core.size + 1 + r.core.size :=
    join_size _ _ _ _
  have hcl := Nat.clog_monotone 2 (Nat.add_le_add_right hold 1)
  have hfl := Nat.clog_monotone 2 (show fresh.core.size + 1 ≤ K + 1 by omega)
  have hrl := Nat.clog_monotone 2 (show r.core.size + 1 ≤ K + 1 by omega)
  omega

theorem replaceSuffix_charged (c : AuxiliaryComponent α κ (Tagged β))
    (hc : Clean c.core) (hp : MarkedPorts c) (key : κ)
    (found : searchResult key c.core = true)
    (fresh : AuxiliaryComponent α κ (Tagged β)) (hfc : Clean fresh.core) (hfp : MarkedPorts fresh)
    (cost : Nat) (repair : SourcePointer.Rearranges (closed (cutRight c key found)) (closed fresh) cost)
    (K : Nat) (hold : c.core.size ≤ K) (hnew : (replaceSuffix c key found fresh).core.size ≤ K) :
    SourcePointer.Rearranges (closed c) (closed (replaceSuffix c key found fresh))
      (cost + 6720 * Nat.clog 2 (K + 1) + 90) := by
  let l := cutLeft c key found
  let record : Record (β := β) := (c.core.size,⟨key,(splitAt key c.core c.balanced found).value⟩)
  have exposed := expose_charged c key found
  have mark := (close_charged (cutRight c key found)).right (l := l.tree) (record := record)
  have repaired := repair.right (l := l.tree) (record := record)
  have reopened := (open_charged fresh hfc hfp).right (l := l.tree) (record := record)
  have joined := join_charged key (splitAt key c.core c.balanced found).value l fresh c.core.size
  have full := (((((open_charged c hc hp).trans exposed).trans mark).trans repaired).trans reopened).trans joined
  apply (full.trans (close_charged (replaceSuffix c key found fresh))).mono
  have hs : (replaceSuffix c key found fresh).core.size = l.core.size + 1 + fresh.core.size :=
    join_size _ _ _ _
  have hcl := Nat.clog_monotone 2 (Nat.add_le_add_right hold 1)
  have hfl := Nat.clog_monotone 2 (show fresh.core.size + 1 ≤ K + 1 by omega)
  have hll := Nat.clog_monotone 2 (show l.core.size + 1 ≤ K + 1 by omega)
  omega

end TangoSquared.Paper20261030.BoundaryObservations
