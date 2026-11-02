import ChaCha.Paper20261030.IntervalExtraction

/-!
# Applying a charged repair to an interior path interval

Expose its two boundary records, close the intervening component, and
run the supplied actual root-to-root repair there. Reopen the resulting
component and incorporate it by two balanced joins. The outside records
and their ports are retained. This lifts a repair of a path suffix to
the whole auxiliary without a traversal of the suffix or of its hanging
subtrees. The argument `repair` is a concrete source trace, not a bound
assumed for the completed access algorithm.
-/

namespace ChaCha.Paper20261030.BoundaryObservations

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent

variable {α κ : Type*} {β : κ → Type*} [Ord κ] [LawfulEqOrd κ]

def replaceMiddle (c : AuxiliaryComponent α κ (Tagged β)) (lo : κ)
    (fl : searchResult lo c.core = true) (hi : κ)
    (fh : searchResult hi (cutRight c lo fl).core = true)
    (fresh : AuxiliaryComponent α κ (Tagged β)) : AuxiliaryComponent α κ (Tagged β) :=
  let r := cutRight c lo fl
  join lo (splitAt lo c.core c.balanced fl).value (cutLeft c lo fl)
    (join hi (splitAt hi r.core r.balanced fh).value fresh (cutRight r hi fh))

theorem replaceMiddle_word (c : AuxiliaryComponent α κ (Tagged β)) (lo : κ)
    (fl : searchResult lo c.core = true) (hi : κ)
    (fh : searchResult hi (cutRight c lo fl).core = true)
    (fresh : AuxiliaryComponent α κ (Tagged β)) :
    (replaceMiddle c lo fl hi fh fresh).core.toListModel = (cutLeft c lo fl).core.toListModel ++
      ⟨lo,(splitAt lo c.core c.balanced fl).value⟩ ::
        (fresh.core.toListModel ++
          ⟨hi,(splitAt hi (cutRight c lo fl).core (cutRight c lo fl).balanced fh).value⟩ ::
            (cutRight (cutRight c lo fl) hi fh).core.toListModel) := by
  simp only [replaceMiddle,join_word]

theorem replaceMiddle_size (c : AuxiliaryComponent α κ (Tagged β)) (lo : κ)
    (fl : searchResult lo c.core = true) (hi : κ)
    (fh : searchResult hi (cutRight c lo fl).core = true)
    (fresh : AuxiliaryComponent α κ (Tagged β)) :
    (replaceMiddle c lo fl hi fh fresh).core.size =
      (cutLeft c lo fl).core.size + 1 +
        (fresh.core.size + 1 + (cutRight (cutRight c lo fl) hi fh).core.size) := by
  simp only [replaceMiddle,join_size]

theorem replaceMiddle_invariant (c : AuxiliaryComponent α κ (Tagged β))
    (hc : Clean c.core) (hp : MarkedPorts c) (lo : κ)
    (fl : searchResult lo c.core = true) (hi : κ)
    (fh : searchResult hi (cutRight c lo fl).core = true)
    (fresh : AuxiliaryComponent α κ (Tagged β)) (hfc : Clean fresh.core) (hfp : MarkedPorts fresh) :
    Clean (replaceMiddle c lo fl hi fh fresh).core ∧ MarkedPorts (replaceMiddle c lo fl hi fh fresh) := by
  obtain ⟨hlo,hl,hr⟩ := clean_split c hc lo fl
  obtain ⟨hhi,hm,hh⟩ := clean_split (cutRight c lo fl) hr hi fh
  exact ⟨clean_join _ _ hlo _ _ hl (clean_join _ _ hhi _ _ hfc hh),
    marked_join _ _ _ _ (marked_cutLeft c hp lo fl)
      (marked_join _ _ _ _ hfp (marked_cutRight _ (marked_cutRight c hp lo fl) hi fh))⟩

theorem replaceMiddle_charged (c : AuxiliaryComponent α κ (Tagged β))
    (hc : Clean c.core) (hp : MarkedPorts c) (lo : κ)
    (fl : searchResult lo c.core = true) (hi : κ)
    (fh : searchResult hi (cutRight c lo fl).core = true)
    (fresh : AuxiliaryComponent α κ (Tagged β)) (hfc : Clean fresh.core) (hfp : MarkedPorts fresh)
    (cost : Nat) (repair : SourcePointer.Rearranges (closed (middle c lo fl hi fh)) (closed fresh) cost)
    (K : Nat) (hold : c.core.size ≤ K) (hnew : (replaceMiddle c lo fl hi fh fresh).core.size ≤ K) :
    SourcePointer.Rearranges (closed c) (closed (replaceMiddle c lo fl hi fh fresh))
      (cost + 13440 * Nat.clog 2 (K + 1) + 176) := by
  let l := cutLeft c lo fl
  let r := cutRight c lo fl
  let m := middle c lo fl hi fh
  let h := cutRight r hi fh
  let lowRecord : Record (β := β) := (c.core.size,⟨lo,(splitAt lo c.core c.balanced fl).value⟩)
  let highRecord : Record (β := β) := (r.core.size,⟨hi,(splitAt hi r.core r.balanced fh).value⟩)
  have first := expose_charged c lo fl
  have second := (expose_charged r hi fh).right (l := l.tree) (record := lowRecord)
  have markMiddle := ((close_charged m).left (r := h.tree) (record := highRecord)).right
    (l := l.tree) (record := lowRecord)
  have repaired := (repair.left (r := h.tree) (record := highRecord)).right
    (l := l.tree) (record := lowRecord)
  have reopened := ((open_charged fresh hfc hfp).left (r := h.tree) (record := highRecord)).right
    (l := l.tree) (record := lowRecord)
  let joinedHigh := join hi (splitAt hi r.core r.balanced fh).value fresh h
  have higher := (join_charged hi (splitAt hi r.core r.balanced fh).value fresh h r.core.size).right
    (l := l.tree) (record := lowRecord)
  have lower := join_charged lo (splitAt lo c.core c.balanced fl).value l joinedHigh c.core.size
  have full := (((((((open_charged c hc hp).trans first).trans second).trans markMiddle).trans
    repaired).trans reopened).trans higher).trans lower
  have finished := full.trans (close_charged (replaceMiddle c lo fl hi fh fresh))
  apply finished.mono
  have hs₁ : l.core.size + 1 + r.core.size = c.core.size := splitAt_size lo c.core c.balanced fl
  have hs₂ : m.core.size + 1 + h.core.size = r.core.size := splitAt_size hi r.core r.balanced fh
  have hs₃ : joinedHigh.core.size = fresh.core.size + 1 + h.core.size := join_size _ _ _ _
  have hs₄ : (replaceMiddle c lo fl hi fh fresh).core.size = l.core.size + 1 + joinedHigh.core.size :=
    join_size _ _ _ _
  have hcLog := Nat.clog_monotone 2 (Nat.add_le_add_right hold 1)
  have hl := Nat.clog_monotone 2 (show l.core.size + 1 ≤ K + 1 by omega)
  have hr := Nat.clog_monotone 2 (show r.core.size + 1 ≤ K + 1 by omega)
  have hh := Nat.clog_monotone 2 (show h.core.size + 1 ≤ K + 1 by omega)
  have hf := Nat.clog_monotone 2 (show fresh.core.size + 1 ≤ K + 1 by omega)
  have hj := Nat.clog_monotone 2 (show joinedHigh.core.size + 1 ≤ K + 1 by omega)
  omega

end ChaCha.Paper20261030.BoundaryObservations
