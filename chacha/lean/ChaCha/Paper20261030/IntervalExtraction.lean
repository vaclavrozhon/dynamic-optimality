import ChaCha.Paper20261030.MarkedMeld
import ChaCha.Paper20261030.MarkedInsertion

/-!
# Extracting an interior interval as a marked port

Two existing boundary separators enclose the interval to detach. Expose
the lower separator, then expose the upper one in its right core. The
middle core is now reached and can be closed. One rotation and two
balanced joins reconstruct a balanced outside core whose intervening
port is exactly the detached middle component. No records are allocated
or discarded. The outer component and detached interval both retain
their physical entry invariants.
-/

namespace ChaCha.Paper20261030.BoundaryObservations

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent

variable {α κ : Type*} {β : κ → Type*} [Ord κ] [LawfulEqOrd κ]

def middle (c : AuxiliaryComponent α κ (Tagged β)) (lo : κ)
    (fl : searchResult lo c.core = true) (hi : κ)
    (fh : searchResult hi (cutRight c lo fl).core = true) : AuxiliaryComponent α κ (Tagged β) :=
  cutLeft (cutRight c lo fl) hi fh

def outside (c : AuxiliaryComponent α κ (Tagged β)) (lo : κ)
    (fl : searchResult lo c.core = true) (hi : κ)
    (fh : searchResult hi (cutRight c lo fl).core = true) : AuxiliaryComponent α κ (Tagged β) :=
  let right := cutRight c lo fl
  join hi (splitAt hi right.core right.balanced fh).value
    (append (cutLeft c lo fl) lo (splitAt lo c.core c.balanced fl).value (closed (middle c lo fl hi fh)))
    (cutRight right hi fh)

theorem middle_invariant (c : AuxiliaryComponent α κ (Tagged β))
    (hc : Clean c.core) (hp : MarkedPorts c) (lo : κ)
    (fl : searchResult lo c.core = true) (hi : κ)
    (fh : searchResult hi (cutRight c lo fl).core = true) :
    Clean (middle c lo fl hi fh).core ∧ MarkedPorts (middle c lo fl hi fh) :=
  ⟨(clean_split (cutRight c lo fl) (clean_split c hc lo fl).2.2 hi fh).2.1,
    marked_cutLeft _ (marked_cutRight c hp lo fl) hi fh⟩

theorem outside_invariant (c : AuxiliaryComponent α κ (Tagged β))
    (hc : Clean c.core) (hp : MarkedPorts c) (lo : κ)
    (fl : searchResult lo c.core = true) (hi : κ)
    (fh : searchResult hi (cutRight c lo fl).core = true) :
    Clean (outside c lo fl hi fh).core ∧ MarkedPorts (outside c lo fl hi fh) := by
  obtain ⟨hlo,hl,hr⟩ := clean_split c hc lo fl
  obtain ⟨hhi,hm,hh⟩ := clean_split (cutRight c lo fl) hr hi fh
  have lowClean := clean_append (cutLeft c lo fl) hl lo _ hlo (closed (middle c lo fl hi fh))
  have lowMarked := marked_append (cutLeft c lo fl) (marked_cutLeft c hp lo fl) lo
    (splitAt lo c.core c.balanced fl).value
    (closed (middle c lo fl hi fh)) (closed_entry _)
  exact ⟨clean_join _ _ hhi _ _ lowClean hh,
    marked_join _ _ _ _ lowMarked (marked_cutRight _ (marked_cutRight c hp lo fl) hi fh)⟩

theorem outside_middle_port (c : AuxiliaryComponent α κ (Tagged β)) (lo : κ)
    (fl : searchResult lo c.core = true) (hi : κ)
    (fh : searchResult hi (cutRight c lo fl).core = true) :
    (outside c lo fl hi fh).ports ((cutLeft c lo fl).core.size + 1) = closed (middle c lo fl hi fh) := by
  simp only [outside,join,append_size,Nat.le_refl,if_true]
  simp only [append,
    show ¬ (cutLeft c lo fl).core.size + 1 ≤ (cutLeft c lo fl).core.size by omega,if_false]

theorem outside_word (c : AuxiliaryComponent α κ (Tagged β)) (lo : κ)
    (fl : searchResult lo c.core = true) (hi : κ)
    (fh : searchResult hi (cutRight c lo fl).core = true) :
    (outside c lo fl hi fh).core.toListModel =
      (cutLeft c lo fl).core.toListModel ++
        [⟨lo,(splitAt lo c.core c.balanced fl).value⟩,
         ⟨hi,(splitAt hi (cutRight c lo fl).core (cutRight c lo fl).balanced fh).value⟩] ++
        (cutRight (cutRight c lo fl) hi fh).core.toListModel := by
  simp only [outside,join_word,append_word,List.append_assoc,List.cons_append,List.nil_append]

theorem extraction_word (c : AuxiliaryComponent α κ (Tagged β)) (lo : κ)
    (fl : searchResult lo c.core = true) (hi : κ)
    (fh : searchResult hi (cutRight c lo fl).core = true) :
    c.core.toListModel = (cutLeft c lo fl).core.toListModel ++
      ⟨lo,(splitAt lo c.core c.balanced fl).value⟩ ::
        ((middle c lo fl hi fh).core.toListModel ++
          ⟨hi,(splitAt hi (cutRight c lo fl).core (cutRight c lo fl).balanced fh).value⟩ ::
            (cutRight (cutRight c lo fl) hi fh).core.toListModel) := by
  have first := splitAt_toList lo c.core c.balanced fl
  have second := splitAt_toList hi (cutRight c lo fl).core (cutRight c lo fl).balanced fh
  change _ = _ at first second
  rw [← first]
  change _ ++ _ :: (cutRight c lo fl).core.toListModel = _
  rw [← second]
  rfl

theorem extract_charged (c : AuxiliaryComponent α κ (Tagged β))
    (hc : Clean c.core) (hp : MarkedPorts c) (lo : κ)
    (fl : searchResult lo c.core = true) (hi : κ)
    (fh : searchResult hi (cutRight c lo fl).core = true) :
    SourcePointer.Rearranges (closed c) (closed (outside c lo fl hi fh))
      (12945 * Nat.clog 2 (c.core.size + 1) + 167) := by
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
  have rotate : SourcePointer.Rearranges
      (.fork lowRecord l.tree (.fork highRecord (closed m) h.tree))
      (.fork highRecord (.fork lowRecord l.tree (closed m)) h.tree) 1 :=
    fun rest => ⟨[],1,.step (.rotateLeft _ _ _ _ _ _) (.nil _),le_rfl⟩
  let low := append l lo (splitAt lo c.core c.balanced fl).value (closed m)
  have insertLow := (append_charged l lo (splitAt lo c.core c.balanced fl).value
    (closed m) c.core.size).left (r := h.tree) (record := highRecord)
  have joined := join_charged hi (splitAt hi r.core r.balanced fh).value low h r.core.size
  have full := ((((((open_charged c hc hp).trans first).trans second).trans markMiddle).trans
    rotate).trans insertLow).trans joined
  have finished := full.trans (close_charged (outside c lo fl hi fh))
  apply finished.mono
  have hs₁ : l.core.size + 1 + r.core.size = c.core.size := splitAt_size lo c.core c.balanced fl
  have hs₂ : m.core.size + 1 + h.core.size = r.core.size := splitAt_size hi r.core r.balanced fh
  have hl := Nat.clog_monotone 2 (show l.core.size + 1 ≤ c.core.size + 1 by omega)
  have hr := Nat.clog_monotone 2 (show r.core.size + 1 ≤ c.core.size + 1 by omega)
  have hh := Nat.clog_monotone 2 (show h.core.size + 1 ≤ c.core.size + 1 by omega)
  have hlow : low.core.size = l.core.size + 1 := append_size _ _ _ _
  have hlo := Nat.clog_monotone 2 (show low.core.size + 1 ≤ c.core.size + 1 by omega)
  omega

end ChaCha.Paper20261030.BoundaryObservations
