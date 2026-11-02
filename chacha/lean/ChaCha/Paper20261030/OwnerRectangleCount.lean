import ChaCha.Paper20261030.CanonicalPrimary
import ChaCha.Paper20261030.DirectionScan

/-!
# Agreement of an owner's LCA count with the rectangle decomposition

The bit-array algorithm counts directions in local primary depths, whereas
the lower bound contracts original keys to dyadic block indices. The
following identities identify both complete direction words and counts.
-/

namespace ChaCha.Paper20261030.Dyadic

open Rectangles Secondary

theorem canonical_direction_word {H h c b : Nat} (hh : h ≤ H)
    (hc : H - h ≤ c) (hcb : c ≤ b) (hb : b < H) (owner x y : Int)
    (hx : ValidKey H x) (hy : ValidKey H y)
    (hxm : x ∈ (canonical h owner).leaves) (hym : y ∈ (canonical h owner).leaves) :
    (if (canonical h owner).referenceLCA x y ≤ b - (H - h) then
      [decide (c - (H - h) < (canonical h owner).referenceLCA x y)] else []) =
    (if coarsen H (b + 1) x = coarsen H (b + 1) y then [] else
      [decide (coarsen (b + 1) (c + 1) (coarsen H (b + 1) x) =
        coarsen (b + 1) (c + 1) (coarsen H (b + 1) y))]) := by
  have hL := canonical_lca_offset hh owner x y hx hy hxm hym
  have htop := ancestor_eq_iff_le_lca hx hy (by omega : b + 1 ≤ H)
  have hcut := ancestor_eq_iff_le_lca hx hy (by omega : c + 1 ≤ H)
  rw [coarsen_comp (by omega : c + 1 ≤ b + 1) (by omega : b + 1 ≤ H),
    coarsen_comp (by omega : c + 1 ≤ b + 1) (by omega : b + 1 ≤ H)]
  have hfirst : (canonical h owner).referenceLCA x y ≤ b - (H - h) ↔
      ¬ b + 1 ≤ lcaDepth H x y := by omega
  have hletter : c - (H - h) < (canonical h owner).referenceLCA x y ↔
      c + 1 ≤ lcaDepth H x y := by omega
  simp only [htop,hcut,hfirst,hletter]
  by_cases hd : b + 1 ≤ lcaDepth H x y <;> simp [hd]

theorem canonical_directionLetters {H h c b : Nat} (hh : h ≤ H)
    (hc : H - h ≤ c) (hcb : c ≤ b) (hb : b < H) (owner : Int)
    (p : Point) (ps : List Point) (hp : ValidKey H p.1)
    (hpm : p.1 ∈ (canonical h owner).leaves)
    (hps : ∀ q ∈ ps, ValidKey H q.1 ∧ q.1 ∈ (canonical h owner).leaves) :
    lcaLetters (canonical h owner) (c - (H - h)) (b - (H - h)) p.1 (ps.map Prod.fst) =
      directionLetters (coarsen (b + 1) (c + 1)) (mapPoint (coarsen H (b + 1)) p)
        (ps.map (mapPoint (coarsen H (b + 1)))) := by
  induction ps generalizing p with
  | nil => rfl
  | cons q qs ih =>
    have hq := hps q (by simp)
    have ht : ∀ r ∈ qs, ValidKey H r.1 ∧ r.1 ∈ (canonical h owner).leaves :=
      fun r hr => hps r (by simp [hr])
    simp only [List.map_cons,lcaLetters,directionLetters,mapPoint]
    rw [canonical_direction_word hh hc hcb hb owner p.1 q.1 hp hq.1 hpm hq.2,
      ih q hq.1 hq.2 ht]
    rfl

theorem canonical_owner_count {H h c b : Nat} (hh : h ≤ H)
    (hc : H - h ≤ c) (hcb : c ≤ b) (hb : b < H) (owner : Int)
    (ps : List Point) (hs : Chronological ps)
    (hps : ∀ q ∈ ps, ValidKey H q.1 ∧ q.1 ∈ (canonical h owner).leaves) :
    localLCAAlternations (canonical h owner) (c - (H - h)) (b - (H - h)) (ps.map Prod.fst) =
      depthAlternations (project (coarsen H (b + 1)) ps.toFinset)
        (coarsen (b + 1) (c + 1)) := by
  cases ps with
  | nil => simp [localLCAAlternations,project,depthAlternations,eventCount]
  | cons p ps =>
    have hp := hps p (by simp)
    have ht : ∀ q ∈ ps, ValidKey H q.1 ∧ q.1 ∈ (canonical h owner).leaves :=
      fun q hq => hps q (by simp [hq])
    simp only [List.map_cons,localLCAAlternations]
    rw [canonical_directionLetters hh hc hcb hb owner p ps hp.1 hp.2 ht]
    have he := directionLetters_depthAlternations (coarsen (b + 1) (c + 1))
      (mapPoint (coarsen H (b + 1)) p) (ps.map (mapPoint (coarsen H (b + 1))))
      (chronological_project hs (coarsen H (b + 1)))
    rw [he]
    congr 1
    ext q
    simp [project]

end ChaCha.Paper20261030.Dyadic
