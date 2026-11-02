import ChaCha.Paper20261030.OwnerRectangleCount
import ChaCha.Paper20261030.AccessWords

/-!
# Numeric indices of the actual primary owner addresses

Addresses at depth `a` correspond bijectively to the keys of the height-`a`
canonical reference. The subtree at such an address is exactly the dyadic
fiber with that index.
-/

namespace ChaCha.Paper20261030.Dyadic

open PreferredProjection Rectangles Secondary

theorem owner_index_word (H a : Nat) (ha : a ≤ H) (owner : Int) :
    ((canonical H owner).ownerPaths a).map (descendantIndex owner) = (canonical a owner).leaves := by
  induction a generalizing H owner with
  | zero => simp [PrefRouter.ownerPaths,canonical,PrefRouter.leaves,descendantIndex]
  | succ a ih =>
    cases H with
    | zero => omega
    | succ H =>
      have ha' : a ≤ H := by omega
      simp only [canonical,PrefRouter.ownerPaths,List.map_append,List.map_map,PrefRouter.leaves]
      have hleft : (fun u => descendantIndex owner (false :: u)) = descendantIndex (2 * owner) := by
        funext u
        simp [descendantIndex]
      have hright : (fun u => descendantIndex owner (true :: u)) = descendantIndex (2 * owner + 1) := by
        funext u
        simp [descendantIndex]
      change List.map (fun u => descendantIndex owner (false :: u)) _ ++
        List.map (fun u => descendantIndex owner (true :: u)) _ = _
      rw [hleft,hright,ih _ ha',ih _ ha']

theorem owner_indices (H a : Nat) (ha : a ≤ H) (owner : Int) :
    ((canonical H owner).ownerPaths a).toFinset.image (descendantIndex owner) =
      (canonical a owner).leaves.toFinset := by
  have he := congrArg List.toFinset (owner_index_word H a ha owner)
  rw [← he]
  ext i
  simp

theorem owner_index_injective (H a : Nat) (ha : a ≤ H) :
    Set.InjOn (descendantIndex 0) (↑((canonical H 0).ownerPaths a).toFinset : Set (List Bool)) := by
  intro u hu v hv he
  have hul := (PrefRouter.mem_ownerPaths.mp (List.mem_toFinset.mp hu)).1
  have hvl := (PrefRouter.mem_ownerPaths.mp (List.mem_toFinset.mp hv)).1
  have hua := canonical_atPath H 0 u (by omega)
  have hva := canonical_atPath H 0 v (by omega)
  rw [hul] at hua
  rw [hvl,← he] at hva
  let subtree := canonical (H - a) (descendantIndex 0 u)
  have ht : subtree.terminal ∈ subtree.leaves := subtree.terminal_mem
  have hglobal := PrefRouter.atPath_leaves hua subtree.terminal ht
  have hup := (PrefRouter.owner_prefix_iff (canonical_nodup H 0) hua hglobal).mpr ht
  have hvp := (PrefRouter.owner_prefix_iff (canonical_nodup H 0) hva hglobal).mpr ht
  rw [List.prefix_iff_eq_take] at hup hvp
  rw [hul] at hup
  rw [hvl] at hvp
  exact hup.trans hvp.symm

theorem owner_fiber {H a : Nat} (ha : a ≤ H) {u : List Bool} (hu : u.length = a)
    (ps : List Point) :
    (ps.filter (fun p => decide (p.1 ∈ (canonical (H - a) (descendantIndex 0 u)).leaves))).toFinset =
      fiber (coarsen H a) (descendantIndex 0 u) ps.toFinset := by
  ext p
  simp [fiber,canonical_mem,coarsen]

/-- One actual memory key's LCA count is the concrete geometric count in
its dyadic owner fiber, with the same timestamps. -/
theorem canonical_key_count {H : Nat} (s : DepthSplit) (u : List Bool)
    (hlen : u.length = s.lo) (hc : s.lo ≤ s.cut) (hcb : s.cut ≤ s.hi) (hb : s.hi < H)
    (ps : List Point) (hs : Chronological ps) (hkeys : ∀ p ∈ ps, ValidKey H p.1) :
    keyLCA (canonical H 0) (s,u) (ps.map Prod.fst) =
      lcaTransitions H (s.cut + 1) (s.hi + 1)
        (fiber (coarsen H s.lo) (descendantIndex 0 u) ps.toFinset) := by
  have hlenH : u.length ≤ H := by omega
  have hat := canonical_atPath H 0 u hlenH
  rw [hlen] at hat
  simp only [keyLCA,hat]
  let qs := ps.filter (fun p => decide (p.1 ∈ (canonical (H - s.lo) (descendantIndex 0 u)).leaves))
  have hqs : Chronological qs := chronological_filter hs _
  have hqkeys : ∀ q ∈ qs, ValidKey H q.1 ∧ q.1 ∈ (canonical (H - s.lo) (descendantIndex 0 u)).leaves := by
    intro q hq
    obtain ⟨hm,howner⟩ := List.mem_filter.mp hq
    exact ⟨hkeys q hm,of_decide_eq_true howner⟩
  have hkeysword : qs.map Prod.fst =
      (ps.map Prod.fst).filter (fun x => decide (x ∈ (canonical (H - s.lo) (descendantIndex 0 u)).leaves)) :=
    keys_filter_points ps (fun x => decide (x ∈ (canonical (H - s.lo) (descendantIndex 0 u)).leaves))
  rw [← hkeysword]
  have hdepth : H - (H - s.lo) = s.lo := by omega
  have he := canonical_owner_count (H := H) (h := H - s.lo) (c := s.cut) (b := s.hi)
    (by omega) (by omega) hcb hb (descendantIndex 0 u) qs hqs hqkeys
  rw [hdepth] at he
  rw [he]
  have hset : qs.toFinset = fiber (coarsen H s.lo) (descendantIndex 0 u) ps.toFinset :=
    owner_fiber (by omega) hlen ps
  rw [hset]
  symm
  apply lcaTransitions_eq_depthAlternations
  · exact instance_fiber (chronological_instance hs) _ _
  · intro p hp
    exact hkeys p (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)
  · omega
  · omega

end ChaCha.Paper20261030.Dyadic
