import TangoSquared.Paper20261030.PersistentMemory
import TangoSquared.Paper20261030.OwnerFlipBound

/-!
# Exact projection of persistent memory to a subtree owner history

The bit-array execution uses global primary depths. The single-owner
analysis uses depths relative to that owner's root. These descriptions
agree after subtracting the owner's depth and filtering out requests in
other subtrees. No relation between the two histories is assumed.
-/

namespace TangoSquared.Paper20261030.Secondary

open PreferredProjection

theorem intervalDepths_eq (s : DepthSplit) (ds : List Nat) :
    intervalDepths s ds = lowDepths s.hi (ds.filter (fun d => decide (s.lo ≤ d))) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    by_cases hlo : s.lo ≤ d <;> by_cases hhi : d ≤ s.hi <;>
      simp [intervalDepths,lowDepths,List.filter_cons,hlo,hhi] at * <;> exact ih

theorem lowDepths_shift (a b : Nat) (hab : a ≤ b) (ds : List Nat) :
    lowDepths b (ds.map (fun d => a + d)) =
      (lowDepths (b - a) ds).map (fun d => a + d) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    by_cases h : d ≤ b - a
    · have h' : a + d ≤ b := by omega
      simp [lowDepths,List.filter_cons,h,h'] at *
      exact ih
    · have h' : ¬ a + d ≤ b := by omega
      simp [lowDepths,List.filter_cons,h,h'] at *
      exact ih

theorem writeWord_shift (a c : Nat) (hac : a ≤ c) (ds : List Nat) :
    writeWord c (ds.map (fun d => a + d)) = writeWord (c - a) ds := by
  simp only [writeWord,List.map_map]
  congr 1
  funext d
  simp only [Function.comp_apply]
  have he : c < a + d ↔ c - a < d := by omega
  simp only [he]

variable {α : Type*} [DecidableEq α]

theorem requestWrites_atPath {primary subtree : PrefRouter α} {s : DepthSplit} {u : List Bool}
    (hn : primary.leaves.Nodup) (hu : primary.atPath u = some subtree) (hlen : u.length = s.lo)
    (hc : s.lo ≤ s.cut) (hb : s.lo ≤ s.hi) {x : α} (hx : x ∈ subtree.leaves) :
    requestWrites primary x (s,u) =
      writeWord (s.cut - s.lo) (lowDepths (s.hi - s.lo) (subtree.exitDepths x)) := by
  have hglobal := PrefRouter.atPath_leaves hu x hx
  have hprefix := (PrefRouter.owner_prefix_iff hn hu hglobal).mpr hx
  have hdepth := PrefRouter.atPath_exitDepths hn hu hx
  rw [hlen] at hdepth
  simp only [requestWrites,if_pos hprefix,intervalDepths_eq,hdepth,
    lowDepths_shift _ _ hb,writeWord_shift _ _ hc]

theorem requestWrites_outside {primary subtree : PrefRouter α} {s : DepthSplit} {u : List Bool}
    (hn : primary.leaves.Nodup) (hu : primary.atPath u = some subtree)
    {x : α} (hx : x ∈ primary.leaves) (hout : x ∉ subtree.leaves) :
    requestWrites primary x (s,u) = [] := by
  have hprefix : ¬ u.IsPrefix (primary.searchPath x) :=
    fun h => hout ((PrefRouter.owner_prefix_iff hn hu hx).mp h)
  simp only [requestWrites,if_neg hprefix]

/-- Exact history equality for every bit of the concrete execution. -/
theorem bitHistory_owner {primary subtree : PrefRouter α} {s : DepthSplit} {u : List Bool}
    (hn : primary.leaves.Nodup) (hu : primary.atPath u = some subtree) (hlen : u.length = s.lo)
    (hc : s.lo ≤ s.cut) (hb : s.lo ≤ s.hi) (xs : List α)
    (hxs : ∀ x ∈ xs, x ∈ primary.leaves) :
    bitHistory primary (s,u) xs =
      (ownerVisits subtree (s.hi - s.lo)
        (xs.filter (fun x => decide (x ∈ subtree.leaves)))).flatMap (writeWord (s.cut - s.lo)) := by
  induction xs generalizing primary subtree with
  | nil => rfl
  | cons x xs ih =>
    have hxglobal := hxs x (by simp)
    have hn' : (primary.access x).leaves.Nodup := by
      simpa only [PrefRouter.access_leaves] using hn
    have htail : ∀ y ∈ xs, y ∈ (primary.access x).leaves := by
      intro y hy
      simpa only [PrefRouter.access_leaves] using hxs y (by simp [hy])
    have hu' : (primary.access x).atPath u = some (subtree.access x) := by
      rw [PrefRouter.atPath_access primary hn x u,hu]
      rfl
    by_cases hx : x ∈ subtree.leaves
    · rw [bitHistory,requestWrites_atPath hn hu hlen hc hb hx,ih hn' hu' htail]
      simp only [List.filter_cons,decide_eq_true hx,↓reduceIte,ownerVisits,
        List.flatMap_cons,PrefRouter.access_leaves]
    · have habsent := subtree.access_absent x hx
      rw [habsent] at hu'
      rw [bitHistory,requestWrites_outside hn hu hxglobal hx,List.nil_append,ih hn' hu' htail]
      simp only [List.filter_cons,decide_eq_false hx,Bool.false_eq_true,↓reduceIte]

/-- Applying the checked owner bound to one actual persistent-memory key. -/
theorem memory_key_flip_bound {primary subtree : PrefRouter α} {s : DepthSplit}
    {u : List Bool} {H : Nat} (hp : primary.Perfect H) (hn : primary.leaves.Nodup)
    (hu : primary.atPath u = some subtree) (hlen : u.length = s.lo)
    (hc : s.lo ≤ s.cut) (hcb : s.cut < s.hi) (hb : s.hi < H)
    (initial : Bool) (xs : List α) (hxs : ∀ x ∈ xs, x ∈ primary.leaves) :
    changesFrom initial (bitHistory primary (s,u) xs) ≤
      2 * localLCAAlternations subtree (s.cut - s.lo) (s.hi - s.lo)
        (xs.filter (fun x => decide (x ∈ subtree.leaves))) +
      2 * ownerResetCount subtree (s.cut - s.lo) (s.hi - s.lo)
        (xs.filter (fun x => decide (x ∈ subtree.leaves))) + 3 := by
  rw [bitHistory_owner hn hu hlen hc (by omega) xs hxs]
  have hlocal : subtree.Perfect (H - s.lo) := by
    apply PrefRouter.atPath_perfect (u := u) (t := primary) _ hu
    convert hp using 1
    omega
  apply owner_flip_bound hlocal (PrefRouter.atPath_nodup hn hu) (by omega) initial
  intro x hx
  exact of_decide_eq_true (List.mem_filter.mp hx).2

end TangoSquared.Paper20261030.Secondary
