import TangoSquared.Paper20261030.SubtreeHistories
import Mathlib.Data.Finset.Image

/-!
# Concrete addresses of primary owners

An address is a Boolean word of child choices. `ownerPaths` enumerates
exactly the vertices at a given depth, and `searchPath` computes the address
of a requested leaf. Preferences do not affect these addresses.
-/

namespace TangoSquared.PreferredProjection.PrefRouter

variable {α : Type*} [DecidableEq α]

def ownerPaths : PrefRouter α → Nat → List (List Bool)
  | _, 0 => [[]]
  | .leaf _, _ + 1 => []
  | .fork _ l r, d + 1 =>
      (ownerPaths l d).map (false :: ·) ++ (ownerPaths r d).map (true :: ·)

theorem ownerPaths_length {H d : Nat} {t : PrefRouter α}
    (hp : Perfect H t) (hd : d ≤ H) : (t.ownerPaths d).length = 2 ^ d := by
  induction d generalizing t H with
  | zero => simp [ownerPaths]
  | succ d ih =>
    cases H with
    | zero => omega
    | succ H =>
      cases t with
      | leaf a => contradiction
      | fork b l r =>
        simp only [ownerPaths,List.length_append,List.length_map,
          ih hp.1 (by omega),ih hp.2 (by omega),pow_succ]
        omega

theorem mem_ownerPaths {t : PrefRouter α} {d : Nat} {u : List Bool} :
    u ∈ t.ownerPaths d ↔ u.length = d ∧ ∃ s, t.atPath u = some s := by
  induction d generalizing t u with
  | zero =>
    cases u <;> simp [ownerPaths,atPath]
  | succ d ih =>
    cases t with
    | leaf a => cases u <;> simp [ownerPaths,atPath]
    | fork b l r =>
      cases u with
      | nil => simp [ownerPaths,atPath]
      | cons dir u => cases dir <;> simp [ownerPaths,atPath,ih]

def searchPath (x : α) : PrefRouter α → List Bool
  | .leaf _ => []
  | .fork _ l r =>
      if x ∈ l.leaves then false :: searchPath x l
      else if x ∈ r.leaves then true :: searchPath x r
      else []

theorem ownerPaths_access (t : PrefRouter α) (x : α) (d : Nat) :
    (t.access x).ownerPaths d = t.ownerPaths d := by
  induction t generalizing d with
  | leaf a => rfl
  | fork b l r ihl ihr =>
    cases d with
    | zero => simp [ownerPaths]
    | succ d =>
      simp only [access]
      split_ifs <;> simp only [ownerPaths,ihl,ihr]

theorem searchPath_access (t : PrefRouter α) (x y : α) :
    (t.access y).searchPath x = t.searchPath x := by
  induction t with
  | leaf a => rfl
  | fork b l r ihl ihr =>
    simp only [access]
    split_ifs <;> simp only [searchPath,access_leaves,ihl,ihr]

theorem searchPath_length {H : Nat} {t : PrefRouter α} (hp : Perfect H t)
    {x : α} (hx : x ∈ t.leaves) : (t.searchPath x).length = H := by
  induction t generalizing H with
  | leaf a => cases H <;> simp_all [Perfect,searchPath]
  | fork b l r ihl ihr =>
    cases H with
    | zero => contradiction
    | succ H =>
      by_cases hl : x ∈ l.leaves
      · simp [searchPath,hl,ihl hp.1 hl]
      · have hr : x ∈ r.leaves := (List.mem_append.mp hx).resolve_left hl
        simp [searchPath,hl,hr,ihr hp.2 hr]

theorem searchPath_leaf {t : PrefRouter α} {x : α} (hx : x ∈ t.leaves) :
    t.atPath (t.searchPath x) = some (.leaf x) := by
  induction t with
  | leaf a =>
    have he : x = a := List.mem_singleton.mp hx
    subst x
    rfl
  | fork b l r ihl ihr =>
    by_cases hl : x ∈ l.leaves
    · simpa [searchPath,hl,atPath] using ihl hl
    · have hr : x ∈ r.leaves := (List.mem_append.mp hx).resolve_left hl
      simpa [searchPath,hl,hr,atPath] using ihr hr

/-- Membership in an actual owner's subtree is equivalent to its address
being a prefix of the requested leaf's address. -/
theorem owner_prefix_iff {t s : PrefRouter α} {u : List Bool} (hn : t.leaves.Nodup)
    (hu : t.atPath u = some s) {x : α} (hx : x ∈ t.leaves) :
    u.IsPrefix (t.searchPath x) ↔ x ∈ s.leaves := by
  induction u generalizing t with
  | nil => cases Option.some.inj hu; simp [hx]
  | cons dir u ih =>
    cases t with
    | leaf a => contradiction
    | fork b l r =>
      obtain ⟨hnl,hnr,hdis⟩ := List.nodup_append.mp hn
      by_cases hl : x ∈ l.leaves
      · cases dir
        · simpa [searchPath,hl] using ih hnl hu hl
        · have hno : x ∉ s.leaves := by
            intro hs
            have hr := atPath_leaves (t := r) (u := u) hu x hs
            exact hdis _ hl _ hr rfl
          simp [searchPath,hl,hno]
      · have hr : x ∈ r.leaves := (List.mem_append.mp hx).resolve_left hl
        cases dir
        · have hno : x ∉ s.leaves := fun hs => hl (atPath_leaves (t := l) (u := u) hu x hs)
          simp [searchPath,hl,hr,hno]
        · simpa [searchPath,hl,hr] using ih hnr hu hr

end TangoSquared.PreferredProjection.PrefRouter
