import TangoSquared.Paper20261030.SecondaryHeads

/-!
# Secondary flips at a concrete primary owner

`ownerVisits` executes actual primary accesses and records the exit depths
inside one secondary interval. `lcaLetters` records directions of the
LCAs of consecutive local requests, omitting LCAs below that interval.
Their first-write words coincide after the initial request. Thus the
Boolean estimate applies without assuming a charging or update contract.
-/

namespace TangoSquared.Paper20261030.Secondary

open PreferredProjection FlipAccounting

variable {α : Type*} [DecidableEq α]

def ownerVisits (t : PrefRouter α) (b : Nat) : List α → List (List Nat)
  | [] => []
  | x :: xs => lowDepths b (t.exitDepths x) :: ownerVisits (t.access x) b xs

def lcaLetters (t : PrefRouter α) (c b : Nat) (previous : α) : List α → List Bool
  | [] => []
  | x :: xs =>
      (if t.referenceLCA previous x ≤ b then [decide (c < t.referenceLCA previous x)] else []) ++
        lcaLetters t c b x xs

theorem lcaLetters_access (t : PrefRouter α) (c b : Nat) (previous z : α) (xs : List α) :
    lcaLetters (t.access z) c b previous xs = lcaLetters t c b previous xs := by
  induction xs generalizing previous with
  | nil => rfl
  | cons x xs ih => simp only [lcaLetters,PrefRouter.referenceLCA_access,ih]

theorem ownerVisits_increasing (t : PrefRouter α) (b : Nat) (xs : List α) :
    ∀ ds ∈ ownerVisits t b xs, ds.Pairwise (· < ·) := by
  induction xs generalizing t with
  | nil => simp [ownerVisits]
  | cons x xs ih =>
    intro ds hds
    rcases List.mem_cons.mp hds with rfl | hds
    · exact lowDepths_increasing b _ (t.exitDepths_increasing x)
    · exact ih _ ds hds

theorem block_heads_cons (c : Nat) (ds : List Nat) (visits : List (List Nat)) :
    (historyBlocks c (ds :: visits)).map Block.head =
      ((visitBlock c ds).map Block.head).toList ++ (historyBlocks c visits).map Block.head := by
  rw [historyBlocks_cons,List.map_append]
  cases visitBlock c ds <;> rfl

/-- Every regular first write is computed from two actual consecutive
requests. The initial preferred assignment is arbitrary. -/
theorem owner_regular_heads {H c b : Nat} {t : PrefRouter α}
    (hp : t.Perfect H) (hn : t.leaves.Nodup) (hb : b < H)
    (previous : α) (hm : previous ∈ t.leaves) (xs : List α)
    (hxs : ∀ x ∈ xs, x ∈ t.leaves) :
    (historyBlocks c (ownerVisits (t.access previous) b xs)).map Block.head =
      lcaLetters t c b previous xs := by
  induction xs generalizing t previous with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ∈ t.leaves := hxs x (by simp)
    have htail : ∀ y ∈ xs, y ∈ (t.access previous).leaves := by
      intro y hy
      simpa only [PrefRouter.access_leaves] using hxs y (by simp [hy])
    have hn' : (t.access previous).leaves.Nodup := by
      simpa only [PrefRouter.access_leaves] using hn
    have hx' : x ∈ (t.access previous).leaves := by
      simpa only [PrefRouter.access_leaves] using hx
    rw [ownerVisits,block_heads_cons,next_visit_head hp hn hb hm hx,
      ih (PrefRouter.perfect_access hp previous) hn' x hx' htail,lcaLetters_access]
    conv_rhs => rw [lcaLetters]
    split_ifs <;> rfl

def localLCAAlternations (t : PrefRouter α) (c b : Nat) : List α → Nat
  | [] => 0
  | previous :: xs => rlCount (lcaLetters t c b previous xs)

def ownerFlipCount (t : PrefRouter α) (c b : Nat) (initial : Bool) (xs : List α) : Nat :=
  changesFrom initial ((ownerVisits t b xs).flatMap (writeWord c))

def ownerResetCount (t : PrefRouter α) (c b : Nat) (xs : List α) : Nat :=
  ((historyBlocks c (ownerVisits t b xs)).map Block.resets).sum

/-- Bound for an actual persistent memory bit, with arbitrary initialized
preference and arbitrary initial primary preferences. -/
theorem owner_flip_bound {H c b : Nat} {t : PrefRouter α}
    (hp : t.Perfect H) (hn : t.leaves.Nodup) (hb : b < H)
    (initial : Bool) (xs : List α) (hxs : ∀ x ∈ xs, x ∈ t.leaves) :
    ownerFlipCount t c b initial xs ≤
      2 * localLCAAlternations t c b xs + 2 * ownerResetCount t c b xs + 3 := by
  cases xs with
  | nil => simp [ownerFlipCount,ownerVisits,localLCAAlternations,ownerResetCount,historyBlocks]
  | cons previous xs =>
    have hm := hxs previous (by simp)
    have htail : ∀ x ∈ xs, x ∈ t.leaves := fun x hx => hxs x (by simp [hx])
    have hh := owner_regular_heads (c := c) hp hn hb previous hm xs htail
    apply writeHistory_head_bound c (ownerVisits t b (previous :: xs))
      (ownerVisits_increasing t b (previous :: xs)) initial (lcaLetters t c b previous xs)
      ((visitBlock c (lowDepths b (t.exitDepths previous))).map Block.head)
    rw [ownerVisits,block_heads_cons,hh]

/-- The manuscript's first-visit claim needs correction: with its prescribed
rightward initialization, one genuine bit can flip twice on its first visit. -/
def firstVisitExample : PrefRouter Nat :=
  .fork true (.fork true (.leaf 0) (.leaf 1)) (.fork true (.leaf 2) (.leaf 3))

theorem first_visit_can_flip_twice :
    firstVisitExample.exitDepths 0 = [0,1] ∧
      ownerFlipCount firstVisitExample 0 1 true [0] = 2 := by
  decide +kernel

end TangoSquared.Paper20261030.Secondary
