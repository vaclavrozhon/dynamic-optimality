import TangoSquared.PreferredProjection
import TangoSquared.Words

/-!
# Concrete abstract Tango accesses and head switches

The tree and all preferred-child bits are explicit. `access` changes the
root-to-request preferences. `HeadStep` changes exactly the first wrong
edge on that path, reached through the current root preferred path.
-/

namespace TangoSquared.PreferredProjection.PrefRouter

open RouterProjection

variable {α : Type*} [DecidableEq α]

def leaves : PrefRouter α → List α
  | .leaf x => [x]
  | .fork _ l r => leaves l ++ leaves r

def height : PrefRouter α → Nat
  | .leaf _ => 0
  | .fork _ l r => max l.height r.height + 1

def access (x : α) : PrefRouter α → PrefRouter α
  | .leaf y => .leaf y
  | .fork b l r =>
      if x ∈ l.leaves then .fork false (access x l) r
      else if x ∈ r.leaves then .fork true l (access x r)
      else .fork b l r

def exitDepths (x : α) : PrefRouter α → List Nat
  | .leaf _ => []
  | .fork b l r =>
      if x ∈ l.leaves then (if b then [0] else []) ++ (exitDepths x l).map Nat.succ
      else if x ∈ r.leaves then (if b then [] else [0]) ++ (exitDepths x r).map Nat.succ
      else []

def accessFlips (x : α) : PrefRouter α → Nat
  | .leaf _ => 0
  | .fork b l r =>
      if x ∈ l.leaves then edgeChange b false + accessFlips x l
      else if x ∈ r.leaves then edgeChange b true + accessFlips x r
      else 0

theorem leaves_erase (t : PrefRouter α) : t.erase.leaves = t.leaves := by
  induction t with
  | leaf a => rfl
  | fork b l r ihl ihr => simp only [PrefRouter.erase,Router.leaves,leaves,ihl,ihr]

theorem access_erase (x : α) (t : PrefRouter α) : (t.access x).erase = t.erase := by
  induction t with
  | leaf y => rfl
  | fork b l r ihl ihr =>
    simp only [access]
    split_ifs <;> simp only [PrefRouter.erase,ihl,ihr]

theorem access_leaves (x : α) (t : PrefRouter α) : (t.access x).leaves = t.leaves := by
  rw [← leaves_erase,access_erase,leaves_erase]

theorem terminal_mem (t : PrefRouter α) : t.terminal ∈ t.leaves := by
  induction t with
  | leaf a => simp [PrefRouter.terminal,leaves]
  | fork b l r ihl ihr =>
    cases b <;> simp [PrefRouter.terminal,leaves,ihl,ihr]

theorem terminal_access (x : α) (t : PrefRouter α) (hx : x ∈ t.leaves) :
    (t.access x).terminal = x := by
  induction t with
  | leaf y => exact (List.mem_singleton.mp hx).symm
  | fork b l r ihl ihr =>
    simp only [leaves,List.mem_append] at hx
    by_cases hl : x ∈ l.leaves
    · simpa [access,hl,PrefRouter.terminal] using ihl hl
    · have hr : x ∈ r.leaves := hx.resolve_left hl
      simpa [access,hl,hr,PrefRouter.terminal] using ihr hr

theorem exitDepths_length (x : α) (t : PrefRouter α) :
    (t.exitDepths x).length = t.accessFlips x := by
  induction t with
  | leaf y => rfl
  | fork b l r ihl ihr =>
    cases b <;> simp only [exitDepths,accessFlips,edgeChange] <;>
      split_ifs <;> simp_all <;> omega

theorem exitDepths_bound (x : α) (t : PrefRouter α) :
    ∀ d ∈ t.exitDepths x, d < t.height := by
  induction t with
  | leaf y => simp [exitDepths]
  | fork b l r ihl ihr =>
    intro d hd
    by_cases hl : x ∈ l.leaves
    · have hcases : d = 0 ∨ ∃ e ∈ l.exitDepths x, e + 1 = d := by
        cases b <;> simp_all [exitDepths]
      rcases hcases with rfl | ⟨e,he,rfl⟩
      · simp [height]
      · have := ihl e he
        simp only [height]
        omega
    · by_cases hr : x ∈ r.leaves
      · have hcases : d = 0 ∨ ∃ e ∈ r.exitDepths x, e + 1 = d := by
          cases b <;> simp_all [exitDepths]
        rcases hcases with rfl | ⟨e,he,rfl⟩
        · simp [height]
        · have := ihr e he
          simp only [height]
          omega
      · simp [exitDepths,hl,hr] at hd

theorem exitDepths_increasing (x : α) (t : PrefRouter α) :
    (t.exitDepths x).Pairwise (· < ·) := by
  induction t with
  | leaf y => simp [exitDepths]
  | fork b l r ihl ihr =>
    have hlmap : ((l.exitDepths x).map Nat.succ).Pairwise (· < ·) :=
      List.Pairwise.map Nat.succ (fun a b hab => Nat.succ_lt_succ hab) ihl
    have hrmap : ((r.exitDepths x).map Nat.succ).Pairwise (· < ·) :=
      List.Pairwise.map Nat.succ (fun a b hab => Nat.succ_lt_succ hab) ihr
    have addZero (xs : List Nat) (hi : (xs.map Nat.succ).Pairwise (· < ·)) :
        (0 :: xs.map Nat.succ).Pairwise (· < ·) := by
      apply List.pairwise_cons.mpr
      refine ⟨?_,hi⟩
      intro a ha
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
      exact Nat.succ_pos k
    by_cases hl : x ∈ l.leaves
    · cases b
      · simpa [exitDepths,hl] using hlmap
      · simpa [exitDepths,hl] using addZero (l.exitDepths x) hlmap
    · by_cases hr : x ∈ r.leaves
      · cases b
        · simpa [exitDepths,hl,hr] using addZero (r.exitDepths x) hrmap
        · simpa [exitDepths,hl,hr] using hrmap
      · simp [exitDepths,hl,hr]

/-- One genuine head switch on the currently preferred root path. -/
inductive HeadStep (x : α) : Nat → PrefRouter α → PrefRouter α → Prop
  | leftRoot (l r : PrefRouter α) (hx : x ∈ l.leaves) :
      HeadStep x 0 (.fork true l r) (.fork false l r)
  | rightRoot (l r : PrefRouter α) (hl : x ∉ l.leaves) (hr : x ∈ r.leaves) :
      HeadStep x 0 (.fork false l r) (.fork true l r)
  | leftDown {d : Nat} {l l' : PrefRouter α} (r : PrefRouter α)
      (h : HeadStep x d l l') : HeadStep x (d + 1) (.fork false l r) (.fork false l' r)
  | rightDown {d : Nat} {r r' : PrefRouter α} (l : PrefRouter α)
      (hl : x ∉ l.leaves) (h : HeadStep x d r r') :
      HeadStep x (d + 1) (.fork true l r) (.fork true l r')

inductive HeadTrace (x : α) : PrefRouter α → List Nat → PrefRouter α → Prop
  | nil (t : PrefRouter α) : HeadTrace x t [] t
  | cons {t u v : PrefRouter α} {d : Nat} {ds : List Nat}
      (step : HeadStep x d t u) (rest : HeadTrace x u ds v) : HeadTrace x t (d :: ds) v

theorem HeadTrace.left {x : α} {l l' : PrefRouter α} {ds : List Nat}
    (h : HeadTrace x l ds l') (r : PrefRouter α) :
    HeadTrace x (.fork false l r) (ds.map Nat.succ) (.fork false l' r) := by
  induction h with
  | nil l => exact .nil _
  | cons step rest ih => exact .cons (.leftDown r step) ih

theorem HeadTrace.right {x : α} {r r' : PrefRouter α} {ds : List Nat}
    (h : HeadTrace x r ds r') (l : PrefRouter α) (hl : x ∉ l.leaves) :
    HeadTrace x (.fork true l r) (ds.map Nat.succ) (.fork true l r') := by
  induction h with
  | nil r => exact .nil _
  | cons step rest ih => exact .cons (.rightDown l hl step) ih

/-- The abstract loop performs exactly the listed head switches and finishes
at the ordinary Tango access state. In particular it terminates. -/
theorem access_headTrace (x : α) (t : PrefRouter α) :
    HeadTrace x t (t.exitDepths x) (t.access x) := by
  induction t with
  | leaf y => exact .nil _
  | fork b l r ihl ihr =>
    by_cases hl : x ∈ l.leaves
    · cases b
      · simpa only [exitDepths,access,if_pos hl,Bool.false_eq_true,↓reduceIte,List.nil_append]
          using ihl.left r
      · simpa only [exitDepths,access,if_pos hl,↓reduceIte,List.singleton_append]
          using HeadTrace.cons (.leftRoot l r hl) (ihl.left r)
    · by_cases hr : x ∈ r.leaves
      · cases b
        · simpa only [exitDepths,access,if_neg hl,if_pos hr,Bool.false_eq_true,↓reduceIte,
            List.singleton_append] using HeadTrace.cons (.rightRoot l r hl hr) (ihr.right l hl)
        · simpa only [exitDepths,access,if_neg hl,if_pos hr,↓reduceIte,List.nil_append]
            using ihr.right l hl
      · simp only [exitDepths,access,if_neg hl,if_neg hr]
        exact .nil _

end TangoSquared.PreferredProjection.PrefRouter
