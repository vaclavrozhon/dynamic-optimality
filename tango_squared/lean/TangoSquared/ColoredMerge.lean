import TangoSquared.BitReversal

/-!
# A cyclic four-symbol merge inequality

The symbols have a color and a branch coordinate. A one-bit potential
proves the comparison between the two orders of binary partition.
The transition lemma is checked by kernel `decide` on its genuinely finite
Boolean state space; the word and cyclic statements are general inductions.
This file does not prove a merge theorem for the full BST optimum or for
secondary demands.
-/

namespace TangoSquared.ColoredMerge

abbrev Symbol := Bool × Bool

structure State where
  c : Bool
  d : Bool
  dc0 : Bool
  dc1 : Bool
  cd0 : Bool
  cd1 : Bool
  deriving DecidableEq

def State.dc (s : State) (c : Bool) := if c then s.dc1 else s.dc0
def State.cd (s : State) (d : Bool) := if d then s.cd1 else s.cd0

def Coherent (s : State) : Prop := s.dc s.c = s.d ∧ s.cd s.d = s.c
instance (s : State) : Decidable (Coherent s) := inferInstanceAs (Decidable (_ ∧ _))

def step (s : State) (x : Symbol) : State where
  c := x.1
  d := x.2
  dc0 := if x.1 then s.dc0 else x.2
  dc1 := if x.1 then x.2 else s.dc1
  cd0 := if x.2 then s.cd0 else x.1
  cd1 := if x.2 then x.1 else s.cd1

/-- Under a recency interpretation, the two most recent distinct symbols
are diagonally opposite exactly when this potential is one. -/
def potential (s : State) : Nat :=
  if s.dc (!s.c) = !s.d ∧ s.cd (!s.d) = !s.c then 1 else 0

def costD (s : State) (x : Symbol) := edgeChange s.d x.2
def costC (s : State) (x : Symbol) := edgeChange s.c x.1
def costDC (s : State) (x : Symbol) := edgeChange (s.dc x.1) x.2
def costCD (s : State) (x : Symbol) := edgeChange (s.cd x.2) x.1

@[simp] theorem step_coherent (s : State) (x : Symbol) : Coherent (step s x) := by
  rcases x with ⟨c, d⟩
  cases c <;> cases d <;> simp [Coherent, step, State.dc, State.cd]

theorem step_bound : ∀ (s : State) (x : Symbol), Coherent s →
    costD s x + costCD s x + potential s ≤
      costC s x + 3 * costDC s x + potential (step s x) := by
  intro ⟨c, d, dc0, dc1, cd0, cd1⟩ ⟨xc, xd⟩
  cases c <;> cases d <;> cases dc0 <;> cases dc1 <;>
    cases cd0 <;> cases cd1 <;> cases xc <;> cases xd <;> decide

@[ext] theorem State.ext {s t : State} (hc : s.c = t.c) (hd : s.d = t.d)
    (hdc0 : s.dc0 = t.dc0) (hdc1 : s.dc1 = t.dc1)
    (hcd0 : s.cd0 = t.cd0) (hcd1 : s.cd1 = t.cd1) : s = t := by
  cases s
  cases t
  simp_all

def run (s : State) : List Symbol → State
  | [] => s
  | x :: xs => run (step s x) xs

def costSum (cost : State → Symbol → Nat) (s : State) : List Symbol → Nat
  | [] => 0
  | x :: xs => cost s x + costSum cost (step s x) xs

theorem run_coherent (s : State) (xs : List Symbol) (hs : Coherent s) :
    Coherent (run s xs) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons x xs ih => exact ih _ (step_coherent _ _)

theorem amortized (s : State) (xs : List Symbol) (hs : Coherent s) :
    costSum costD s xs + costSum costCD s xs + potential s ≤
      costSum costC s xs + 3 * costSum costDC s xs + potential (run s xs) := by
  induction xs generalizing s with
  | nil => simp [costSum, run]
  | cons x xs ih =>
    have hstep := step_bound s x hs
    have htail := ih (step s x) (step_coherent s x)
    simp only [costSum, run]
    omega

/-- Directions filtered by color. -/
def byC (c : Bool) (xs : List Symbol) : List Bool :=
  xs.filterMap (fun x => if x.1 = c then some x.2 else none)

/-- Colors filtered by direction. -/
def byD (d : Bool) (xs : List Symbol) : List Bool :=
  xs.filterMap (fun x => if x.2 = d then some x.1 else none)

@[simp] theorem run_c (s : State) (xs : List Symbol) :
    (run s xs).c = (xs.map Prod.fst).getLastD s.c := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [run, ih, step, List.map_cons, List.getLastD_cons]

@[simp] theorem run_d (s : State) (xs : List Symbol) :
    (run s xs).d = (xs.map Prod.snd).getLastD s.d := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [run, ih, step, List.map_cons, List.getLastD_cons]

@[simp] theorem run_dc (s : State) (xs : List Symbol) (c : Bool) :
    (run s xs).dc c = (byC c xs).getLastD (s.dc c) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [run, ih]
    rcases x with ⟨xc, xd⟩
    cases c <;> cases xc <;> simp only [byC, List.filterMap_cons, State.dc, step, Bool.false_eq_true, Bool.true_eq_false, if_false, if_true, List.getLastD_cons]

@[simp] theorem run_cd (s : State) (xs : List Symbol) (d : Bool) :
    (run s xs).cd d = (byD d xs).getLastD (s.cd d) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [run, ih]
    rcases x with ⟨xc, xd⟩
    cases d <;> cases xd <;> simp only [byD, List.filterMap_cons, State.cd, step, Bool.false_eq_true, Bool.true_eq_false, if_false, if_true, List.getLastD_cons]

@[simp] theorem last_absorb {α : Type*} (xs : List α) (a : α) :
    xs.getLastD (xs.getLastD a) = xs.getLastD a := by
  cases xs <;> simp only [List.getLastD_nil, List.getLastD_cons]

theorem run_idempotent (s : State) (xs : List Symbol) :
    run (run s xs) xs = run s xs := by
  apply State.ext
  · simp only [run_c, last_absorb]
  · simp only [run_d, last_absorb]
  · change (run (run s xs) xs).dc false = (run s xs).dc false
    simp only [run_dc, last_absorb]
  · change (run (run s xs) xs).dc true = (run s xs).dc true
    simp only [run_dc, last_absorb]
  · change (run (run s xs) xs).cd false = (run s xs).cd false
    simp only [run_cd, last_absorb]
  · change (run (run s xs) xs).cd true = (run s xs).cd true
    simp only [run_cd, last_absorb]

@[simp] theorem sumD (s : State) (xs : List Symbol) :
    costSum costD s xs = changesFrom s.d (xs.map Prod.snd) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp [costSum, ih, costD, step]

@[simp] theorem sumC (s : State) (xs : List Symbol) :
    costSum costC s xs = changesFrom s.c (xs.map Prod.fst) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp [costSum, ih, costC, step]

@[simp] theorem sumDC (s : State) (xs : List Symbol) :
    costSum costDC s xs =
      changesFrom s.dc0 (byC false xs) + changesFrom s.dc1 (byC true xs) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨c, d⟩
    cases c <;> simp [costSum, ih, costDC, State.dc, step, byC] <;> omega

@[simp] theorem sumCD (s : State) (xs : List Symbol) :
    costSum costCD s xs =
      changesFrom s.cd0 (byD false xs) + changesFrom s.cd1 (byD true xs) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨c, d⟩
    cases d <;> simp [costSum, ih, costCD, State.cd, step, byD] <;> omega

theorem changesFrom_last_eq_cyclic {α : Type*} [DecidableEq α]
    (xs : List α) (a : α) :
    changesFrom (xs.getLastD a) xs = cyclicAlternations xs := by
  cases xs <;> simp only [List.getLastD_nil, List.getLastD_cons, cyclicAlternations, changesFrom_nil]

/-- The general cyclic comparison between the two binary partition orders. -/
theorem cyclic_four_symbol (xs : List Symbol) :
    cyclicAlternations (xs.map Prod.snd) +
      cyclicAlternations (byD false xs) + cyclicAlternations (byD true xs) ≤
    cyclicAlternations (xs.map Prod.fst) +
      3 * (cyclicAlternations (byC false xs) + cyclicAlternations (byC true xs)) := by
  let initial : State := ⟨false, false, false, false, false, false⟩
  have hi : Coherent initial := by simp [initial, Coherent, State.dc, State.cd]
  have h := amortized (run initial xs) xs (run_coherent initial xs hi)
  rw [run_idempotent] at h
  simp only [sumD, sumCD, sumC, sumDC, run_d, run_c] at h
  have hdc0 := run_dc initial xs false
  have hdc1 := run_dc initial xs true
  have hcd0 := run_cd initial xs false
  have hcd1 := run_cd initial xs true
  simp only [State.dc, Bool.false_eq_true, ↓reduceIte, State.cd] at hdc0 hcd0
  simp only [State.dc, State.cd, ↓reduceIte] at hdc1 hcd1
  rw [hdc0, hdc1, hcd0, hcd1] at h
  simp only [changesFrom_last_eq_cyclic] at h
  omega


open Primary

abbrev ColoredKey := Bool × Key

def colorFilter (c : Bool) (xs : List ColoredKey) : List ColoredKey :=
  xs.filter (fun x => x.1 == c)

def rootPairs (xs : List ColoredKey) : List Symbol :=
  xs.filterMap (fun x => match x.2 with
    | [] => none
    | d :: _ => some (x.1, d))

def child (d : Bool) (xs : List ColoredKey) : List ColoredKey :=
  xs.filterMap (fun x => match x.2 with
    | [] => none
    | b :: tail => if b = d then some (x.1, tail) else none)

def UniformHeight (h : Nat) (xs : List ColoredKey) : Prop :=
  ∀ x ∈ xs, x.2.length = h

theorem child_height {h : Nat} {xs : List ColoredKey}
    (hx : UniformHeight (h + 1) xs) (d : Bool) : UniformHeight h (child d xs) := by
  intro y hy
  obtain ⟨x, hxm, hxy⟩ := List.mem_filterMap.mp hy
  have hh := hx x hxm
  rcases x with ⟨c, key⟩
  cases key with
  | nil => simp at hh
  | cons b tail =>
    dsimp at hxy hh
    split_ifs at hxy with hb
    · cases hxy
      simpa using hh

theorem root_direction (xs : List ColoredKey) :
    (xs.map Prod.snd).filterMap (branch []) = (rootPairs xs).map Prod.snd := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨c, key⟩
    cases key with
    | nil => simp_all [rootPairs, branch]
    | cons b tail => simp_all [rootPairs, BitReversal.branch_root_cons]

theorem child_direction (d : Bool) (u : Key) (xs : List ColoredKey) :
    (xs.map Prod.snd).filterMap (branch (d :: u)) =
      ((child d xs).map Prod.snd).filterMap (branch u) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨c, key⟩
    cases key with
    | nil => simp_all [child, branch]
    | cons b tail =>
      cases he : branch u tail <;> cases d <;> cases b <;>
        simp_all [child]

theorem child_colors (d : Bool) (xs : List ColoredKey) :
    (child d xs).map Prod.fst = byD d (rootPairs xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨c, key⟩
    cases key with
    | nil => simp_all [child, rootPairs, byD]
    | cons b tail => cases d <;> cases b <;> simp_all [child, rootPairs, byD]

theorem root_color {h : Nat} {xs : List ColoredKey}
    (hx : UniformHeight (h + 1) xs) :
    (rootPairs xs).map Prod.fst = xs.map Prod.fst := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ht : UniformHeight (h + 1) xs := fun y hy => hx y (by simp [hy])
    have hh := hx x (by simp)
    rcases x with ⟨c, key⟩
    cases key with
    | nil => simp at hh
    | cons b tail => simp_all [rootPairs]

theorem color_root_direction (c : Bool) (xs : List ColoredKey) :
    (rootPairs (colorFilter c xs)).map Prod.snd = byC c (rootPairs xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨xc, key⟩
    cases key with
    | nil => cases c <;> cases xc <;> simp_all [colorFilter, rootPairs, byC]
    | cons b tail => cases c <;> cases xc <;> simp_all [colorFilter, rootPairs, byC]

theorem child_colorFilter (c d : Bool) (xs : List ColoredKey) :
    child d (colorFilter c xs) = colorFilter c (child d xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨xc, key⟩
    cases key with
    | nil => cases c <;> cases xc <;> simp_all [colorFilter, child]
    | cons b tail =>
      cases c <;> cases xc <;> cases d <;> cases b <;> simp_all [colorFilter, child]

theorem primary_succ (h : Nat) (xs : List ColoredKey) :
    cyclicPrimary (h + 1) (xs.map Prod.snd) =
      cyclicAlternations ((rootPairs xs).map Prod.snd) +
        cyclicPrimary h ((child false xs).map Prod.snd) +
        cyclicPrimary h ((child true xs).map Prod.snd) := by
  unfold cyclicPrimary
  rw [BitReversal.owners_sum_succ]
  simp only [root_direction, child_direction]

/-- The actual complete-reference primary count obeys a two-color merge bound.
Colors belong to occurrences, so the same key may occur with both colors. -/
theorem cyclicPrimary_merge (h : Nat) (xs : List ColoredKey)
    (hx : UniformHeight h xs) :
    cyclicPrimary h (xs.map Prod.snd) ≤
      3 * cyclicPrimary h ((colorFilter false xs).map Prod.snd) +
      3 * cyclicPrimary h ((colorFilter true xs).map Prod.snd) +
      cyclicAlternations (xs.map Prod.fst) := by
  induction h generalizing xs with
  | zero => simp [cyclicPrimary, owners]
  | succ h ih =>
    have h0 := ih (child false xs) (child_height hx false)
    have h1 := ih (child true xs) (child_height hx true)
    have hl := cyclic_four_symbol (rootPairs xs)
    rw [root_color hx] at hl
    rw [← child_colors false xs, ← child_colors true xs] at hl
    rw [← color_root_direction false xs, ← color_root_direction true xs] at hl
    rw [primary_succ, primary_succ, primary_succ]
    rw [child_colorFilter false false, child_colorFilter false true,
      child_colorFilter true false, child_colorFilter true true]
    omega

theorem cyclicAlternations_le_length {α : Type*} [DecidableEq α] (xs : List α) :
    cyclicAlternations xs ≤ xs.length := by
  have bound : ∀ (ys : List α) (a : α), changesFrom a ys ≤ ys.length := by
    intro ys
    induction ys with
    | nil => simp
    | cons y ys ih =>
      intro a
      have ht := ih y
      simp only [changesFrom_cons, List.length_cons]
      have he : edgeChange a y ≤ 1 := by unfold edgeChange; split_ifs <;> omega
      omega
  cases xs with
  | nil => rfl
  | cons x xs => exact bound (x :: xs) (xs.getLastD x)

theorem cyclicPrimary_merge_length (h : Nat) (xs : List ColoredKey)
    (hx : UniformHeight h xs) :
    cyclicPrimary h (xs.map Prod.snd) ≤
      3 * cyclicPrimary h ((colorFilter false xs).map Prod.snd) +
      3 * cyclicPrimary h ((colorFilter true xs).map Prod.snd) + xs.length := by
  have hm := cyclicPrimary_merge h xs hx
  have hc := cyclicAlternations_le_length (xs.map Prod.fst)
  simp only [List.length_map] at hc
  omega

end TangoSquared.ColoredMerge
