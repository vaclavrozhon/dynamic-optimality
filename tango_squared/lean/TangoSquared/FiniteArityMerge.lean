import TangoSquared.ColoredMerge
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Cyclic merging with arbitrary finite child alphabets

The symbol alphabet is not restricted to two branches.  A one-bit
recency potential pays the comparison between partitioning by symbol
and partitioning by occurrence color.  The state and all word counts
are concrete; no charging hypothesis is assumed.
-/

namespace TangoSquared.FiniteArityMerge

variable {α : Type*} [DecidableEq α]

abbrev Symbol (α : Type*) := Bool × α

structure State (α : Type*) where
  c : Bool
  d : α
  dc0 : α
  dc1 : α
  cd : α → Bool

def State.dc (s : State α) (c : Bool) : α := if c then s.dc1 else s.dc0

def Coherent (s : State α) : Prop := s.dc s.c = s.d ∧ s.cd s.d = s.c

def step (s : State α) (x : Symbol α) : State α where
  c := x.1
  d := x.2
  dc0 := if x.1 then s.dc0 else x.2
  dc1 := if x.1 then x.2 else s.dc1
  cd := fun a => if a = x.2 then x.1 else s.cd a

def potential (s : State α) : Nat :=
  if s.dc (!s.c) ≠ s.d ∧ s.cd (s.dc (!s.c)) = !s.c then 1 else 0

def costD (s : State α) (x : Symbol α) := edgeChange s.d x.2
def costC (s : State α) (x : Symbol α) := edgeChange s.c x.1
def costDC (s : State α) (x : Symbol α) := edgeChange (s.dc x.1) x.2
def costCD (s : State α) (x : Symbol α) := edgeChange (s.cd x.2) x.1

@[simp] theorem step_coherent (s : State α) (x : Symbol α) :
    Coherent (step s x) := by
  rcases x with ⟨c, d⟩
  cases c <;> simp [Coherent, step, State.dc]

theorem edge_le_one (a b : α) : edgeChange a b ≤ 1 := by
  unfold edgeChange
  split_ifs <;> omega

theorem potential_le_one (s : State α) : potential s ≤ 1 := by
  unfold potential
  split_ifs <;> omega

theorem step_bound (s : State α) (x : Symbol α) (hs : Coherent s) :
    costD s x + costCD s x + potential s ≤
      costC s x + 3 * costDC s x + potential (step s x) := by
  by_cases hd : s.dc x.1 = x.2
  · rcases s with ⟨c, d, d0, d1, cd⟩
    rcases x with ⟨xc, xd⟩
    cases c <;> cases xc <;>
      simp only [Coherent, State.dc,
        Bool.false_eq_true, if_false, if_true] at hs hd ⊢
    all_goals
      rcases hs with ⟨hroot, hcolor⟩
      subst xd
      subst d
      simp only [State.dc, costD, costCD, costC, costDC, potential, step,
        Bool.not_false, Bool.not_true, Bool.false_eq_true,
        if_false, if_true, edgeChange_self]
      split_ifs <;> simp_all [edgeChange] <;> split_ifs <;> omega
  · have hdc : costDC s x = 1 := edgeChange_of_ne hd
    have hD := edge_le_one s.d x.2
    have hCD := edge_le_one (s.cd x.2) x.1
    have hP := potential_le_one s
    unfold costD costCD at *
    omega

omit [DecidableEq α] in
@[ext] theorem State.ext {s t : State α} (hc : s.c = t.c) (hd : s.d = t.d)
    (h0 : s.dc0 = t.dc0) (h1 : s.dc1 = t.dc1) (hcd : s.cd = t.cd) : s = t := by
  cases s
  cases t
  simp_all

def run (s : State α) : List (Symbol α) → State α
  | [] => s
  | x :: xs => run (step s x) xs

def costSum (cost : State α → Symbol α → Nat) (s : State α) :
    List (Symbol α) → Nat
  | [] => 0
  | x :: xs => cost s x + costSum cost (step s x) xs

theorem run_coherent (s : State α) (xs : List (Symbol α)) (hs : Coherent s) :
    Coherent (run s xs) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons x xs ih => exact ih _ (step_coherent _ _)

theorem amortized (s : State α) (xs : List (Symbol α)) (hs : Coherent s) :
    costSum costD s xs + costSum costCD s xs + potential s ≤
      costSum costC s xs + 3 * costSum costDC s xs + potential (run s xs) := by
  induction xs generalizing s with
  | nil => simp [costSum, run]
  | cons x xs ih =>
    have hstep := step_bound s x hs
    have htail := ih (step s x) (step_coherent s x)
    simp only [costSum, run]
    omega

def byC (c : Bool) (xs : List (Symbol α)) : List α :=
  xs.filterMap (fun x => if x.1 = c then some x.2 else none)

def byD (d : α) (xs : List (Symbol α)) : List Bool :=
  xs.filterMap (fun x => if x.2 = d then some x.1 else none)

@[simp] theorem run_c (s : State α) (xs : List (Symbol α)) :
    (run s xs).c = (xs.map Prod.fst).getLastD s.c := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [run, ih, step, List.map_cons, List.getLastD_cons]

@[simp] theorem run_d (s : State α) (xs : List (Symbol α)) :
    (run s xs).d = (xs.map Prod.snd).getLastD s.d := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [run, ih, step, List.map_cons, List.getLastD_cons]

@[simp] theorem run_dc (s : State α) (xs : List (Symbol α)) (c : Bool) :
    (run s xs).dc c = (byC c xs).getLastD (s.dc c) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [run, ih]
    rcases x with ⟨xc, xd⟩
    cases c <;> cases xc <;>
      simp only [byC, List.filterMap_cons, State.dc, step,
        Bool.false_eq_true, Bool.true_eq_false, if_false, if_true,
        List.getLastD_cons]

@[simp] theorem run_cd (s : State α) (xs : List (Symbol α)) (d : α) :
    (run s xs).cd d = (byD d xs).getLastD (s.cd d) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [run, ih]
    rcases x with ⟨xc, xd⟩
    by_cases h : xd = d
    · subst xd
      simp only [byD, List.filterMap_cons, step, ↓reduceIte, List.getLastD_cons]
    · simp [byD, step, h, Ne.symm h]

theorem run_idempotent (s : State α) (xs : List (Symbol α)) :
    run (run s xs) xs = run s xs := by
  apply State.ext
  · simp only [run_c, ColoredMerge.last_absorb]
  · simp only [run_d, ColoredMerge.last_absorb]
  · change (run (run s xs) xs).dc false = (run s xs).dc false
    simp only [run_dc, ColoredMerge.last_absorb]
  · change (run (run s xs) xs).dc true = (run s xs).dc true
    simp only [run_dc, ColoredMerge.last_absorb]
  · funext d
    simp only [run_cd, ColoredMerge.last_absorb]

@[simp] theorem sumD (s : State α) (xs : List (Symbol α)) :
    costSum costD s xs = changesFrom s.d (xs.map Prod.snd) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp [costSum, ih, costD, step]

@[simp] theorem sumC (s : State α) (xs : List (Symbol α)) :
    costSum costC s xs = changesFrom s.c (xs.map Prod.fst) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp [costSum, ih, costC, step]

@[simp] theorem sumDC (s : State α) (xs : List (Symbol α)) :
    costSum costDC s xs =
      changesFrom s.dc0 (byC false xs) + changesFrom s.dc1 (byC true xs) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨c, d⟩
    cases c <;> simp [costSum, ih, costDC, State.dc, step, byC] <;> omega

theorem byD_cons_cost (s : State α) (x : Symbol α)
    (xs : List (Symbol α)) (d : α) :
    changesFrom (s.cd d) (byD d (x :: xs)) =
      (if d = x.2 then costCD s x else 0) +
        changesFrom ((step s x).cd d) (byD d xs) := by
  rcases x with ⟨c, a⟩
  by_cases h : d = a
  · subst d
    simp only [byD, List.filterMap_cons, step, ↓reduceIte,
      changesFrom, costCD]
  · simp [byD, step, h, Ne.symm h]

@[simp] theorem sumCD [Fintype α] (s : State α) (xs : List (Symbol α)) :
    costSum costCD s xs = ∑ d : α, changesFrom (s.cd d) (byD d xs) := by
  induction xs generalizing s with
  | nil => simp [costSum, byD]
  | cons x xs ih =>
    simp only [costSum, ih, byD_cons_cost, Finset.sum_add_distrib]
    simp

/-- The local merge inequality has a constant independent of alphabet size. -/
theorem cyclic_finite_alphabet [Fintype α] (xs : List (Symbol α)) :
    cyclicAlternations (xs.map Prod.snd) +
      (∑ d : α, cyclicAlternations (byD d xs)) ≤
    cyclicAlternations (xs.map Prod.fst) +
      3 * (cyclicAlternations (byC false xs) + cyclicAlternations (byC true xs)) := by
  cases xs with
  | nil => simp [byD, byC, cyclicAlternations]
  | cons x xs =>
    let initial : State α := ⟨false, x.2, x.2, x.2, fun _ => false⟩
    have hi : Coherent initial := by simp [initial, Coherent, State.dc]
    have h := amortized (run initial (x :: xs)) (x :: xs)
      (run_coherent initial (x :: xs) hi)
    rw [run_idempotent] at h
    simp only [sumD, sumCD, sumC, sumDC, run_d, run_c, run_cd] at h
    have hdc0 := run_dc initial (x :: xs) false
    have hdc1 := run_dc initial (x :: xs) true
    simp only [State.dc, Bool.false_eq_true, if_false, if_true] at hdc0 hdc1
    rw [hdc0, hdc1] at h
    simp only [ColoredMerge.changesFrom_last_eq_cyclic] at h
    omega

inductive PartitionTree (β : Type*) where
  | leaf
  | split (arity : Nat) (branch : β → Fin arity)
      (children : Fin arity → PartitionTree β)

variable {β : Type*}

def byColor (c : Bool) (xs : List (Bool × β)) : List (Bool × β) :=
  xs.filter (fun x => x.1 == c)

def child {k : Nat} (branch : β → Fin k) (i : Fin k)
    (xs : List (Bool × β)) : List (Bool × β) :=
  xs.filter (fun x => branch x.2 == i)

def pairs {k : Nat} (branch : β → Fin k) (xs : List (Bool × β)) :
    List (Symbol (Fin k)) := xs.map (fun x => (x.1, branch x.2))

def cyclicCost : PartitionTree β → List (Bool × β) → Nat
  | .leaf, _ => 0
  | .split _ branch children, xs =>
      cyclicAlternations (xs.map (fun x => branch x.2)) +
        ∑ i, cyclicCost (children i) (child branch i xs)

theorem pairs_colors {k : Nat} (branch : β → Fin k) (xs : List (Bool × β)) :
    (pairs branch xs).map Prod.fst = xs.map Prod.fst := by
  simp [pairs, List.map_map]

theorem pairs_directions {k : Nat} (branch : β → Fin k)
    (xs : List (Bool × β)) :
    (pairs branch xs).map Prod.snd = xs.map (fun x => branch x.2) := by
  simp [pairs, List.map_map]

theorem child_colors {k : Nat} (branch : β → Fin k) (i : Fin k)
    (xs : List (Bool × β)) :
    (child branch i xs).map Prod.fst = byD i (pairs branch xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : branch x.2 = i <;> simp_all [child, pairs, byD]

theorem color_directions {k : Nat} (branch : β → Fin k) (c : Bool)
    (xs : List (Bool × β)) :
    (byColor c xs).map (fun x => branch x.2) = byC c (pairs branch xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨xc, key⟩
    cases c <;> cases xc <;> simp_all [byColor, pairs, byC]

theorem child_byColor {k : Nat} (branch : β → Fin k) (c : Bool) (i : Fin k)
    (xs : List (Bool × β)) :
    child branch i (byColor c xs) = byColor c (child branch i xs) := by
  simp only [child, byColor, List.filter_filter]
  congr 1
  funext x
  exact Bool.and_comm _ _

/-- Colored cyclic merging on a concrete arbitrary finite-arity hierarchy. -/
theorem cyclicCost_merge (tree : PartitionTree β) (xs : List (Bool × β)) :
    cyclicCost tree xs ≤
      3 * cyclicCost tree (byColor false xs) +
      3 * cyclicCost tree (byColor true xs) +
      cyclicAlternations (xs.map Prod.fst) := by
  induction tree generalizing xs with
  | leaf => simp [cyclicCost]
  | split k branch children ih =>
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => ih i (child branch i xs))
    have hroot := cyclic_finite_alphabet (pairs branch xs)
    rw [pairs_colors, pairs_directions] at hroot
    simp only [← child_colors, ← color_directions] at hroot
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    simp only [cyclicCost, child_byColor]
    omega

theorem cyclicCost_merge_length (tree : PartitionTree β)
    (xs : List (Bool × β)) :
    cyclicCost tree xs ≤
      3 * cyclicCost tree (byColor false xs) +
      3 * cyclicCost tree (byColor true xs) + xs.length := by
  have hm := cyclicCost_merge tree xs
  have hc := ColoredMerge.cyclicAlternations_le_length (xs.map Prod.fst)
  simp only [List.length_map] at hc
  omega

end TangoSquared.FiniteArityMerge
