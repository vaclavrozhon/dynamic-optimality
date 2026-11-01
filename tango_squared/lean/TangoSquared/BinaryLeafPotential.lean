import TangoSquared.FragmentHierarchy
import TangoSquared.CyclicPrimaryBudget

/-! The leaves of the actual fragment hierarchy telescope to the primary count. -/

namespace TangoSquared.CyclicRuns

/-- In a binary alphabet, the direction of a nonconstant edge is its destination. -/
theorem edgeDirection_bool (a b : Bool) :
    edgeDirection a b = if a = b then [] else [b] := by cases a <;> cases b <;> decide

theorem directionsFrom_bool_last (a : Bool) (xs : List Bool) :
    (directionsFrom a xs).getLastD a = xs.getLastD a := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    rw [directionsFrom, edgeDirection_bool]
    by_cases h : a = b
    · subst b
      simpa only [if_pos rfl, ↓reduceIte, List.nil_append, List.getLastD_cons] using ih a
    · simpa only [if_neg h, List.singleton_append, List.getLastD_cons] using ih b

theorem changesFrom_directionsFrom_bool (a : Bool) (xs : List Bool) :
    TurnAccounting.changesFrom a (directionsFrom a xs) = TangoSquared.changesFrom a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    rw [directionsFrom, edgeDirection_bool]
    by_cases h : a = b
    · subst b
      simpa only [if_pos rfl, ↓reduceIte, List.nil_append, TangoSquared.changesFrom,
        edgeChange_self, Nat.zero_add] using ih a
    · simp only [List.singleton_append, TurnAccounting.changesFrom,
        TurnAccounting.turn, TangoSquared.changesFrom, edgeChange, if_neg h]
      rw [ih b]

/-- Every change in a closed binary key word is a turn. -/
theorem cyclicTurns_binary_directions (a : Bool) (xs : List Bool)
    (hclosed : xs.getLastD a = a) :
    TurnAccounting.cyclicTurns (directionsFrom a xs) = TangoSquared.changesFrom a xs := by
  have hlast := (directionsFrom_bool_last a xs).trans hclosed
  have hchanges := changesFrom_directionsFrom_bool a xs
  cases hd : directionsFrom a xs with
  | nil => simpa [hd, TurnAccounting.cyclicTurns, TurnAccounting.changesFrom] using hchanges
  | cons b bs =>
    have hl : bs.getLastD b = a := by simpa only [hd, List.getLastD_cons] using hlast
    simpa only [hd, TurnAccounting.cyclicTurns, List.getLastD_cons, hl] using hchanges

theorem wordTurns_bool (xs : List Bool) : wordTurns xs = cyclicAlternations xs := by
  cases xs with
  | nil => rfl
  | cons a as =>
    exact cyclicTurns_binary_directions (as.getLastD a) (a :: as) (by rw [List.getLastD_cons])

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

theorem edgeDirection_strictMono (f : α → β) (hf : StrictMono f) (a b : α) :
    edgeDirection (f a) (f b) = edgeDirection a b := by
  simp [edgeDirection, hf.injective.eq_iff, hf.lt_iff_lt]

theorem directionsFrom_strictMono (f : α → β) (hf : StrictMono f) (a : α) (xs : List α) :
    directionsFrom (f a) (xs.map f) = directionsFrom a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons, directionsFrom, edgeDirection_strictMono f hf, ih]

/-- Relabeling an ordered alphabet without changing its order preserves every turn. -/
theorem wordTurns_strictMono (f : α → β) (hf : StrictMono f) (xs : List α) :
    wordTurns (xs.map f) = wordTurns xs := by
  cases xs with
  | nil => rfl
  | cons a as =>
    simp only [List.map_cons, wordTurns, cyclicDirections, List.getLastD_map]
    rw [← List.map_cons, directionsFrom_strictMono f hf]

/-- A word confined to one fine cell has no directions and no turns. -/
theorem directionsFrom_constant (a : α) (xs : List α) (h : ∀ x ∈ xs, x = a) :
    directionsFrom a xs = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    subst x
    simp only [directionsFrom, edgeDirection_self, List.nil_append]
    exact ih (fun y hy => h y (by simp [hy]))

theorem wordTurns_constant (a : α) (xs : List α) (h : ∀ x ∈ xs, x = a) :
    wordTurns xs = 0 := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    have hx := h x (by simp)
    subst x
    have hl : xs.getLastD a = a := h _ List.getLastD_mem_cons
    simp only [wordTurns, cyclicDirections, hl, directionsFrom_constant a (a :: xs) h]
    rfl

end TangoSquared.CyclicRuns

namespace TangoSquared
open Primary CyclicRuns

/-- The fine labels of a singleton depth fragment are precisely its two child labels. -/
theorem leaf_projection_eq_branch_embedding {H d : Nat} {u : Key}
    (hu : u.length = d) (hd : d < H) (xs : List Key) (hleaves : OnLeaves H xs) :
    (ownerWord u xs).map (List.take (d + 1)) =
      (xs.filterMap (branch u)).map (fun b => u ++ [b]) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : x.length = H := hleaves x (by simp)
    have ih' := ih (fun y hy => hleaves y (by simp [hy]))
    by_cases hp : u.IsPrefix x
    · have hlen : u.length < x.length := by omega
      obtain ⟨b, hb⟩ := branch_some_of_prefix hp hlen
      have htake : x.take (d + 1) = u ++ [b] := by
        rw [List.take_add_one, ← hu, ← List.prefix_iff_eq_take.mp hp]
        have hbit : x[u.length]? = some b := by simpa only [branch, if_pos hp] using hb
        rw [hbit]
        rfl
      simpa [ownerWord, hp, hb, htake] using congrArg (List.cons (u ++ [b])) ih'
    · have hb : branch u x = none := by simp [branch, hp]
      simpa [ownerWord, hp, hb] using ih'

/-- Each nonterminal singleton depth fragment contributes the owner's child alternations. -/
theorem singleton_fragment_owner_turns {H d : Nat} {u : Key}
    (hu : u ∈ level d) (hd : d < H) (xs : List Key) (hleaves : OnLeaves H xs) :
    wordTurns ((ownerWord u xs).map (List.take (min (d + 1) H))) =
      cyclicAlternations (xs.filterMap (branch u)) := by
  rw [Nat.min_eq_left (by omega), leaf_projection_eq_branch_embedding ((mem_level u d).1 hu) hd xs hleaves]
  have hf : StrictMono (fun b : Bool => u ++ [b]) := by
    intro a b hab
    exact List.Lex.append_left _ (List.Lex.rel hab) u
  rw [wordTurns_strictMono _ hf, wordTurns_bool]

/-- The final singleton depth consists of one leaf and contributes no turns. -/
theorem terminal_fragment_owner_turns {H : Nat} {u : Key}
    (hu : u ∈ level H) (xs : List Key) (hleaves : OnLeaves H xs) :
    wordTurns ((ownerWord u xs).map (List.take (min (H + 1) H))) = 0 := by
  apply wordTurns_constant u
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  obtain ⟨hxin, hprefix⟩ := List.mem_filter.mp hx
  have hp : u.IsPrefix x := of_decide_eq_true hprefix
  have hxH := hleaves x hxin
  have huH := (mem_level u H).1 hu
  have he : u = x := by
    have he := List.prefix_iff_eq_take.mp hp
    simpa only [huH, ← hxH, List.take_length] using he
  subst x
  simp [← huH]

/-- The depth-H potential is identically zero. -/
theorem fragmentPotential_terminal (H : Nat) (xs : List Key) (hleaves : OnLeaves H xs) :
    fragmentPotential H xs H H = 0 := by
  unfold fragmentPotential
  apply Finset.sum_eq_zero
  intro u hu
  rw [terminal_fragment_owner_turns hu xs hleaves]
  rfl


/-- A nonterminal singleton potential is the primary count on its owner level. -/
theorem fragmentPotential_singleton {H d : Nat} (hd : d < H)
    (xs : List Key) (hleaves : OnLeaves H xs) :
    fragmentPotential H xs d d =
      ∑ u ∈ level d, (cyclicAlternations (xs.filterMap (branch u)) : ℤ) := by
  unfold fragmentPotential
  apply Finset.sum_congr rfl
  intro u hu
  rw [singleton_fragment_owner_turns hu hd xs hleaves]

/-- All internal owners are partitioned exactly by their depth. -/
theorem level_eq_owner_fiber {H d : Nat} (hd : d < H) :
    level d = (owners H).filter (fun u => u.length = d) := by
  ext u
  simp only [mem_level, Finset.mem_filter, mem_owners]
  omega

/-- The complete concrete leaf potential equals the cyclic primary alternation count. -/
theorem binary_leaf_potential (H : Nat) (xs : List Key) (hleaves : OnLeaves H xs) :
    ∑ d ∈ Finset.Icc 0 H, fragmentPotential H xs d d = (cyclicPrimary H xs : ℤ) := by
  have hi : Finset.Icc 0 H = Finset.range (H + 1) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hi, Finset.sum_range_succ, fragmentPotential_terminal H xs hleaves, add_zero]
  have hlevels : ∑ d ∈ Finset.range H, fragmentPotential H xs d d =
      ∑ d ∈ Finset.range H, ∑ u ∈ (owners H).filter (fun u => u.length = d),
        (cyclicAlternations (xs.filterMap (branch u)) : ℤ) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hd' : d < H := Finset.mem_range.mp hd
    rw [fragmentPotential_singleton hd' xs hleaves, level_eq_owner_fiber hd']
  rw [hlevels]
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := owners H) (t := Finset.range H) (g := fun u : Key => u.length)
    (fun u hu => Finset.mem_range.mpr ((mem_owners u H).1 hu))
    (fun u => (cyclicAlternations (xs.filterMap (branch u)) : ℤ))
  rw [hfiber]
  unfold cyclicPrimary
  generalize owners H = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert u s hu ih => simp only [Finset.sum_insert hu, Int.natCast_add, ih]

/-- The actual fragment telescope is therefore paid by the primary leaf budget. -/
theorem fragment_potential_telescope_primary (H : Nat) (xs : List Key)
    (hleaves : OnLeaves H xs) :
    (∑ s ∈ (DepthTree.midpoint 0 H (Nat.zero_le H)).nodes,
      splitPotentialDifference H xs s) + fragmentPotential H xs 0 H =
        (cyclicPrimary H xs : ℤ) := by
  rw [fragment_potential_telescope, binary_leaf_potential H xs hleaves]

end TangoSquared
