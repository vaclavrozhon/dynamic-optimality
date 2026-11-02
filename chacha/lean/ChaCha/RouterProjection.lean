import Mathlib.Data.Finset.Max

/-!
# The structural kernel of alphabetic router projection

`Router.prune` retains selected external leaves and suppresses unary vertices.
The results below concern this topology, its leaf word, and abstract successor
rounding. They do not assert a BST simulation, history transport, or a cost bound.
No actual separator labels occur here: those are reassigned from the final
ordered retained port word in the proposed physical compiler.
-/

namespace ChaCha.RouterProjection

inductive Router (α : Type*) where
  | empty : Router α
  | leaf : α → Router α
  | fork : Router α → Router α → Router α
  deriving DecidableEq

namespace Router

variable {α : Type*}

/-- Remove a unary vertex; retain a genuine binary split. -/
def join : Router α → Router α → Router α
  | .empty, r => r
  | l, .empty => l
  | l, r => .fork l r

@[simp] theorem join_empty (l : Router α) : join l .empty = l := by
  cases l <;> rfl

@[simp] theorem empty_join (r : Router α) : join .empty r = r := rfl

def prune (p : α → Bool) : Router α → Router α
  | .empty => .empty
  | .leaf a => if p a then .leaf a else .empty
  | .fork l r => join (prune p l) (prune p r)

def leaves : Router α → List α
  | .empty => []
  | .leaf a => [a]
  | .fork l r => leaves l ++ leaves r

def height : Router α → Nat
  | .empty => 0
  | .leaf _ => 0
  | .fork l r => max (height l) (height r) + 1

@[simp] theorem leaves_join (l r : Router α) :
    leaves (join l r) = leaves l ++ leaves r := by
  cases l <;> cases r <;> simp [join, leaves]

@[simp] theorem prune_join (p : α → Bool) (l r : Router α) :
    prune p (join l r) = join (prune p l) (prune p r) := by
  cases l <;> cases r <;>
    first | rfl | simp only [join_empty, prune]

/-- Projection does not reorder retained external ports. -/
theorem leaves_prune (p : α → Bool) (t : Router α) :
    leaves (prune p t) = (leaves t).filter p := by
  induction t with
  | empty => simp [prune, leaves]
  | leaf a => cases hp : p a <;> simp [prune, leaves, hp]
  | fork l r ihl ihr => simp [prune, leaves, ihl, ihr]

/-- Successive physical leaf restrictions compose by intersection. -/
theorem prune_prune (p q : α → Bool) (t : Router α) :
    prune p (prune q t) = prune (fun a => q a && p a) t := by
  induction t with
  | empty => rfl
  | leaf a => cases hp : p a <;> cases hq : q a <;> simp [prune, hp, hq]
  | fork l r ihl ihr => simp [prune, prune_join, ihl, ihr]

/-- A smaller retained set can be projected directly or through a larger set. -/
theorem prune_nested (p q : α → Bool)
    (hpq : ∀ a, p a = true → q a = true) (t : Router α) :
    prune p (prune q t) = prune p t := by
  rw [prune_prune]
  congr 1
  funext a
  cases hp : p a with
  | false => simp
  | true => simp [hpq a hp]

theorem height_join_le (l r : Router α) :
    height (join l r) ≤ max (height l) (height r) + 1 := by
  cases l <;> cases r <;> simp [join, height]

/-- Pruning and unary contraction cannot increase router height. -/
theorem height_prune_le (p : α → Bool) (t : Router α) :
    height (prune p t) ≤ height t := by
  induction t with
  | empty => simp [prune, height]
  | leaf a => simp [prune]; split <;> simp [height]
  | fork l r ihl ihr =>
      exact (height_join_le _ _).trans
        (Nat.add_le_add_right (max_le_max ihl ihr) 1)

end Router

/-- Specification of rounding upward to the least retained port.
For a finite arm, a permanently retained terminal sentry supplies existence.
This specification also works on any partially ordered set where the least
retained upper bound exists. -/
structure UpwardRound {α : Type*} [PartialOrder α]
    (retained : Set α) (round : α → α) : Prop where
  retained_round : ∀ x, round x ∈ retained
  le_round : ∀ x, x ≤ round x
  least : ∀ x y, y ∈ retained → x ≤ y → round x ≤ y

namespace UpwardRound

variable {α : Type*} [PartialOrder α]
variable {J K : Set α} {rJ rK : α → α}

theorem idempotent (hJ : UpwardRound J rJ) (x : α) :
    rJ (rJ x) = rJ x := by
  apply le_antisymm
  · exact hJ.least _ _ (hJ.retained_round x) le_rfl
  · exact hJ.le_round _

/-- Rounding through a larger retained set cannot change final rounding
to a nested smaller retained set. -/
theorem nested (hJ : UpwardRound J rJ) (hK : UpwardRound K rK)
    (hJK : J ⊆ K) (x : α) : rJ (rK x) = rJ x := by
  have hmid : rK x ≤ rJ x :=
    hK.least x (rJ x) (hJK (hJ.retained_round x)) (hJ.le_round x)
  apply le_antisymm
  · exact hJ.least (rK x) (rJ x) (hJ.retained_round x) hmid
  · exact hJ.least x (rJ (rK x)) (hJ.retained_round (rK x))
      ((hK.le_round x).trans (hJ.le_round (rK x)))

end UpwardRound

namespace FiniteArm

variable {α : Type*} [LinearOrder α] [OrderTop α]

/-- The retained terminal/top port makes every upward search nonempty. -/
theorem eligible_nonempty (s : Finset α) (hs : ⊤ ∈ s) (x : α) :
    (s.filter (fun y => x ≤ y)).Nonempty := by
  exact ⟨⊤, Finset.mem_filter.mpr ⟨hs, le_top⟩⟩

/-- Concrete successor rounding on a finite retained arm alphabet. -/
def round (s : Finset α) (hs : ⊤ ∈ s) (x : α) : α :=
  (s.filter (fun y => x ≤ y)).min' (eligible_nonempty s hs x)

theorem round_spec (s : Finset α) (hs : ⊤ ∈ s) :
    UpwardRound (↑s : Set α) (round s hs) := by
  constructor
  · intro x
    exact (Finset.mem_filter.mp
      (Finset.min'_mem _ (eligible_nonempty s hs x))).1
  · intro x
    exact (Finset.mem_filter.mp
      (Finset.min'_mem _ (eligible_nonempty s hs x))).2
  · intro x y hy hxy
    exact Finset.min'_le _ y (Finset.mem_filter.mpr ⟨hy, hxy⟩)

theorem round_nested (j k : Finset α) (hj : ⊤ ∈ j) (hk : ⊤ ∈ k)
    (hjk : j ⊆ k) (x : α) :
    round j hj (round k hk x) = round j hj x := by
  exact UpwardRound.nested (round_spec j hj) (round_spec k hk) hjk x

end FiniteArm

end ChaCha.RouterProjection
