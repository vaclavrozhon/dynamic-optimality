import TangoSquared.Demands

/-!
# Elementary flip accounting for nested preference histories

These lemmas formalize the binary-word part of the tertiary conversion and
the cyclic left-write estimate used in the synchronized-copy obstruction.
They do not formalize the owner-indexed emission construction or either
complete Tango-cubed theorem.
-/

namespace TangoSquared.FlipAccounting

/-- Potential of a bit pointing left (`false`). -/
def leftPotential (b : Bool) : Nat := if b then 0 else 1

/-- Changing the initial state affects a nonempty scan by at most one. -/
theorem changesFrom_initial_le (a b : Bool) (xs : List Bool) :
    changesFrom a xs ≤ changesFrom b xs + 1 := by
  cases xs with
  | nil => simp
  | cons c cs =>
    cases a <;> cases b <;> cases c <;> simp [changesFrom, edgeChange] <;> omega

/-- Directed R-to-L changes pay for all changes, with a one-bit endpoint credit. -/
theorem changesFrom_le_twice_rlFrom (a : Bool) (xs : List Bool) :
    changesFrom a xs ≤ 2 * rlFrom a xs + leftPotential a := by
  induction xs generalizing a with
  | nil => simp [leftPotential]
  | cons b bs ih =>
    have h := ih b
    cases a <;> cases b <;>
      simp_all [changesFrom, edgeChange, rlFrom, rlCharge, leftPotential] <;> omega

theorem alternations_le_twice_rlCount_add_one (xs : List Bool) :
    alternations xs ≤ 2 * rlCount xs + 1 := by
  cases xs with
  | nil => simp [rlCount, rlFrom]
  | cons b bs =>
    have h := changesFrom_le_twice_rlFrom b bs
    cases b <;>
      simp_all [alternations, rlCount, rlFrom, rlCharge, leftPotential]
    all_goals omega

theorem changesFrom_le_alternations_add_one (a : Bool) (xs : List Bool) :
    changesFrom a xs ≤ alternations xs + 1 := by
  cases xs with
  | nil => simp
  | cons b bs =>
    cases a <;> cases b <;> simp [changesFrom, alternations, edgeChange] <;> omega

theorem alternations_cons_le_add_one (a : Bool) (xs : List Bool) :
    alternations (a :: xs) ≤ alternations xs + 1 := by
  exact changesFrom_le_alternations_add_one a xs

/-- A possible exceptional first head and an arbitrary initial bit cost at most
three beyond twice the R-to-L count of the regular head word. -/
theorem exceptional_head_bound (initial : Bool) (first : Option Bool)
    (heads : List Bool) :
    changesFrom initial (first.toList ++ heads) ≤ 2 * rlCount heads + 3 := by
  have h := alternations_le_twice_rlCount_add_one heads
  cases first with
  | none =>
    have h' := changesFrom_le_alternations_add_one initial heads
    simp only [Option.toList_none, List.nil_append]
    omega
  | some b =>
    have h' := changesFrom_le_alternations_add_one initial (b :: heads)
    have h'' := alternations_cons_le_add_one b heads
    simp only [Option.toList_some, List.singleton_append]
    omega

/-- A monotone nonempty L*R* block with duplicate letters suppressed. -/
inductive Block where
  | left
  | right
  | reset
  deriving DecidableEq

def Block.word : Block → List Bool
  | .left => [false]
  | .right => [true]
  | .reset => [false, true]

def Block.head : Block → Bool
  | .left => false
  | .right => true
  | .reset => false

def Block.resets : Block → Nat
  | .left => 0
  | .right => 0
  | .reset => 1

/-- Restoring each mixed block's final R costs at most two changes globally,
including its effect on the following block. -/
theorem restore_resets (initial : Bool) (blocks : List Block) :
    changesFrom initial (blocks.flatMap Block.word) ≤
      changesFrom initial (blocks.map Block.head) +
        2 * (blocks.map Block.resets).sum := by
  induction blocks generalizing initial with
  | nil => simp
  | cons b bs ih =>
    cases b with
    | left =>
      have h := ih false
      simp only [List.flatMap_cons, Block.word, List.singleton_append,
        List.map_cons, Block.head, Block.resets, List.sum_cons,
        Nat.zero_add, changesFrom_cons]
      omega
    | right =>
      have h := ih true
      simp only [List.flatMap_cons, Block.word, List.singleton_append,
        List.map_cons, Block.head, Block.resets, List.sum_cons,
        Nat.zero_add, changesFrom_cons]
      omega
    | reset =>
      have h := ih true
      have hc := changesFrom_initial_le true false (bs.map Block.head)
      simp only [List.flatMap_cons, Block.word, List.cons_append,
        List.nil_append, List.map_cons, Block.head, Block.resets,
        List.sum_cons, changesFrom_cons]
      have he : edgeChange false true = 1 := by decide
      rw [he]
      omega

/-- The numerical head/reset estimate used for each nonterminal tertiary bit. -/
theorem head_reset_bound (initial : Bool) (blocks : List Block)
    (regularHeads : List Bool) (first : Option Bool)
    (hheads : blocks.map Block.head = first.toList ++ regularHeads) :
    changesFrom initial (blocks.flatMap Block.word) ≤
      2 * rlCount regularHeads + 2 * (blocks.map Block.resets).sum + 3 := by
  have hr := restore_resets initial blocks
  have hh := exceptional_head_bound initial first regularHeads
  rw [hheads] at hr
  omega

/-- A left write can pay for entering and later leaving the left state.
The endpoint potential makes this valid without a cyclicity assumption. -/
theorem changesFrom_left_writes (initial : Bool) (xs : List Bool) :
    changesFrom initial xs + leftPotential (xs.getLastD initial) ≤
      2 * xs.count false + leftPotential initial := by
  induction xs generalizing initial with
  | nil => simp
  | cons b bs ih =>
    have h := ih b
    have hl : (b :: bs).getLastD initial = bs.getLastD b := List.getLastD_cons
    rw [hl]
    cases initial <;> cases b <;>
      simp_all [changesFrom, edgeChange, leftPotential] <;> omega

/-- In a closed bit history, changes are at most twice the left writes.
Owner copies can be summed independently; no sharing is assumed. -/
theorem closed_changes_le_twice_left_writes (initial : Bool) (xs : List Bool)
    (closed : xs.getLastD initial = initial) :
    changesFrom initial xs ≤ 2 * xs.count false := by
  have h := changesFrom_left_writes initial xs
  rw [closed] at h
  omega

end TangoSquared.FlipAccounting
