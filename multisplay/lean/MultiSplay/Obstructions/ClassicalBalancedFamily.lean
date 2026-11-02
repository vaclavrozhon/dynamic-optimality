import MultiSplay.Obstructions.ClassicalMaximum

/-! The balanced auxiliary family from `ClassicalPotentialObstruction.tex`.
For height 2s+1, the first access performs s literal right-right doubles.
The predecessor subtree is right-spine left-heavy, so its subsequent splay
cannot erase the strictly positive first-splay potential increase. -/

namespace MultiSplay.Obstructions.Classical

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree

/-- A full balanced tree, parameterized by its maximum label. The family
used below has enough labels to avoid truncated subtraction. -/
def perfect : Nat → Nat → RawTree Nat
  | 0,_ => .empty
  | height+1,key => .node (perfect height (key-2^height)) (key+1-2^height) (perfect height key)

 theorem perfect_two (height key : Nat) :
    perfect (height+2) key =
      .node (perfect (height+1) (key-2^(height+1))) (key+1-2^(height+1))
        (.node (perfect height (key-2^height)) (key+1-2^height) (perfect height key)) := rfl

 theorem perfect_size (height key : Nat) : (perfect height key).size+1 = 2^height := by
  induction height generalizing key with
  | zero => rfl
  | succ height ih =>
    have left := ih (key-2^height)
    have right := ih key
    simp only [perfect,size,pow_succ]
    omega

def leftBlock (s key : Nat) : RawTree Nat :=
  .node (perfect (2*s+2) (key-2^(2*s+2))) (key+1-2^(2*s+2))
    (perfect (2*s+1) (key-2^(2*s+1)))

def maximumLeft : Nat → Nat → RawTree Nat
  | 0,_ => .empty
  | s+1,key => .node (leftBlock s key) (key+1-2^(2*s+1)) (maximumLeft s key)

 theorem maximum_doubles (s key : Nat) :
    MaxDoubles key (perfect (2*s+1) key) (.node (maximumLeft s key) key .empty) s := by
  induction s with
  | zero => simpa only [perfect,maximumLeft,Nat.mul_zero,Nat.zero_add,pow_zero,Nat.add_sub_cancel] using MaxDoubles.refl (.node .empty key .empty)
  | succ s ih =>
    rw [show 2*(s+1)+1 = (2*s+1)+2 by omega,perfect_two]
    have trace := (ih.right (perfect (2*s+1) (key-2^(2*s+1))) (key+1-2^(2*s+1))).right
      (perfect (2*s+2) (key-2^(2*s+2))) (key+1-2^(2*s+2))
    exact trace.append (.step (.root _ _ _ _ _) (.refl _))

 theorem maximum_splay (s key : Nat) :
    Auxiliary.Splay key (perfect (2*s+1) key) (.node (maximumLeft s key) key .empty) (2*s) :=
  (maximum_doubles s key).finish

 theorem maximumLeft_size (s key : Nat) : (maximumLeft s key).size+2 = 2^(2*s+1) := by
  have same := (maximum_splay s key).size_eq
  have total := perfect_size (2*s+1) key
  simp only [size,Nat.add_zero] at same
  omega

 theorem leftBlock_size (s key : Nat) : (leftBlock s key).size+1 = 3*2^(2*s+1) := by
  have left := perfect_size (2*s+2) (key-2^(2*s+2))
  have right := perfect_size (2*s+1) (key-2^(2*s+1))
  have power : 2^(2*s+2) = 2*2^(2*s+1) := by
    rw [show 2*s+2 = (2*s+1)+1 by omega,pow_succ,Nat.mul_comm]
  have left' := left.trans power
  simp only [leftBlock,size]
  omega

 theorem maximumLeft_heavy (s key : Nat) : RightHeavy (maximumLeft s key) := by
  induction s with
  | zero => trivial
  | succ s ih =>
    have left := leftBlock_size s key
    have right := maximumLeft_size s key
    exact ⟨by omega,ih⟩

 theorem maximumLeft_spine (s key : Nat) (positive : 0 < s) :
    MaxSpine (key-1) (maximumLeft s key) (s-1) := by
  induction s with
  | zero => omega
  | succ s ih =>
    cases s with
    | zero =>
      have same : key+1-2 = key-1 := by omega
      simpa only [maximumLeft,Nat.mul_zero,Nat.zero_add,pow_one,same,Nat.sub_self]
        using MaxSpine.root (key := key-1) (leftBlock 0 key)
    | succ s =>
      have rest := ih (by omega)
      simpa only [maximumLeft,Nat.add_sub_cancel] using MaxSpine.right (leftBlock (s+1) key)
        (key+1-2^(2*(s+1)+1)) rest

 theorem right_context_difference {α : Type*} (left before after : RawTree α) (root : α)
    (same : before.size = after.size) :
    potential (.node left root after)-potential (.node left root before) = potential after-potential before := by
  simp only [potential,same]
  ring

 theorem maximum_potential_gain (s key : Nat) :
    potential (perfect (2*s+1) key)+(s : ℝ)*Real.logb 2 6 ≤
        potential (.node (maximumLeft s key) key .empty) ∧
      (0 < s → potential (perfect (2*s+1) key)+(s : ℝ)*Real.logb 2 6 <
        potential (.node (maximumLeft s key) key .empty)) := by
  induction s with
  | zero => simp [perfect,maximumLeft,potential]
  | succ s ih =>
    let a := perfect (2*s+2) (key-2^(2*s+2))
    let b := perfect (2*s+1) (key-2^(2*s+1))
    let c := maximumLeft s key
    let x := key+1-2^(2*s+2)
    let y := key+1-2^(2*s+1)
    have aSize := perfect_size (2*s+2) (key-2^(2*s+2))
    have bSize := perfect_size (2*s+1) (key-2^(2*s+1))
    have cSize := maximumLeft_size s key
    have power : 2^(2*s+2) = 2*2^(2*s+1) := by
      rw [show 2*s+2 = (2*s+1)+1 by omega,pow_succ,Nat.mul_comm]
    have aSize' := aSize.trans power
    have grow := double_increase a b c x y key (by dsimp [a,b]; omega) (by dsimp [b,c]; omega)
    have innerSize := (maximum_splay s key).size_eq
    have inside := right_context_difference b (perfect (2*s+1) key) (.node c key .empty) y innerSize
    have parentSize : (node b y (perfect (2*s+1) key)).size = (node b y (node c key empty)).size := by
      simp only [size,innerSize,c]
    have outside := right_context_difference a (node b y (perfect (2*s+1) key)) (node b y (node c key empty)) x parentSize
    rw [show 2*(s+1)+1 = (2*s+1)+2 by omega,perfect_two]
    change potential (node a x (node b y (perfect (2*s+1) key)))+((s+1 : Nat) : ℝ)*Real.logb 2 6 ≤
        potential (node (node (node a x b) y c) key empty) ∧
      (0 < s+1 → potential (node a x (node b y (perfect (2*s+1) key)))+((s+1 : Nat) : ℝ)*Real.logb 2 6 <
        potential (node (node (node a x b) y c) key empty))
    have first := ih.1
    change potential (perfect (2*s+1) key)+(s : ℝ)*Real.logb 2 6 ≤ potential (node c key empty) at first
    push_cast
    constructor
    · linarith
    · intro _
      linarith

/-- Two genuine bottom-up splays: maximum and then predecessor below it.
The first has 2s rotations, the second s−1, and the potential strictly
increases by more than s log₂ 6. -/
theorem two_splay_family (s key : Nat) (positive : 0 < s) :
    ∃ finalLeft : RawTree Nat,
      Auxiliary.Splay key (perfect (2*s+1) key) (.node (maximumLeft s key) key .empty) (2*s) ∧
      Auxiliary.Splay (key-1) (maximumLeft s key) (.node finalLeft (key-1) .empty) (s-1) ∧
      2*s+(s-1) = 3*s-1 ∧
      potential (perfect (2*s+1) key)+(s : ℝ)*Real.logb 2 6 <
        potential (.node (.node finalLeft (key-1) .empty) key .empty) := by
  obtain ⟨finalLeft,predecessor,monotone⟩ :=
    (maximumLeft_spine s key positive).splay_nondecrease (maximumLeft_heavy s key)
  have gain := (maximum_potential_gain s key).2 positive
  have same := predecessor.size_eq
  have total : potential (node (maximumLeft s key) key empty) ≤
      potential (node (node finalLeft (key-1) empty) key empty) := by
    change potential (maximumLeft s key)+0+rank ((maximumLeft s key).size+1+0) ≤
      potential (node finalLeft (key-1) empty)+0+rank ((node finalLeft (key-1) empty).size+1+0)
    rw [same]
    linarith
  exact ⟨finalLeft,maximum_splay s key,predecessor,by omega,gain.trans_le total⟩

end MultiSplay.Obstructions.Classical
