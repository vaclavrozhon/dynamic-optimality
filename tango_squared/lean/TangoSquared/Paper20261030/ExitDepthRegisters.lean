import TangoSquared.Paper20261030.BitwiseExitDepth

/-! A tail-recursive, constant-register implementation of bit length.
`widthLoop` retains a fuel counter, the remaining word, and its processed
bit count. Its register invariant bounds every intermediate integer.
This performs at most H local arithmetic iterations and no tree access.
The BST cost model counts pointer instructions, not these computations.
-/

namespace TangoSquared.Paper20261030.Dyadic

theorem size_div_two_succ (word : Nat) (nonzero : word ≠ 0) :
    (word/2).size+1 = word.size := by
  induction word using Nat.binaryRec' with
  | zero => exact False.elim (nonzero rfl)
  | bit bit word positive ih =>
    rw [Nat.size_bit nonzero,Nat.bit_div_two]

def widthLoop : Nat → Nat → Nat → Nat
  | 0,_,count => count
  | fuel+1,word,count => if word = 0 then count else widthLoop fuel (word/2) (count+1)

theorem widthLoop_correct (fuel word count : Nat) (enough : word.size ≤ fuel) :
    widthLoop fuel word count = word.size+count := by
  induction fuel generalizing word count with
  | zero => simp only [widthLoop]; omega
  | succ fuel ih =>
    by_cases zero : word = 0
    · simp only [widthLoop,zero,ite_true,Nat.size_zero,Nat.zero_add]
    · have size := size_div_two_succ word zero
      rw [widthLoop,if_neg zero,ih (word/2) (count+1) (by omega)]
      omega

def computeExitDepth (height : Nat) (x z : Int) : Nat :=
  height - widthLoop height (x.toNat ^^^ z.toNat) 0

theorem computeExitDepth_correct {H : Nat} {x z : Int} (hx : ValidKey H x) (hz : ValidKey H z) :
    computeExitDepth H x z = exitDepth H x z := by
  simp only [computeExitDepth,widthLoop_correct _ _ _ (xor_size_le hx hz),Nat.add_zero,exitDepth]

structure WidthRegisters where
  fuel : Nat
  word : Nat
  count : Nat

def WidthRegisters.next (state : WidthRegisters) : Option WidthRegisters :=
  match state.fuel with
  | 0 => none
  | fuel+1 => if state.word = 0 then none else some ⟨fuel,state.word/2,state.count+1⟩

def WidthRegisters.Bounded (height : Nat) (state : WidthRegisters) : Prop :=
  state.fuel+state.count ≤ height ∧ state.word.size ≤ state.fuel

theorem WidthRegisters.bounded_next {H : Nat} {before after : WidthRegisters}
    (bounded : before.Bounded H) (step : before.next = some after) : after.Bounded H := by
  rcases before with ⟨fuel,word,count⟩
  cases fuel with
  | zero => simp [next] at step
  | succ fuel =>
    by_cases zero : word = 0
    · simp [next,zero] at step
    · simp only [next,zero,ite_false,Option.some.injEq] at step
      subst after
      have size := size_div_two_succ word zero
      unfold Bounded at *
      dsimp at *
      omega

theorem WidthRegisters.register_bounds {H : Nat} {state : WidthRegisters} (bounded : state.Bounded H) :
    state.fuel ≤ H ∧ state.count ≤ H ∧ state.word < 2^H := by
  have size : state.word.size ≤ H := by obtain ⟨first,last⟩ := bounded; omega
  exact ⟨by obtain ⟨first,last⟩ := bounded; omega,
    by obtain ⟨first,last⟩ := bounded; omega,Nat.size_le.mp size⟩

theorem WidthRegisters.initial_bounded {H : Nat} {x z : Int} (hx : ValidKey H x) (hz : ValidKey H z) :
    (WidthRegisters.mk H (x.toNat ^^^ z.toNat) 0).Bounded H :=
  ⟨by simp,xor_size_le hx hz⟩

end TangoSquared.Paper20261030.Dyadic
