import ChaCha.Entropy.Histogram
import Lean.Elab.Tactic.Omega

/-! # A weighted median among the original ordered keys

Selecting the first occurrence whose cumulative weight crosses half
the total leaves at most half the weight on either side. No extra key
is inserted, and zero-weight entries are allowed by the selection lemma.
-/

namespace ChaCha.Entropy

theorem exists_weight_crossing (f : Int → Nat) (keys : List Int) (target : Nat)
    (below : target < weight f keys) :
    ∃ left key right, keys = left ++ key::right ∧
      weight f left ≤ target ∧ target < weight f left + f key := by
  induction keys generalizing target with
  | nil => simp only [weight_nil] at below; omega
  | cons key keys ih =>
      by_cases before : target < f key
      · exact ⟨[],key,keys,rfl,by simp,by simpa using before⟩
      · have remaining : target-f key < weight f keys := by
          simp only [weight_cons] at below
          omega
        obtain ⟨left,pivot,right,same,low,high⟩ := ih (target-f key) remaining
        refine ⟨key::left,pivot,right,by simp only [List.cons_append,same],?_,?_⟩
        · simp only [weight_cons]
          omega
        · simp only [weight_cons]
          omega

theorem exists_weighted_median (f : Int → Nat) (keys : List Int)
    (positive : 0 < weight f keys) :
    ∃ left key right, keys = left ++ key::right ∧
      2*weight f left ≤ weight f keys ∧ 2*weight f right ≤ weight f keys ∧ 0 < f key := by
  obtain ⟨left,key,right,same,low,high⟩ := exists_weight_crossing f keys (weight f keys/2) (by omega)
  have total : weight f keys = weight f left+f key+weight f right := by
    rw [same,weight_append,weight_cons]
    omega
  exact ⟨left,key,right,same,by omega,by omega,by omega⟩

theorem weight_pos_of_nonempty (f : Int → Nat) (keys : List Int) (nonempty : keys ≠ [])
    (positive : ∀ key ∈ keys, 0 < f key) : 0 < weight f keys := by
  cases keys with
  | nil => contradiction
  | cons key keys =>
      have head := positive key (by simp)
      simp only [weight_cons]
      omega

end ChaCha.Entropy
