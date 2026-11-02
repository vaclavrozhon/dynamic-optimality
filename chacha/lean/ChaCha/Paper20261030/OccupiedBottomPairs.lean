import ChaCha.Paper20261030.ReferenceHeight

/-! The manuscript appendix's embedding for arbitrary universe sizes.
With `pairs <= n <= 2*pairs` and `extra = n-pairs`, the first `2*extra`
ranks are unchanged and the remaining ranks occupy the remaining even
leaves. Every bottom sibling pair is occupied. -/

namespace ChaCha.Paper20261030.OccupiedBottomPairs

def embed (extra rank : Nat) : Nat := if rank < 2*extra then rank else 2*rank-2*extra

theorem embed_strictMono (extra : Nat) : StrictMono (embed extra) := by
  intro a b smaller
  unfold embed
  split <;> split <;> omega

theorem embed_next (extra rank : Nat) : embed extra (rank+1) ≤ embed extra rank+2 := by
  unfold embed
  split <;> split <;> omega

theorem embed_range {pairs n : Nat} (lower : pairs ≤ n) (upper : n ≤ 2*pairs)
    {rank : Nat} (member : rank < n) : embed (n-pairs) rank < 2*pairs := by
  unfold embed
  split <;> omega

theorem even_occupied {pairs n : Nat} (lower : pairs ≤ n) (upper : n ≤ 2*pairs)
    {pair : Nat} (member : pair < pairs) :
    ∃ rank < n, embed (n-pairs) rank = 2*pair := by
  by_cases first : pair < n-pairs
  · exact ⟨2*pair,by omega,by simp [embed,show 2*pair < 2*(n-pairs) by omega]⟩
  · refine ⟨pair+(n-pairs),by omega,?_⟩
    simp only [embed,if_neg (show ¬pair+(n-pairs) < 2*(n-pairs) by omega)]
    omega

theorem odd_occupied_iff {pairs n pair : Nat} (lower : pairs ≤ n) (upper : n ≤ 2*pairs) :
    (∃ rank < n, embed (n-pairs) rank = 2*pair+1) ↔ pair < n-pairs := by
  constructor
  · rintro ⟨rank,member,equal⟩
    unfold embed at equal
    split at equal <;> omega
  · intro member
    refine ⟨2*pair+1,by omega,?_⟩
    simp [embed,show 2*pair+1 < 2*(n-pairs) by omega]

theorem full_identity {pairs rank : Nat} (member : rank < 2*pairs) :
    embed (2*pairs-pairs) rank = rank := by
  have extra : 2*pairs-pairs = pairs := by omega
  simp [embed,extra,member]

/-- Every nontrivial universe has exactly the scale used in the appendix:
`N = 2^(h+1)`, `N/2 < n <= N < 2n`. -/
theorem reference_scale (n : Nat) (nontrivial : 2 ≤ n) :
    ∃ h : Nat, 2^h < n ∧ n ≤ 2^(h+1) ∧ 2^(h+1) < 2*n := by
  have positive := Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < n)
  have small := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega : 1 < n)
  have large := Nat.le_pow_clog (by decide : 1 < 2) n
  let h := (Nat.clog 2 n).pred
  have height : h+1 = Nat.clog 2 n := by dsimp [h]; omega
  refine ⟨h,small,?_,?_⟩
  · simpa only [height] using large
  · rw [pow_succ,Nat.mul_comm]
    exact Nat.mul_lt_mul_of_pos_left small (by decide)

/-- Every internal node above the bottom level contains an actual key
in each half; at the bottom level its even leaf is always present. -/
theorem every_pair_nonempty {pairs n : Nat} (lower : pairs ≤ n) (upper : n ≤ 2*pairs)
    {pair : Nat} (member : pair < pairs) :
    ∃ rank < n, embed (n-pairs) rank / 2 = pair := by
  obtain ⟨rank,valid,equal⟩ := even_occupied lower upper member
  exact ⟨rank,valid,by rw [equal]; omega⟩

end ChaCha.Paper20261030.OccupiedBottomPairs
