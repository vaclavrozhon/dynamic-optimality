import MultiSplay.EndpointCounterBound
import Splay.Accounting.OfflineNormalForm

/-!
# A balanced reference on exactly the original keys

The endpoint lower bound applies to an arbitrary indexed reference. Choosing
an existing balanced BST makes its exponential-in-height initialization term
linear in the original universe, without adding keys to the MultiSplay tree.
-/

namespace MultiSplay

open DynamicOptimality

noncomputable def balancedReference (n : Nat) : BST 0 n :=
  Splay.Accounting.OfflineNormalForm.balancedTree n

theorem balancedReference_height_le (n : Nat) :
    (balancedReference n).height ≤ Nat.clog 2 (n+1) :=
  Splay.Accounting.OfflineNormalForm.balancedTree_height_le n

theorem balancedReference_height_le_log (n : Nat) :
    (balancedReference n).height ≤ 2*Splay.Analysis.stabilizedLog n :=
  (balancedReference_height_le n).trans
    (Splay.Accounting.OfflineNormalForm.clog_succ_le_two_stabilizedLog n)

/-- The lower-bound initialization counts at most twice the actual keys. -/
theorem balancedReference_initialization_le (n : Nat) :
    2^(balancedReference n).height-1 ≤ 2*n := by
  have height := balancedReference_height_le n
  by_cases zero : n = 0
  · subst n
    have trivial : (balancedReference 0).height = 0 := by simpa using height
    simp [trivial]
  · have positive : 1 < n+1 := by omega
    have power := Nat.pow_pred_clog_lt_self (b := 2) (by decide) positive
    rw [Nat.pred_eq_sub_one] at power
    have logPositive : 0 < Nat.clog 2 (n+1) := Nat.clog_pos (by decide) positive
    have exponent : Nat.clog 2 (n+1) = (Nat.clog 2 (n+1)-1)+1 := by omega
    have whole : 2^Nat.clog 2 (n+1) = 2^(Nat.clog 2 (n+1)-1)*2 := by
      conv_lhs => rw [exponent]
      exact Nat.pow_add_one _ _
    have bounded := Nat.pow_le_pow_right (by decide : 0 < 2) height
    rw [whole] at bounded
    omega

/-- All actual primary and secondary counters have a uniform OPT bound on
this exact-key reference, including the empty universe. -/
theorem balancedReference_counters_le_OPT {n : Nat} (requests : List (Fin n))
    (hierarchy : ChaCha.DepthTree 0 (balancedReference n).height)
    (state : EndpointEncoding.State) :
    requests.length +
      (EndpointEncoding.actualHistory state
        ((requests.map Fin.val).map (EndpointEncoding.nodeAddress (balancedReference n)))).length +
      Secondary.actualLedger hierarchy (fun _ => true) state
        ((requests.map Fin.val).map (EndpointEncoding.nodeAddress (balancedReference n))) ≤
      2137120*(OPT requests+n) := by
  have counters := EndpointEncoding.reference_actual_counters_le_OPT requests
    (balancedReference n) hierarchy state
  have initialization := balancedReference_initialization_le n
  omega

end MultiSplay
