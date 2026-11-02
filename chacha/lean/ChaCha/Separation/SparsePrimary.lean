import ChaCha.AnchorPrimary

/-!
# The primary comb estimate for sparse binary keys

On keys with at most one true bit, the existing complete-reference primary
counter is at most twice the request count. Unary portions of the reference
need not be removed explicitly. The proof charges a branching alternation
to a request whose unique true bit occurs at that branching level.
-/

namespace ChaCha.Separation

open Primary AnchorPrimary

theorem child_true_count {keys : List Key} {budget : Nat}
    (bounded : ∀ key ∈ keys, key.count true ≤ budget)
    (direction : Bool) {key : Key} (member : key ∈ child direction keys) :
    key.count true+(if direction then 1 else 0) ≤ budget := by
  obtain ⟨original,present,selected⟩ := List.mem_filterMap.mp member
  cases original with
  | nil => simp at selected
  | cons bit tail =>
      change (if bit = direction then some tail else none) = some key at selected
      by_cases same : bit = direction
      · subst bit
        have equal : tail = key := by simpa using selected
        subst key
        cases direction <;> simpa [List.count_cons,Nat.add_comm] using bounded _ present
      · simp [same] at selected

theorem child_true_eq_nil {keys : List Key}
    (zero : ∀ key ∈ keys, key.count true = 0) : child true keys = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro key member
  have impossible := child_true_count (budget := 0) (fun key present => (zero key present).le) true member
  simp at impossible

theorem children_length_le (keys : List Key) :
    (child false keys).length+(child true keys).length ≤ keys.length := by
  induction keys with
  | nil => simp [child]
  | cons key keys ih =>
      cases key with
      | nil => simp only [child,List.filterMap_cons,List.length_cons] at *; omega
      | cons bit tail => cases bit <;> simp_all [child] <;> omega

theorem primary_zero_true (height : Nat) (keys : List Key)
    (zero : ∀ key ∈ keys, key.count true = 0) : primaryCount height keys = 0 := by
  induction height generalizing keys with
  | zero => simp [primaryCount,primaryAlternations,owners]
  | succ height ih =>
      have leftZero : ∀ key ∈ child false keys, key.count true = 0 := by
        intro key member
        have bound := child_true_count (budget := 0) (fun key present => (zero key present).le) false member
        simpa using bound
      have empty := child_true_eq_nil zero
      have root := root_bound false keys
      simp only [Bool.not_false,empty,List.length_nil,Nat.mul_zero,Nat.le_zero] at root
      rw [primary_succ,root,ih _ leftZero,empty]
      simp [primaryCount,primaryAlternations,alternations]

/-- The bound is uniform in the ambient reference height and holds for any
ordering and multiplicity of the sparse keys, including the empty word. -/
theorem primary_one_true (height : Nat) (keys : List Key)
    (sparse : ∀ key ∈ keys, key.count true ≤ 1) : primaryCount height keys ≤ 2*keys.length := by
  induction height generalizing keys with
  | zero => simp [primaryCount,primaryAlternations,owners]
  | succ height ih =>
      have leftSparse : ∀ key ∈ child false keys, key.count true ≤ 1 := by
        intro key member
        simpa using child_true_count sparse false member
      have rightZero : ∀ key ∈ child true keys, key.count true = 0 := by
        intro key member
        have bound := child_true_count sparse true member
        change key.count true+1 ≤ 1 at bound
        omega
      have left := ih _ leftSparse
      have right := primary_zero_true height _ rightZero
      have root := root_bound false keys
      simp only [Bool.not_false] at root
      have total := children_length_le keys
      rw [primary_succ,right]
      omega

end ChaCha.Separation
