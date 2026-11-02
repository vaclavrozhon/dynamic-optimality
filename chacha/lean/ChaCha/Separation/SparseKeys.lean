import ChaCha.Separation.NumericPrimary
import ChaCha.Separation.SparsePrimary
import ChaCha.Separation.RankEmbedding

/-!
# Sparse original keys for the explicit separation

Rank zero is key zero; positive rank j is key 2^(2^(j-1)). Each key has
at most one nonzero bit. Repeated bit reversal on the ranks retains its
robust geometric certificate under this increasing embedding, whereas
the actual fixed-reference primary counter is linear in the word length.
-/

namespace ChaCha.Separation

open Primary AnchorPrimary PreferredProjection
open Paper20261030 Paper20261030.Dyadic Paper20261030.Rectangles

def sparseKey : Nat → Int
  | 0 => 0
  | index+1 => 2^(2^index)

theorem sparseKey_increasing : StrictMono sparseKey := by
  apply strictMono_nat_of_lt_succ
  intro index
  cases index with
  | zero => simp [sparseKey]
  | succ index =>
      exact pow_lt_pow_right₀ (by decide : (1 : Int) < 2)
        (pow_lt_pow_right₀ (by decide : (1 : Nat) < 2) (by omega))

def sparseBits (height : Nat) : Nat → Key
  | 0 => List.replicate height false
  | index+1 => List.replicate (height-(2^index+1)) false ++ true::List.replicate (2^index) false

theorem descendantIndex_append (owner : Int) (first last : Key) :
    descendantIndex owner (first++last) = descendantIndex (descendantIndex owner first) last := by
  induction first generalizing owner with
  | nil => rfl
  | cons bit first ih => simpa only [List.cons_append,descendantIndex] using ih _

theorem descendantIndex_false (owner : Int) (count : Nat) :
    descendantIndex owner (List.replicate count false) = 2^count*owner := by
  induction count generalizing owner with
  | zero => simp [descendantIndex]
  | succ count ih =>
      rw [List.replicate_succ,descendantIndex,ih,pow_succ]
      simp only [Bool.false_eq_true,if_false,Int.add_zero]
      exact (mul_assoc _ _ _).symm

theorem sparseBits_value (height index : Nat) :
    descendantIndex 0 (sparseBits height index) = sparseKey index := by
  cases index with
  | zero => simp [sparseBits,sparseKey,descendantIndex_false]
  | succ index =>
      simp [sparseBits,sparseKey,descendantIndex_append,descendantIndex_false,descendantIndex]

theorem count_false (count : Nat) : (List.replicate count false).count true = 0 := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ,List.count_cons,ih]

theorem sparseBits_count (height index : Nat) : (sparseBits height index).count true ≤ 1 := by
  cases index <;> simp [sparseBits,List.count_append,List.count_cons,count_false]

/-- The height of the original perfect primary reference. -/
def sparseHeight (count : Nat) : Nat := 2^(count-1)

theorem sparseBits_length {count index : Nat} (valid : index < count) :
    (sparseBits (sparseHeight count) index).length = sparseHeight count := by
  cases index with
  | zero => simp [sparseBits]
  | succ index =>
      have power : 2^index < sparseHeight count :=
        pow_lt_pow_right₀ (by decide : (1 : Nat) < 2) (by omega)
      simp only [sparseBits,List.length_append,List.length_replicate,List.length_cons]
      omega

theorem sparseKey_valid {count index : Nat} (valid : index < count) :
    ValidKey (sparseHeight count) (sparseKey index) := by
  apply (canonical_zero_mem _ _).mp
  have present := descendantIndex_mem (sparseBits (sparseHeight count) index) 0
  simpa only [sparseBits_length valid,sparseBits_value] using present

theorem sparse_primary_linear (count : Nat) (requests : List Nat)
    (valid : ∀ key ∈ requests, key < count) :
    (canonical (sparseHeight count) 0).primaryWilber (requests.map sparseKey) ≤ 2*requests.length := by
  let bits := requests.map (sparseBits (sparseHeight count))
  have lengths : ∀ key ∈ bits, key.length = sparseHeight count := by
    intro key member
    obtain ⟨index,present,rfl⟩ := List.mem_map.mp member
    exact sparseBits_length (valid index present)
  have encoded : bits.map (descendantIndex 0) = requests.map sparseKey := by
    simp only [bits,List.map_map,Function.comp_def,sparseBits_value]
  have same := numeric_primary_eq (sparseHeight count) 0 bits lengths
  rw [encoded] at same
  rw [same]
  have bound := primary_one_true (sparseHeight count) bits (by
    intro key member
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
    exact sparseBits_count _ _)
  simpa only [bits,List.length_map] using bound

def rankRequests (height copies : Nat) : List Nat :=
  (numericRepeatedWord height copies).map Int.toNat

theorem rankRequests_valid (height copies : Nat) :
    ∀ key ∈ rankRequests height copies, key < 2^height := by
  intro key member
  obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
  have bounds := numericRepeatedWord_valid height copies original present
  have nonnegative : 0 ≤ original := bounds.1
  have upper : original < ((2^height : Nat) : Int) := by simpa using bounds.2
  omega

theorem rankRequests_cast (height copies : Nat) :
    (rankRequests height copies).map (fun key : Nat => (key : Int)) = numericRepeatedWord height copies := by
  unfold rankRequests
  rw [List.map_map]
  calc
    _ = (numericRepeatedWord height copies).map id := by
      apply List.map_congr_left
      intro key member
      exact Int.toNat_of_nonneg (numericRepeatedWord_valid height copies key member).1
    _ = _ := List.map_id _

def sparseRequests (height copies : Nat) : List Int := (rankRequests height copies).map sparseKey

theorem sparseRequests_length (height copies : Nat) :
    (sparseRequests height copies).length = copies*2^height := by
  simp only [sparseRequests,rankRequests,List.length_map,numericRepeatedWord_length]

theorem sparseRequests_valid (height copies : Nat) :
    ∀ key ∈ sparseRequests height copies, ValidKey (sparseHeight (2^height)) key := by
  intro key member
  obtain ⟨rank,present,rfl⟩ := List.mem_map.mp member
  exact sparseKey_valid (rankRequests_valid height copies rank present)

theorem sparseRequests_primary (height copies : Nat) :
    (canonical (sparseHeight (2^height)) 0).primaryWilber (sparseRequests height copies) ≤
      2*(copies*2^height) := by
  have bound := sparse_primary_linear (2^height) (rankRequests height copies) (rankRequests_valid height copies)
  simpa only [sparseRequests,rankRequests,List.length_map,numericRepeatedWord_length] using bound

theorem sparseRequests_robust_lower (height copies : Nat) (positive : 0 < copies) :
    height*(copies*2^height)+1 ≤ robustBound (accessPoints (sparseRequests height copies))+2^height := by
  have embedding := robust_increasing_embedding sparseKey sparseKey_increasing (2^height)
    (rankRequests height copies) (rankRequests_valid height copies)
  rw [rankRequests_cast] at embedding
  have lower := numericRepeatedWord_robust_lower height copies positive
  change robustBound (accessPoints (numericRepeatedWord height copies)) ≤
    robustBound (accessPoints (sparseRequests height copies)) at embedding
  omega

end ChaCha.Separation
