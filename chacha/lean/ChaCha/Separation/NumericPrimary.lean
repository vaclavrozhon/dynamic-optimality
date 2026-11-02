import ChaCha.Separation.WordCounts
import ChaCha.Paper20261030.RobustCountingBound

/-!
# Boolean words and the actual numeric primary reference

The numeric key of a bit word is its existing `descendantIndex` from the
chosen reference owner. The theorem below identifies the two already used
primary counters exactly, rather than replacing the numeric counter by a
new statistic. Repeated bit reversal consequently supplies an actual
robust-rectangle lower bound with the first-visit correction retained.
-/

namespace ChaCha.Separation

open Primary AnchorPrimary PreferredProjection
open Paper20261030 Paper20261030.Dyadic Paper20261030.Rectangles

theorem descendantIndex_mem (bits : Key) (owner : Int) :
    descendantIndex owner bits ∈ (canonical bits.length owner).leaves := by
  induction bits generalizing owner with
  | nil => simp [descendantIndex,canonical,PrefRouter.leaves]
  | cons bit bits ih =>
      cases bit <;>
        simp only [List.length_cons,descendantIndex,canonical,PrefRouter.leaves,List.mem_append,
          Bool.false_eq_true,if_false,if_true,Int.add_zero]
      · exact Or.inl (ih _)
      · exact Or.inr (ih _)

theorem encoded_side_mem (height : Nat) (owner : Int) (bit side : Bool) (tail : Key)
    (length : tail.length = height) :
    descendantIndex owner (bit::tail) ∈
      (canonical height (2*owner+if side then 1 else 0)).leaves ↔ bit = side := by
  have present : descendantIndex owner (bit::tail) ∈
      (canonical height (2*owner+if bit then 1 else 0)).leaves := by
    simpa only [descendantIndex,length] using descendantIndex_mem tail (2*owner+if bit then 1 else 0)
  have quotient := (canonical_mem height _ _).mp present
  rw [canonical_mem,quotient]
  cases bit <;> cases side <;> simp <;> omega

theorem child_key_length (height : Nat) (keys : List Key)
    (lengths : ∀ key ∈ keys, key.length = height+1) (direction : Bool)
    {key : Key} (member : key ∈ child direction keys) : key.length = height := by
  obtain ⟨original,present,selected⟩ := List.mem_filterMap.mp member
  cases original with
  | nil => simp at selected
  | cons bit tail =>
      change (if bit = direction then some tail else none) = some key at selected
      by_cases same : bit = direction
      · have equal : tail = key := by simpa only [if_pos same,Option.some.injEq] using selected
        have length := lengths _ present
        simp only [List.length_cons,equal] at length
        omega
      · simp [same] at selected

theorem encoded_words (height : Nat) (owner : Int) (keys : List Key)
    (lengths : ∀ key ∈ keys, key.length = height+1) :
    PrefRouter.leftWord (canonical height (2*owner)).leaves
        (keys.map (descendantIndex owner)) = (child false keys).map (descendantIndex (2*owner)) ∧
    PrefRouter.rightWord (canonical height (2*owner)).leaves (canonical height (2*owner+1)).leaves
        (keys.map (descendantIndex owner)) = (child true keys).map (descendantIndex (2*owner+1)) ∧
    PrefRouter.branchWord (canonical height (2*owner)).leaves (canonical height (2*owner+1)).leaves
        (keys.map (descendantIndex owner)) = rootWord keys := by
  induction keys with
  | nil => simp [PrefRouter.leftWord,PrefRouter.rightWord,PrefRouter.branchWord,child,rootWord]
  | cons key keys ih =>
      have rest := ih (fun key member => lengths key (by simp [member]))
      have length := lengths key (by simp)
      cases key with
      | nil => simp at length
      | cons bit tail =>
          have tailLength : tail.length = height := by simp only [List.length_cons] at length; omega
          have left := encoded_side_mem height owner bit false tail tailLength
          have right := encoded_side_mem height owner bit true tail tailLength
          cases bit <;>
            simp_all [PrefRouter.leftWord,PrefRouter.rightWord,PrefRouter.branchWord,
              child,rootWord,descendantIndex,BitReversal.branch_root_cons]

/-- Exact equality of the complete Boolean and numeric reference counters. -/
theorem numeric_primary_eq (height : Nat) (owner : Int) (keys : List Key)
    (lengths : ∀ key ∈ keys, key.length = height) :
    (canonical height owner).primaryWilber (keys.map (descendantIndex owner)) =
      primaryCount height keys := by
  induction height generalizing owner keys with
  | zero => simp [canonical,PrefRouter.primaryWilber,primaryCount,primaryAlternations,owners]
  | succ height ih =>
      obtain ⟨left,right,root⟩ := encoded_words height owner keys lengths
      rw [canonical,PrefRouter.primaryWilber,left,right,root,
        ih _ _ (fun key member => child_key_length height keys lengths false member),
        ih _ _ (fun key member => child_key_length height keys lengths true member),primary_succ]

theorem repeatedWord_key_length {height copies : Nat} {key : Key}
    (member : key ∈ repeatedWord height copies) : key.length = height := by
  rw [repeatedWord_eq_periods] at member
  obtain ⟨period,present,inside⟩ := List.mem_flatten.mp member
  have same := (List.mem_replicate.mp present).2
  subst period
  exact BitReversal.key_length inside

def numericRepeatedWord (height copies : Nat) : List Int :=
  (repeatedWord height copies).map (descendantIndex 0)

theorem numericRepeatedWord_length (height copies : Nat) :
    (numericRepeatedWord height copies).length = copies*2^height := by
  simp [numericRepeatedWord,repeatedWord_length]

theorem numericRepeatedWord_valid (height copies : Nat) :
    ∀ key ∈ numericRepeatedWord height copies, ValidKey height key := by
  intro key member
  obtain ⟨bits,present,rfl⟩ := List.mem_map.mp member
  apply (canonical_zero_mem height _).mp
  simpa only [repeatedWord_key_length present] using descendantIndex_mem bits 0

theorem numericRepeatedWord_primary_exact (height copies : Nat) (positive : 0 < copies) :
    (canonical height 0).primaryWilber (numericRepeatedWord height copies)+2^height =
      height*(copies*2^height)+1 := by
  rw [numericRepeatedWord,numeric_primary_eq height 0 _ (fun key member => repeatedWord_key_length member)]
  exact repeatedWord_primary_exact height copies positive

theorem numericRepeatedWord_robust_lower (height copies : Nat) (positive : 0 < copies) :
    height*(copies*2^height)+1 ≤
      Rectangles.robustBound (accessPoints (numericRepeatedWord height copies))+2^height := by
  have lower := primaryWilber_robust _ (numericRepeatedWord_valid height copies)
  have count := numericRepeatedWord_primary_exact height copies positive
  omega

end ChaCha.Separation
