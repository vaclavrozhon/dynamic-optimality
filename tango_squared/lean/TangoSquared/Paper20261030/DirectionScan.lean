import TangoSquared.Paper20261030.ChronologicalWords

/-!
# A chronological Boolean scan counts the geometric depth alternations

Consecutive equal projected keys emit no letter. Distinct keys emit DOWN
when their segment labels agree and UP otherwise. Starting UP, the scan's
DOWN-to-UP count equals the previously defined geometric event count.
-/

namespace TangoSquared.Paper20261030.Rectangles

open scoped BigOperators

def directionLetters (f : Int → Int) (previous : Point) : List Point → List Bool
  | [] => []
  | q :: qs => (if previous.1 = q.1 then [] else [decide (f previous.1 = f q.1)]) ++
      directionLetters f q qs

noncomputable def directionBit (P : Finset Point) (f : Int → Int) (p : Point) : Bool :=
  by classical exact decide (ActiveDown P f p)

noncomputable def downUpIndicator (P : Finset Point) (f : Int → Int) (p : Point) : Nat :=
  by classical exact if DownUpAt P f p then 1 else 0

theorem rlCharge_self (b : Bool) : rlCharge b b = 0 := by cases b <;> rfl

theorem direction_edge {P : Finset Point} (hP : Instance P) (f : Int → Int)
    {p q : Point} (hn : Next P p q) :
    rlCharge (directionBit P f p) (directionBit P f q) = downUpIndicator P f q := by
  classical
  have he := downUpAt_iff_previous hP f hn
  by_cases hp : ActiveDown P f p <;> by_cases hq : ActiveDown P f q <;>
    simp [directionBit,downUpIndicator,he,hp,hq,rlCharge]

theorem direction_scan_sum {P : Finset Point} (hP : Instance P) (f : Int → Int)
    (p : Point) (ps : List Point) (hchain : (p :: ps).IsChain (Next P)) :
    rlFrom (directionBit P f p) (ps.map (directionBit P f)) =
      (ps.map (downUpIndicator P f)).sum := by
  induction ps generalizing p with
  | nil => rfl
  | cons q qs ih =>
    obtain ⟨hn,ht⟩ := List.isChain_cons_cons.mp hchain
    simp only [List.map_cons,rlFrom_cons,List.sum_cons,direction_edge hP f hn,ih q ht]

theorem directionLetters_scan {P : Finset Point} (hP : Instance P) (f : Int → Int)
    (p : Point) (ps : List Point) (hchain : (p :: ps).IsChain (Next P)) :
    rlFrom (directionBit P f p) (directionLetters f p ps) =
      rlFrom (directionBit P f p) (ps.map (directionBit P f)) := by
  classical
  induction ps generalizing p with
  | nil => rfl
  | cons q qs ih =>
    obtain ⟨hn,ht⟩ := List.isChain_cons_cons.mp hchain
    by_cases hk : p.1 = q.1
    · have he : directionBit P f q = directionBit P f p := by
        simp only [directionBit,activeDown_repeat hP f hn hk]
      rw [directionLetters,if_pos hk,List.nil_append,List.map_cons,rlFrom_cons]
      rw [← he,rlCharge_self,Nat.zero_add]
      exact ih q ht
    · have he : directionBit P f q = decide (f p.1 = f q.1) := by
        simp only [directionBit,activeDown_change hP f hn hk]
      rw [directionLetters,if_neg hk,List.singleton_append,List.map_cons,rlFrom_cons,rlFrom_cons,
        ← he,ih q ht]

theorem sum_toFinset_word {ps : List Point} (hn : ps.Nodup) (f : Point → Nat) :
    (∑ p ∈ ps.toFinset, f p) = (ps.map f).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨hp,ht⟩ := List.nodup_cons.mp hn
    have hp' : p ∉ ps.toFinset := by simpa only [List.mem_toFinset] using hp
    simp only [List.toFinset_cons,Finset.sum_insert hp',List.map_cons,List.sum_cons,ih ht]

/-- The exact finite-point/counting bridge, including repeated keys. -/
theorem directionLetters_depthAlternations (f : Int → Int) (p : Point) (ps : List Point)
    (hs : Chronological (p :: ps)) :
    rlCount (directionLetters f p ps) = depthAlternations (p :: ps).toFinset f := by
  classical
  have hP := chronological_instance hs
  have hfirst := chronological_first hs
  have hinit : directionBit (p :: ps).toFinset f p = false := by
    simp only [directionBit,decide_eq_false_iff_not]
    exact activeDown_initial f hfirst
  have hzero : downUpIndicator (p :: ps).toFinset f p = 0 := by
    have hno : ¬ DownUpAt (p :: ps).toFinset f p := by
      rintro ⟨q,hq,_⟩
      have := hfirst q hq.1
      have := hq.2.2.1
      omega
    simp only [downUpIndicator,if_neg hno]
  rw [rlCount,← hinit,directionLetters_scan hP f p ps (chronological_chain hs),
    direction_scan_sum hP f p ps (chronological_chain hs),depthAlternations_eq_downUp hP]
  change _ = ∑ q ∈ (p :: ps).toFinset, downUpIndicator (p :: ps).toFinset f q
  rw [sum_toFinset_word (chronological_nodup hs),List.map_cons,List.sum_cons,hzero,Nat.zero_add]

end TangoSquared.Paper20261030.Rectangles
