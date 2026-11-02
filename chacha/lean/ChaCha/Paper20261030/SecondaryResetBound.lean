import ChaCha.Paper20261030.PrimaryFlipBound
import ChaCha.Reference

/-!
# Mixed secondary visits during one actual access

A mixed visit is a secondary interval receiving both a left and a right
depth access. The recursion below counts these intervals in the concrete
depth reference. Their number is at most the number of depth accesses
minus one. Including the final completion depth therefore leaves at most
one mixed interval per actual primary flip.
-/

namespace ChaCha.Paper20261030.Secondary

def lowDepths (c : Nat) (ds : List Nat) : List Nat :=
  ds.filter (fun d => decide (d ≤ c))

def highDepths (c : Nat) (ds : List Nat) : List Nat :=
  ds.filter (fun d => decide (c < d))

theorem depth_partition_length (c : Nat) (ds : List Nat) :
    (lowDepths c ds).length + (highDepths c ds).length = ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    by_cases h : d ≤ c
    · have hn : ¬ c < d := by omega
      simp [lowDepths,highDepths,h,hn] at *
      omega
    · have hn : c < d := by omega
      simp [lowDepths,highDepths,h,hn] at *
      omega

def mixedVisits : {a b : Nat} → DepthTree a b → List Nat → Nat
  | _, _, .leaf _, _ => 0
  | _, _, .node c _ _ l r, ds =>
      (if lowDepths c ds = [] ∨ highDepths c ds = [] then 0 else 1) +
        mixedVisits l (lowDepths c ds) + mixedVisits r (highDepths c ds)

theorem mixedVisits_bound {a b : Nat} (t : DepthTree a b) (ds : List Nat) :
    mixedVisits t ds + (if ds = [] then 0 else 1) ≤ ds.length := by
  induction t generalizing ds with
  | leaf a =>
    cases ds <;> simp [mixedVisits]
  | node c ha hb l r ihl ihr =>
    have hl := ihl (lowDepths c ds)
    have hr := ihr (highDepths c ds)
    have hp := depth_partition_length c ds
    by_cases hds : ds = []
    · subst ds
      simp [lowDepths,highDepths] at hl hr
      simp [mixedVisits,lowDepths,highDepths,show mixedVisits l [] = 0 by omega,
        show mixedVisits r [] = 0 by omega]
    · by_cases hl0 : lowDepths c ds = []
      · simp only [hl0,List.length_nil,if_pos] at hl
        have hr0 : highDepths c ds ≠ [] := by
          intro h
          simp [hl0,h] at hp
          exact hds (List.length_eq_zero_iff.mp hp.symm)
        simp only [mixedVisits,if_neg hds,hl0,true_or,if_pos]
        simp only [if_neg hr0] at hr
        simp only [hl0,List.length_nil,Nat.zero_add] at hp
        omega
      · by_cases hr0 : highDepths c ds = []
        · simp only [hr0,List.length_nil,if_pos] at hr
          simp only [if_neg hl0] at hl
          simp only [mixedVisits,if_neg hds,hr0,or_true,if_pos]
          simp only [hr0,List.length_nil,Nat.add_zero] at hp
          omega
        · simp only [if_neg hl0] at hl
          simp only [if_neg hr0] at hr
          simp only [mixedVisits,if_neg hds,hl0,hr0,false_or,if_false]
          omega

open PreferredProjection in
/-- This includes mixed visits at the completion root. The right-hand side
is the number of steps of `access_headTrace`, not an assumed budget. -/
theorem actual_access_mixed_bound {α : Type*} [DecidableEq α]
    {a b : Nat} (secondary : DepthTree a b) (primary : PrefRouter α) (x : α)
    (completion : Nat) :
    mixedVisits secondary (primary.exitDepths x ++ [completion]) ≤ primary.accessFlips x := by
  have h := mixedVisits_bound secondary (primary.exitDepths x ++ [completion])
  simp only [List.append_eq_nil_iff,List.cons_ne_self,and_false,if_false,
    List.length_append,List.length_singleton,PrefRouter.exitDepths_length] at h
  omega

end ChaCha.Paper20261030.Secondary
