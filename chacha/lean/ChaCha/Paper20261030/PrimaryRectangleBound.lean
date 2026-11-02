import ChaCha.Paper20261030.MemoryCountAssembly
import ChaCha.Paper20261030.SwitchScan

/-!
# Primary alternations are paid by independent rectangles

At a primary fork, the projected two-letter word has exactly the root's
branch alternations. Robust rectangle superadditivity pays simultaneously
for that projection and both child subwords. Induction therefore bounds
the actual Wilber count by the robust rectangle maximum.
-/

namespace ChaCha.Paper20261030.Dyadic

open PreferredProjection Rectangles Secondary

def branchIndex (owner : Int) (b : Bool) : Int := 2 * owner + if b then 1 else 0

theorem branchIndex_injective (owner : Int) : Function.Injective (branchIndex owner) := by
  intro a b he
  cases a <;> cases b <;> simp_all [branchIndex]

theorem canonical_branchWord (h : Nat) (owner : Int) (xs : List Int)
    (hxs : ∀ x ∈ xs, x ∈ (canonical (h + 1) owner).leaves) :
    (PrefRouter.branchWord (canonical h (2 * owner)).leaves
      (canonical h (2 * owner + 1)).leaves xs).map (branchIndex owner) =
      xs.map (fun x => x / (2 : Int) ^ h) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have ht : ∀ y ∈ xs, y ∈ (canonical (h + 1) owner).leaves := fun y hy => hxs y (by simp [hy])
    by_cases hl : x ∈ (canonical h (2 * owner)).leaves
    · have hdiv := (canonical_mem h (2 * owner) x).mp hl
      simp [PrefRouter.branchWord,hl,branchIndex,hdiv,ih ht]
      exact ih ht
    · have hr : x ∈ (canonical h (2 * owner + 1)).leaves := (List.mem_append.mp hx).resolve_left hl
      have hdiv := (canonical_mem h (2 * owner + 1) x).mp hr
      simp [PrefRouter.branchWord,hl,hr,branchIndex,hdiv,ih ht]
      exact ih ht

theorem primaryWilber_robustBound (H : Nat) (owner : Int) (ps : List Point)
    (hs : Chronological ps) (hkeys : ∀ p ∈ ps, p.1 ∈ (canonical H owner).leaves) :
    (canonical H owner).primaryWilber (ps.map Prod.fst) ≤ robustBound ps.toFinset := by
  induction H generalizing owner ps with
  | zero => simp [canonical,PrefRouter.primaryWilber]
  | succ h ih =>
    let f : Int → Int := fun x => x / (2 : Int) ^ h
    let L := (canonical h (2 * owner)).leaves
    let R := (canonical h (2 * owner + 1)).leaves
    let psL := ps.filter (fun p => decide (p.1 ∈ L))
    let psR := ps.filter (fun p => decide (p.1 ∉ L ∧ p.1 ∈ R))
    have hL : ∀ p ∈ psL, p.1 ∈ (canonical h (2 * owner)).leaves := by
      intro p hp
      exact of_decide_eq_true (List.mem_filter.mp hp).2
    have hR : ∀ p ∈ psR, p.1 ∈ (canonical h (2 * owner + 1)).leaves := by
      intro p hp
      exact (of_decide_eq_true (List.mem_filter.mp hp).2).2
    have hl := ih (2 * owner) psL (chronological_filter hs _) hL
    have hr := ih (2 * owner + 1) psR (chronological_filter hs _) hR
    have hleftkeys : psL.map Prod.fst = PrefRouter.leftWord L (ps.map Prod.fst) :=
      keys_filter_points ps (fun x => decide (x ∈ L))
    have hrightkeys : psR.map Prod.fst = PrefRouter.rightWord L R (ps.map Prod.fst) :=
      keys_filter_points ps (fun x => decide (x ∉ L ∧ x ∈ R))
    have hleftset : psL.toFinset = fiber f (2 * owner) ps.toFinset := by
      ext p
      simp [psL,L,f,fiber,canonical_mem]
    have hrightset : psR.toFinset = fiber f (2 * owner + 1) ps.toFinset := by
      ext p
      simp [psR,L,R,f,fiber,canonical_mem]
      omega
    rw [hleftset] at hl
    rw [hrightset] at hr
    have hinput : ∀ x ∈ ps.map Prod.fst, x ∈ (canonical (h + 1) owner).leaves := by
      intro x hx
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
      exact hkeys p hp
    have hword := canonical_branchWord h owner (ps.map Prod.fst) hinput
    have hswitch := alternations_switchCount (ps.map (mapPoint f)) (chronological_project hs f)
    have hproject : (ps.map (mapPoint f)).toFinset = project f ps.toFinset := by
      ext p
      simp [project]
    rw [hproject] at hswitch
    have hmap : (ps.map (mapPoint f)).map Prod.fst = (ps.map Prod.fst).map f := by
      simp only [List.map_map]
      rfl
    rw [hmap,← hword,alternations_injective_map _ (branchIndex_injective owner)] at hswitch
    have hsbound := switchCount_le_robustBound (instance_project (chronological_instance hs) f)
    have hmono : Monotone f := fun x y hxy => Int.ediv_le_ediv (pow_pos (by decide) _) hxy
    have hsplit := robustBound_split (chronological_instance hs) f hmono {2 * owner,2 * owner + 1}
    rw [Finset.sum_pair (by omega : 2 * owner ≠ 2 * owner + 1)] at hsplit
    simp only [canonical,PrefRouter.primaryWilber]
    change alternations (PrefRouter.branchWord L R (ps.map Prod.fst)) +
      (canonical h (2 * owner)).primaryWilber (PrefRouter.leftWord L (ps.map Prod.fst)) +
      (canonical h (2 * owner + 1)).primaryWilber (PrefRouter.rightWord L R (ps.map Prod.fst)) ≤ _
    rw [← hleftkeys,← hrightkeys]
    change alternations (PrefRouter.branchWord L R (ps.map Prod.fst)) = _ at hswitch
    omega

theorem primaryWilber_rectangleBound {H : Nat} (xs : List Int)
    (hkeys : ∀ x ∈ xs, ValidKey H x) :
    (canonical H 0).primaryWilber xs ≤ rectangleBound (accessPoints xs) := by
  have hword : ∀ p ∈ pointWord 0 xs, p.1 ∈ (canonical H 0).leaves := by
    intro p hp
    have hm : p.1 ∈ (pointWord 0 xs).map Prod.fst := List.mem_map.mpr ⟨p,hp,rfl⟩
    rw [pointWord_keys] at hm
    exact (canonical_zero_mem H p.1).mpr (hkeys p.1 hm)
  have h := primaryWilber_robustBound H 0 (pointWord 0 xs) (pointWord_chronological 0 xs) hword
  rw [pointWord_keys,pointWord_toFinset] at h
  exact h.trans (robustBound_le_rectangleBound _)

/-- Both genuine and completion-root secondary flips are controlled by
the actual rectangle maximum, with initialization included. -/
theorem secondaryCost_le_rectangles {h : Nat} (reference : DepthTree 0 h) (xs : List Int)
    (hkeys : ∀ x ∈ xs, ValidKey (h + 1) x) :
    secondaryCost reference (MemoryState.initial (canonical (h + 1) 0)) xs ≤
      12 * rectangleBound (accessPoints xs) + 5 * (canonical (h + 1) 0).internalVertices := by
  have hs := secondaryCost_rectangle_bound reference xs hkeys
  have hp := primaryWilber_rectangleBound xs hkeys
  omega

end ChaCha.Paper20261030.Dyadic
