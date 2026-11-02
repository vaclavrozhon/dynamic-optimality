import DynamicOptimality.Funnel.OccurrencePast
import DynamicOptimality.Funnel.AdjacentPairs
import DynamicOptimality.Funnel.Counts

/-! # Exact equality between geometric funnel switches and warm path changes -/

namespace DynamicOptimality.Funnel

variable {α : Type*} [LinearOrder α] {m : Nat}

open Warm

def apexSwitches (word : Fin m → α) (active : Finset (Fin m)) (p : Fin m) :
    Finset (Fin m × Fin m) := Finset.univ.filter (fun pair => Switch word active p pair.1 pair.2)

@[simp] theorem mem_apexSwitches {word : Fin m → α} {active : Finset (Fin m)} {p q r : Fin m} :
    (q,r) ∈ apexSwitches word active p ↔ Switch word active p q r := by simp [apexSwitches]

theorem count_eq_sum (word : Fin m → α) (active : Finset (Fin m)) :
    count word active = ∑ p : Fin m, (apexSwitches word active p).card := by
  unfold count
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro p hp
  symm
  apply Finset.card_bij (fun pair _ => (p,pair))
  · intro pair member
    exact Finset.mem_filter.mpr ⟨mem_switches.mpr (mem_apexSwitches.mp member),rfl⟩
  · intro a ha b hb equal
    exact congrArg Prod.snd equal
  · rintro ⟨r,q,s⟩ member
    obtain ⟨edge,same⟩ := Finset.mem_filter.mp member
    change r = p at same
    subst r
    exact ⟨(q,s),mem_apexSwitches.mpr (mem_switches.mp edge),rfl⟩

theorem opposite_iff_side_ne {x a b : α} (aDifferent : a ≠ x) (bDifferent : b ≠ x) :
    Opposite x a b ↔ decide (a < x) ≠ decide (b < x) := by
  rcases lt_or_gt_of_ne aDifferent with ax | xa <;>
    rcases lt_or_gt_of_ne bDifferent with bx | xb
  · simp [Opposite,ax,bx,not_lt_of_gt ax,not_lt_of_gt bx]
  · simp [Opposite,ax,xb,not_lt_of_gt ax,not_lt_of_gt xb]
  · simp [Opposite,xa,bx,not_lt_of_gt xa,not_lt_of_gt bx]
  · simp [Opposite,xa,xb,not_lt_of_gt xa,not_lt_of_gt xb]

theorem apexSwitches_eq_path_pairs (word : List α) (p : Fin word.length) :
    apexSwitches word.get Finset.univ p =
      ((descendingPairs (occurrencePast word.get (word.get p) (priorTimes p))).filter
        (fun pair => decide (decide (word.get pair.1 < word.get p) ≠
          decide (word.get pair.2 < word.get p)))).toFinset := by
  let history := occurrencePast word.get (word.get p) (priorTimes p)
  have sorted := (priorTimes_sorted p).sublist (occurrencePast_sublist word.get (word.get p) (priorTimes p))
  have members : ∀ q, q ∈ history ↔ Visible word.get Finset.univ p q := occurrencePast_visible word p
  ext ⟨q,r⟩
  rw [mem_apexSwitches]
  change Switch word.get Finset.univ p q r ↔
    (q,r) ∈ ((descendingPairs history).filter (fun pair => decide
      (decide (word.get pair.1 < word.get p) ≠ decide (word.get pair.2 < word.get p)))).toFinset
  rw [List.mem_toFinset,List.mem_filter,descendingPairs_iff history sorted]
  simp only [decide_eq_true_eq,members]
  constructor
  · intro h
    refine ⟨⟨h.1,h.2.1,h.2.2.1,?_⟩,
      (opposite_iff_side_ne h.1.2.2.2.1 h.2.1.2.2.2.1).mp h.2.2.2.1⟩
    intro s visible qs sr
    exact h.2.2.2.2 s (Finset.mem_univ _) qs sr visible
  · rintro ⟨⟨hq,hr,qr,empty⟩,different⟩
    refine ⟨hq,hr,qr,(opposite_iff_side_ne hq.2.2.2.1 hr.2.2.2.1).mpr different,?_⟩
    intro s _ qs sr visible
    exact empty s visible qs sr

theorem apexSwitches_card_eq_changes (word : List α) (p : Fin word.length) :
    (apexSwitches word.get Finset.univ p).card =
      changes ((ancestors (word.get p) (cartesian (word.take p.val).reverse)).map
        (fun q => decide (q < word.get p))) := by
  rw [apexSwitches_eq_path_pairs]
  have sorted := (priorTimes_sorted p).sublist
    (occurrencePast_sublist word.get (word.get p) (priorTimes p))
  have nodup : (occurrencePast word.get (word.get p) (priorTimes p)).Nodup :=
    sorted.imp (fun h => ne_of_gt h)
  rw [List.toFinset_card_of_nodup ((descendingPairs_nodup _ nodup).filter _),
    descendingPairs_changes (fun q : Fin word.length => decide (word.get q < word.get p))]
  rw [← occurrencePast_ancestors word p,List.map_map]
  rfl

/-- This is the original closed-rectangle count, with no added baseline and
with repeated occurrences retained until their visibility is decided. -/
theorem wordCount_eq_sum_path_changes (word : List α) :
    wordCount word = ∑ p : Fin word.length,
      changes ((ancestors (word.get p) (cartesian (word.take p.val).reverse)).map
        (fun q => decide (q < word.get p))) := by
  rw [wordCount,count_eq_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact apexSwitches_card_eq_changes word p

end DynamicOptimality.Funnel
