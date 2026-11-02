import DynamicOptimality.Funnel.WarmVisibility

/-! # The ordered past funnel and its warm search path

`past` scans a newest-first history. A newly scanned key blocks precisely
those older visible keys whose closed rectangle contains it. Equal query
keys stop the scan. Thus the order, not merely the set, of warm ancestors
is the order of the geometric past funnel, reversed in time.
-/

namespace DynamicOptimality.Funnel.Warm

open ChaCha.MTR ChaCha.MTR.Tree

variable {α : Type*} [LinearOrder α]

def past (x : α) : List α → List α
  | [] => []
  | a :: history => if a = x then [] else
      a :: (past x history).filter (fun q => decide (¬ Between q x a))

theorem mem_past (history : List α) (x q : α) : q ∈ past x history ↔ Exposed x q history := by
  induction history with
  | nil => simp [past,Exposed]
  | cons a history ih =>
    by_cases same : a = x
    · subst a
      simp [past,Exposed,between_right,eq_comm]
    · simp only [past,same,↓reduceIte,List.mem_cons,List.mem_filter,decide_eq_true_eq,ih,Exposed]
      constructor
      · rintro (rfl | ⟨exposed,outside⟩)
        · exact Or.inl ⟨rfl,same⟩
        · exact Or.inr ⟨outside,exposed⟩
      · rintro (⟨rfl,_⟩ | ⟨outside,exposed⟩)
        · exact Or.inl rfl
        · exact Or.inr ⟨exposed,outside⟩

/-- Restricting to a convex set containing the query filters its past funnel
without changing the order of the remaining entries. -/
theorem past_filter (history : List α) (x : α) (keep : α → Bool)
    (queryKept : keep x = true)
    (convex : ∀ q a, keep q = true → Between q x a → keep a = true) :
    past x (history.filter keep) = (past x history).filter keep := by
  induction history with
  | nil => simp [past]
  | cons a history ih =>
    by_cases same : a = x
    · subst a
      simp [past,queryKept]
    · by_cases kept : keep a = true
      · simp only [List.filter_cons,kept,Bool.false_eq_true,↓reduceIte,past,same,↓reduceIte,ih]
        congr 1
        exact List.filter_comm _ _ _
      · simp only [List.filter_cons,kept,Bool.false_eq_true,↓reduceIte,past,same,↓reduceIte,ih]
        rw [List.filter_filter]
        apply List.filter_congr
        intro q _
        by_cases hq : keep q = true
        · have outside : ¬ Between q x a := fun h => kept (convex q a hq h)
          simp [hq,outside]
        · simp [hq]

private theorem not_between_below {a x q : α} (ax : a < x) :
    ¬ Between q x a ↔ a < q := by
  rcases le_or_gt q a with qa | aq
  · simp [Between,qa,ax.le,not_lt_of_ge qa]
  · simp [Between,not_le_of_gt aq,not_le_of_gt ax,aq]

private theorem not_between_above {a x q : α} (xa : x < a) :
    ¬ Between q x a ↔ q < a := by
  rcases le_or_gt a q with aq | qa
  · simp [Between,aq,xa.le,not_lt_of_ge aq]
  · simp [Between,not_le_of_gt qa,not_le_of_gt xa,qa]

theorem ancestors_eq_past (history : List α) (x : α) :
    ancestors x (cartesian history) = past x history := by
  induction history using length_induction with
  | step history ih =>
    cases history with
    | nil => simp [ancestors,past]
    | cons a rest =>
      have leftLength : (rest.filter (fun y => decide (y < a))).length < (a::rest).length :=
        (List.length_filter_le _ _).trans_lt (by simp)
      have rightLength : (rest.filter (fun y => decide (a < y))).length < (a::rest).length :=
        (List.length_filter_le _ _).trans_lt (by simp)
      rw [cartesian_cons]
      rcases lt_trichotomy x a with xa | rfl | ax
      · simp only [ancestors,xa,↓reduceIte,past,ne_of_gt xa,↓reduceIte,ih _ leftLength]
        have restrict := past_filter rest x (fun y => decide (y < a)) (decide_eq_true xa) (by
          intro q z hq hz
          have qa : q < a := of_decide_eq_true hq
          apply decide_eq_true
          rcases hz with ⟨_,zx⟩ | ⟨_,zq⟩
          · exact zx.trans_lt xa
          · exact zq.trans_lt qa)
        rw [restrict]
        congr 1
        apply List.filter_congr
        intro q _
        simp only [not_between_above xa]
      · simp [ancestors,past]
      · simp only [ancestors,not_lt_of_gt ax,ax,↓reduceIte,past,ne_of_lt ax,↓reduceIte,ih _ rightLength]
        have restrict := past_filter rest x (fun y => decide (a < y)) (decide_eq_true ax) (by
          intro q z hq hz
          have aq : a < q := of_decide_eq_true hq
          apply decide_eq_true
          rcases hz with ⟨qz,_⟩ | ⟨xz,_⟩
          · exact aq.trans_le qz
          · exact ax.trans_le xz)
        rw [restrict]
        congr 1
        apply List.filter_congr
        intro q _
        simp only [not_between_below ax]

end DynamicOptimality.Funnel.Warm
