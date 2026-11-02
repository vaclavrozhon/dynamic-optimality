import DynamicOptimality.Funnel.WarmCartesian

/-! # The exact warm search path

A key is exposed in a newest-first history if its newest occurrence precedes
all occurrences in the closed interval from that key to the requested key.
These are exactly the proper search ancestors in the warm Cartesian tree.
Thus unseen keys use their insertion search path without adding cold nodes.
-/

namespace DynamicOptimality.Funnel.Warm

open ChaCha.MTR ChaCha.MTR.Tree

variable {α : Type*} [LinearOrder α]

/-- Closed-rectangle visibility expressed in a newest-first history. -/
def Exposed (x q : α) : List α → Prop
  | [] => False
  | a :: history => (a = q ∧ q ≠ x) ∨ (¬ Between q x a ∧ Exposed x q history)

/-- The proper search ancestors, excluding the queried key when present. -/
def ancestors (x : α) : Tree α → List α
  | .empty => []
  | .node l a r =>
    if x < a then a :: ancestors x l
    else if a < x then a :: ancestors x r
    else []

theorem Exposed.ne {history : List α} {x q : α} (h : Exposed x q history) : q ≠ x := by
  induction history with
  | nil => exact h.elim
  | cons a history ih => exact h.elim And.right (fun h => ih h.2)

theorem Exposed.mem {history : List α} {x q : α} (h : Exposed x q history) : q ∈ history := by
  induction history with
  | nil => exact h.elim
  | cons a history ih =>
    rcases h with ⟨rfl,_⟩ | ⟨_,h⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

@[simp] theorem not_exposed_self (x : α) (history : List α) : ¬ Exposed x x history :=
  fun h => h.ne rfl

/-- Filtering cannot change a visibility test if it retains every possible blocker. -/
theorem exposed_filter (history : List α) (x q : α) (keep : α → Bool)
    (blockers : ∀ z, Between q x z → keep z = true) :
    Exposed x q (history.filter keep) ↔ Exposed x q history := by
  induction history with
  | nil => rfl
  | cons a history ih =>
    by_cases kept : keep a = true
    · simp only [List.filter_cons,kept,↓reduceIte,Exposed,ih]
    · have outside : ¬ Between q x a := fun h => kept (blockers a h)
      have different : a ≠ q := by
        intro same
        apply outside
        subst a
        exact between_left _ _
      simp [List.filter_cons,kept,Exposed,ih,outside,different]

private theorem exposed_filter_below (history : List α) (x q a : α)
    (hx : x < a) (hq : q < a) :
    Exposed x q (history.filter (fun z => decide (z < a))) ↔ Exposed x q history := by
  apply exposed_filter
  intro z hz
  apply decide_eq_true
  rcases hz with ⟨_,hz⟩ | ⟨_,hz⟩
  · exact hz.trans_lt hx
  · exact hz.trans_lt hq

private theorem exposed_filter_above (history : List α) (x q a : α)
    (hx : a < x) (hq : a < q) :
    Exposed x q (history.filter (fun z => decide (a < z))) ↔ Exposed x q history := by
  apply exposed_filter
  intro z hz
  apply decide_eq_true
  rcases hz with ⟨hz,_⟩ | ⟨hz,_⟩
  · exact hq.trans_le hz
  · exact hx.trans_le hz

theorem mem_ancestors_cartesian (history : List α) (x q : α) :
    q ∈ ancestors x (cartesian history) ↔ Exposed x q history := by
  induction history using length_induction with
  | step history ih =>
    cases history with
    | nil => simp [ancestors,Exposed]
    | cons a rest =>
      have leftLength : (rest.filter (fun y => decide (y < a))).length < (a::rest).length :=
        (List.length_filter_le _ _).trans_lt (by simp)
      have rightLength : (rest.filter (fun y => decide (a < y))).length < (a::rest).length :=
        (List.length_filter_le _ _).trans_lt (by simp)
      rw [cartesian_cons]
      rcases lt_trichotomy x a with xa | rfl | ax
      · simp only [ancestors,xa,↓reduceIte,List.mem_cons,ih _ leftLength,Exposed]
        rcases lt_trichotomy q a with qa | rfl | aq
        · have out : ¬ Between q x a := by
            rintro (⟨_,h⟩ | ⟨_,h⟩)
            · exact (not_le_of_gt xa) h
            · exact (not_le_of_gt qa) h
          simp [ne_of_lt qa,ne_of_gt qa,out,exposed_filter_below rest x q a xa qa]
        · simp [ne_of_gt xa]
        · have blocked : Between q x a := Or.inr ⟨xa.le,aq.le⟩
          have absent : ¬ Exposed x q (rest.filter (fun z => decide (z < a))) := by
            intro h
            have less : q < a := of_decide_eq_true (List.mem_filter.mp h.mem).2
            exact lt_asymm aq less
          simp [ne_of_gt aq,ne_of_lt aq,blocked,absent]
      · simp [ancestors,Exposed,between_right,eq_comm]
      · simp only [ancestors,not_lt_of_gt ax,ax,↓reduceIte,List.mem_cons,ih _ rightLength,Exposed]
        rcases lt_trichotomy q a with qa | rfl | aq
        · have blocked : Between q x a := Or.inl ⟨qa.le,ax.le⟩
          have absent : ¬ Exposed x q (rest.filter (fun z => decide (a < z))) := by
            intro h
            have greater : a < q := of_decide_eq_true (List.mem_filter.mp h.mem).2
            exact lt_asymm qa greater
          simp [ne_of_gt qa,ne_of_lt qa,blocked,absent]
        · simp [ne_of_lt ax]
        · have out : ¬ Between q x a := by
            rintro (⟨h,_⟩ | ⟨h,_⟩)
            · exact (not_le_of_gt aq) h
            · exact (not_le_of_gt ax) h
          simp [ne_of_lt aq,ne_of_gt aq,out,exposed_filter_above rest x q a ax aq]

end DynamicOptimality.Funnel.Warm
