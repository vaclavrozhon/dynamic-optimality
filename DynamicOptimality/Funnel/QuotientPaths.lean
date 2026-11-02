import DynamicOptimality.Funnel.WarmQuotient
import DynamicOptimality.Funnel.WarmPaths
import Mathlib.Data.List.TakeWhile

/-! # The template path covers exactly the foreign prefix labels -/

namespace DynamicOptimality.Funnel.Warm

open ChaCha.MTR ChaCha.MTR.Tree ChaCha.ConvexSearchQuotient

def foreignPrefix (label : Int → Int) (x : Int) (tree : Tree Int) : List Int :=
  (ancestors x tree).takeWhile (fun a => decide (label a ≠ label x))

theorem foreignPrefix_ne (label : Int → Int) (x : Int) (tree : Tree Int) {q : Int}
    (member : q ∈ foreignPrefix label x tree) : label q ≠ label x := by
  have kept : decide (label q ≠ label x) = true :=
    List.mem_takeWhile_imp (p := fun q => decide (label q ≠ label x)) member
  exact of_decide_eq_true kept

private theorem key_lt_of_label_lt {label : Int → Int} (mono : Monotone label)
    {a b : Int} (strict : label a < label b) : a < b := by
  by_contra failed
  have := mono (show b ≤ a by omega)
  omega

theorem project_ancestors_sublist (label : Int → Int) (mono : Monotone label)
    (tree : Tree Int) (x lo hi : Int) (lower : lo ≤ label x) (upper : label x ≤ hi) :
    (ancestors (label x) (project label lo hi tree)).Sublist
      ((foreignPrefix label x tree).map label) := by
  induction tree generalizing lo hi with
  | empty => simp [ancestors,project,foreignPrefix]
  | node l a r ihl ihr =>
    by_cases below : label a < lo
    · have ax : a < x := key_lt_of_label_lt mono (by omega)
      have foreign : label a ≠ label x := by omega
      simp only [project,below,↓reduceIte,foreignPrefix,ancestors,not_lt_of_gt ax,ax,
        ↓reduceIte,List.takeWhile_cons,(decide_eq_true foreign),↓reduceIte,List.map_cons]
      exact (ihr lo hi lower upper).cons _
    · by_cases above : hi < label a
      · have xa : x < a := key_lt_of_label_lt mono (by omega)
        have foreign : label a ≠ label x := by omega
        simp only [project,below,above,↓reduceIte,foreignPrefix,ancestors,xa,
          ↓reduceIte,List.takeWhile_cons,(decide_eq_true foreign),↓reduceIte,List.map_cons]
        exact (ihl lo hi lower upper).cons _
      · simp only [project,below,above,↓reduceIte]
        rcases lt_trichotomy (label x) (label a) with xa | same | ax
        · have keys := key_lt_of_label_lt mono xa
          have foreign : label a ≠ label x := by omega
          simp only [ancestors,xa,keys,↓reduceIte,foreignPrefix,List.takeWhile_cons,
            (decide_eq_true foreign),↓reduceIte,List.map_cons]
          exact (ihl lo (label a - 1) lower (by omega)).cons_cons _
        · simp only [ancestors,same,lt_self_iff_false,↓reduceIte]
          exact List.nil_sublist _
        · have keys := key_lt_of_label_lt mono ax
          have foreign : label a ≠ label x := by omega
          simp only [ancestors,not_lt_of_gt ax,ax,not_lt_of_gt keys,keys,↓reduceIte,
            foreignPrefix,List.takeWhile_cons,(decide_eq_true foreign),↓reduceIte,List.map_cons]
          exact (ihr (label a + 1) hi (by omega) upper).cons_cons _

/-- Every in-range component appearing before the own component contributes
its unique representative to the template search path. -/
theorem prefix_label_mem_project (label : Int → Int) (mono : Monotone label)
    (tree : Tree Int) (ordered : Ordered tree) (x lo hi : Int)
    (lower : lo ≤ label x) (upper : label x ≤ hi) {q : Int}
    (member : q ∈ foreignPrefix label x tree)
    (qLower : lo ≤ label q) (qUpper : label q ≤ hi) :
    label q ∈ ancestors (label x) (project label lo hi tree) := by
  induction tree generalizing lo hi with
  | empty => simp [foreignPrefix,ancestors] at member
  | node l a r ihl ihr =>
    obtain ⟨ol,orr,left,right⟩ := ordered_parts ordered
    by_cases below : label a < lo
    · have ax : a < x := key_lt_of_label_lt mono (by omega)
      have foreign : label a ≠ label x := by omega
      simp only [foreignPrefix,ancestors,not_lt_of_gt ax,ax,↓reduceIte,List.takeWhile_cons,
        (decide_eq_true foreign),↓reduceIte,List.mem_cons] at member
      simp only [project,below,↓reduceIte]
      rcases member with rfl | member
      · omega
      · exact ihr orr lo hi lower upper member qLower qUpper
    · by_cases above : hi < label a
      · have xa : x < a := key_lt_of_label_lt mono (by omega)
        have foreign : label a ≠ label x := by omega
        simp only [foreignPrefix,ancestors,xa,↓reduceIte,List.takeWhile_cons,
          (decide_eq_true foreign),↓reduceIte,List.mem_cons] at member
        simp only [project,below,above,↓reduceIte]
        rcases member with rfl | member
        · omega
        · exact ihl ol lo hi lower upper member qLower qUpper
      · simp only [project,below,above,↓reduceIte]
        rcases lt_trichotomy (label x) (label a) with xa | same | ax
        · have keys := key_lt_of_label_lt mono xa
          have foreign : label a ≠ label x := by omega
          simp only [foreignPrefix,ancestors,keys,↓reduceIte,List.takeWhile_cons,
            (decide_eq_true foreign),↓reduceIte,List.mem_cons] at member
          simp only [ancestors,xa,↓reduceIte,List.mem_cons]
          rcases member with rfl | member
          · exact Or.inl rfl
          · by_cases equal : label q = label a
            · exact Or.inl equal
            · have inPath : q ∈ ancestors x l := (List.takeWhile_sublist _).subset member
              have qa := mono (left q (ancestors_mem inPath)).le
              exact Or.inr (ihl ol lo (label a - 1) lower (by omega) member qLower (by omega))
        · have own : label a = label x := same.symm
          by_cases keys : x < a
          · simp [foreignPrefix,ancestors,keys,own] at member
          · by_cases other : a < x
            · simp [foreignPrefix,ancestors,keys,other,own] at member
            · simp [foreignPrefix,ancestors,keys,other] at member
        · have keys := key_lt_of_label_lt mono ax
          have foreign : label a ≠ label x := by omega
          simp only [foreignPrefix,ancestors,not_lt_of_gt keys,keys,↓reduceIte,List.takeWhile_cons,
            (decide_eq_true foreign),↓reduceIte,List.mem_cons] at member
          simp only [ancestors,not_lt_of_gt ax,ax,↓reduceIte,List.mem_cons]
          rcases member with rfl | member
          · exact Or.inl rfl
          · by_cases equal : label q = label a
            · exact Or.inl equal
            · have inPath : q ∈ ancestors x r := (List.takeWhile_sublist _).subset member
              have aq := mono (right q (ancestors_mem inPath)).le
              exact Or.inr (ihr orr (label a + 1) hi (by omega) upper member (by omega) qUpper)

end DynamicOptimality.Funnel.Warm
