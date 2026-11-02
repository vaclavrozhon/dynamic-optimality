import DynamicOptimality.Funnel.WarmPaths
import Mathlib.Data.List.FinRange

/-! # The past funnel as an ordered list of occurrences

Keeping occurrence identities until after the visibility test makes repeated
keys harmless: the same key at an intervening time blocks its older copy.
-/

namespace DynamicOptimality.Funnel.Warm

variable {α τ : Type*} [LinearOrder α]

def occurrencePast (key : τ → α) (x : α) : List τ → List τ
  | [] => []
  | a :: rest => if key a = x then [] else
      a :: (occurrencePast key x rest).filter (fun q => decide (¬ Between (key q) x (key a)))

theorem occurrencePast_map (key : τ → α) (x : α) (history : List τ) :
    (occurrencePast key x history).map key = past x (history.map key) := by
  induction history with
  | nil => rfl
  | cons a rest ih =>
    by_cases same : key a = x
    · simp [occurrencePast,past,same]
    · simp only [occurrencePast,same,↓reduceIte,List.map_cons,past]
      rw [← ih,List.filter_map]
      rfl

theorem occurrencePast_sublist (key : τ → α) (x : α) (history : List τ) :
    (occurrencePast key x history).Sublist history := by
  induction history with
  | nil => exact List.Sublist.slnil
  | cons a rest ih =>
    simp only [occurrencePast]
    split_ifs
    · exact List.nil_sublist _
    · exact (List.filter_sublist.trans ih).cons_cons a

/-- In decreasing time order the scan keeps precisely the visible occurrences. -/
theorem mem_occurrencePast [LinearOrder τ] (key : τ → α) (x : α) (history : List τ)
    (sorted : history.Pairwise (fun a b => b < a)) (q : τ) :
    q ∈ occurrencePast key x history ↔ q ∈ history ∧ key q ≠ x ∧
      ∀ r ∈ history, q < r → ¬ Between (key q) x (key r) := by
  induction history with
  | nil => simp [occurrencePast]
  | cons a rest ih =>
    obtain ⟨largest,tailSorted⟩ := List.pairwise_cons.mp sorted
    by_cases same : key a = x
    · simp only [occurrencePast,same,↓reduceIte,List.not_mem_nil,false_iff]
      rintro ⟨member,different,empty⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact different same
      · apply empty a (List.mem_cons_self) (largest q member)
        rw [same]
        exact between_right _ _
    · simp only [occurrencePast,same,↓reduceIte,List.mem_cons,List.mem_filter,
        decide_eq_true_eq,ih tailSorted]
      constructor
      · rintro (rfl | ⟨⟨member,different,empty⟩,outside⟩)
        · refine ⟨Or.inl rfl,same,?_⟩
          intro r hr ar
          rcases hr with rfl | hr
          · exact (lt_irrefl _ ar).elim
          · exact (lt_asymm ar (largest r hr)).elim
        · refine ⟨Or.inr member,different,?_⟩
          intro r hr qr
          rcases hr with rfl | hr
          · exact outside
          · exact empty r hr qr
      · rintro ⟨(rfl | member),different,empty⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨⟨member,different,fun r hr => empty r (Or.inr hr)⟩,
            empty a (Or.inl rfl) (largest q member)⟩

/-- All strictly earlier times, from newest to oldest. -/
def priorTimes {m : Nat} (p : Fin m) : List (Fin m) :=
  ((List.finRange m).take p.val).reverse

theorem mem_priorTimes {m : Nat} (p q : Fin m) : q ∈ priorTimes p ↔ q < p := by
  rw [priorTimes,List.mem_reverse,List.mem_iff_getElem]
  constructor
  · rintro ⟨i,bound,equal⟩
    have value := congrArg Fin.val equal
    simp only [List.getElem_take,List.getElem_finRange,Fin.val_cast] at value
    simp only [List.length_take,List.length_finRange] at bound
    change q.val < p.val
    omega
  · intro bound
    refine ⟨q.val,?_,?_⟩
    · simp only [List.length_take,List.length_finRange]
      change q.val < p.val at bound
      omega
    · apply Fin.ext
      simp only [List.getElem_take,List.getElem_finRange,Fin.val_cast]

theorem priorTimes_sorted {m : Nat} (p : Fin m) :
    (priorTimes p).Pairwise (fun a b => b < a) := by
  apply List.pairwise_reverse.mpr
  have full : (List.finRange m).Pairwise (· < ·) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj ij
    simpa only [Fin.lt_def,List.getElem_finRange,Fin.val_cast] using ij
  exact full.sublist (List.take_sublist _ _)

theorem priorTimes_map (word : List α) (p : Fin word.length) :
    (priorTimes p).map word.get = (word.take p.val).reverse := by
  rw [priorTimes,List.map_reverse,List.map_take,← List.ofFn_eq_map,List.ofFn_get]

theorem occurrencePast_visible (word : List α) (p q : Fin word.length) :
    q ∈ occurrencePast word.get (word.get p) (priorTimes p) ↔
      Visible word.get Finset.univ p q := by
  rw [mem_occurrencePast _ _ _ (priorTimes_sorted p)]
  simp only [mem_priorTimes,Visible,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨before,different,empty⟩
    exact ⟨before,different,fun r _ qr rp => empty r rp qr⟩
  · rintro ⟨before,different,empty⟩
    exact ⟨before,different,fun r rp qr => empty r True.intro qr rp⟩

theorem occurrencePast_ancestors (word : List α) (p : Fin word.length) :
    (occurrencePast word.get (word.get p) (priorTimes p)).map word.get =
      ancestors (word.get p) (cartesian (word.take p.val).reverse) := by
  rw [occurrencePast_map,priorTimes_map,ancestors_eq_past]

end DynamicOptimality.Funnel.Warm
