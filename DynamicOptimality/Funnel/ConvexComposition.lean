import DynamicOptimality.Funnel.LocalComposition
import DynamicOptimality.Funnel.WarmRun

/-! # Convex composition of closed-rectangle funnel switches

A monotone map names the disjoint key intervals. Its image word is the
component template; filtering by one label gives that component's access word.
The proof accounts for nine units per access and telescopes the nonnegative
mixed-edge potential from the empty warm history.
-/

namespace DynamicOptimality.Funnel.Warm

open ChaCha.MTR ChaCha.MTR.Tree ChaCha.ConvexSearchQuotient

theorem clipped_eq_map (label : Int → Int) (history : List Int) (lo hi : Int)
    (range : ∀ q ∈ history, lo ≤ label q ∧ label q ≤ hi) :
    clipped label lo hi history = history.map label := by
  unfold clipped
  congr 1
  exact List.filter_eq_self.mpr (fun q hq => decide_eq_true (range q hq))

theorem history_access_composition (label : Int → Int) (mono : Monotone label)
    (history : List Int) (x lo hi : Int)
    (lower : lo ≤ label x) (upper : label x ≤ hi)
    (range : ∀ q ∈ history, lo ≤ label q ∧ label q ≤ hi) :
    pathCost history x + 2 * mixed label (cartesian (x :: history)) ≤
      pathCost (history.map label) (label x) +
      pathCost (history.filter (fun q => decide (label q = label x))) x +
      2 * mixed label (cartesian history) + 9 := by
  have treeRange : ∀ q ∈ inorder (cartesian history), lo ≤ label q ∧ label q ≤ hi := by
    intro q member
    exact range q ((mem_cartesian history q).mp member)
  have bound := access_composition label mono (cartesian history) (ordered_cartesian history)
    x lo hi lower upper treeRange
  rw [access_cartesian,project_cartesian label mono,clipped_eq_map label history lo hi range,
    ← convex_ancestors_eq_filter history label mono x] at bound
  exact bound

def componentRuns (label : Int → Int) (components : Finset Int) (history word : List Int) : Nat :=
  ∑ c ∈ components, pathRun (history.filter (fun q => decide (label q = c)))
    (word.filter (fun q => decide (label q = c)))

theorem componentRuns_cons (label : Int → Int) (components : Finset Int)
    (history : List Int) (x : Int) (rest : List Int) (own : label x ∈ components) :
    componentRuns label components history (x :: rest) =
      pathCost (history.filter (fun q => decide (label q = label x))) x +
      componentRuns label components (x :: history) rest := by
  unfold componentRuns
  have term : ∀ c ∈ components,
      pathRun (history.filter (fun q => decide (label q = c)))
          ((x :: rest).filter (fun q => decide (label q = c))) =
        (if c = label x then pathCost (history.filter (fun q => decide (label q = label x))) x else 0) +
        pathRun ((x :: history).filter (fun q => decide (label q = c)))
          (rest.filter (fun q => decide (label q = c))) := by
    intro c _
    by_cases same : label x = c
    · subst c
      simp [pathRun]
    · simp [same,Ne.symm same]
  rw [Finset.sum_congr rfl term,Finset.sum_add_distrib]
  simp [own]

theorem pathRun_composition (label : Int → Int) (mono : Monotone label)
    (components : Finset Int) (history word : List Int) (lo hi : Int)
    (historyRange : ∀ q ∈ history, lo ≤ label q ∧ label q ≤ hi)
    (wordRange : ∀ q ∈ word, lo ≤ label q ∧ label q ≤ hi)
    (covered : ∀ q ∈ word, label q ∈ components) :
    pathRun history word + 2 * mixed label (cartesian (word.reverse ++ history)) ≤
      pathRun (history.map label) (word.map label) +
      componentRuns label components history word +
      2 * mixed label (cartesian history) + 9 * word.length := by
  induction word generalizing history with
  | nil => simp [pathRun,componentRuns]
  | cons x rest ih =>
    have queryRange := wordRange x List.mem_cons_self
    have nextRange : ∀ q ∈ x :: history, lo ≤ label q ∧ label q ≤ hi := by
      intro q member
      rcases List.mem_cons.mp member with rfl | member
      · exact queryRange
      · exact historyRange q member
    have restRange : ∀ q ∈ rest, lo ≤ label q ∧ label q ≤ hi :=
      fun q hq => wordRange q (List.mem_cons_of_mem _ hq)
    have restCovered : ∀ q ∈ rest, label q ∈ components :=
      fun q hq => covered q (List.mem_cons_of_mem _ hq)
    have bound := ih (x :: history) nextRange restRange restCovered
    have localBound := history_access_composition label mono history x lo hi
      queryRange.1 queryRange.2 historyRange
    rw [componentRuns_cons label components history x rest (covered x List.mem_cons_self)]
    simp only [pathRun,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append,
      List.length_cons] at bound ⊢
    omega

end DynamicOptimality.Funnel.Warm

namespace DynamicOptimality.Funnel

open Warm

/-- Convex interval composition for the exact repeated-key funnel count.
The finite component set may include empty components. -/
theorem convex_composition_bounded (label : Int → Int) (mono : Monotone label)
    (word : List Int) (components : Finset Int) (lo hi : Int)
    (range : ∀ q ∈ word, lo ≤ label q ∧ label q ≤ hi)
    (covered : ∀ q ∈ word, label q ∈ components) :
    wordCount word ≤ wordCount (word.map label) +
      (∑ c ∈ components, wordCount (word.filter (fun q => decide (label q = c)))) +
      9 * word.length := by
  have bound := pathRun_composition label mono components [] word lo hi
    (by simp) range covered
  simp only [List.map_nil,List.filter_nil,cartesian_nil,mixed,List.append_nil,Nat.mul_zero,
    Nat.add_zero,componentRuns,← wordCount_eq_pathRun] at bound
  omega

/-- No numerical interval endpoints are part of the final theorem. -/
theorem convex_composition (label : Int → Int) (mono : Monotone label) (word : List Int) :
    wordCount word ≤ wordCount (word.map label) +
      (∑ c ∈ (word.map label).toFinset,
        wordCount (word.filter (fun q => decide (label q = c)))) + 9 * word.length := by
  cases word with
  | nil => simp
  | cons x rest =>
    let components := ((x :: rest).map label).toFinset
    have nonempty : components.Nonempty := ⟨label x,by simp [components]⟩
    have covered : ∀ q ∈ x :: rest, label q ∈ components := by
      intro q member
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨q,member,rfl⟩)
    exact convex_composition_bounded label mono (x :: rest) components
      (components.min' nonempty) (components.max' nonempty)
      (fun q member => ⟨Finset.min'_le _ _ (covered q member),
        Finset.le_max' _ _ (covered q member)⟩) covered

end DynamicOptimality.Funnel
