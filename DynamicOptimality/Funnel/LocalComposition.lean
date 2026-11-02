import DynamicOptimality.Funnel.MixedCounts
import DynamicOptimality.Funnel.QuotientPrefixBound
import DynamicOptimality.Funnel.SuffixBound
import DynamicOptimality.Funnel.RunBookkeeping

/-! # One access: convex component composition with a mixed-edge potential

The prefix before the first own-component key projects onto the template.
After that first key, every foreign key has the same search side. Repeated
component runs are paid by the change in the number of mixed physical edges.
-/

namespace DynamicOptimality.Funnel.Warm

open ChaCha.MTR ChaCha.MTR.Tree ChaCha.ConvexSearchQuotient

theorem suffix_starts_own (label : Int → Int) (tree : Tree Int) (x : Int) :
    ownSuffix label x tree = [] ∨
      ∃ r rest, ownSuffix label x tree = r :: rest ∧ label r = label x := by
  cases suffix : ownSuffix label x tree with
  | nil => exact Or.inl rfl
  | cons r rest =>
    refine Or.inr ⟨r,rest,rfl,?_⟩
    have stopped := List.head?_dropWhile_not (fun a => decide (label a ≠ label x)) (ancestors x tree)
    have suffixEq : (ancestors x tree).dropWhile (fun a => decide (label a ≠ label x)) = r :: rest := suffix
    rw [suffixEq] at stopped
    simpa only [List.head?_cons,decide_eq_false_iff_not,not_not] using stopped

theorem path_run_account (label : Int → Int) (tree : Tree Int) (x : Int) :
    ((ancestors x tree).map label).toFinset.card +
        ownRuns (fun q => decide (label q = label x)) false (ownSuffix label x tree) +
        (runHeads ((foreignPrefix label x tree).map label)).length ≤
      ((foreignPrefix label x tree).map label).toFinset.card +
        (runHeads ((ancestors x tree).map label)).length + 1 := by
  have foreign : ∀ a ∈ (foreignPrefix label x tree).map label, a ≠ label x := by
    intro a member
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp member
    exact foreignPrefix_ne label x tree hq
  have start : (ownSuffix label x tree).map label = [] ∨
      ∃ rest, (ownSuffix label x tree).map label = label x :: rest := by
    rcases suffix_starts_own label tree x with empty | ⟨r,rest,eq,own⟩
    · exact Or.inl (by simp [empty])
    · exact Or.inr ⟨rest.map label,by simp [eq,own]⟩
  have bound := prefix_suffix_run_account (label x)
    ((foreignPrefix label x tree).map label) ((ownSuffix label x tree).map label) foreign start
  simpa only [← List.map_append,prefix_append_suffix,ownRuns_map] using bound

theorem path_changes_bound (label : Int → Int) (mono : Monotone label)
    (tree : Tree Int) (ordered : Ordered tree) (x lo hi : Int)
    (lower : lo ≤ label x) (upper : label x ≤ hi)
    (range : ∀ q ∈ inorder tree, lo ≤ label q ∧ label q ≤ hi) :
    changes ((ancestors x tree).map (fun q => decide (q < x))) +
        2 * ((ancestors x tree).map label).toFinset.card ≤
      changes ((ancestors (label x) (project label lo hi tree)).map
        (fun z => decide (z < label x))) +
      changes (((ancestors x tree).filter (fun q => decide (label q = label x))).map
        (fun q => decide (q < x))) +
      2 * (runHeads ((ancestors x tree).map label)).length + 3 := by
  have prefixBound := prefix_changes_bound label mono tree ordered x lo hi lower upper range
  have suffix := suffix_changes_bound label mono tree x ordered
  have joined := changes_append_le
    ((foreignPrefix label x tree).map (fun q => decide (q < x)))
    ((ownSuffix label x tree).map (fun q => decide (q < x)))
  rw [← List.map_append,prefix_append_suffix] at joined
  have account := path_run_account label tree x
  omega

/-- The potential is twice the number of physical tree edges whose endpoints
belong to different convex components. The estimate includes insertion of a
previously unseen key and repeated requests. -/
theorem access_composition (label : Int → Int) (mono : Monotone label)
    (tree : Tree Int) (ordered : Ordered tree) (x lo hi : Int)
    (lower : lo ≤ label x) (upper : label x ≤ hi)
    (range : ∀ q ∈ inorder tree, lo ≤ label q ∧ label q ≤ hi) :
    changes ((ancestors x tree).map (fun q => decide (q < x))) +
        2 * mixed label (access x tree) ≤
      changes ((ancestors (label x) (project label lo hi tree)).map
        (fun z => decide (z < label x))) +
      changes (((ancestors x tree).filter (fun q => decide (label q = label x))).map
        (fun q => decide (q < x))) +
      2 * mixed label tree + 9 := by
  have changes := path_changes_bound label mono tree ordered x lo hi lower upper range
  have potential := mixed_access_bound label mono tree x ordered
  have runs := runHeads_length_le ((ancestors x tree).map label)
  omega

end DynamicOptimality.Funnel.Warm
