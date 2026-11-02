import MultiSplay.ForestSplayRun
import MultiSplay.RawForestSplayComparison

/-!
# Universal splay-side comparison for multisplay

`DistinctSplayTrace` is the supplied physical execution: every search and split
uses the standard bottom-up splay rules, every join reuses the current children,
and current keys are distinct. The comparator realizes exactly the same domain
word, but its component shapes and its preparation rotations are arbitrary.

The theorem constructs the bounded normalizer, all local ordinal coordinates,
the global placements, and the complete persistent interface history. The
constant is uniform in component capacity, alphabets, initial shapes, and the
whole execution. This is the original interface factor; E(G) is not used.
-/

namespace MultiSplay.CommonForest

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder size)

variable {α : Type*}

/-- The portable raw-forest splay theorem. The supplied actual run, rather than
an existentially chosen replacement, receives the cost bound. -/
theorem forest_splay_bound :
    ∃ constant : Nat, 0 < constant ∧ ∀ (α : Type*) [Inhabited α] (capacity : Nat)
      {sources targets before after : List (RawTree α)} {word : List (Event α)} {budget cost : Nat},
      Program sources word targets budget → Capacity capacity sources →
      (∀ event ∈ word, Domains.JoinFits capacity event) →
      DistinctSplayTrace before word after cost →
      before.map inorder = sources.map inorder →
      cost ≤ constant * ((before.map size).sum + before.length + budget) *
        Splay.Analysis.targetFactor capacity := by
  obtain ⟨constant, positive, bound⟩ := exists_splay_comparison
  refine ⟨constant, positive, ?_⟩
  intro α _ capacity sources targets before after word budget cost comparator fits joins actual domains
  obtain ⟨final, work, constructed, _, paid⟩ := bound α capacity comparator fits joins domains
  have exactCost := (actual.deterministic constructed (List.Perm.refl _)).2
  exact exactCost ▸ paid

theorem UniqueKeys.context_middle {front selected back : List (RawTree α)}
    (unique : UniqueKeys (front++selected++back)) : UniqueKeys selected := by
  change ((front++selected++back).flatMap inorder).Nodup at unique
  simp only [List.flatMap_append] at unique
  exact (List.nodup_append'.mp (List.nodup_append'.mp unique).1).2.1

theorem Step.pointer {before after : List (RawTree α)} {word : List (Event α)} {cost : Nat}
    (step : Step Auxiliary.Splay idle before word after cost) (unique : UniqueKeys before) :
    Step PointerSplay idle before word after cost := by
  induction step with
  | search execution => exact .search ⟨execution, execution.pointer (unique.component (by simp))⟩
  | split execution => exact .split ⟨execution, execution.pointer (unique.component (by simp))⟩
  | join left right pivot => exact .join left right pivot
  | prepare execution => exact .prepare execution
  | context step front back ih => exact (ih unique.context_middle).context front back
  | reorder order => exact .reorder order

/-- The same bounded run also carries concrete pointer implementations of
every constituent splay, with `3 * rotations + 1` pointer operations. -/
theorem DistinctSplayTrace.toPointer {before after : List (RawTree α)} {word : List (Event α)} {cost : Nat}
    (trace : DistinctSplayTrace before word after cost) : PointerSplayTrace before word after cost := by
  induction trace with
  | nil => exact .nil _
  | cons unique step remaining ih => exact .cons (step.pointer unique) ih

end MultiSplay.CommonForest
