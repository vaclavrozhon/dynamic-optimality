import DynamicOptimality.Funnel.Alternation
import Mathlib.Data.List.Pairwise

/-! # Contracting monochromatic runs

One representative of each consecutive equal-label run suffices for counting
side changes. Any subsequence with distinct labels remains a subsequence after
this contraction, so deletion costs are charged to repeated runs, not to the
number of physical nodes in a long monochromatic run.
-/

namespace DynamicOptimality.Funnel

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def prependRun (a : α) (word : List α) : List α :=
  if word.head? = some a then word else a :: word

def runHeads : List α → List α
  | [] => []
  | a :: rest => prependRun a (runHeads rest)

@[simp] theorem head_runHeads (word : List α) : (runHeads word).head? = word.head? := by
  cases word with
  | nil => rfl
  | cons a rest =>
    simp only [runHeads,prependRun,List.head?_cons]
    split_ifs with same
    · exact same
    · rfl

theorem runHeads_cons (a : α) (rest : List α) :
    runHeads (a :: rest) = if rest.head? = some a then runHeads rest else a :: runHeads rest := by
  simp only [runHeads,prependRun,head_runHeads]

theorem prependRun_mono (a : α) {small large : List α} (sublist : small.Sublist large) :
    (prependRun a small).Sublist (prependRun a large) := by
  by_cases smallHead : small.head? = some a
  · by_cases largeHead : large.head? = some a
    · simpa [prependRun,smallHead,largeHead] using sublist
    · simpa [prependRun,smallHead,largeHead] using sublist.cons a
  · by_cases largeHead : large.head? = some a
    · cases large with
      | nil => simp at largeHead
      | cons b large =>
        simp only [List.head?_cons,Option.some.injEq] at largeHead
        subst b
        have tail : small.Sublist large := by
          rcases List.sublist_cons_iff.mp sublist with tail | ⟨rest,same,_⟩
          · exact tail
          · exact (smallHead (by simp [same])).elim
        simpa [prependRun,smallHead] using tail.cons_cons a
    · simpa [prependRun,smallHead,largeHead] using sublist.cons_cons a

theorem runHeads_mono {small large : List α} (sublist : small.Sublist large) :
    (runHeads small).Sublist (runHeads large) := by
  induction sublist with
  | slnil => exact List.Sublist.slnil
  | cons a sublist ih =>
    simp only [runHeads,prependRun]
    split_ifs
    · exact ih
    · exact ih.cons a
  | cons_cons a sublist ih => exact prependRun_mono a ih

theorem runHeads_sublist (word : List α) : (runHeads word).Sublist word := by
  induction word with
  | nil => exact List.Sublist.slnil
  | cons a word ih =>
    simp only [runHeads,prependRun]
    split_ifs
    · exact ih.cons a
    · exact ih.cons_cons a

theorem runHeads_eq_of_nodup {word : List α} (nodup : word.Nodup) : runHeads word = word := by
  induction word with
  | nil => rfl
  | cons a word ih =>
    obtain ⟨absent,tail⟩ := List.nodup_cons.mp nodup
    have different : word.head? ≠ some a := by
      intro same
      exact absent (List.mem_of_head? same)
    simp [runHeads_cons,different,ih tail]

theorem nodup_sublist_runHeads {small large : List α} (nodup : small.Nodup)
    (sublist : small.Sublist large) : small.Sublist (runHeads large) := by
  simpa only [runHeads_eq_of_nodup nodup] using runHeads_mono sublist

/-- Contracting equal labels preserves changes after any relabeling. -/
theorem changesFrom_runHeads (label : α → β) (previous : Option β) (word : List α) :
    changesFrom previous ((runHeads word).map label) = changesFrom previous (word.map label) := by
  induction word generalizing previous with
  | nil => rfl
  | cons a word ih =>
    cases word with
    | nil => simp [runHeads,prependRun,changesFrom]
    | cons b word =>
      rw [runHeads_cons]
      by_cases same : b = a
      · subst b
        simp only [List.head?_cons,ite_true,List.map_cons,changesFrom,changeStep,ite_true,Nat.zero_add]
        have tail := ih previous
        simpa only [List.map_cons,changesFrom,changeStep,ite_true,Nat.zero_add] using tail
      · simp only [List.head?_cons,Option.some.injEq,same,↓reduceIte,List.map_cons,changesFrom]
        rw [ih (some (label a))]
        rfl

theorem projection_changes_bound (label : α → β) {small large : List α}
    (nodup : small.Nodup) (sublist : small.Sublist large) :
    changes (large.map label) + 2 * small.length ≤
      changes (small.map label) + 2 * (runHeads large).length := by
  have bound := changes_deletion_bound ((nodup_sublist_runHeads nodup sublist).map label)
  simpa only [List.length_map,changes,changesFrom_runHeads] using bound

end DynamicOptimality.Funnel
