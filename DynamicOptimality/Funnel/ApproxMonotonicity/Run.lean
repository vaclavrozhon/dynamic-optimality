import DynamicOptimality.Funnel.ApproxMonotonicity.Promotion
import DynamicOptimality.Funnel.WarmRun

/-! # Approximate monotonicity of the actual geometric funnel count

The intermediate crossing run allows warm insertion of previously unseen
keys. This is only a combinatorial accounting device: its exact relation to
`wordCount` is supplied by the already proved warm path identity. No paid
BST execution, key-universe expansion, or comparison oracle is assumed.
-/

namespace DynamicOptimality.Funnel.ApproxMonotonicity

open ChaCha.MTR ChaCha.MTR.Tree Warm
variable {α : Type*} [LinearOrder α]

def crossingRun (tree : Tree α) : List α → Nat
  | [] => 0
  | x :: rest => crossingDepth x tree + crossingRun (access x tree) rest

/-- A single earlier promotion changes the total future crossing cost by
at most four times its crossing depth in the distinguished subtree. -/
theorem Promotion.run_bound {y : α} {before after focus : Tree α}
    (related : Promotion y before after focus) (ordered : Ordered before) (word : List α) :
    crossingRun before word ≤ crossingRun after word + 4 * crossingDepth y focus := by
  induction word generalizing before after focus with
  | nil => simp [crossingRun]
  | cons x rest ih =>
    rcases lt_trichotomy x y with xy | rfl | yx
    · have localBound := related.upper_charge ordered none x xy
      have later := ih (related.advance_above x xy) (ordered_access x before ordered)
      simp only [crossingRun,crossingDepth] at localBound later ⊢
      omega
    · have localBound := related.equal_charge none
      have equal := related.access_eq
      simp only [crossingRun,crossingDepth,equal] at localBound ⊢
      omega
    · have localBound := related.lower_charge ordered none x yx
      have later := ih (related.advance_below x yx) (ordered_access x before ordered)
      simp only [crossingRun,crossingDepth] at localBound later ⊢
      omega

/-- The factor four follows directly by induction on a subsequence witness.
Deleting its first request uses the one-promotion bound for the entire
remaining smaller word, avoiding a separate reverse deletion schedule. -/
theorem crossingRun_sublist {small large : List α} (sublist : small.Sublist large)
    (tree : Tree α) (ordered : Ordered tree) :
    crossingRun tree small ≤ 4 * crossingRun tree large := by
  induction sublist generalizing tree with
  | slnil => simp [crossingRun]
  | @cons small large x sublist ih =>
    have perturbation := (Promotion.root (y := x) tree).run_bound ordered small
    have rest := ih (access x tree) (ordered_access x tree ordered)
    simp only [crossingRun]
    omega
  | cons_cons x sublist ih =>
    have rest := ih (access x tree) (ordered_access x tree ordered)
    simp only [crossingRun]
    omega

private theorem map_some_changes (previous : Option Bool) (word : List Bool) :
    changesFrom (previous.map some) (word.map some) = changesFrom previous word := by
  induction word generalizing previous with
  | nil => rfl
  | cons a word ih =>
    simp only [List.map_cons,changesFrom,← Option.map_some a some,ih]
    congr 1
    cases previous <;> simp [changeStep]

private theorem append_one_bounds {β : Type*} [DecidableEq β]
    (previous : Option β) (word : List β) (a : β) :
    changesFrom previous word ≤ changesFrom previous (word ++ [a]) ∧
      changesFrom previous (word ++ [a]) ≤ changesFrom previous word + 1 := by
  induction word generalizing previous with
  | nil =>
    have bound := changeStep_le previous a
    simp only [List.nil_append,changesFrom,Nat.add_zero]
    omega
  | cons b word ih =>
    have bound := ih (some b)
    simp only [List.cons_append,changesFrom]
    omega

theorem crossingDepth_bounds (x : α) (tree : Tree α) :
    changes (sidePath x tree) ≤ crossingDepth x tree ∧
      crossingDepth x tree ≤ changes (sidePath x tree) + 2 := by
  have bounds := append_one_bounds (none : Option (Option Bool)) ((sidePath x tree).map some) none
  have mapped := map_some_changes none (sidePath x tree)
  simp only [Option.map_none] at mapped
  simp only [crossingDepth,crossingFrom,Option.map_none,changes]
  omega

theorem warm_crossingRun_bounds (history word : List α) :
    pathRun history word ≤ crossingRun (cartesian history) word ∧
      crossingRun (cartesian history) word ≤ pathRun history word + 2 * word.length := by
  induction word generalizing history with
  | nil => simp [crossingRun,pathRun]
  | cons x rest ih =>
    have current := crossingDepth_bounds x (cartesian history)
    have later := ih (x :: history)
    simp only [crossingRun,pathRun,access_cartesian,List.length_cons]
    change changes (sidePath x (cartesian history)) ≤ _ ∧ _ at current
    change pathCost history x ≤ _ ∧ _ ≤ pathCost history x + 2 at current
    omega

end DynamicOptimality.Funnel.ApproxMonotonicity

namespace DynamicOptimality.Funnel

variable {α : Type*} [LinearOrder α]

/-- Levy--Tarjan approximate subsequence monotonicity, with the explicit
linear warm-initialization term and the repository's geometric funnel count.
Repeated keys and empty words are included. -/
theorem wordCount_sublist {small large : List α} (sublist : small.Sublist large) :
    wordCount small ≤ 4 * wordCount large + 8 * large.length := by
  have monotone := ApproxMonotonicity.crossingRun_sublist sublist
    (.empty : ChaCha.MTR.Tree α) (by simp [ChaCha.MTR.Tree.Ordered,ChaCha.MTR.Tree.inorder])
  have lower := (ApproxMonotonicity.warm_crossingRun_bounds [] small).1
  have upper := (ApproxMonotonicity.warm_crossingRun_bounds [] large).2
  rw [Warm.wordCount_eq_pathRun,Warm.wordCount_eq_pathRun]
  simp only [Warm.cartesian] at lower upper
  omega

end DynamicOptimality.Funnel
