import TangoSquared.Paper20261030.PrimaryRectangleBound

/-!
# Verified abstract Tango-squared execution bound

`abstractWork` counts the actual inner accesses and genuine secondary
flips, including completion-root flips. This is the completed counting
part of the upper bound. It is not a physical BST cost theorem: balanced
auxiliary operations and the representation simulation remain to be proved.
-/

namespace TangoSquared.Paper20261030.Secondary

open PreferredProjection

variable {α : Type*} [DecidableEq α]

theorem runMemory_append (s : MemoryState α) (xs ys : List α) :
    runMemory s (xs ++ ys) = runMemory (runMemory s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (s.advance x)

theorem memoryCost_append (keys : Finset MemoryKey) (s : MemoryState α) (xs ys : List α) :
    memoryCost keys s (xs ++ ys) = memoryCost keys s xs + memoryCost keys (runMemory s xs) ys := by
  induction xs generalizing s with
  | nil => simp [memoryCost,runMemory]
  | cons x xs ih => simp only [List.cons_append,memoryCost,runMemory,ih]; omega

theorem completionCost_append (primary : PrefRouter α) (xs ys : List α) :
    completionCost primary (xs ++ ys) = completionCost primary xs + completionCost (primary.run xs) ys := by
  induction xs generalizing primary with
  | nil => simp [completionCost,PrefRouter.run]
  | cons x xs ih => simp only [List.cons_append,completionCost,PrefRouter.run,ih]; omega

/-- Exact online composition of states and costs: the suffix starts from
the actual stored state after the prefix. -/
theorem secondaryCost_append {a b : Nat} (reference : DepthTree a b) (s : MemoryState α)
    (xs ys : List α) :
    secondaryCost reference s (xs ++ ys) =
      secondaryCost reference s xs + secondaryCost reference (runMemory s xs) ys := by
  unfold secondaryCost
  rw [memoryCost_append,completionCost_append,memoryKeys_runMemory,runMemory_primary]
  omega

theorem primary_run_terminal (primary : PrefRouter α) (xs : List α)
    (hxs : ∀ x ∈ xs, x ∈ primary.leaves) :
    (primary.run xs).terminal = xs.getLastD primary.terminal := by
  induction xs generalizing primary with
  | nil => rfl
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have ht : ∀ y ∈ xs, y ∈ (primary.access x).leaves := by
      intro y hy
      simpa only [PrefRouter.access_leaves] using hxs y (by simp [hy])
    rw [PrefRouter.run,ih _ ht,PrefRouter.terminal_access x primary hx,List.getLastD_cons]

/-- Every completed request leaves the active preferred endpoint at the
requested leaf; repeated requests have the same interpretation. -/
theorem runMemory_serves (s : MemoryState α) (xs : List α)
    (hxs : ∀ x ∈ xs, x ∈ s.primary.leaves) :
    (runMemory s xs).primary.terminal = xs.getLastD s.primary.terminal := by
  rw [runMemory_primary]
  exact primary_run_terminal s.primary xs hxs

end TangoSquared.Paper20261030.Secondary

namespace TangoSquared.Paper20261030.Dyadic

open Rectangles Secondary

def abstractWork {h : Nat} (reference : DepthTree 0 h) (xs : List Int) : Nat :=
  (canonical (h + 1) 0).depthAccessCount xs +
    secondaryCost reference (MemoryState.initial (canonical (h + 1) 0)) xs

/-- Actual inner accesses and secondary flips of the initialized online
abstract algorithm are bounded by the rectangle maximum and linear terms. -/
theorem abstract_work_bound {h : Nat} (reference : DepthTree 0 h) (xs : List Int)
    (hkeys : ∀ x ∈ xs, ValidKey (h + 1) x) :
    abstractWork reference xs ≤ xs.length + 13 * rectangleBound (accessPoints xs) +
      6 * (canonical (h + 1) 0).internalVertices := by
  have hs := secondaryCost_le_rectangles reference xs hkeys
  have hp := primaryWilber_rectangleBound xs hkeys
  have hd := (canonical (h + 1) 0).depth_access_bound xs
  unfold abstractWork
  omega

/-- The primary reference has `2^(h+1)` leaves; this form exposes the full
linear allowance without natural-number subtraction. -/
theorem abstract_work_bound_leaves {h : Nat} (reference : DepthTree 0 h) (xs : List Int)
    (hkeys : ∀ x ∈ xs, ValidKey (h + 1) x) :
    abstractWork reference xs + 6 ≤
      xs.length + 13 * rectangleBound (accessPoints xs) + 6 * 2 ^ (h + 1) := by
  have hb := abstract_work_bound reference xs hkeys
  have hl := Secondary.perfect_leaf_count (canonical_perfect (h + 1) 0)
  have hi := (canonical (h + 1) 0).internal_vertices_leaves
  omega

end TangoSquared.Paper20261030.Dyadic
