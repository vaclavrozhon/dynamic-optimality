import TangoSquared.Paper20261030.PreferredPathSizes
import Mathlib.Data.List.Range

/-!
# Exact total size of the restricted local references

The references below are actual pruned ordered trees, one for every
primary preferred path. The proof derives their sizes from their retained
depth labels and the concrete path partition.
-/

namespace TangoSquared.Paper20261030.LocalReferences

open RouterProjection PreferredProjection

variable {α : Type*}

def vertices : Router α → Nat
  | .empty => 0
  | .leaf _ => 1
  | .fork l r => vertices l + vertices r + 1

theorem vertices_eq_internal_add_leaves (t : Router α) :
    vertices t = Paper20261030.Router.internalCount t + t.leaves.length := by
  induction t with
  | empty => rfl
  | leaf a => rfl
  | fork l r ihl ihr =>
    simp only [vertices,Paper20261030.Router.internalCount,Router.leaves,List.length_append]
    omega

theorem vertices_full (t : Router α) (ht : Paper20261030.Router.Full t) (hne : t ≠ .empty) :
    vertices t + 1 = 2 * t.leaves.length := by
  have := Paper20261030.Router.full_leaf_count t ht hne
  rw [vertices_eq_internal_add_leaves]
  omega

theorem filtered_range_length (n k : Nat) :
    ((List.range n).filter (fun d => decide (k ≤ d))).length = n - k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.filter_append,List.length_append,ih]
    by_cases hk : k ≤ n
    · simp only [List.filter_cons,decide_eq_true hk,↓reduceIte,List.filter_nil,List.length_cons,
        List.length_nil]
      omega
    · simp only [List.filter_cons,decide_eq_false hk,Bool.false_eq_true,↓reduceIte,List.filter_nil,List.length_nil,
        Nat.add_zero]
      omega

def dormantReference (H r : Nat) (B : Router Nat) : Router Nat :=
  B.prune (fun d => decide (H - r - 1 ≤ d))

theorem dormantReference_leaves {H r : Nat} {B : Router Nat}
    (hB : B.leaves = List.range (H + 1)) (hr : r < H) :
    (dormantReference H r B).leaves.length = r + 2 := by
  rw [dormantReference,Router.leaves_prune,hB,filtered_range_length]
  omega

theorem dormantReference_vertices {H r : Nat} {B : Router Nat}
    (hB : B.leaves = List.range (H + 1)) (hr : r < H) :
    vertices (dormantReference H r B) = 2 * r + 3 := by
  have hl := dormantReference_leaves hB hr
  have hne : dormantReference H r B ≠ .empty := by
    intro he
    rw [he] at hl
    change 0 = r + 2 at hl
    omega
  have hv : vertices (dormantReference H r B) + 1 =
      2 * (dormantReference H r B).leaves.length :=
    vertices_full _ (Paper20261030.Router.full_prune _ B) hne
  omega

def localReferences (H : Nat) (B : Router Nat) (t : PrefRouter α) : List (Router Nat) :=
  B :: t.dormantInternal.map (fun r => dormantReference H r B)

theorem localReferences_count (H : Nat) (B : Router Nat) (t : PrefRouter α) :
    (localReferences H B t).length = t.leaves.length := by
  simp only [localReferences,List.length_cons,List.length_map]
  exact t.path_count

/-- The exact `5n-4` storage count for all local secondary references. -/
theorem localReferences_total_size {H : Nat} {B : Router Nat} {t : PrefRouter α}
    (ht : t.Perfect H) (hfull : Paper20261030.Router.Full B)
    (hB : B.leaves = List.range (H + 1)) :
    ((localReferences H B t).map vertices).sum + 4 = 5 * t.leaves.length := by
  have hne : B ≠ .empty := by
    intro he
    have hl := congrArg List.length hB
    simp only [he,Router.leaves,List.length_nil,List.length_range] at hl
    omega
  have hroot := vertices_full B hfull hne
  rw [hB,List.length_range] at hroot
  have hpaths := t.path_internal_partition
  have hcount := t.path_count
  have hnodes := t.internal_vertices_leaves
  have hheight := PrefRouter.perfect_rootInternal ht
  have hdormant := PrefRouter.perfect_dormantInternal_lt ht
  have hsum : ((t.dormantInternal.map (fun r => dormantReference H r B)).map vertices).sum =
      2 * t.dormantInternal.sum + 3 * t.dormantInternal.length := by
    have hm : ((t.dormantInternal.map (fun r => dormantReference H r B)).map vertices) =
        t.dormantInternal.map (fun r => 2 * r + 3) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro r hr
      exact dormantReference_vertices hB (hdormant r hr)
    rw [hm]
    induction t.dormantInternal with
    | nil => rfl
    | cons r rs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      omega
  simp only [localReferences,List.map_cons,List.sum_cons,hsum]
  omega

end TangoSquared.Paper20261030.LocalReferences
