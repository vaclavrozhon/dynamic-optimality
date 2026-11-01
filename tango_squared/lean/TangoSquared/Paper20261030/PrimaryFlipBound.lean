import TangoSquared.Paper20261030.TangoRestriction
import TangoSquared.Paper20261030.PreferredPathSizes
import TangoSquared.FlipAccounting

/-!
# Actual primary flips and depth-access count

Every original request performs its concrete increasing head-switch trace
and one final completion access. The primary flip bound compares these
operations with first-initialization-free branch alternations at every
primary vertex.
-/

namespace TangoSquared.PreferredProjection.PrefRouter

variable {α : Type*} [DecidableEq α]

def branchWord (L R : List α) (xs : List α) : List Bool :=
  xs.filterMap (fun x => if x ∈ L then some false else if x ∈ R then some true else none)

def leftWord (L : List α) (xs : List α) : List α := xs.filter (fun x => decide (x ∈ L))

def rightWord (L R : List α) (xs : List α) : List α :=
  xs.filter (fun x => decide (x ∉ L ∧ x ∈ R))

theorem runFlips_fork (b : Bool) (l r : PrefRouter α) (xs : List α) :
    runFlips (.fork b l r) xs = changesFrom b (branchWord l.leaves r.leaves xs) +
      l.runFlips (leftWord l.leaves xs) + r.runFlips (rightWord l.leaves r.leaves xs) := by
  induction xs generalizing b l r with
  | nil => simp [runFlips,branchWord,leftWord,rightWord]
  | cons x xs ih =>
    by_cases hl : x ∈ l.leaves
    · have htail := ih false (l.access x) r
      simp only [access_leaves] at htail
      simp only [runFlips,accessFlips,access,if_pos hl]
      rw [htail]
      simp [branchWord,leftWord,rightWord,hl,changesFrom,runFlips]
      omega
    · by_cases hr : x ∈ r.leaves
      · have htail := ih true l (r.access x)
        simp only [access_leaves] at htail
        simp only [runFlips,accessFlips,access,if_neg hl,if_pos hr]
        rw [htail]
        simp [branchWord,leftWord,rightWord,hl,hr,changesFrom,runFlips]
        omega
      · have htail := ih b l r
        simp only [runFlips,accessFlips,access,if_neg hl,if_neg hr,Nat.zero_add]
        rw [htail]
        simp [branchWord,leftWord,rightWord,hl,hr]

def primaryWilber : PrefRouter α → List α → Nat
  | .leaf _, _ => 0
  | .fork _ l r, xs =>
      alternations (branchWord l.leaves r.leaves xs) +
        primaryWilber l (leftWord l.leaves xs) +
        primaryWilber r (rightWord l.leaves r.leaves xs)

theorem runFlips_leaf (y : α) (xs : List α) : runFlips (.leaf y) xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [runFlips,accessFlips,access,Nat.zero_add] using ih

/-- First visits contribute at most one initialized flip per internal vertex. -/
theorem primary_flip_bound (t : PrefRouter α) (xs : List α) :
    t.runFlips xs ≤ t.primaryWilber xs + t.internalVertices := by
  induction t generalizing xs with
  | leaf y => simp only [runFlips_leaf,primaryWilber,internalVertices,Nat.add_zero,le_refl]
  | fork b l r ihl ihr =>
    rw [runFlips_fork]
    have hl := ihl (leftWord l.leaves xs)
    have hr := ihr (rightWord l.leaves r.leaves xs)
    have hb := FlipAccounting.changesFrom_le_alternations_add_one b (branchWord l.leaves r.leaves xs)
    simp only [primaryWilber,internalVertices]
    omega

def depthAccessCount (t : PrefRouter α) : List α → Nat
  | [] => 0
  | x :: xs => (t.exitDepths x).length + 1 + depthAccessCount (t.access x) xs

theorem depthAccessCount_eq (t : PrefRouter α) (xs : List α) :
    t.depthAccessCount xs = xs.length + t.runFlips xs := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    simp only [depthAccessCount,exitDepths_length,runFlips,List.length_cons,ih]
    omega

/-- Exact operation count and its Wilber upper bound for the terminating loop. -/
theorem depth_access_bound (t : PrefRouter α) (xs : List α) :
    t.depthAccessCount xs ≤ xs.length + t.primaryWilber xs + t.internalVertices := by
  rw [depthAccessCount_eq]
  have := t.primary_flip_bound xs
  omega

end TangoSquared.PreferredProjection.PrefRouter
