import TangoSquared.Paper20261030.AbstractTango
import TangoSquared.Paper20261030.Restriction

/-!
# Sizes of the actual primary preferred paths

The preferred root component and all off-path components are extracted
recursively from the concrete preference-decorated tree. Their internal
vertex counts partition all primary internal vertices. No numerical path
partition hypothesis is assumed.
-/

namespace TangoSquared.PreferredProjection.PrefRouter

variable {α : Type*}

def rootInternal : PrefRouter α → Nat
  | .leaf _ => 0
  | .fork b l r => (if b then rootInternal r else rootInternal l) + 1

def dormantInternal : PrefRouter α → List Nat
  | .leaf _ => []
  | .fork b l r =>
      if b then l.rootInternal :: (l.dormantInternal ++ r.dormantInternal)
      else l.dormantInternal ++ (r.rootInternal :: r.dormantInternal)

def internalVertices : PrefRouter α → Nat
  | .leaf _ => 0
  | .fork _ l r => internalVertices l + internalVertices r + 1

theorem path_internal_partition (t : PrefRouter α) :
    t.rootInternal + t.dormantInternal.sum = t.internalVertices := by
  induction t with
  | leaf a => rfl
  | fork b l r ihl ihr =>
    cases b <;> simp only [rootInternal,dormantInternal,internalVertices,
      Bool.false_eq_true,↓reduceIte,List.sum_cons,List.sum_append] <;> omega

theorem path_count (t : PrefRouter α) : t.dormantInternal.length + 1 = t.leaves.length := by
  induction t with
  | leaf a => rfl
  | fork b l r ihl ihr =>
    cases b <;> simp only [dormantInternal,leaves,Bool.false_eq_true,↓reduceIte,
      List.length_cons,List.length_append] <;> omega

theorem internal_vertices_leaves (t : PrefRouter α) : t.internalVertices + 1 = t.leaves.length := by
  induction t with
  | leaf a => rfl
  | fork b l r ihl ihr =>
    simp only [internalVertices,leaves,List.length_append]
    omega

/-- Every leaf of the primary tree occurs at the same depth. -/
def Perfect : Nat → PrefRouter α → Prop
  | 0, .leaf _ => True
  | h + 1, .fork _ l r => Perfect h l ∧ Perfect h r
  | _, _ => False

theorem perfect_rootInternal {H : Nat} {t : PrefRouter α} (ht : Perfect H t) :
    t.rootInternal = H := by
  induction H generalizing t with
  | zero => cases t <;> simp_all [Perfect,rootInternal]
  | succ h ih =>
    cases t with
    | leaf a => contradiction
    | fork b l r =>
      obtain ⟨hl,hr⟩ := ht
      cases b <;> simp [rootInternal,ih hl,ih hr]

theorem perfect_dormantInternal_lt {H : Nat} {t : PrefRouter α} (ht : Perfect H t) :
    ∀ r ∈ t.dormantInternal, r < H := by
  induction H generalizing t with
  | zero => cases t <;> simp_all [Perfect,dormantInternal]
  | succ h ih =>
    cases t with
    | leaf a => contradiction
    | fork b l r =>
      obtain ⟨hl,hr⟩ := ht
      intro k hk
      have hli := ih hl
      have hri := ih hr
      cases b <;> simp only [dormantInternal,Bool.false_eq_true,↓reduceIte,
        List.mem_cons,List.mem_append] at hk
      · rcases hk with hk | hk | hk
        · have := hli k hk; omega
        · rw [hk,perfect_rootInternal hr]; omega
        · have := hri k hk; omega
      · rcases hk with hk | hk | hk
        · rw [hk,perfect_rootInternal hl]; omega
        · have := hli k hk; omega
        · have := hri k hk; omega

/-- Actual exit-leaf counts: one completion exit per path, and one extra
sentinel for every dormant path. -/
def localLeafCounts (t : PrefRouter α) : List Nat :=
  (t.rootInternal + 1) :: t.dormantInternal.map (fun r => r + 2)

theorem localLeafCounts_count (t : PrefRouter α) : t.localLeafCounts.length = t.leaves.length := by
  simp only [localLeafCounts,List.length_cons,List.length_map]
  exact path_count t

theorem localLeafCounts_sum (t : PrefRouter α) :
    t.localLeafCounts.sum + 2 = 3 * t.leaves.length := by
  have hp := path_internal_partition t
  have hc := path_count t
  have hi := internal_vertices_leaves t
  have hsum : (t.dormantInternal.map (fun r => r + 2)).sum =
      t.dormantInternal.sum + 2 * t.dormantInternal.length := by
    induction t.dormantInternal with
    | nil => rfl
    | cons a as ih => simp only [List.map_cons,List.sum_cons,List.length_cons]; omega
  simp only [localLeafCounts,List.sum_cons,hsum]
  omega

end TangoSquared.PreferredProjection.PrefRouter
