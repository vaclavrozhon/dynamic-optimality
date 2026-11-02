import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# Actual move-to-root BSTs and the normalized three-key tour

This file uses an ordinary binary tree with keys at internal nodes. `moveToRoot`
performs the usual recursive search and rotations, rather than an abstract
transition relation. Its intended domain is present-key searches in an ordered
BST. The tour lemmas retain four arbitrary hanging subtrees, so their equalities
are not merely tests on isolated three-node trees.
-/

namespace ChaCha.MTR

inductive Tree (α : Type*) where
  | empty : Tree α
  | node (left : Tree α) (key : α) (right : Tree α) : Tree α
  deriving Repr, DecidableEq

namespace Tree

variable {α : Type*}

def inorder : Tree α → List α
  | .empty => []
  | .node l x r => inorder l ++ [x] ++ inorder r

def rootKey : Tree α → Option α
  | .empty => none
  | .node _ x _ => some x

def size : Tree α → Nat
  | .empty => 0
  | .node l _ r => size l + 1 + size r

def rotateRight : Tree α → Tree α
  | .node (.node A a B) b C => .node A a (.node B b C)
  | t => t

def rotateLeft : Tree α → Tree α
  | .node A a (.node B b C) => .node (.node A a B) b C
  | t => t

@[simp] theorem inorder_rotateRight (t : Tree α) :
    inorder (rotateRight t) = inorder t := by
  cases t with
  | empty => rfl
  | node l b C => cases l <;> simp [rotateRight, inorder, List.append_assoc]

@[simp] theorem inorder_rotateLeft (t : Tree α) :
    inorder (rotateLeft t) = inorder t := by
  cases t with
  | empty => rfl
  | node A a r => cases r <;> simp [rotateLeft, inorder, List.append_assoc]

variable [LinearOrder α]

/-- A search depth, with failure distinguished from a zero-depth root query. -/
def searchDepth (x : α) : Tree α → Option Nat
  | .empty => none
  | .node l y r =>
      if x < y then (searchDepth x l).map Nat.succ
      else if y < x then (searchDepth x r).map Nat.succ
      else some 0

/-- Standard bottom-up move-to-root search. -/
def moveToRoot (x : α) : Tree α → Tree α
  | .empty => .empty
  | .node l y r =>
      if x < y then rotateRight (.node (moveToRoot x l) y r)
      else if y < x then rotateLeft (.node l y (moveToRoot x r))
      else .node l y r

/-- A BST has a strictly increasing inorder word. -/
def Ordered (t : Tree α) : Prop := (inorder t).Pairwise (· < ·)

@[simp] theorem inorder_moveToRoot (x : α) (t : Tree α) :
    inorder (moveToRoot x t) = inorder t := by
  induction t with
  | empty => rfl
  | node l y r ihl ihr =>
    simp only [moveToRoot]
    split
    · simp [inorder, ihl]
    · split <;> simp [inorder, ihr]

theorem ordered_moveToRoot (x : α) {t : Tree α} (h : Ordered t) :
    Ordered (moveToRoot x t) := by
  simpa [Ordered] using h

@[simp] theorem moveToRoot_root (l r : Tree α) (x : α) :
    moveToRoot x (.node l x r) = .node l x r := by
  simp [moveToRoot]

@[simp] theorem searchDepth_root (l r : Tree α) (x : α) :
    searchDepth x (.node l x r) = some 0 := by
  simp [searchDepth]

/-- Successful search really brings its requested key to the root. -/
theorem rootKey_moveToRoot_of_searchDepth (x : α) (t : Tree α) (d : Nat)
    (h : searchDepth x t = some d) : rootKey (moveToRoot x t) = some x := by
  induction t generalizing d with
  | empty => simp [searchDepth] at h
  | node l y r ihl ihr =>
    by_cases hxy : x < y
    · simp only [searchDepth, hxy, ↓reduceIte] at h
      cases hs : searchDepth x l with
      | none => simp [hs] at h
      | some e =>
        have hi := ihl e hs
        simp only [moveToRoot, hxy, ↓reduceIte]
        cases hm : moveToRoot x l with
        | empty => simp [hm, rootKey] at hi
        | node A a B =>
          simpa [hm, rotateRight, rootKey] using hi
    · by_cases hyx : y < x
      · simp only [searchDepth, hxy, hyx, ↓reduceIte] at h
        cases hs : searchDepth x r with
        | none => simp [hs] at h
        | some e =>
          have hi := ihr e hs
          simp only [moveToRoot, hxy, hyx, ↓reduceIte]
          cases hm : moveToRoot x r with
          | empty => simp [hm, rootKey] at hi
          | node A a B =>
            simpa [hm, rotateLeft, rootKey] using hi
      · have heq : x = y := le_antisymm (le_of_not_gt hyx) (le_of_not_gt hxy)
        simp [moveToRoot, rootKey, heq]

end Tree

open Tree

/-- The five BST shapes on three fixed ordered keys. -/
inductive Shape3 where
  | t1 | t2 | t3 | t4 | t5
  deriving DecidableEq, Repr

/-- Insert arbitrary hanging trees in the four inorder gaps. -/
def hull3 {α : Type*} (a b c : α) (A B C D : Tree α) : Shape3 → Tree α
  | .t1 => .node A a (.node B b (.node C c D))
  | .t2 => .node A a (.node (.node B b C) c D)
  | .t3 => .node (.node A a B) b (.node C c D)
  | .t4 => .node (.node A a (.node B b C)) c D
  | .t5 => .node (.node (.node A a B) b C) c D

/-- The tour visits every three-key shape. -/
def tour3 : List Shape3 := [.t1, .t3, .t5, .t2, .t4, .t3, .t1]

/-- Queries indexed by their inorder rank: a=0, b=1, c=2. -/
def tourQueries : List (Fin 3) := [1, 2, 0, 2, 1, 0]

variable {α : Type*} [LinearOrder α]

theorem tour_step_1 (a b c : α) (A B C D : Tree α) (hab : a < b) :
    moveToRoot b (hull3 a b c A B C D .t1) = hull3 a b c A B C D .t3 := by
  simp [hull3, moveToRoot, hab, not_lt.mpr (le_of_lt hab), rotateLeft]

theorem tour_step_2 (a b c : α) (A B C D : Tree α) (hbc : b < c) :
    moveToRoot c (hull3 a b c A B C D .t3) = hull3 a b c A B C D .t5 := by
  simp [hull3, moveToRoot, hbc, not_lt.mpr (le_of_lt hbc), rotateLeft]

theorem tour_step_3 (a b c : α) (A B C D : Tree α) (hab : a < b) (hbc : b < c) :
    moveToRoot a (hull3 a b c A B C D .t5) = hull3 a b c A B C D .t2 := by
  simp [hull3, moveToRoot, hab, lt_trans hab hbc, rotateRight]

theorem tour_step_4 (a b c : α) (A B C D : Tree α) (hab : a < b) (hbc : b < c) :
    moveToRoot c (hull3 a b c A B C D .t2) = hull3 a b c A B C D .t4 := by
  simp [hull3, moveToRoot, lt_trans hab hbc,
    not_lt.mpr (le_of_lt (lt_trans hab hbc)), rotateLeft]

theorem tour_step_5 (a b c : α) (A B C D : Tree α) (hab : a < b) (hbc : b < c) :
    moveToRoot b (hull3 a b c A B C D .t4) = hull3 a b c A B C D .t3 := by
  simp [hull3, moveToRoot, hab, hbc, not_lt.mpr (le_of_lt hab),
    rotateLeft, rotateRight]

theorem tour_step_6 (a b c : α) (A B C D : Tree α) (hab : a < b) :
    moveToRoot a (hull3 a b c A B C D .t3) = hull3 a b c A B C D .t1 := by
  simp [hull3, moveToRoot, hab, rotateRight]


/-- Access the three-key skeleton by inorder rank. -/
def key3 (a b c : α) (q : Fin 3) : α :=
  if q.val = 0 then a else if q.val = 1 then b else c

/-- The actual MTR transitions on the five skeleton shapes. -/
def nextShape : Shape3 → Fin 3 → Shape3
  | .t1, q => if q.val = 0 then .t1 else if q.val = 1 then .t3 else .t4
  | .t2, q => if q.val = 0 then .t2 else if q.val = 1 then .t3 else .t4
  | .t3, q => if q.val = 0 then .t1 else if q.val = 1 then .t3 else .t5
  | .t4, q => if q.val = 0 then .t2 else if q.val = 1 then .t3 else .t4
  | .t5, q => if q.val = 0 then .t2 else if q.val = 1 then .t3 else .t5

/-- All fifteen transitions hold with arbitrary hanging subtrees. -/
theorem moveToRoot_hull3 (a b c : α) (A B C D : Tree α)
    (hab : a < b) (hbc : b < c) (s : Shape3) (q : Fin 3) :
    moveToRoot (key3 a b c q) (hull3 a b c A B C D s) =
      hull3 a b c A B C D (nextShape s q) := by
  have hac := lt_trans hab hbc
  cases s <;> fin_cases q <;>
    simp [key3, hull3, moveToRoot, nextShape, hab, hbc, hac,
      not_lt.mpr (le_of_lt hab), not_lt.mpr (le_of_lt hbc),
      not_lt.mpr (le_of_lt hac), rotateLeft, rotateRight]

/-- Two possible primary reference shapes after suppressing unary paths. -/
inductive Reference3 where
  | rightSplit  -- a | (b,c)
  | leftSplit   -- (a,b) | c
  deriving DecidableEq, Repr

/-- Preferences: top split first, lower split second; false means left. -/
abbrev Preferences3 := Bool × Bool

/-- Interval representatives of the three-key skeleton. -/
def preferences3 : Reference3 → Shape3 → Preferences3
  | .rightSplit, .t1 => (false, false)
  | .rightSplit, .t2 => (false, true)
  | .rightSplit, .t3 => (true, false)
  | .rightSplit, .t4 => (true, true)
  | .rightSplit, .t5 => (true, true)
  | .leftSplit, .t1 => (false, false)
  | .leftSplit, .t2 => (false, false)
  | .leftSplit, .t3 => (false, true)
  | .leftSplit, .t4 => (true, false)
  | .leftSplit, .t5 => (true, true)

/-- Updating precisely the primary ancestors of the requested leaf. -/
def updatePreferences3 (r : Reference3) (p : Preferences3) (q : Fin 3) : Preferences3 :=
  match r with
  | .rightSplit =>
    if q.val = 0 then (false, p.2)
    else if q.val = 1 then (true, false) else (true, true)
  | .leftSplit =>
    if q.val = 2 then (true, p.2)
    else if q.val = 0 then (false, false) else (false, true)

/-- Number of changed primary preferences. -/
def bitChanges (p p' : Preferences3) : Nat :=
  (if p.1 = p'.1 then 0 else 1) + (if p.2 = p'.2 then 0 else 1)

/-- The preference table is coherent with actual MTR transitions. -/
theorem preferences3_next (r : Reference3) (s : Shape3) (q : Fin 3) :
    preferences3 r (nextShape s q) = updatePreferences3 r (preferences3 r s) q := by
  cases r <;> cases s <;> fin_cases q <;> decide

/-- A list of requests has exactly one primary flip at every step. -/
def OneFlipPath (r : Reference3) : Shape3 → List (Fin 3) → Prop
  | _, [] => True
  | s, q :: qs =>
      bitChanges (preferences3 r s) (updatePreferences3 r (preferences3 r s) q) = 1 ∧
      OneFlipPath r (nextShape s q) qs

instance (r : Reference3) (s : Shape3) (qs : List (Fin 3)) :
    Decidable (OneFlipPath r s qs) := by
  induction qs generalizing s with
  | nil => exact isTrue True.intro
  | cons q qs ih =>
    unfold OneFlipPath
    exact instDecidableAnd

/-- The physical final skeleton after a request word. -/
def runShape (s : Shape3) (qs : List (Fin 3)) : Shape3 :=
  qs.foldl nextShape s

/-- The six-step tour from the manuscript, checked by Lean's kernel. -/
theorem right_tour_one_flip : OneFlipPath .rightSplit .t1 tourQueries := by decide

theorem right_tour_closed : runShape .t1 tourQueries = .t1 := by decide

/-- Reflection exchanges a with c and left with right. -/
def reflectedTourQueries : List (Fin 3) := [1, 0, 2, 0, 1, 2]

theorem left_tour_one_flip : OneFlipPath .leftSplit .t5 reflectedTourQueries := by decide

theorem left_tour_closed : runShape .t5 reflectedTourQueries = .t5 := by decide

/-- Execute actual move-to-root operations. -/
def run (t : Tree α) (qs : List α) : Tree α := qs.foldl (fun t x => moveToRoot x t) t

/-- Every finite skeleton word lifts to a physical MTR execution, preserving gaps. -/
theorem run_hull3 (a b c : α) (A B C D : Tree α) (hab : a < b) (hbc : b < c)
    (s : Shape3) (qs : List (Fin 3)) :
    run (hull3 a b c A B C D s) (qs.map (key3 a b c)) =
      hull3 a b c A B C D (runShape s qs) := by
  induction qs generalizing s with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.map_cons, run, List.foldl_cons, runShape]
    rw [moveToRoot_hull3 a b c A B C D hab hbc s q]
    exact ih _

/-- A shape's search depth is independent of its hanging subtrees. -/
def shapeDepth : Shape3 → Fin 3 → Nat
  | .t1, q => q.val
  | .t2, q => if q.val = 0 then 0 else if q.val = 1 then 2 else 1
  | .t3, q => if q.val = 1 then 0 else 1
  | .t4, q => if q.val = 0 then 1 else if q.val = 1 then 2 else 0
  | .t5, q => 2 - q.val

theorem searchDepth_hull3 (a b c : α) (A B C D : Tree α)
    (hab : a < b) (hbc : b < c) (s : Shape3) (q : Fin 3) :
    searchDepth (key3 a b c q) (hull3 a b c A B C D s) = some (shapeDepth s q) := by
  have hac := lt_trans hab hbc
  cases s <;> fin_cases q <;>
    simp [key3, hull3, searchDepth, shapeDepth, hab, hbc, hac,
      not_lt.mpr (le_of_lt hab), not_lt.mpr (le_of_lt hbc),
      not_lt.mpr (le_of_lt hac)]

theorem shapeDepth_le_two (s : Shape3) (q : Fin 3) : shapeDepth s q ≤ 2 := by
  cases s <;> fin_cases q <;> decide


/-- The chosen first occurrence of each shape in the respective six-step tour. -/
def tourPhase : Reference3 → Shape3 → Fin 6
  | .rightSplit, .t1 => 0
  | .rightSplit, .t2 => 3
  | .rightSplit, .t3 => 1
  | .rightSplit, .t4 => 4
  | .rightSplit, .t5 => 2
  | .leftSplit, .t1 => 2
  | .leftSplit, .t2 => 4
  | .leftSplit, .t3 => 1
  | .leftSplit, .t4 => 3
  | .leftSplit, .t5 => 0

def queryAtPhase (r : Reference3) (i : Fin 6) : Fin 3 :=
  match r with
  | .rightSplit => ([1, 2, 0, 2, 1, 0] : List (Fin 3)).get i
  | .leftSplit => ([1, 0, 2, 0, 1, 2] : List (Fin 3)).get i

/-- Follow the directed tour from the selected occurrence of s to that of t. -/
def pathBetween (r : Reference3) (s t : Shape3) : List (Fin 3) :=
  let start := (tourPhase r s).val
  let dist := ((tourPhase r t).val + 6 - start) % 6
  (List.range dist).map (fun i => queryAtPhase r ⟨(start + i) % 6, Nat.mod_lt _ (by decide)⟩)

/-- Search-node cost of a skeleton request word. -/
def shapeCost : Shape3 → List (Fin 3) → Nat
  | _, [] => 0
  | s, q :: qs => shapeDepth s q + 1 + shapeCost (nextShape s q) qs

/-- The genuinely finite directed graph calculation behind three-key coercion. -/
theorem pathBetween_spec (r : Reference3) (s t : Shape3) :
    (pathBetween r s t).length ≤ 5 ∧
    runShape s (pathBetween r s t) = t ∧
    OneFlipPath r s (pathBetween r s t) ∧
    shapeCost s (pathBetween r s t) ≤ 15 := by
  cases r <;> cases s <;> cases t <;> decide

/-- Actual search-node cost. All callers below prove the searches successful. -/
def runCost : Tree α → List α → Nat
  | _, [] => 0
  | t, x :: xs => (searchDepth x t).getD 0 + 1 + runCost (moveToRoot x t) xs

theorem runCost_hull3 (a b c : α) (A B C D : Tree α) (hab : a < b) (hbc : b < c)
    (s : Shape3) (qs : List (Fin 3)) :
    runCost (hull3 a b c A B C D s) (qs.map (key3 a b c)) = shapeCost s qs := by
  induction qs generalizing s with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.map_cons, runCost, shapeCost]
    rw [searchDepth_hull3 a b c A B C D hab hbc s q,
      moveToRoot_hull3 a b c A B C D hab hbc s q]
    simpa using congrArg (fun n => shapeDepth s q + 1 + n) (ih (nextShape s q))

/-- Any three-key rooted hull transformation has a concrete bounded MTR simulation.

The normalization conclusion here is explicitly about the induced reference.
The further theorem identifying this with all preferences in an arbitrary ambient
primary reference is a separate bridge, not an assumption hidden in this result.
-/
theorem three_key_simulation (a b c : α) (A B C D : Tree α)
    (hab : a < b) (hbc : b < c) (r : Reference3) (s t : Shape3) :
    ∃ qs : List (Fin 3),
      qs.length ≤ 5 ∧
      run (hull3 a b c A B C D s) (qs.map (key3 a b c)) = hull3 a b c A B C D t ∧
      OneFlipPath r s qs ∧
      runCost (hull3 a b c A B C D s) (qs.map (key3 a b c)) ≤ 15 := by
  refine ⟨pathBetween r s t, ?_⟩
  obtain ⟨hlen, hend, hflip, hcost⟩ := pathBetween_spec r s t
  refine ⟨hlen, ?_, hflip, ?_⟩
  · rw [run_hull3 a b c A B C D hab hbc s, hend]
  · rw [runCost_hull3 a b c A B C D hab hbc s]
    exact hcost


namespace Tree

/-- The physical nodes visited by an ordinary BST search. -/
def searchPath (x : α) : Tree α → List α
  | .empty => []
  | .node l y r => y ::
      (if x < y then searchPath x l else if y < x then searchPath x r else [])

/-- First physical node in a closed key interval. -/
def representative (lo hi : α) : Tree α → Option α
  | .empty => none
  | .node l y r =>
      if y < lo then representative lo hi r
      else if hi < y then representative lo hi l
      else some y

/-- A returned representative belongs to its stated interval. -/
theorem representative_mem_interval (lo hi : α) (t : Tree α) (y : α)
    (h : representative lo hi t = some y) : lo ≤ y ∧ y ≤ hi := by
  induction t with
  | empty => simp [representative] at h
  | node l a r ihl ihr =>
    by_cases hal : a < lo
    · simp only [representative, hal, ↓reduceIte] at h
      exact ihr h
    · by_cases hha : hi < a
      · simp only [representative, hal, hha, ↓reduceIte] at h
        exact ihl h
      · simp only [representative, hal, hha, ↓reduceIte, Option.some.injEq] at h
        subst y
        exact ⟨le_of_not_gt hal, le_of_not_gt hha⟩

/-- The interval representative lies on every search path into that interval.

This direction needs no BST invariant: all recursive comparisons are forced by
interval membership, and the first in-range node is necessarily visited.
-/
theorem representative_on_searchPath (lo hi x y : α) (t : Tree α)
    (hlo : lo ≤ x) (hhi : x ≤ hi) (hrep : representative lo hi t = some y) :
    y ∈ searchPath x t := by
  induction t with
  | empty => simp [representative] at hrep
  | node l a r ihl ihr =>
    by_cases hal : a < lo
    · have hax : a < x := lt_of_lt_of_le hal hlo
      simp only [representative, hal, ↓reduceIte] at hrep
      simp only [searchPath, not_lt.mpr (le_of_lt hax), hax, ↓reduceIte,
        List.mem_cons]
      exact Or.inr (ihr hrep)
    · by_cases hha : hi < a
      · have hxa : x < a := lt_of_le_of_lt hhi hha
        simp only [representative, hal, hha, ↓reduceIte] at hrep
        simp only [searchPath, hxa, ↓reduceIte, List.mem_cons]
        exact Or.inr (ihl hrep)
      · simp only [representative, hal, hha, ↓reduceIte, Option.some.injEq] at hrep
        subst y
        simp [searchPath]

/-- A successful in-range search guarantees that the interval is represented. -/
theorem representative_exists_of_searchDepth (lo hi x : α) (t : Tree α) (d : Nat)
    (hlo : lo ≤ x) (hhi : x ≤ hi) (hs : searchDepth x t = some d) :
    ∃ y, representative lo hi t = some y := by
  induction t generalizing d with
  | empty => simp [searchDepth] at hs
  | node l a r ihl ihr =>
    by_cases hal : a < lo
    · have hax : a < x := lt_of_lt_of_le hal hlo
      simp only [searchDepth, not_lt.mpr (le_of_lt hax), hax, ↓reduceIte] at hs
      cases hsr : searchDepth x r with
      | none => simp [hsr] at hs
      | some e =>
        obtain ⟨y, hy⟩ := ihr e hsr
        exact ⟨y, by simpa [representative, hal] using hy⟩
    · by_cases hha : hi < a
      · have hxa : x < a := lt_of_le_of_lt hhi hha
        simp only [searchDepth, hxa, ↓reduceIte] at hs
        cases hsl : searchDepth x l with
        | none => simp [hsl] at hs
        | some e =>
          obtain ⟨y, hy⟩ := ihl e hsl
          exact ⟨y, by simpa [representative, hal, hha] using hy⟩
      · exact ⟨a, by simp [representative, hal, hha]⟩

/-- A set of keys forms a rooted hull if their complete successful search paths
are contained in it. This includes ancestor closure, rather than only membership.
-/
def RootedHull (t : Tree α) (K : Set α) : Prop :=
  ∀ x ∈ K, (∃ d, searchDepth x t = some d) ∧ ∀ y ∈ searchPath x t, y ∈ K

/-- Any primary interval meeting a rooted hull has its representative in the hull. -/
theorem representative_in_rootedHull (lo hi x : α) (t : Tree α) (K : Set α)
    (hhull : RootedHull t K) (hx : x ∈ K) (hlo : lo ≤ x) (hhi : x ≤ hi) :
    ∃ y ∈ K, representative lo hi t = some y ∧ lo ≤ y ∧ y ≤ hi := by
  obtain ⟨⟨d, hd⟩, hpath⟩ := hhull x hx
  obtain ⟨y, hy⟩ := representative_exists_of_searchDepth lo hi x t d hlo hhi hd
  exact ⟨y, hpath y (representative_on_searchPath lo hi x y t hlo hhi hy),
    hy, representative_mem_interval lo hi t y hy⟩

end Tree

end ChaCha.MTR
