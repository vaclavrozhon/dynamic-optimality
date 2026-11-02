import ChaCha.Recency
import Mathlib.Data.Int.Interval

/-!
# Actual search paths in a fixed convex key quotient

The projection keeps the first representative of each monotone cell and
recursively removes that cell from its descendants. The output is an
actual tree of integer cell labels, not an assumed comparator witness.
The path theorem works even for a proper interval of cells.
-/

namespace ChaCha.ConvexSearchQuotient

open MTR MTR.Tree

def project (f : Int → Int) (lo hi : Int) : Tree Int → Tree Int
  | .empty => .empty
  | .node l x r =>
      if f x < lo then project f lo hi r
      else if hi < f x then project f lo hi l
      else .node (project f lo (f x - 1) l) (f x)
        (project f (f x + 1) hi r)

theorem searchPath_sublist (f : Int → Int) (hf : Monotone f)
    (t : Tree Int) (x lo hi : Int) (hlo : lo ≤ f x) (hhi : f x ≤ hi) :
    (searchPath (f x) (project f lo hi t)).Sublist ((searchPath x t).map f) := by
  induction t generalizing lo hi with
  | empty => simp [project, searchPath]
  | node l y r ihl ihr =>
    by_cases hyl : f y < lo
    · have hyx : y < x := by
        by_contra h
        have := hf (show x ≤ y by omega)
        omega
      have hxy : ¬ x < y := by omega
      simp only [project, hyl, ↓reduceIte, searchPath, hxy, hyx, List.map_cons]
      exact (ihr lo hi hlo hhi).cons _
    · by_cases hhy : hi < f y
      · have hxy : x < y := by
          by_contra h
          have := hf (show y ≤ x by omega)
          omega
        simp only [project, hyl, hhy, ↓reduceIte, searchPath, hxy, List.map_cons]
        exact (ihl lo hi hlo hhi).cons _
      · simp only [project, hyl, hhy, ↓reduceIte]
        by_cases hxy : f x < f y
        · have hxy' : x < y := by
            by_contra h
            have := hf (show y ≤ x by omega)
            omega
          simp only [searchPath, hxy, hxy', ↓reduceIte, List.map_cons]
          exact (ihl lo (f y - 1) hlo (by omega)).cons_cons _
        · by_cases hyx : f y < f x
          · have hyx' : y < x := by
              by_contra h
              have := hf (show x ≤ y by omega)
              omega
            have hxy' : ¬ x < y := by omega
            simp only [searchPath, hxy, hyx, hxy', hyx', ↓reduceIte, List.map_cons]
            exact (ihr (f y + 1) hi (by omega) hhi).cons_cons _
          · have heq : f x = f y := by omega
            simp only [searchPath, hxy, hyx, ↓reduceIte]
            by_cases hxy' : x < y
            · simp only [hxy', ↓reduceIte, List.map_cons]
              exact List.Sublist.cons_cons _ (List.nil_sublist _)
            · by_cases hyx' : y < x
              · simp only [hxy', hyx', ↓reduceIte, List.map_cons]
                exact List.Sublist.cons_cons _ (List.nil_sublist _)
              · simp [hxy', hyx']

theorem searchPath_length_le (f : Int → Int) (hf : Monotone f)
    (t : Tree Int) (x lo hi : Int) (hlo : lo ≤ f x) (hhi : f x ≤ hi) :
    (searchPath (f x) (project f lo hi t)).length ≤ (searchPath x t).length := by
  simpa using (searchPath_sublist f hf t x lo hi hlo hhi).length_le

theorem inorder_bounds (f : Int → Int) (t : Tree Int) (lo hi : Int)
    {z : Int} (hz : z ∈ inorder (project f lo hi t)) : lo ≤ z ∧ z ≤ hi := by
  induction t generalizing lo hi with
  | empty => simp [project, inorder] at hz
  | node l x r ihl ihr =>
    by_cases hxl : f x < lo
    · simp only [project, hxl, ↓reduceIte] at hz
      exact ihr lo hi hz
    · by_cases hhx : hi < f x
      · simp only [project, hxl, hhx, ↓reduceIte] at hz
        exact ihl lo hi hz
      · simp only [project, hxl, hhx, ↓reduceIte, inorder,
          List.mem_append, List.mem_singleton] at hz
        rcases hz with (hz | hz) | hz
        · have := ihl lo (f x - 1) hz
          constructor <;> omega
        · subst z
          constructor <;> omega
        · have := ihr (f x + 1) hi hz
          constructor <;> omega

theorem ordered_project (f : Int → Int) (t : Tree Int) (lo hi : Int) :
    Ordered (project f lo hi t) := by
  induction t generalizing lo hi with
  | empty => simp [project, Ordered, inorder]
  | node l x r ihl ihr =>
    by_cases hxl : f x < lo
    · simpa only [project, hxl, ↓reduceIte] using ihr lo hi
    · by_cases hhx : hi < f x
      · simpa only [project, hxl, hhx, ↓reduceIte] using ihl lo hi
      · simp only [project, hxl, hhx, ↓reduceIte, Ordered, inorder,
          List.pairwise_append, List.pairwise_singleton, List.mem_singleton]
        refine ⟨⟨ihl lo (f x - 1), trivial, ?_⟩, ihr (f x + 1) hi, ?_⟩
        · intro a ha b hb
          subst b
          have := inorder_bounds f l lo (f x - 1) ha
          omega
        · intro a ha b hb
          have hbr := inorder_bounds f r (f x + 1) hi hb
          simp only [List.mem_append, List.mem_singleton] at ha
          rcases ha with ha | ha
          · have := inorder_bounds f l lo (f x - 1) ha
            omega
          · subst a
            omega

theorem project_rotateRight_target (f : Int → Int) (lo hi x y : Int)
    (A B C : Tree Int) (hxy : f x ≤ f y) :
    project f lo hi (.node A x (.node B y C)) =
      if lo ≤ f x ∧ f x < f y ∧ f y ≤ hi then
        rotateRight (project f lo hi (.node (.node A x B) y C))
      else project f lo hi (.node (.node A x B) y C) := by
  by_cases hyl : f y < lo
  · have hxl : f x < lo := by omega
    have hn : ¬ (lo ≤ f x ∧ f x < f y ∧ f y ≤ hi) := by omega
    simp [project, hyl, hxl, hn]
  · by_cases hhy : hi < f y
    · have hn : ¬ (lo ≤ f x ∧ f x < f y ∧ f y ≤ hi) := by omega
      by_cases hxl : f x < lo
      · simp [project, hyl, hhy, hxl, hn]
      · by_cases hhx : hi < f x
        · simp [project, hyl, hhy, hxl, hhx, hn]
        · have hyl' : ¬ f y < f x + 1 := by omega
          simp [project, hyl, hhy, hxl, hhx, hn, hyl']
    · by_cases hxl : f x < lo
      · have hn : ¬ (lo ≤ f x ∧ f x < f y ∧ f y ≤ hi) := by omega
        have hxhi : ¬ (f y - 1 < f x) := by omega
        simp [project, hyl, hhy, hxl, hn]
      · by_cases heq : f x = f y
        · have hn : ¬ (lo ≤ f x ∧ f x < f y ∧ f y ≤ hi) := by omega
          simp [project, hyl, hhy, heq]
        · have hcond : lo ≤ f x ∧ f x < f y ∧ f y ≤ hi := by omega
          have hhx : ¬ hi < f x := by omega
          have hxhi : ¬ f y - 1 < f x := by omega
          have hyl' : ¬ f y < f x + 1 := by omega
          simp [project, hyl, hhy, hxl, hhx, hxhi, hyl', hcond, rotateRight]

theorem project_rotateLeft_target (f : Int → Int) (lo hi x y : Int)
    (A B C : Tree Int) (hxy : f x ≤ f y) :
    project f lo hi (.node (.node A x B) y C) =
      if lo ≤ f x ∧ f x < f y ∧ f y ≤ hi then
        rotateLeft (project f lo hi (.node A x (.node B y C)))
      else project f lo hi (.node A x (.node B y C)) := by
  by_cases hyl : f y < lo
  · have hxl : f x < lo := by omega
    have hn : ¬ (lo ≤ f x ∧ f x < f y ∧ f y ≤ hi) := by omega
    simp [project, hyl, hxl, hn]
  · by_cases hhy : hi < f y
    · have hn : ¬ (lo ≤ f x ∧ f x < f y ∧ f y ≤ hi) := by omega
      by_cases hxl : f x < lo
      · simp [project, hyl, hhy, hxl, hn]
      · by_cases hhx : hi < f x
        · simp [project, hyl, hhy, hxl, hhx, hn]
        · have hyl' : ¬ f y < f x + 1 := by omega
          simp [project, hyl, hhy, hxl, hhx, hn, hyl']
    · by_cases hxl : f x < lo
      · have hn : ¬ (lo ≤ f x ∧ f x < f y ∧ f y ≤ hi) := by omega
        have hxhi : ¬ (f y - 1 < f x) := by omega
        simp [project, hyl, hhy, hxl, hn]
      · by_cases heq : f x = f y
        · have hn : ¬ (lo ≤ f x ∧ f x < f y ∧ f y ≤ hi) := by omega
          simp [project, hyl, hhy, heq]
        · have hcond : lo ≤ f x ∧ f x < f y ∧ f y ≤ hi := by omega
          have hhx : ¬ hi < f x := by omega
          have hxhi : ¬ f y - 1 < f x := by omega
          have hyl' : ¬ f y < f x + 1 := by omega
          simp [project, hyl, hhy, hxl, hhx, hxhi, hyl', hcond, rotateLeft]

theorem project_moveToRoot (f : Int → Int) (hf : Monotone f)
    (t : Tree Int) (x lo hi : Int) (d : Nat)
    (hs : searchDepth x t = some d) :
    project f lo hi (moveToRoot x t) =
      if InInterval lo hi (f x) then moveToRoot (f x) (project f lo hi t)
      else project f lo hi t := by
  induction t generalizing lo hi d with
  | empty => simp [searchDepth] at hs
  | node l y r ihl ihr =>
    by_cases hxy : x < y
    · simp only [searchDepth, hxy, ↓reduceIte] at hs
      cases hd : searchDepth x l with
      | none => simp [hd] at hs
      | some e =>
        have hroot := rootKey_moveToRoot_of_searchDepth x l e hd
        cases hm : moveToRoot x l with
        | empty => simp [hm, rootKey] at hroot
        | node A z B =>
          simp only [hm, rootKey, Option.some.injEq] at hroot
          subst z
          have hmap := hf (le_of_lt hxy)
          have hrot : project f lo hi (moveToRoot x (.node l y r)) =
              if lo ≤ f x ∧ f x < f y ∧ f y ≤ hi then
                rotateRight (project f lo hi (.node (moveToRoot x l) y r))
              else project f lo hi (.node (moveToRoot x l) y r) := by
            simpa only [moveToRoot, hxy, ↓reduceIte, hm, rotateRight] using
              project_rotateRight_target f lo hi x y A B r hmap
          rw [hrot]
          by_cases hyl : f y < lo
          · have hxl : f x < lo := by omega
            have hn : ¬ (lo ≤ f x ∧ f x < f y ∧ f y ≤ hi) := by omega
            simp [project, hyl, InInterval, not_le_of_gt hxl]
          · by_cases hhy : hi < f y
            · have hn : ¬ (lo ≤ f x ∧ f x < f y ∧ f y ≤ hi) := by omega
              simpa only [hn, ↓reduceIte, project, hyl, hhy] using ihl lo hi e hd
            · by_cases hxl : f x < lo
              · have hn : ¬ (lo ≤ f x ∧ f x < f y ∧ f y ≤ hi) := by omega
                have hsub := ihl lo (f y - 1) e hd
                simp only [InInterval, not_le_of_gt hxl, false_and, ↓reduceIte] at hsub
                simp only [↓reduceIte, project, hyl, hhy, hsub,
                  InInterval, not_le_of_gt hxl, false_and]
              · by_cases heq : f x = f y
                · have hn : ¬ (lo ≤ f x ∧ f x < f y ∧ f y ≤ hi) := by omega
                  have hsub := ihl lo (f y - 1) e hd
                  have hout : ¬ f x ≤ f y - 1 := by omega
                  simp only [InInterval, hout, and_false, ↓reduceIte] at hsub
                  have hin : InInterval lo hi (f x) := by constructor <;> omega
                  simp [project, hyl, hhy, hsub, heq]
                · have hcond : lo ≤ f x ∧ f x < f y ∧ f y ≤ hi := by omega
                  have hsub := ihl lo (f y - 1) e hd
                  have hin' : InInterval lo (f y - 1) (f x) := by constructor <;> omega
                  have hin : InInterval lo hi (f x) := by constructor <;> omega
                  simp only [hin', ↓reduceIte] at hsub
                  simp [hcond, project, hyl, hhy, hin, hsub, moveToRoot]
    · by_cases hyx : y < x
      · simp only [searchDepth, hxy, hyx, ↓reduceIte] at hs
        cases hd : searchDepth x r with
        | none => simp [hd] at hs
        | some e =>
          have hroot := rootKey_moveToRoot_of_searchDepth x r e hd
          cases hm : moveToRoot x r with
          | empty => simp [hm, rootKey] at hroot
          | node B z C =>
            simp only [hm, rootKey, Option.some.injEq] at hroot
            subst z
            have hmap := hf (le_of_lt hyx)
            have hrot : project f lo hi (moveToRoot x (.node l y r)) =
                if lo ≤ f y ∧ f y < f x ∧ f x ≤ hi then
                  rotateLeft (project f lo hi (.node l y (moveToRoot x r)))
                else project f lo hi (.node l y (moveToRoot x r)) := by
              simpa only [moveToRoot, hxy, hyx, ↓reduceIte, hm, rotateLeft] using
                project_rotateLeft_target f lo hi y x l B C hmap
            rw [hrot]
            by_cases hyl : f y < lo
            · have hn : ¬ (lo ≤ f y ∧ f y < f x ∧ f x ≤ hi) := by omega
              simpa only [hn, ↓reduceIte, project, hyl] using ihr lo hi e hd
            · by_cases hhy : hi < f y
              · have hhx : hi < f x := by omega
                have hn : ¬ (lo ≤ f y ∧ f y < f x ∧ f x ≤ hi) := by omega
                simp [project, hyl, hhy, InInterval, not_le_of_gt hhx]
              · by_cases hhx : hi < f x
                · have hn : ¬ (lo ≤ f y ∧ f y < f x ∧ f x ≤ hi) := by omega
                  have hsub := ihr (f y + 1) hi e hd
                  simp only [InInterval, not_le_of_gt hhx, and_false, ↓reduceIte] at hsub
                  simp only [↓reduceIte, project, hyl, hhy, hsub,
                    InInterval, not_le_of_gt hhx, and_false]
                · by_cases heq : f x = f y
                  · have hn : ¬ (lo ≤ f y ∧ f y < f x ∧ f x ≤ hi) := by omega
                    have hsub := ihr (f y + 1) hi e hd
                    have hout : ¬ f y + 1 ≤ f x := by omega
                    simp only [InInterval, hout, false_and, ↓reduceIte] at hsub
                    have hin : InInterval lo hi (f x) := by constructor <;> omega
                    simp [project, hyl, hhy, hsub, heq]
                  · have hcond : lo ≤ f y ∧ f y < f x ∧ f x ≤ hi := by omega
                    have hsub := ihr (f y + 1) hi e hd
                    have hin' : InInterval (f y + 1) hi (f x) := by constructor <;> omega
                    have hin : InInterval lo hi (f x) := by constructor <;> omega
                    have hnot : ¬ f x < f y := by omega
                    simp only [hin', ↓reduceIte] at hsub
                    simp [hcond, project, hyl, hhy, hin, hsub, moveToRoot, hnot]
      · have heq : x = y := by omega
        subst y
        by_cases hin : InInterval lo hi (f x)
        · have hxl : ¬ f x < lo := by have := hin.1; omega
          have hhx : ¬ hi < f x := by have := hin.2; omega
          simp [hin, project, hxl, hhx]
        · simp [hin]

theorem searchDepth_project (f : Int → Int) (hf : Monotone f)
    (t : Tree Int) (x lo hi : Int) (d : Nat)
    (hs : searchDepth x t = some d) (hlo : lo ≤ f x) (hhi : f x ≤ hi) :
    ∃ e, e ≤ d ∧ searchDepth (f x) (project f lo hi t) = some e := by
  induction t generalizing lo hi d with
  | empty => simp [searchDepth] at hs
  | node l y r ihl ihr =>
    by_cases hxy : x < y
    · simp only [searchDepth, hxy, ↓reduceIte] at hs
      cases hd : searchDepth x l with
      | none => simp [hd] at hs
      | some q =>
        simp only [hd, Option.map_some, Option.some.injEq] at hs
        have hmap := hf (le_of_lt hxy)
        have hyl : ¬ f y < lo := by omega
        by_cases hhy : hi < f y
        · obtain ⟨e, he, hd'⟩ := ihl lo hi q hd hlo hhi
          exact ⟨e, by omega, by simpa [project, hyl, hhy] using hd'⟩
        · by_cases hlt : f x < f y
          · obtain ⟨e, he, hd'⟩ := ihl lo (f y - 1) q hd hlo (by omega)
            refine ⟨e + 1, by omega, ?_⟩
            simp [project, hyl, hhy, searchDepth, hlt, hd']
          · have heq : f x = f y := by omega
            exact ⟨0, by omega, by simp [project, hyl, hhy, heq]⟩
    · by_cases hyx : y < x
      · simp only [searchDepth, hxy, hyx, ↓reduceIte] at hs
        cases hd : searchDepth x r with
        | none => simp [hd] at hs
        | some q =>
          simp only [hd, Option.map_some, Option.some.injEq] at hs
          have hmap := hf (le_of_lt hyx)
          by_cases hyl : f y < lo
          · obtain ⟨e, he, hd'⟩ := ihr lo hi q hd hlo hhi
            exact ⟨e, by omega, by simpa [project, hyl] using hd'⟩
          · have hhy : ¬ hi < f y := by omega
            by_cases hlt : f y < f x
            · obtain ⟨e, he, hd'⟩ := ihr (f y + 1) hi q hd (by omega) hhi
              refine ⟨e + 1, by omega, ?_⟩
              have hnot : ¬ f x < f y := by omega
              simp [project, hyl, hhy, searchDepth, hlt, hnot, hd']
            · have heq : f x = f y := by omega
              exact ⟨0, by omega, by simp [project, hyl, hhy, heq]⟩
      · have heq : x = y := by omega
        subst y
        have hyl : ¬ f x < lo := by omega
        have hhy : ¬ hi < f x := by omega
        exact ⟨0, by omega, by simp [project, hyl, hhy]⟩

def localWord (f : Int → Int) (lo hi : Int) (xs : List Int) : List Int :=
  xs.filterMap (fun x => if InInterval lo hi (f x) then some (f x) else none)

theorem project_run (f : Int → Int) (hf : Monotone f)
    (t : Tree Int) (xs : List Int) (lo hi : Int) (hs : Successful t xs) :
    project f lo hi (MTR.run t xs) =
      MTR.run (project f lo hi t) (localWord f lo hi xs) := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨⟨d, hd⟩, ht⟩ := hs
    change project f lo hi (MTR.run (moveToRoot x t) xs) = _
    rw [ih _ ht, project_moveToRoot f hf t x lo hi d hd]
    by_cases hin : InInterval lo hi (f x)
    · simp only [hin, ↓reduceIte, localWord, List.filterMap_cons, MTR.run,
        List.foldl_cons]
    · simp only [hin, ↓reduceIte, localWord, List.filterMap_cons]

theorem successful_localWord (f : Int → Int) (hf : Monotone f)
    (t : Tree Int) (xs : List Int) (lo hi : Int) (hs : Successful t xs) :
    Successful (project f lo hi t) (localWord f lo hi xs) := by
  induction xs generalizing t with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨⟨d, hd⟩, ht⟩ := hs
    have hp := project_moveToRoot f hf t x lo hi d hd
    have htail := ih (moveToRoot x t) ht
    by_cases hin : InInterval lo hi (f x)
    · obtain ⟨e, _, he⟩ := searchDepth_project f hf t x lo hi d hd hin.1 hin.2
      simp only [hin, ↓reduceIte] at hp
      simp only [localWord, List.filterMap_cons, hin, ↓reduceIte, Successful]
      exact ⟨⟨e, he⟩, by simpa only [hp, localWord] using htail⟩
    · simp only [hin, ↓reduceIte] at hp
      simpa only [localWord, List.filterMap_cons, hin, ↓reduceIte, hp] using htail

theorem runCost_localWord_le (f : Int → Int) (hf : Monotone f)
    (t : Tree Int) (xs : List Int) (lo hi : Int) (hs : Successful t xs) :
    runCost (project f lo hi t) (localWord f lo hi xs) ≤ runCost t xs := by
  induction xs generalizing t with
  | nil => exact le_rfl
  | cons x xs ih =>
    obtain ⟨⟨d, hd⟩, ht⟩ := hs
    have hp := project_moveToRoot f hf t x lo hi d hd
    have htail := ih (moveToRoot x t) ht
    by_cases hin : InInterval lo hi (f x)
    · obtain ⟨e, he, hd'⟩ := searchDepth_project f hf t x lo hi d hd hin.1 hin.2
      simp only [hin, ↓reduceIte] at hp
      rw [hp] at htail
      simp only [localWord, List.filterMap_cons, hin, ↓reduceIte, runCost,
        hd, hd', Option.getD_some]
      change e + 1 + runCost (moveToRoot (f x) (project f lo hi t))
        (localWord f lo hi xs) ≤ d + 1 + runCost (moveToRoot x t) xs
      omega
    · simp only [hin, ↓reduceIte] at hp
      rw [hp] at htail
      simp only [localWord, List.filterMap_cons, hin, ↓reduceIte, runCost,
        hd, Option.getD_some]
      change runCost (project f lo hi t) (localWord f lo hi xs) ≤
        d + 1 + runCost (moveToRoot x t) xs
      omega

/-- A bound on each actual intermediate successful MTR search. -/
def Shallow (k : Nat) : Tree Int → List Int → Prop
  | _, [] => True
  | t, x :: xs => (∃ d, d ≤ k ∧ searchDepth x t = some d) ∧
      Shallow k (moveToRoot x t) xs

theorem Shallow.successful {k : Nat} {t : Tree Int} {xs : List Int}
    (h : Shallow k t xs) : Successful t xs := by
  induction xs generalizing t with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨⟨d, _, hd⟩, ht⟩ := h
    exact ⟨⟨d, hd⟩, ih ht⟩

theorem shallow_localWord (f : Int → Int) (hf : Monotone f)
    (t : Tree Int) (xs : List Int) (lo hi : Int) (k : Nat)
    (hs : Shallow k t xs) :
    Shallow k (project f lo hi t) (localWord f lo hi xs) := by
  induction xs generalizing t with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨⟨d, hdk, hd⟩, ht⟩ := hs
    have hp := project_moveToRoot f hf t x lo hi d hd
    have htail := ih (moveToRoot x t) ht
    by_cases hin : InInterval lo hi (f x)
    · obtain ⟨e, hed, he⟩ := searchDepth_project f hf t x lo hi d hd hin.1 hin.2
      simp only [hin, ↓reduceIte] at hp
      simp only [localWord, List.filterMap_cons, hin, ↓reduceIte, Shallow]
      exact ⟨⟨e, by omega, he⟩, by simpa only [hp, localWord] using htail⟩
    · simp only [hin, ↓reduceIte] at hp
      simpa only [localWord, List.filterMap_cons, hin, ↓reduceIte, hp] using htail

/-- Retain the first member of every consecutive equal-key run. -/
def compressFrom (previous : Option Int) : List Int → List Int
  | [] => []
  | x :: xs => if previous = some x then compressFrom previous xs
      else x :: compressFrom (some x) xs

def compress (xs : List Int) : List Int := compressFrom none xs

def RootMatches (previous : Option Int) (t : Tree Int) : Prop :=
  ∀ x, previous = some x → rootKey t = some x

private theorem mtr_eq_of_root {t : Tree Int} {x : Int}
    (h : rootKey t = some x) : moveToRoot x t = t := by
  cases t with
  | empty => simp [rootKey] at h
  | node l y r =>
    simp only [rootKey, Option.some.injEq] at h
    subst y
    exact moveToRoot_root l r x

theorem run_compressFrom (t : Tree Int) (xs : List Int) (previous : Option Int)
    (hs : Successful t xs) (hprev : RootMatches previous t) :
    MTR.run t (compressFrom previous xs) = MTR.run t xs := by
  induction xs generalizing t previous with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨⟨d, hd⟩, ht⟩ := hs
    by_cases heq : previous = some x
    · have hm := mtr_eq_of_root (hprev x heq)
      have ht' : Successful t xs := by simpa [hm] using ht
      simpa only [compressFrom, heq, ↓reduceIte, MTR.run, List.foldl_cons, hm]
        using ih t previous ht' hprev
    · have hp : RootMatches (some x) (moveToRoot x t) := by
        intro y hy
        have hxy : x = y := Option.some.inj hy
        subst y
        exact rootKey_moveToRoot_of_searchDepth x t d hd
      simpa only [compressFrom, heq, ↓reduceIte, MTR.run, List.foldl_cons]
        using ih (moveToRoot x t) (some x) ht hp

theorem run_compress (t : Tree Int) (xs : List Int) (hs : Successful t xs) :
    MTR.run t (compress xs) = MTR.run t xs :=
  run_compressFrom t xs none hs (by intro x hx; cases hx)

theorem shallow_compressFrom (t : Tree Int) (xs : List Int)
    (previous : Option Int) (k : Nat)
    (hs : Shallow k t xs) (hprev : RootMatches previous t) :
    Shallow k t (compressFrom previous xs) := by
  induction xs generalizing t previous with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨⟨d, hdk, hd⟩, ht⟩ := hs
    by_cases heq : previous = some x
    · have hm := mtr_eq_of_root (hprev x heq)
      have ht' : Shallow k t xs := by simpa [hm] using ht
      simpa only [compressFrom, heq, ↓reduceIte] using ih t previous ht' hprev
    · have hp : RootMatches (some x) (moveToRoot x t) := by
        intro y hy
        have hxy : x = y := Option.some.inj hy
        subst y
        exact rootKey_moveToRoot_of_searchDepth x t d hd
      simp only [compressFrom, heq, ↓reduceIte, Shallow]
      exact ⟨⟨d, hdk, hd⟩, ih (moveToRoot x t) (some x) ht hp⟩

theorem shallow_compress (t : Tree Int) (xs : List Int) (k : Nat)
    (hs : Shallow k t xs) : Shallow k t (compress xs) :=
  shallow_compressFrom t xs none k hs (by intro x hx; cases hx)

theorem Shallow.runCost_le {k : Nat} {t : Tree Int} {xs : List Int}
    (hs : Shallow k t xs) : runCost t xs ≤ (k + 1) * xs.length := by
  induction xs generalizing t with
  | nil => simp [runCost]
  | cons x xs ih =>
    obtain ⟨⟨d, hdk, hd⟩, ht⟩ := hs
    have hi := ih ht
    simp only [runCost, hd, Option.getD_some, List.length_cons, Nat.mul_add,
      Nat.mul_one]
    omega

/-- The concrete cheap local witness used after global shallow normalization.
The later sum over disjoint reference blocks is a separate theorem. -/
theorem compressed_local_cost (f : Int → Int) (hf : Monotone f)
    (t : Tree Int) (xs : List Int) (lo hi : Int) (k : Nat)
    (hs : Shallow k t xs) :
    runCost (project f lo hi t) (compress (localWord f lo hi xs)) ≤
      (k + 1) * (compress (localWord f lo hi xs)).length :=
  (shallow_compress _ _ _ (shallow_localWord f hf t xs lo hi k hs)).runCost_le

end ChaCha.ConvexSearchQuotient
