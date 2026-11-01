import TangoSquared.Paper20261030.ChronologicalWords

/-!
# Access words as chronological point lists

The list representation and the finite-set representation have exactly the
same points. Repeated keys retain their distinct timestamps. Filtering
points by a key predicate projects to the ordinary filtered access word.
-/

namespace TangoSquared.Paper20261030.Rectangles

def pointWord (start : Int) : List Int → List Point
  | [] => []
  | x :: xs => (x,start) :: pointWord (start + 1) xs

theorem pointWord_keys (start : Int) (xs : List Int) :
    (pointWord start xs).map Prod.fst = xs := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih => simp only [pointWord,List.map_cons,ih]

theorem pointWord_time {start : Int} {xs : List Int} {p : Point} (hp : p ∈ pointWord start xs) :
    start ≤ p.2 := by
  induction xs generalizing start with
  | nil => contradiction
  | cons x xs ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact le_rfl
    · have := ih hp; omega

theorem pointWord_chronological (start : Int) (xs : List Int) : Chronological (pointWord start xs) := by
  induction xs generalizing start with
  | nil => simp [pointWord,Chronological]
  | cons x xs ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih _⟩
    intro p hp
    have := pointWord_time hp
    change start < p.2
    omega

theorem mem_pointWord (start : Int) (xs : List Int) (p : Point) :
    p ∈ pointWord start xs ↔ ∃ i : Fin xs.length, p = (xs[i.val],start + (i.val : Int)) := by
  induction xs generalizing start with
  | nil => simp [pointWord]
  | cons x xs ih =>
    constructor
    · intro hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨⟨0,by simp⟩,by simp⟩
      · obtain ⟨i,hi⟩ := (ih (start + 1)).mp hp
        refine ⟨⟨i.val + 1,by simpa using i.isLt⟩,?_⟩
        simp only [List.getElem_cons_succ,hi]
        congr 1
        omega
    · rintro ⟨i,hi⟩
      cases he : i.val with
      | zero =>
        have hp : p = (x,start) := by simpa [he] using hi
        simp [pointWord,hp]
      | succ j =>
        have hj : j < xs.length := by have := i.isLt; simp only [List.length_cons,he] at this; omega
        apply List.mem_cons_of_mem
        apply (ih (start + 1)).mpr
        refine ⟨⟨j,hj⟩,?_⟩
        simp only [he,List.getElem_cons_succ] at hi
        rw [hi]
        dsimp only
        congr 1
        omega

theorem pointWord_toFinset (xs : List Int) : (pointWord 0 xs).toFinset = accessPoints xs := by
  ext p
  simp only [List.mem_toFinset,mem_pointWord,accessPoints,Finset.mem_image,Finset.mem_univ,true_and,
    zero_add]
  exact exists_congr (fun i => eq_comm)

theorem keys_filter_points (ps : List Point) (keep : Int → Bool) :
    (ps.filter (fun p => keep p.1)).map Prod.fst = (ps.map Prod.fst).filter keep := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases h : keep p.1 <;> simp [h,ih]

theorem pointWord_filtered_keys (start : Int) (xs : List Int) (keep : Int → Bool) :
    ((pointWord start xs).filter (fun p => keep p.1)).map Prod.fst = xs.filter keep := by
  rw [keys_filter_points,pointWord_keys]

end TangoSquared.Paper20261030.Rectangles
