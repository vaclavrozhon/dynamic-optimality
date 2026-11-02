import ChaCha.Paper20261030.LCABound

/-!
# Access sequences and the checked fragment lower bound

The point instance of a word has one row for each list index. Thus repeated
keys remain distinct access events. The public theorem applies directly to
arbitrary finite access words on a perfect primary reference.
-/

namespace ChaCha.Paper20261030.Rectangles

def accessPoints (xs : List Int) : Finset Point :=
  Finset.univ.image (fun i : Fin xs.length => (xs[i.val], (i.val : Int)))

theorem accessPoint_injective (xs : List Int) :
    Function.Injective (fun i : Fin xs.length => ((xs[i.val], (i.val : Int)) : Point)) := by
  intro i j he
  apply Fin.ext
  have ht := congrArg Prod.snd he
  change (i.val : Int) = (j.val : Int) at ht
  omega

theorem accessPoints_instance (xs : List Int) : Instance (accessPoints xs) := by
  intro p hp q hq ht
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
  have hij : i = j := by
    apply Fin.ext
    dsimp only at ht
    omega
  subst j
  rfl

theorem accessPoints_card (xs : List Int) : (accessPoints xs).card = xs.length := by
  rw [accessPoints,Finset.card_image_of_injective _ (accessPoint_injective xs)]
  simp

theorem accessPoints_keys {xs : List Int} {H : Nat}
    (hkeys : ∀ x ∈ xs, Dyadic.ValidKey H x) :
    ∀ p ∈ accessPoints xs, Dyadic.ValidKey H p.1 := by
  intro p hp
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
  exact hkeys xs[i.val] (List.getElem_mem i.isLt)

end ChaCha.Paper20261030.Rectangles

namespace ChaCha.Paper20261030.Dyadic

open Rectangles

/-- The manuscript's fragment lower bound on ordinary finite access words. -/
theorem sequence_lcaBound {h : Nat} (t : DepthTree 0 h) (xs : List Int)
    (hkeys : ∀ x ∈ xs, ValidKey (h + 1) x) :
    lcaBound (h + 1) t (accessPoints xs) ≤ 5 * rectangleBound (accessPoints xs) :=
  lcaBound_le_rectangleBound t (accessPoints_instance xs) (accessPoints_keys hkeys)

end ChaCha.Paper20261030.Dyadic
