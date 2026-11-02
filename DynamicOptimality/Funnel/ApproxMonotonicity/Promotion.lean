import DynamicOptimality.Funnel.ApproxMonotonicity.Reflection

/-! # A single promoted key inside a common tree context

`Promotion y before after focus` says that `after` is obtained by replacing
one distinguished subtree `focus` by `Warm.access y focus`. Every ancestor
of the distinguished subtree places `y` on its correct side. The key may be
absent from `focus`; this is essential for warm insertion histories.
-/

namespace DynamicOptimality.Funnel.ApproxMonotonicity

open ChaCha.MTR ChaCha.MTR.Tree Warm
variable {α : Type*} [LinearOrder α]

inductive Promotion (y : α) : Tree α → Tree α → Tree α → Prop where
  | root (focus : Tree α) : Promotion y focus (access y focus) focus
  | left {l u focus : Tree α} (a : α) (r : Tree α)
      (related : Promotion y l u focus) (side : y < a) :
      Promotion y (.node l a r) (.node u a r) focus
  | right (l : Tree α) (a : α) {r u focus : Tree α}
      (related : Promotion y r u focus) (side : a < y) :
      Promotion y (.node l a r) (.node l a u) focus

namespace Promotion

variable {y : α} {before after focus : Tree α}

theorem focus_mem (related : Promotion y before after focus) {a : α}
    (member : a ∈ inorder focus) : a ∈ inorder before := by
  induction related with
  | root => exact member
  | left _ _ _ _ ih => simp [inorder,ih member]
  | right _ _ _ _ ih => simp [inorder,ih member]

theorem focus_ordered (related : Promotion y before after focus) (ordered : Ordered before) :
    Ordered focus := by
  induction related with
  | root => exact ordered
  | left _ _ _ _ ih => exact ih (ordered_parts ordered).1
  | right _ _ _ _ ih => exact ih (ordered_parts ordered).2.1

theorem restrict_below (related : Promotion y before after focus) (x : α) (yx : y < x) :
    Promotion y (Warm.below x before) (Warm.below x after) (Warm.below x focus) := by
  induction related with
  | root focus => simpa [below_access,yx] using Promotion.root (y := y) (Warm.below x focus)
  | left a r related ya ih =>
    by_cases ax : a < x
    · simpa [Warm.below,ax] using Promotion.left a (Warm.below x r) ih ya
    · simpa [Warm.below,ax] using ih
  | right l a related ay ih =>
    have ax := ay.trans yx
    simpa [Warm.below,ax] using Promotion.right (Warm.below x l) a ih ay

theorem restrict_above (related : Promotion y before after focus) (x : α) (xy : x < y) :
    Promotion y (Warm.above x before) (Warm.above x after) (Warm.above x focus) := by
  induction related with
  | root focus => simpa [above_access,xy] using Promotion.root (y := y) (Warm.above x focus)
  | left a r related ya ih =>
    have xa := xy.trans ya
    simpa [Warm.above,xa] using Promotion.left a (Warm.above x r) ih ya
  | right l a related ay ih =>
    by_cases xa : x < a
    · simpa [Warm.above,xa] using Promotion.right (Warm.above x l) a ih ay
    · simpa [Warm.above,xa] using ih

theorem above_eq (related : Promotion y before after focus) (x : α) (yx : y ≤ x) :
    Warm.above x before = Warm.above x after := by
  induction related with
  | root focus => simp [above_access,not_lt_of_ge yx]
  | left a r related ya ih => by_cases xa : x < a <;> simp [Warm.above,xa,ih]
  | right l a related ay ih =>
    have no : ¬ x < a := not_lt_of_ge ((ay.trans_le yx).le)
    simp [Warm.above,no,ih]

theorem below_eq (related : Promotion y before after focus) (x : α) (xy : x ≤ y) :
    Warm.below x before = Warm.below x after := by
  induction related with
  | root focus => simp [below_access,not_lt_of_ge xy]
  | left a r related ya ih =>
    have no : ¬ a < x := not_lt_of_ge ((xy.trans_lt ya).le)
    simp [Warm.below,no,ih]
  | right l a related ay ih => by_cases ax : a < x <;> simp [Warm.below,ax,ih]

theorem access_eq (related : Promotion y before after focus) :
    access y before = access y after := by
  simp only [access,related.below_eq y le_rfl,related.above_eq y le_rfl]

theorem advance_below (related : Promotion y before after focus) (x : α) (yx : y < x) :
    Promotion y (access x before) (access x after) (Warm.below x focus) := by
  unfold access
  rw [← related.above_eq x yx.le]
  exact Promotion.left x (Warm.above x before) (related.restrict_below x yx) yx

theorem advance_above (related : Promotion y before after focus) (x : α) (xy : x < y) :
    Promotion y (access x before) (access x after) (Warm.above x focus) := by
  unfold access
  rw [← related.below_eq x xy.le]
  exact Promotion.right (Warm.below x before) x (related.restrict_above x xy) xy

theorem mirror (related : Promotion y before after focus) :
    Promotion (α := αᵒᵈ) y (ApproxMonotonicity.mirror before)
      (ApproxMonotonicity.mirror after) (ApproxMonotonicity.mirror focus) := by
  induction related with
  | root focus =>
    exact (access_mirror (α := α) y focus) ▸
      (Promotion.root (α := αᵒᵈ) (y := y) (ApproxMonotonicity.mirror focus))
  | left a r related ya ih =>
    exact Promotion.right (α := αᵒᵈ) (ApproxMonotonicity.mirror r) a ih ya
  | right l a related ay ih =>
    exact Promotion.left (α := αᵒᵈ) a (ApproxMonotonicity.mirror l) ih ay

/-- The local crossing charge survives an arbitrary common outer context. -/
theorem lower_charge (related : Promotion y before after focus) (ordered : Ordered before)
    (boundary : Option Bool) (x : α) (yx : y < x) :
    crossingFrom boundary x before + 4 * crossingDepth y (Warm.below x focus) ≤
      crossingFrom boundary x after + 4 * crossingDepth y focus := by
  induction related generalizing boundary with
  | root focus => exact local_below boundary focus ordered x y yx
  | @left l u focus a r related ya ih =>
    obtain ⟨ol,orr,left,right⟩ := ordered_parts ordered
    by_cases xa : x < a
    · have bound := ih ol (some false)
      rw [crossingFrom_left boundary l r a x xa,crossingFrom_left boundary u r a x xa]
      omega
    · have fixed : Warm.below x focus = focus := below_eq_self x focus (by
        intro z hz
        exact (left z (related.focus_mem hz)).trans_le (le_of_not_gt xa))
      rw [fixed]
      by_cases ax : a < x
      · rw [crossingFrom_right boundary l r a x ax,crossingFrom_right boundary u r a x ax]
      · have same : x = a := le_antisymm (le_of_not_gt ax) (le_of_not_gt xa)
        subst x
        simp
  | @right l a r u focus related ay ih =>
    obtain ⟨ol,orr,left,right⟩ := ordered_parts ordered
    have ax := ay.trans yx
    have bound := ih orr (some true)
    rw [crossingFrom_right boundary l r a x ax,crossingFrom_right boundary l u a x ax]
    omega

theorem upper_charge (related : Promotion y before after focus) (ordered : Ordered before)
    (boundary : Option Bool) (x : α) (xy : x < y) :
    crossingFrom boundary x before + 4 * crossingDepth y (Warm.above x focus) ≤
      crossingFrom boundary x after + 4 * crossingDepth y focus := by
  have dual := related.mirror.lower_charge (ordered_mirror before ordered)
    (boundary.map (! ·)) x xy
  rw [below_mirror] at dual
  change crossingFrom (α := αᵒᵈ) (boundary.map (! ·)) x (ApproxMonotonicity.mirror before) +
    4 * crossingDepth (α := αᵒᵈ) y (ApproxMonotonicity.mirror (Warm.above (α := α) x focus)) ≤
      crossingFrom (α := αᵒᵈ) (boundary.map (! ·)) x (ApproxMonotonicity.mirror after) +
        4 * crossingDepth (α := αᵒᵈ) y (ApproxMonotonicity.mirror focus) at dual
  rw [crossingFrom_mirror boundary x before,crossingDepth_mirror y (Warm.above x focus),
    crossingFrom_mirror boundary x after,crossingDepth_mirror y focus] at dual
  exact dual

theorem equal_charge (related : Promotion y before after focus) (boundary : Option Bool) :
    crossingFrom boundary y before ≤ crossingFrom boundary y after + 4 * crossingDepth y focus := by
  induction related generalizing boundary with
  | root focus => exact local_equal boundary focus y
  | @left l u focus a r related ya ih =>
    have bound := ih (some false)
    rw [crossingFrom_left boundary l r a y ya,crossingFrom_left boundary u r a y ya]
    omega
  | @right l a r u focus related ay ih =>
    have bound := ih (some true)
    rw [crossingFrom_right boundary l r a y ay,crossingFrom_right boundary l u a y ay]
    omega

end Promotion
end DynamicOptimality.Funnel.ApproxMonotonicity
