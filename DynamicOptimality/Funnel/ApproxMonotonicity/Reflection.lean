import DynamicOptimality.Funnel.ApproxMonotonicity.Crossing
import DynamicOptimality.Funnel.ApproxMonotonicity.Pruning

/-! # Order reflection of the crossing comparison

Reflecting both tree children and the key order preserves every crossing.
This transfers the lower-interval proof to the upper-interval case exactly.
-/

namespace DynamicOptimality.Funnel.ApproxMonotonicity

open ChaCha.MTR ChaCha.MTR.Tree Warm
variable {α : Type*} [LinearOrder α]

def mirror : Tree α → Tree α
  | .empty => .empty
  | .node l a r => .node (mirror r) a (mirror l)

@[simp] theorem inorder_mirror (tree : Tree α) :
    inorder (mirror tree) = (inorder tree).reverse := by
  induction tree with
  | empty => rfl
  | node l a r ihl ihr => simp [mirror,inorder,ihl,ihr,List.reverse_append,List.append_assoc,List.singleton_append]

theorem ordered_mirror (tree : Tree α) (ordered : Ordered tree) : Ordered (α := αᵒᵈ) (mirror tree) := by
  change (inorder (mirror tree)).Pairwise (fun a b : α => b < a)
  rw [inorder_mirror,List.pairwise_reverse]
  exact ordered

@[simp] theorem below_mirror (cut : α) (tree : Tree α) :
    below (α := αᵒᵈ) cut (mirror tree) = mirror (above cut tree) := by
  induction tree with
  | empty => rfl
  | node l a r ihl ihr =>
    change (if cut < a then .node (below (α := αᵒᵈ) cut (mirror r)) a (below (α := αᵒᵈ) cut (mirror l))
      else below (α := αᵒᵈ) cut (mirror r)) = _
    by_cases h : cut < a <;> simp [above,h,mirror,ihl,ihr] <;> rfl

@[simp] theorem above_mirror (cut : α) (tree : Tree α) :
    above (α := αᵒᵈ) cut (mirror tree) = mirror (below cut tree) := by
  induction tree with
  | empty => rfl
  | node l a r ihl ihr =>
    change (if a < cut then .node (above (α := αᵒᵈ) cut (mirror r)) a (above (α := αᵒᵈ) cut (mirror l))
      else above (α := αᵒᵈ) cut (mirror l)) = _
    by_cases h : a < cut <;> simp [below,h,mirror,ihl,ihr] <;> rfl

@[simp] theorem access_mirror (x : α) (tree : Tree α) :
    access (α := αᵒᵈ) x (mirror tree) = mirror (access x tree) := by
  simp [access,mirror]
  rfl

@[simp] theorem sidePath_mirror (x : α) (tree : Tree α) :
    sidePath (α := αᵒᵈ) x (mirror tree) = (sidePath x tree).map (! ·) := by
  induction tree with
  | empty => rfl
  | node l a r ihl ihr =>
    rcases lt_trichotomy x a with xa | rfl | ax
    · rw [sidePath_left l r a x xa]
      simpa [mirror,ihl] using sidePath_right (α := αᵒᵈ) (mirror r) (mirror l) a x xa
    · simp [mirror]
    · rw [sidePath_right l r a x ax]
      simpa [mirror,ihr] using sidePath_left (α := αᵒᵈ) (mirror r) (mirror l) a x ax

private theorem changesFrom_map {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (f : β → γ) (injective : Function.Injective f) (previous : Option β) (word : List β) :
    changesFrom (previous.map f) (word.map f) = changesFrom previous word := by
  induction word generalizing previous with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons,changesFrom,← Option.map_some a f,ih]
    congr 1
    cases previous with
    | none => rfl
    | some b => simp [changeStep,injective.eq_iff]

private theorem flip_injective : Function.Injective (Option.map (! ·) : Option Bool → Option Bool) := by
  intro a b same
  cases a <;> cases b <;> simp_all

@[simp] theorem crossingFrom_mirror (boundary : Option Bool) (x : α) (tree : Tree α) :
    crossingFrom (α := αᵒᵈ) (boundary.map (! ·)) x (mirror tree) = crossingFrom boundary x tree := by
  have preserved := changesFrom_map (Option.map (! ·)) flip_injective
    (boundary.map some) ((sidePath x tree).map some ++ [none])
  simpa [crossingFrom,sidePath_mirror,List.map_append,List.map_map,Option.map_map,
    Function.comp_def] using preserved

@[simp] theorem crossingDepth_mirror (x : α) (tree : Tree α) :
    crossingDepth (α := αᵒᵈ) x (mirror tree) = crossingDepth x tree := by
  exact congrArg (· + 1) (crossingFrom_mirror none x tree)

/-- The reflected local perturbation inequality retains the upper interval. -/
theorem local_above (boundary : Option Bool) (tree : Tree α) (ordered : Ordered tree)
    (x y : α) (xy : x < y) :
    crossingFrom boundary x tree + 4 * crossingDepth y (above x tree) ≤
      crossingFrom boundary x (access y tree) + 4 * crossingDepth y tree := by
  have dual := local_below (α := αᵒᵈ) (boundary.map (! ·)) (mirror tree)
    (ordered_mirror tree ordered) x y xy
  rw [below_mirror,access_mirror] at dual
  change crossingFrom (α := αᵒᵈ) (boundary.map (! ·)) x (mirror tree) +
    4 * crossingDepth (α := αᵒᵈ) y (mirror (above (α := α) x tree)) ≤
      crossingFrom (α := αᵒᵈ) (boundary.map (! ·)) x (mirror (access (α := α) y tree)) +
        4 * crossingDepth (α := αᵒᵈ) y (mirror tree) at dual
  rw [crossingFrom_mirror boundary x tree,crossingDepth_mirror y (above x tree),
    crossingFrom_mirror boundary x (access y tree),crossingDepth_mirror y tree] at dual
  exact dual

end DynamicOptimality.Funnel.ApproxMonotonicity
