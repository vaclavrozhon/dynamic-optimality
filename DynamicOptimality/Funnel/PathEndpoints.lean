import DynamicOptimality.Funnel.MixedEdges
import Mathlib.Data.List.Pairwise

/-! # Endpoints and interval labels of the two search spines -/

namespace DynamicOptimality.Funnel.Warm

open ChaCha.MTR ChaCha.MTR.Tree

variable {α β : Type*}

def lastParent (parent : α) (path : List α) : α := path.getLast?.getD parent

@[simp] theorem lastParent_nil (parent : α) : lastParent parent [] = parent := rfl

@[simp] theorem lastParent_cons (parent a : α) (path : List α) :
    lastParent parent (a :: path) = lastParent a path := by
  simp [lastParent,List.getLast?_cons]

theorem lastParent_map (label : α → β) (parent : α) (path : List α) :
    label (lastParent parent path) = lastParent (label parent) (path.map label) := by
  induction path generalizing parent with
  | nil => rfl
  | cons a path ih => simpa only [lastParent_cons,List.map_cons] using ih a

theorem lastParent_mem (parent : α) (path : List α) (nonempty : path ≠ []) :
    lastParent parent path ∈ path := by
  simpa only [lastParent,List.getLast?_eq_some_getLast nonempty,Option.getD_some] using
    List.getLast_mem nonempty

variable [LinearOrder α] [LinearOrder β]

theorem lastParent_eq_upper (parent top : β) (path : List β)
    (sorted : path.Pairwise (· ≤ ·)) (bounded : ∀ z ∈ path, z ≤ top)
    (present : top ∈ path) : lastParent parent path = top := by
  have nonempty := List.ne_nil_of_mem present
  simp only [lastParent,List.getLast?_eq_some_getLast nonempty,Option.getD_some]
  exact le_antisymm (bounded _ (List.getLast_mem nonempty)) (sorted.rel_getLast present)

theorem lastParent_eq_lower (parent bottom : β) (path : List β)
    (sorted : path.Pairwise (· ≥ ·)) (bounded : ∀ z ∈ path, bottom ≤ z)
    (present : bottom ∈ path) : lastParent parent path = bottom :=
  lastParent_eq_upper (β := OrderDual β) parent bottom path sorted bounded present

theorem left_labels_sorted (label : α → β) (mono : Monotone label)
    (tree : Tree α) (x : α) (ordered : Ordered tree) :
    (((ancestors x tree).filter (fun q => decide (q < x))).map label).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  exact (left_ancestors_increasing tree x ordered).imp (fun h => mono h.le)

theorem right_labels_sorted (label : α → β) (mono : Monotone label)
    (tree : Tree α) (x : α) (ordered : Ordered tree) :
    (((ancestors x tree).filter (fun q => decide (x < q))).map label).Pairwise (· ≥ ·) := by
  rw [List.pairwise_map]
  exact (right_ancestors_decreasing tree x ordered).imp (fun h => mono h.le)

theorem left_labels_bounded (label : α → β) (mono : Monotone label)
    (tree : Tree α) (x : α) :
    ∀ z ∈ ((ancestors x tree).filter (fun q => decide (q < x))).map label, z ≤ label x := by
  intro z member
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp member
  exact mono (of_decide_eq_true (List.mem_filter.mp hq).2).le

theorem right_labels_bounded (label : α → β) (mono : Monotone label)
    (tree : Tree α) (x : α) :
    ∀ z ∈ ((ancestors x tree).filter (fun q => decide (x < q))).map label, label x ≤ z := by
  intro z member
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp member
  exact mono (of_decide_eq_true (List.mem_filter.mp hq).2).le

theorem left_last_label (label : α → β) (mono : Monotone label)
    (tree : Tree α) (x : α) (ordered : Ordered tree)
    (present : label x ∈ ((ancestors x tree).filter (fun q => decide (q < x))).map label) :
    label (lastParent x ((ancestors x tree).filter (fun q => decide (q < x)))) = label x := by
  rw [lastParent_map label]
  exact lastParent_eq_upper _ _ _ (left_labels_sorted label mono tree x ordered)
    (left_labels_bounded label mono tree x) present

theorem right_last_label (label : α → β) (mono : Monotone label)
    (tree : Tree α) (x : α) (ordered : Ordered tree)
    (present : label x ∈ ((ancestors x tree).filter (fun q => decide (x < q))).map label) :
    label (lastParent x ((ancestors x tree).filter (fun q => decide (x < q)))) = label x := by
  rw [lastParent_map label]
  exact lastParent_eq_lower _ _ _ (right_labels_sorted label mono tree x ordered)
    (right_labels_bounded label mono tree x) present

omit [LinearOrder β] in
theorem not_mem_ancestors (tree : Tree α) (x : α) : x ∉ ancestors x tree := by
  induction tree with
  | empty => simp [ancestors]
  | node l a r ihl ihr =>
    by_cases xa : x < a
    · simp [ancestors,xa,ne_of_lt xa,ihl]
    · by_cases ax : a < x
      · simp [ancestors,xa,ax,ne_of_gt ax,ihr]
      · simp [ancestors,xa,ax]

end DynamicOptimality.Funnel.Warm
