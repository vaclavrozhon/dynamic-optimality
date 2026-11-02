import DynamicOptimality.Funnel.PathEndpoints
import DynamicOptimality.Funnel.AlternationOrder

/-! # Counting changes on the two monotone search spines -/

namespace DynamicOptimality.Funnel.Warm

open ChaCha.MTR ChaCha.MTR.Tree

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

theorem chainCost_account (label : α → β) (parent : α) (path : List α) (gap : Tree α) :
    chainCost label parent path gap = changesFrom (some (label parent)) (path.map label) +
      mixed label gap + rootCharge label (lastParent parent path) gap := by
  induction path generalizing parent with
  | nil => simp [chainCost,changesFrom,rooted]
  | cons a path ih =>
    simp only [chainCost,List.map_cons,changesFrom,changeStep,lastParent_cons,ih]
    omega

theorem rootCharge_le (label : α → β) (parent : α) (tree : Tree α) :
    rootCharge label parent tree ≤ 1 := by
  cases tree with
  | empty => simp [rootCharge]
  | node l a r => simp only [rootCharge]; split_ifs <;> omega

theorem rootCharge_congr (label : α → β) {a b : α} (same : label a = label b) (tree : Tree α) :
    rootCharge label a tree = rootCharge label b tree := by
  cases tree <;> simp [rootCharge,same]

theorem side_labels_union (label : α → β) (tree : Tree α) (x : α) :
    (((ancestors x tree).filter (fun q => decide (q < x))).map label).toFinset ∪
      (((ancestors x tree).filter (fun q => decide (x < q))).map label).toFinset =
        ((ancestors x tree).map label).toFinset := by
  ext z
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_map,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro (⟨q,⟨hq,_⟩,eq⟩ | ⟨q,⟨hq,_⟩,eq⟩) <;> exact ⟨q,hq,eq⟩
  · rintro ⟨q,hq,rfl⟩
    rcases lt_trichotomy q x with qx | rfl | xq
    · exact Or.inl ⟨q,⟨hq,qx⟩,rfl⟩
    · exact (not_mem_ancestors tree q hq).elim
    · exact Or.inr ⟨q,⟨hq,xq⟩,rfl⟩

theorem side_labels_inter_subset (label : α → β) (mono : Monotone label)
    (tree : Tree α) (x : α) :
    (((ancestors x tree).filter (fun q => decide (q < x))).map label).toFinset ∩
      (((ancestors x tree).filter (fun q => decide (x < q))).map label).toFinset ⊆ {label x} := by
  intro z member
  obtain ⟨hl,hr⟩ := Finset.mem_inter.mp member
  have lower := right_labels_bounded label mono tree x z (List.mem_toFinset.mp hr)
  have upper := left_labels_bounded label mono tree x z (List.mem_toFinset.mp hl)
  exact Finset.mem_singleton.mpr (le_antisymm upper lower)

theorem side_labels_card_sum (label : α → β) (mono : Monotone label)
    (tree : Tree α) (x : α) :
    (((ancestors x tree).filter (fun q => decide (q < x))).map label).toFinset.card +
      (((ancestors x tree).filter (fun q => decide (x < q))).map label).toFinset.card ≤
        ((ancestors x tree).map label).toFinset.card + 1 := by
  have account := Finset.card_union_add_card_inter
    (((ancestors x tree).filter (fun q => decide (q < x))).map label).toFinset
    (((ancestors x tree).filter (fun q => decide (x < q))).map label).toFinset
  rw [side_labels_union] at account
  have inter := Finset.card_le_card (side_labels_inter_subset label mono tree x)
  simp only [Finset.card_singleton] at inter
  omega

theorem focus_empty_or_query (tree : Tree α) (x : α) :
    focus x tree = .empty ∨ ∃ l r, focus x tree = .node l x r := by
  induction tree with
  | empty => exact Or.inl rfl
  | node l a r ihl ihr =>
    by_cases xa : x < a
    · simpa only [focus,xa,↓reduceIte] using ihl
    · by_cases ax : a < x
      · simpa only [focus,xa,ax,↓reduceIte] using ihr
      · have same : a = x := le_antisymm (le_of_not_gt xa) (le_of_not_gt ax)
        subst a
        exact Or.inr ⟨l,r,by simp [focus]⟩

/-- The two new attachments cost at most one more mixed edge than the old
attachments and the former edge into the queried key. -/
theorem terminal_charges (label : α → β) (mono : Monotone label)
    (tree : Tree α) (x : α) (ordered : Ordered tree) :
    rootCharge label (lastParent x ((ancestors x tree).filter (fun q => decide (q < x))))
        (leftChild (focus x tree)) +
      rootCharge label (lastParent x ((ancestors x tree).filter (fun q => decide (x < q))))
        (rightChild (focus x tree)) ≤
    rootCharge label x (leftChild (focus x tree)) +
      rootCharge label x (rightChild (focus x tree)) +
      rootCharge label (lastParent x (ancestors x tree)) (focus x tree) + 1 := by
  rcases focus_empty_or_query tree x with empty | ⟨l,r,found⟩
  · simp [empty,leftChild,rightChild,rootCharge]
  · simp only [found,leftChild,rightChild]
    by_cases present : label x ∈ ((ancestors x tree).map label).toFinset
    · rw [← side_labels_union label tree x] at present
      rcases Finset.mem_union.mp present with left | right
      · have same := left_last_label label mono tree x ordered (List.mem_toFinset.mp left)
        rw [rootCharge_congr label same l]
        have other := rootCharge_le label
          (lastParent x ((ancestors x tree).filter (fun q => decide (x < q)))) r
        omega
      · have same := right_last_label label mono tree x ordered (List.mem_toFinset.mp right)
        rw [rootCharge_congr label same r]
        have other := rootCharge_le label
          (lastParent x ((ancestors x tree).filter (fun q => decide (q < x)))) l
        omega
    · by_cases empty : ancestors x tree = []
      · simp only [empty,List.filter_nil,lastParent_nil]
        omega
      · have absent : label (lastParent x (ancestors x tree)) ≠ label x := by
          intro same
          apply present
          apply List.mem_toFinset.mpr
          exact List.mem_map.mpr ⟨_,lastParent_mem x _ empty,same⟩
        have old : rootCharge label (lastParent x (ancestors x tree)) (.node l x r) = 1 := by
          simp only [rootCharge,absent,↓reduceIte]
        rw [old]
        have left := rootCharge_le label
          (lastParent x ((ancestors x tree).filter (fun q => decide (q < x)))) l
        have right := rootCharge_le label
          (lastParent x ((ancestors x tree).filter (fun q => decide (x < q)))) r
        omega

theorem original_changes (label : α → β) (tree : Tree α) (x : α) :
    changesFrom (some (label x)) ((ancestors x tree).map label) =
      rootCharge label x tree + changes ((ancestors x tree).map label) := by
  cases tree with
  | empty => simp [ancestors,changes,changesFrom,rootCharge]
  | node l a r =>
    by_cases xa : x < a
    · simp [ancestors,xa,changes,changesFrom,changeStep,rootCharge]
    · by_cases ax : a < x
      · simp [ancestors,xa,ax,changes,changesFrom,changeStep,rootCharge]
      · have same : a = x := le_antisymm (le_of_not_gt xa) (le_of_not_gt ax)
        subst a
        simp [ancestors,changes,changesFrom,rootCharge]

/-- The local mixed-edge potential estimate. Repeated interval runs in the
physical search pay for their excess alternations after splitting into spines. -/
theorem mixed_access_bound (label : α → β) (mono : Monotone label)
    (tree : Tree α) (x : α) (ordered : Ordered tree) :
    mixed label (access x tree) + changes ((ancestors x tree).map label) ≤
      mixed label tree + ((ancestors x tree).map label).toFinset.card + 2 := by
  have before := original_path_account label x x tree
  have after := access_path_account label x tree ordered
  rw [chainCost_account,original_changes] at before
  rw [chainCost_account,chainCost_account] at after
  have left := changes_anchored_le_card (label x)
    (((ancestors x tree).filter (fun q => decide (q < x))).map label)
    (left_labels_sorted label mono tree x ordered)
  have right := changes_anchored_le_card_decreasing (label x)
    (((ancestors x tree).filter (fun q => decide (x < q))).map label)
    (right_labels_sorted label mono tree x ordered)
  have cards := side_labels_card_sum label mono tree x
  have terminal := terminal_charges label mono tree x ordered
  have target : mixed label (focus x tree) = mixed label (leftChild (focus x tree)) +
      mixed label (rightChild (focus x tree)) + rootCharge label x (leftChild (focus x tree)) +
      rootCharge label x (rightChild (focus x tree)) := by
    rcases focus_empty_or_query tree x with empty | ⟨l,r,found⟩
    · simp [empty,leftChild,rightChild,mixed,rootCharge]
    · simp only [found,leftChild,rightChild,mixed]
  unfold rooted at before
  omega

end DynamicOptimality.Funnel.Warm
