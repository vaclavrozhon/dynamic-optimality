import ChaCha.Paper20261030.AuxiliarySourceControllers

/-! Payload relabeling for the existing auxiliary tree. The standard
library's `Impl.map` changes application values while preserving cached
sizes, keys, and shape. These lemmas connect the controller compiler's
false entry markers to the already maintained clean component records. -/

namespace ChaCha.Paper20261030.Auxiliary.PayloadMap

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open MTR DynamicOptimality BoundaryObservations

variable {κ : Type*} {β γ : κ → Type*} [Ord κ]

theorem balanced (f : (key : κ) → β key → γ key) {tree : Impl κ β} (h : tree.Balanced) :
    (tree.map f).Balanced := (sameKeys_map (t := tree) (f := f)).symm.balanced h

theorem recordTree_map (f : (key : κ) → β key → γ key) (tree : Impl κ β) :
    recordTree (tree.map f) = Relabel.tree (fun entry : NodeRecord κ β =>
      (entry.1,⟨entry.2.1,f entry.2.1 entry.2.2⟩)) (recordTree tree) := by
  induction tree <;> simp [Impl.map,recordTree,Relabel.tree, *]

theorem search_map (f : (key : κ) → β key → γ key) (request : κ) (tree : Impl κ β) :
    searchResult request (tree.map f) = searchResult request tree := by
  induction tree <;> simp [Impl.map,searchResult, *]

theorem bin_map (f : (key : κ) → β key → γ key) (key : κ) (value : β key) (left right : Impl κ β) :
    (bin key value left right).map f = bin key (f key value) (left.map f) (right.map f) := by
  simp only [bin,Impl.map,size_map]

theorem balance_map (f : (key : κ) → β key → γ key) (key : κ) (value : β key) (left right : Impl κ β) :
    (balanceₘ key value left right).map f = balanceₘ key (f key value) (left.map f) (right.map f) := by
  unfold balanceₘ
  simp only [size_map]
  split
  · exact bin_map f key value left right
  · split
    · cases right with
      | leaf => rename_i impossible; have : (0 : Nat) > delta * _ := impossible; omega
      | inner size rk rv rl rr =>
        simp only [Impl.map,rotateL,size_map]
        split
        · simp only [singleL,bin,Impl.map,size_map,Impl.size_inner]
        · cases rl <;> simp only [Impl.map,singleL,doubleL,bin,size_map,Impl.size_inner,Impl.size_leaf]
    · split
      · cases left with
        | leaf => rename_i impossible; have : (0 : Nat) > delta * _ := impossible; omega
        | inner size lk lv ll lr =>
          simp only [Impl.map,rotateR,size_map]
          split
          · simp only [singleR,bin,Impl.map,size_map,Impl.size_inner]
          · cases lr <;> simp only [Impl.map,singleR,doubleR,bin,size_map,Impl.size_inner,Impl.size_leaf]
      · exact bin_map f key value left right

theorem balanceLErase_map (f : (key : κ) → β key → γ key) (key : κ) (value : β key)
    (left right : Impl κ β) (hl : left.Balanced) (hr : right.Balanced)
    (hp : BalanceLErasePrecond left.size right.size) :
    (balanceLErase key value left right hl hr hp).map f =
      balanceLErase key (f key value) (left.map f) (right.map f) (balanced f hl) (balanced f hr)
        (by simpa only [size_map] using hp) := by
  rw [balanceLErase_eq_balanceL!,balanceL!_eq_balance! hl hr hp,
    balance!_eq_balanceₘ hl hr (Or.inl hp),balance_map]
  have mapped : BalanceLErasePrecond (left.map f).size (right.map f).size := by simpa only [size_map] using hp
  rw [balanceLErase_eq_balanceL!,balanceL!_eq_balance! (balanced f hl) (balanced f hr) mapped,
    balance!_eq_balanceₘ (balanced f hl) (balanced f hr) (Or.inl mapped)]

theorem balanceRErase_map (f : (key : κ) → β key → γ key) (key : κ) (value : β key)
    (left right : Impl κ β) (hl : left.Balanced) (hr : right.Balanced)
    (hp : BalanceLErasePrecond right.size left.size) :
    (balanceRErase key value left right hl hr hp).map f =
      balanceRErase key (f key value) (left.map f) (right.map f) (balanced f hl) (balanced f hr)
        (by simpa only [size_map] using hp) := by
  rw [balanceRErase_eq_balanceR!,balanceR!_eq_balance! hl hr hp,
    balance!_eq_balanceₘ hl hr (Or.inr hp),balance_map]
  have mapped : BalanceLErasePrecond (right.map f).size (left.map f).size := by simpa only [size_map] using hp
  rw [balanceRErase_eq_balanceR!,balanceR!_eq_balance! (balanced f hl) (balanced f hr) mapped,
    balance!_eq_balanceₘ (balanced f hl) (balanced f hr) (Or.inr mapped)]

theorem insertMin_map (f : (key : κ) → β key → γ key) (key : κ) (value : β key)
    (tree : Impl κ β) (h : tree.Balanced) :
    (insertMin key value tree h).impl.map f =
      (insertMin key (f key value) (tree.map f) (balanced f h)).impl := by
  induction tree with
  | leaf => rfl
  | inner size k v left right ihl ihr =>
    simp only [insertMin,Impl.map,balanceL_eq_balanceLErase,balanceLErase_map,ihl]

theorem insertMax_map (f : (key : κ) → β key → γ key) (key : κ) (value : β key)
    (tree : Impl κ β) (h : tree.Balanced) :
    (insertMax key value tree h).impl.map f =
      (insertMax key (f key value) (tree.map f) (balanced f h)).impl := by
  induction tree with
  | leaf => rfl
  | inner size k v left right ihl ihr =>
    simp only [insertMax,Impl.map,balanceR_eq_balanceRErase,balanceRErase_map,ihr]

theorem link_map (f : (key : κ) → β key → γ key) (key : κ) (value : β key)
    (left right : Impl κ β) (hl : left.Balanced) (hr : right.Balanced) :
    (link key value left right hl hr).impl.map f =
      (link key (f key value) (left.map f) (right.map f) (balanced f hl) (balanced f hr)).impl := by
  cases left with
  | leaf => simpa only [link,Impl.map] using insertMin_map f key value right hr
  | inner sl lk lv ll lr =>
    cases right with
    | leaf => simpa only [link,Impl.map] using insertMax_map f key value (.inner sl lk lv ll lr) hl
    | inner sr rk rv rl rr =>
      by_cases hright : delta*sl < sr
      · rw [link,dif_pos hright]
        simp only [Impl.map]
        rw [link,dif_pos hright]
        simp only [balanceLErase_map,link_map f key value (.inner sl lk lv ll lr) rl,Impl.map]
      · by_cases hleft : delta*sr < sl
        · rw [link,dif_neg hright,dif_pos hleft]
          simp only [Impl.map]
          rw [link,dif_neg hright,dif_pos hleft]
          simp only [balanceRErase_map,link_map f key value lr (.inner sr rk rv rl rr),Impl.map]
        · rw [link,dif_neg hright,dif_neg hleft]
          simp only [Impl.map]
          rw [link,dif_neg hright,dif_neg hleft]
termination_by sizeOf left+sizeOf right

def splitResultMap (f : (key : κ) → β key → γ key) {key : κ} (result : SplitResult β key) :
    SplitResult γ key :=
  ⟨f key result.value,result.left.map f,result.right.map f,
    balanced f result.left_balanced,balanced f result.right_balanced⟩

theorem splitResult_ext {key : κ} (a b : SplitResult β key)
    (value : a.value = b.value) (left : a.left = b.left) (right : a.right = b.right) : a = b := by
  cases a
  cases b
  cases value
  cases left
  cases right
  rfl

theorem split_map [LawfulEqOrd κ] (f : (key : κ) → β key → γ key) (key : κ)
    (tree : Impl κ β) (h : tree.Balanced) (found : searchResult key tree = true) :
    splitResultMap f (splitAt key tree h found) =
      splitAt key (tree.map f) (balanced f h) (by simpa only [search_map] using found) := by
  induction tree with
  | leaf => simp only [searchResult,Bool.false_eq_true] at found
  | inner size k v left right ihl ihr =>
    cases comparison : compare key k with
    | eq =>
      have same := compare_eq_iff_eq.mp comparison
      subst k
      simp only [splitAt,Impl.map]
      split <;> rename_i hb <;> simp only [comparison,reduceCtorEq] at hb
      rfl
    | lt =>
      have child : searchResult key left = true := by simpa only [searchResult,comparison] using found
      have ih := ihl h.left child
      simp only [splitAt,Impl.map]
      split <;> rename_i hb <;> simp only [comparison,reduceCtorEq] at hb
      apply splitResult_ext <;> simp only [splitResultMap,link_map,← ih]
      all_goals simp only [link_eq_link!,← ih,splitResultMap]
    | gt =>
      have child : searchResult key right = true := by simpa only [searchResult,comparison] using found
      have ih := ihr h.right child
      simp only [splitAt,Impl.map]
      split <;> rename_i hb <;> simp only [comparison,reduceCtorEq] at hb
      apply splitResult_ext <;> simp only [splitResultMap,link_map,← ih]
      all_goals simp only [link_eq_link!,← ih,splitResultMap]

theorem split_impl_map [LawfulEqOrd κ] (f : (key : κ) → β key → γ key) (key : κ)
    (tree : Impl κ β) (h : tree.Balanced) (found : searchResult key tree = true) :
    (splitAt key tree h found).impl.map f =
      (splitAt key (tree.map f) (balanced f h) (by simpa only [search_map] using found)).impl := by
  rw [← split_map]
  exact bin_map f key _ _ _

variable {α ρ : Type*}

theorem clean_restore (tree : Impl κ (fun _ => ρ×Bool)) (clean : Clean tree) :
    (tree.map (fun _ value => value.1)).map (fun _ value => (value,false)) = tree := by
  induction tree with
  | leaf => rfl
  | inner size key value left right ihl ihr =>
    rcases value with ⟨value,bit⟩
    obtain ⟨root,leftClean,rightClean⟩ := clean
    change bit = false at root
    subst bit
    simp only [Impl.map,ihl leftClean,ihr rightClean]

theorem tree_as_map (tree : Impl κ (fun _ => ρ))
    (ports : Nat → ColoredStorage.Source α (GapSource.Controller.MarkedRecord κ ρ)) (base : Nat) :
    SourceController.tree tree ports base =
      GapSource.encode (recordTree (tree.map (fun _ value => (value,false)))) ports base := by
  exact congrArg (fun tree => GapSource.encode tree ports base)
    (recordTree_map (fun (_ : κ) (value : ρ) => (value,false)) tree).symm

theorem clean_encode (tree : Impl κ (fun _ => ρ×Bool)) (clean : Clean tree)
    (ports : Nat → ColoredStorage.Source α (GapSource.Controller.MarkedRecord κ ρ)) (base : Nat) :
    SourceController.tree (tree.map (fun _ value => value.1)) ports base =
      GapSource.encode (recordTree tree) ports base := by
  unfold SourceController.tree
  have mapped := recordTree_map (fun (_ : κ) (value : ρ) => (value,false))
    (tree.map (fun _ value => value.1))
  rw [clean_restore tree clean] at mapped
  exact congrArg (fun tree => GapSource.encode tree ports base) mapped.symm

theorem clean_source (component : AuxiliaryComponent α κ (fun _ => ρ×Bool)) (clean : Clean component.core) :
    SourceController.tree (component.core.map (fun _ value => value.1)) component.ports 0 = component.tree := by
  unfold SourceController.tree AuxiliaryComponent.tree
  have mapped := recordTree_map (fun (_ : κ) (value : ρ) => (value,false))
    (component.core.map (fun _ value => value.1))
  rw [clean_restore component.core clean] at mapped
  exact congrArg (fun tree => GapSource.encode tree component.ports 0) mapped.symm

end ChaCha.Paper20261030.Auxiliary.PayloadMap
