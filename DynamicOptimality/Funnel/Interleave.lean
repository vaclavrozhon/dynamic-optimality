import DynamicOptimality.Funnel.ShuffleMTR
import Mathlib.Order.Fin.Basic

/-! # Constructive occurrence interleavings and source expansion

The inductive relation records which source supplies each output occurrence.
Repeated keys and overlapping alphabets are unrestricted. Expanding either
source by extra occurrences yields an expanded interleaving containing the
original output as a subsequence.
-/

namespace DynamicOptimality.Funnel

variable {α : Type*} [LinearOrder α]

inductive Interleave : List α → List α → List α → Prop
  | nil : Interleave [] [] []
  | left (x : α) {X Y W : List α} : Interleave X Y W → Interleave (x :: X) Y (x :: W)
  | right (x : α) {X Y W : List α} : Interleave X Y W → Interleave X (x :: Y) (x :: W)

theorem Interleave.left_prefix {X Y W : List α} (shuffle : Interleave X Y W) (before : List α) :
    Interleave (before ++ X) Y (before ++ W) := by
  induction before with
  | nil => exact shuffle
  | cons a before ih => exact .left a ih

theorem Interleave.right_prefix {X Y W : List α} (shuffle : Interleave X Y W) (before : List α) :
    Interleave X (before ++ Y) (before ++ W) := by
  induction before with
  | nil => exact shuffle
  | cons a before ih => exact .right a ih

theorem Interleave.append (X Y : List α) : Interleave X Y (X ++ Y) := by
  simpa using ((Interleave.nil (α := α)).right_prefix Y).left_prefix X

private theorem cons_sublist_split {a : α} {tail large : List α} (sublist : (a :: tail).Sublist large) :
    ∃ before after, large = before ++ a :: after ∧ tail.Sublist after := by
  induction large with
  | nil => simp at sublist
  | cons b large ih =>
    cases sublist with
    | cons _ sublist =>
      obtain ⟨before,after,equal,sublist⟩ := ih sublist
      exact ⟨b :: before,after,by simp [equal],sublist⟩
    | cons_cons _ sublist => exact ⟨[],large,rfl,sublist⟩

theorem Interleave.expand {X Y W : List α} (shuffle : Interleave X Y W)
    {expandedX expandedY : List α} (leftSub : X.Sublist expandedX) (rightSub : Y.Sublist expandedY) :
    ∃ expandedW, Interleave expandedX expandedY expandedW ∧ W.Sublist expandedW := by
  induction shuffle generalizing expandedX expandedY with
  | nil => exact ⟨expandedX ++ expandedY,.append _ _,List.nil_sublist _⟩
  | @left x X Y W shuffle ih =>
    obtain ⟨before,after,equal,sublist⟩ := cons_sublist_split leftSub
    obtain ⟨expandedW,interleave,retained⟩ := ih sublist rightSub
    subst expandedX
    exact ⟨before ++ x :: expandedW,(Interleave.left x interleave).left_prefix before,
      (retained.cons_cons x).trans (List.sublist_append_right _ _)⟩
  | @right x X Y W shuffle ih =>
    obtain ⟨before,after,equal,sublist⟩ := cons_sublist_split rightSub
    obtain ⟨expandedW,interleave,retained⟩ := ih leftSub sublist
    subst expandedY
    exact ⟨before ++ x :: expandedW,(Interleave.right x interleave).right_prefix before,
      (retained.cons_cons x).trans (List.sublist_append_right _ _)⟩

private def prependZero {m n : Nat} (embedding : Fin m ↪o Fin n) : Fin (m+1) ↪o Fin (n+1) :=
  OrderEmbedding.ofStrictMono (Fin.cases 0 (fun i => (embedding i).succ)) (by
    intro i j strict
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ strict).elim
      | succ j => simp
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (Fin.not_lt_zero _ strict).elim
      | succ j => exact Fin.succ_lt_succ_iff.mpr (embedding.strictMono (Fin.succ_lt_succ_iff.mp strict)))

private theorem shuffle_nil : Nonempty (Shuffle ([] : List α) [] []) := by
  refine ⟨{
    left := (OrderIso.refl _).toOrderEmbedding
    right := (OrderIso.refl _).toOrderEmbedding
    left_keys := ?_
    right_keys := ?_
    disjoint := ?_
    cover := ?_ }⟩
  · intro p; exact p.elim0
  · intro p; exact p.elim0
  · simp
  · simp

def Shuffle.symm {X Y W : List α} (shuffle : Shuffle X Y W) : Shuffle Y X W where
  left := shuffle.right
  right := shuffle.left
  left_keys := shuffle.right_keys
  right_keys := shuffle.left_keys
  disjoint := shuffle.disjoint.symm
  cover := by simpa only [Finset.union_comm] using shuffle.cover

def Shuffle.cons_left {X Y W : List α} (shuffle : Shuffle X Y W) (x : α) :
    Shuffle (x :: X) Y (x :: W) := by
  let left : Fin (x :: X).length ↪o Fin (x :: W).length := prependZero shuffle.left
  let right : Fin Y.length ↪o Fin (x :: W).length := shuffle.right.trans (Fin.succOrderEmb _)
  refine { left := left, right := right, left_keys := ?_,right_keys := ?_,disjoint := ?_,cover := ?_ }
  · intro p
    cases p using Fin.cases with
    | zero => rfl
    | succ p =>
      change (x :: W).get ((shuffle.left p).succ) = (x :: X).get p.succ
      simpa only [List.get_eq_getElem,Fin.val_succ,List.getElem_cons_succ] using shuffle.left_keys p
  · intro p
    change (x :: W).get ((shuffle.right p).succ) = Y.get p
    simpa only [List.get_eq_getElem,Fin.val_succ,List.getElem_cons_succ] using shuffle.right_keys p
  · apply Finset.disjoint_left.mpr
    intro p leftMember rightMember
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp leftMember
    obtain ⟨j,_,equal⟩ := Finset.mem_image.mp rightMember
    cases i using Fin.cases with
    | zero =>
      have impossible : (shuffle.right j).succ = 0 := equal
      exact Fin.succ_ne_zero _ impossible
    | succ i =>
      have same : shuffle.right j = shuffle.left i := Fin.succ_injective _ equal
      exact (Finset.disjoint_left.mp shuffle.disjoint)
        (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,same.symm⟩)
        (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
  · apply Finset.ext
    intro p
    simp only [Finset.mem_union,Finset.mem_univ,iff_true]
    cases p using Fin.cases with
    | zero => exact Or.inl (Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩)
    | succ p =>
      have covered : p ∈ Finset.univ.image shuffle.left ∪ Finset.univ.image shuffle.right := by
        rw [shuffle.cover]
        exact Finset.mem_univ _
      rcases Finset.mem_union.mp covered with fromLeft | fromRight
      · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp fromLeft
        exact Or.inl (Finset.mem_image.mpr ⟨i.succ,Finset.mem_univ _,rfl⟩)
      · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp fromRight
        exact Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

theorem Interleave.exists_shuffle {X Y W : List α} (interleave : Interleave X Y W) :
    Nonempty (Shuffle X Y W) := by
  induction interleave with
  | nil => exact shuffle_nil
  | left x _ ih => obtain ⟨shuffle⟩ := ih; exact ⟨shuffle.cons_left x⟩
  | right x _ ih => obtain ⟨shuffle⟩ := ih; exact ⟨(shuffle.symm.cons_left x).symm⟩

theorem Interleave.mtr_bound {X Y W : List α} (interleave : Interleave X Y W)
    (leftTree rightTree : ChaCha.MTR.Tree α)
    (leftSuccess : ChaCha.MTR.Tree.Successful leftTree X)
    (rightSuccess : ChaCha.MTR.Tree.Successful rightTree Y) :
    wordCount W + W.length ≤ 3 *
      (ChaCha.MTR.runCost leftTree X + ChaCha.MTR.runCost rightTree Y) := by
  obtain ⟨shuffle⟩ := interleave.exists_shuffle
  exact shuffle.mtr_bound leftTree rightTree leftSuccess rightSuccess

end DynamicOptimality.Funnel
