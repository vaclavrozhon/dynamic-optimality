import TangoSquared.Paper20261030.AuxiliaryComponents

/-!
# Charged search from an auxiliary root to its actual gap port

At separator `j`, a requested depth `d` goes left when `d ≤ j` and right
otherwise. The execution reads that separator and follows an actual child
edge. It finishes at the attached port root, without entering the port's
interior. The index used in the specification counts inorder gaps; the
execution does not jump to that index.
-/

namespace TangoSquared.Paper20261030.Auxiliary

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open Metadata ColoredStorage SourcePointer

variable {α : Type*} {β : Nat → Type*}

def gapIndex (d : Nat) : Impl Nat β → Nat
  | .leaf => 0
  | .inner _ key _ l r => if d ≤ key then gapIndex d l else l.size + 1 + gapIndex d r

theorem gapIndex_bound (d : Nat) (t : Impl Nat β) (ht : t.Balanced) : gapIndex d t ≤ t.size := by
  induction t with
  | leaf => exact le_rfl
  | inner sz key value l r ihl ihr =>
    have hl := ihl ht.left
    have hr := ihr ht.right
    have hs := ht.eq
    simp only [gapIndex]
    split <;> simp only [size_inner] <;> omega

theorem gapIndex_count (d : Nat) (t : Impl Nat β) (ht : t.Balanced) (ho : t.Ordered) :
    gapIndex d t = (t.toListModel.filter (fun e => decide (e.1 < d))).length := by
  induction t with
  | leaf => rfl
  | inner sz key value l r ihl ihr =>
    change (l.toListModel ++ ⟨key,value⟩ :: r.toListModel).Pairwise _ at ho
    obtain ⟨hol,hor,hcross⟩ := List.pairwise_append.mp ho
    obtain ⟨hroot,horr⟩ := List.pairwise_cons.mp hor
    by_cases hd : d ≤ key
    · have hempty : (r.toListModel.filter (fun e => decide (e.1 < d))) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro e he hf
        have hg := Nat.compare_eq_lt.mp (hroot e he)
        change key < e.1 at hg
        have hf' : e.1 < d := of_decide_eq_true hf
        omega
      simp only [gapIndex,if_pos hd,toListModel_inner,List.filter_append,List.filter_cons,
        show decide (key < d) = false from decide_eq_false (by omega),Bool.false_eq_true,
        if_false,hempty,List.append_nil,ihl ht.left hol]
    · have hfull : (l.toListModel.filter (fun e => decide (e.1 < d))) = l.toListModel := by
        apply List.filter_eq_self.mpr
        intro e he
        have hg := Nat.compare_eq_lt.mp (hcross e he ⟨key,value⟩ (by simp))
        change e.1 < key at hg
        exact decide_eq_true (by omega)
      simp only [gapIndex,if_neg hd,toListModel_inner,List.filter_append,List.filter_cons,
        show decide (key < d) = true from decide_eq_true (by omega),if_true,hfull,
        List.length_append,List.length_cons,ihr ht.right horr,size_eq_length l ht.left]
      omega

theorem search_port_charged (d : Nat) (t : Impl Nat β) (ht : t.Balanced)
    (ports : Nat → Source α (NodeRecord Nat β)) (base : Nat)
    (ancestors : List (SourcePointer.Frame α (NodeRecord Nat β))) :
    ∃ (actual : SourcePointer.Cursor α (NodeRecord Nat β)) (reads : List (NodeRecord Nat β)) (cost : Nat),
      SourcePointer.Trace ⟨GapSource.encode (recordTree t) ports base,ancestors⟩ reads actual cost ∧
      actual.focus = ports (base + gapIndex d t) ∧
      actual.tree = SourcePointer.plug (GapSource.encode (recordTree t) ports base) ancestors ∧
      cost ≤ 2 * height t := by
  induction t generalizing base ancestors with
  | leaf => exact ⟨⟨ports base,ancestors⟩,[],0,.nil _,by simp [gapIndex],rfl,le_rfl⟩
  | inner sz key value l r ihl ihr =>
    have hs := recordTree_size_of_balanced l ht.left
    by_cases hd : d ≤ key
    · obtain ⟨actual,reads,cost,trace,hfocus,htree,hcost⟩ := ihl ht.left base
        (.left (sz,⟨key,value⟩) (GapSource.encode (recordTree r) ports (base + l.size + 1)) :: ancestors)
      have full := SourcePointer.Trace.read (SourcePointer.Trace.step
        (SourcePointer.Step.left (GapSource.encode (recordTree l) ports base)
          (GapSource.encode (recordTree r) ports (base + l.size + 1)) (sz,⟨key,value⟩) ancestors) trace)
      refine ⟨actual,(sz,⟨key,value⟩) :: reads,cost + 1 + 1,?_,?_,?_,?_⟩
      · simpa only [recordTree,GapSource.encode,hs,Source.rootRecord] using full
      · simpa only [gapIndex,if_pos hd] using hfocus
      · simpa only [recordTree,GapSource.encode,hs,SourcePointer.plug] using htree
      · simp only [height]; omega
    · obtain ⟨actual,reads,cost,trace,hfocus,htree,hcost⟩ := ihr ht.right (base + l.size + 1)
        (.right (GapSource.encode (recordTree l) ports base) (sz,⟨key,value⟩) :: ancestors)
      have full := SourcePointer.Trace.read (SourcePointer.Trace.step
        (SourcePointer.Step.right (GapSource.encode (recordTree l) ports base)
          (GapSource.encode (recordTree r) ports (base + l.size + 1)) (sz,⟨key,value⟩) ancestors) trace)
      refine ⟨actual,(sz,⟨key,value⟩) :: reads,cost + 1 + 1,?_,?_,?_,?_⟩
      · simpa only [recordTree,GapSource.encode,hs,Source.rootRecord] using full
      · simpa only [gapIndex,if_neg hd,Nat.add_assoc] using hfocus
      · simpa only [recordTree,GapSource.encode,hs,SourcePointer.plug] using htree
      · simp only [height]; omega

theorem search_port_log (d : Nat) (t : Impl Nat β) (ht : t.Balanced)
    (ports : Nat → Source α (NodeRecord Nat β)) (base : Nat)
    (ancestors : List (SourcePointer.Frame α (NodeRecord Nat β))) :
    ∃ (actual : SourcePointer.Cursor α (NodeRecord Nat β)) (reads : List (NodeRecord Nat β)) (cost : Nat),
      SourcePointer.Trace ⟨GapSource.encode (recordTree t) ports base,ancestors⟩ reads actual cost ∧
      actual.focus = ports (base + gapIndex d t) ∧
      actual.tree = SourcePointer.plug (GapSource.encode (recordTree t) ports base) ancestors ∧
      cost ≤ 6 * Nat.clog 2 (t.size + 1) := by
  obtain ⟨actual,reads,cost,trace,hfocus,htree,hcost⟩ := search_port_charged d t ht ports base ancestors
  have hh := balanced_height_log ht
  exact ⟨actual,reads,cost,trace,hfocus,htree,by omega⟩

end TangoSquared.Paper20261030.Auxiliary
