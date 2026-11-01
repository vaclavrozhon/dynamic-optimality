import DynamicOptimality.HullSeparation
import TangoSquared.Paper20261030.RobustArboralBound

/-! Geometric histories of actual rooted-hull BST accesses. Every key
stores its most recent touch time, the tree is a max-heap by these times,
and the finite history is arborally satisfied. All three properties are
preserved by the existing hull execution, with no assumed geometric
simulation contract. -/

namespace TangoSquared.Paper20261030.BSTHistory

open Rectangles DynamicOptimality MTR.Tree MTR.Tree.PriorityHull

def augment (history : Finset Point) (selected : List Int) (time : Int) : Finset Point :=
  history ∪ selected.toFinset.image (fun key => (key,time))

theorem old_mem {history : Finset Point} {selected : List Int} {time : Int} {point : Point}
    (member : point ∈ history) : point ∈ augment history selected time := Finset.mem_union_left _ member

theorem new_mem {history : Finset Point} {selected : List Int} {time key : Int}
    (member : key ∈ selected) : (key,time) ∈ augment history selected time :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨key,List.mem_toFinset.mpr member,rfl⟩)

structure Valid (tree : MTR.Tree Int) (history : Finset Point) (memory : Int → Int) (time : Int) : Prop where
  keys : ∀ point ∈ history, point.1 ∈ tree.inorder
  latest : ∀ key ∈ tree.inorder, (key,memory key) ∈ history
  below : ∀ point ∈ history, point.2 ≤ memory point.1
  past : ∀ key ∈ tree.inorder, memory key < time
  heap : Heap memory tree
  satisfied : ArboralDilation.Satisfied (history : Set Point)

theorem Valid.time_lt {tree history memory time} (valid : Valid tree history memory time)
    {point : Point} (member : point ∈ history) : point.2 < time :=
  (valid.below point member).trans_lt (valid.past point.1 (valid.keys point member))

theorem hull_inorder {before after : MTR.Tree Int} {key : Int}
    (access : MTR.HullAccess key before after) : before.inorder = after.inorder := by
  obtain ⟨_,_,rotations⟩ := graft_simulation_linear access.source access.target access.same_keys access.gaps 0
  simpa only [access.source_tree,access.target_tree] using rotations.inorder_eq

theorem Valid.new_old_witness {before after : MTR.Tree Int} {request : Int}
    (access : MTR.HullAccess request before after) (ordered : before.Ordered)
    {history memory time} (valid : Valid before history memory time)
    {key : Int} (selected : key ∈ access.source.inorder) {old : Point} (member : old ∈ history)
    (different : key ≠ old.1) :
    ∃ point ∈ augment history access.source.inorder time,
      point ≠ (key,time) ∧ point ≠ old ∧ min key old.1 ≤ point.1 ∧ point.1 ≤ max key old.1 ∧
      old.2 ≤ point.2 ∧ point.2 ≤ time := by
  have oldTime := valid.time_lt member
  have sourceHeap : Heap memory (graft access.source access.gaps 0) := by rw [access.source_tree]; exact valid.heap
  have sourceOrdered : Ordered (graft access.source access.gaps 0) := by rw [access.source_tree]; exact ordered
  have oldPresent : old.1 ∈ (graft access.source access.gaps 0).inorder := by
    rw [access.source_tree]
    exact valid.keys old member
  obtain touched | recent | ⟨middle,middleSelected,notNew,notOld,lo,hi⟩ :=
    hull_key_separation access.source access.gaps 0 memory sourceHeap sourceOrdered selected oldPresent
  · refine ⟨(old.1,time),new_mem touched,?_,?_,min_le_right _ _,le_max_right _ _,oldTime.le,le_rfl⟩
    · intro equal; exact different (congrArg Prod.fst equal).symm
    · intro equal; have := congrArg Prod.snd equal; omega
  · have inTree := (inorder_sublist_graft access.source access.gaps 0).subset selected
    rw [access.source_tree] at inTree
    have lastTime := valid.past key inTree
    refine ⟨(key,memory key),old_mem (valid.latest key inTree),?_,?_,min_le_left _ _,le_max_left _ _,
      (valid.below old member).trans recent,lastTime.le⟩
    · intro equal; have := congrArg Prod.snd equal; omega
    · intro equal; exact different (congrArg Prod.fst equal)
  · refine ⟨(middle,time),new_mem middleSelected,?_,?_,lo,hi,oldTime.le,le_rfl⟩
    · intro equal; exact notNew (congrArg Prod.fst equal)
    · intro equal; exact notOld (congrArg Prod.fst equal)

theorem Valid.augment_satisfied {before after : MTR.Tree Int} {request : Int}
    (access : MTR.HullAccess request before after) (ordered : before.Ordered)
    {history memory time} (valid : Valid before history memory time) :
    ArboralDilation.Satisfied (augment history access.source.inorder time : Set Point) := by
  intro a t b u aMember bMember keyOrder timeNe
  change (a,t) ∈ augment history access.source.inorder time at aMember
  change (b,u) ∈ augment history access.source.inorder time at bMember
  obtain oldA | newA := Finset.mem_union.mp aMember
  · obtain oldB | newB := Finset.mem_union.mp bMember
    · obtain ⟨point,member,box,notA,notB⟩ := valid.satisfied a t b u oldA oldB keyOrder timeNe
      exact ⟨point,old_mem member,box,notA,notB⟩
    · obtain ⟨key,selected,equal⟩ := Finset.mem_image.mp newB
      have keys := congrArg Prod.fst equal
      have times := congrArg Prod.snd equal
      dsimp only at keys times
      subst key
      subst u
      obtain ⟨point,member,notB,notA,lo,hi,tlo,thi⟩ := valid.new_old_witness access ordered
        (List.mem_toFinset.mp selected) oldA (by dsimp; omega)
      refine ⟨point,member,?_,notA,notB⟩
      have past := valid.time_lt oldA
      simp only [ArboralDilation.InRectangle]
      dsimp only at lo hi tlo
      exact ⟨by omega,by omega,by omega,by omega⟩
  · obtain ⟨key,selected,equal⟩ := Finset.mem_image.mp newA
    have keys := congrArg Prod.fst equal
    have times := congrArg Prod.snd equal
    dsimp only at keys times
    subst key
    subst t
    obtain oldB | newB := Finset.mem_union.mp bMember
    · obtain ⟨point,member,notA,notB,lo,hi,tlo,thi⟩ := valid.new_old_witness access ordered
        (List.mem_toFinset.mp selected) oldB (by dsimp; omega)
      refine ⟨point,member,?_,notA,notB⟩
      have past := valid.time_lt oldB
      simp only [ArboralDilation.InRectangle]
      dsimp only at lo hi tlo
      exact ⟨by omega,by omega,by omega,by omega⟩
    · obtain ⟨_,_,equal⟩ := Finset.mem_image.mp newB
      exact False.elim (timeNe (congrArg Prod.snd equal))

theorem Valid.step {before after : MTR.Tree Int} {request : Int}
    (access : MTR.HullAccess request before after) (ordered : before.Ordered)
    {history memory time} (valid : Valid before history memory time) :
    Valid after (augment history access.source.inorder time)
      (touchTime access.source.inorder time memory) (time+1) := by
  have word := hull_inorder access
  have selectedMember : ∀ key ∈ access.source.inorder, key ∈ before.inorder := by
    intro key member
    have inTree := (inorder_sublist_graft access.source access.gaps 0).subset member
    simpa only [access.source_tree] using inTree
  constructor
  · intro point member
    rw [← word]
    obtain old | fresh := Finset.mem_union.mp member
    · exact valid.keys point old
    · obtain ⟨key,selected,rfl⟩ := Finset.mem_image.mp fresh
      exact selectedMember key (List.mem_toFinset.mp selected)
  · intro key member
    unfold touchTime
    split
    · exact new_mem (by assumption)
    · exact old_mem (valid.latest key (by rwa [word]))
  · intro point member
    obtain old | fresh := Finset.mem_union.mp member
    · unfold touchTime
      split
      · exact (valid.time_lt old).le
      · exact valid.below point old
    · obtain ⟨key,selected,rfl⟩ := Finset.mem_image.mp fresh
      simp only [touchTime,if_pos (List.mem_toFinset.mp selected),le_refl]
  · intro key member
    have past := valid.past key (by rwa [word])
    unfold touchTime
    split <;> omega
  · exact hull_touch_heap access ordered memory time valid.heap (fun key member => (valid.past key member).le)
  · exact valid.augment_satisfied access ordered

theorem augment_card (history : Finset Point) (selected : List Int) (time : Int) :
    (augment history selected time).card ≤ history.card+selected.length := by
  have union := Finset.card_union_le history (selected.toFinset.image (fun key => (key,time)))
  have image := Finset.card_image_le (s := selected.toFinset) (f := fun key => (key,time))
  have distinct := List.toFinset_card_le (l := selected)
  exact union.trans (Nat.add_le_add_left (image.trans distinct) _)

def initialPoints (tree : MTR.Tree Int) : Finset Point := tree.inorder.toFinset.image (fun key => (key,-1))

theorem initial_valid (tree : MTR.Tree Int) : Valid tree (initialPoints tree) (fun _ => -1) 0 := by
  constructor
  · intro point member
    obtain ⟨key,keyMember,rfl⟩ := Finset.mem_image.mp member
    exact List.mem_toFinset.mp keyMember
  · intro key member
    exact Finset.mem_image.mpr ⟨key,List.mem_toFinset.mpr member,rfl⟩
  · intro point member
    obtain ⟨key,_,rfl⟩ := Finset.mem_image.mp member
    exact le_rfl
  · intro key member; decide
  · exact heap_uniform tree (fun _ => -1) (-1) (by simp)
  · intro a t b u aMember bMember _ different
    obtain ⟨_,_,first⟩ := Finset.mem_image.mp aMember
    obtain ⟨_,_,last⟩ := Finset.mem_image.mp bMember
    have firstTime := congrArg Prod.snd first
    have lastTime := congrArg Prod.snd last
    exact False.elim (different (firstTime.symm.trans lastTime))

theorem initialPoints_card (tree : MTR.Tree Int) : (initialPoints tree).card ≤ tree.size := by
  have image := Finset.card_image_le (s := tree.inorder.toFinset) (f := fun key : Int => (key,(-1 : Int)))
  have distinct := List.toFinset_card_le (l := tree.inorder)
  rw [length_inorder] at distinct
  exact image.trans distinct

end TangoSquared.Paper20261030.BSTHistory
