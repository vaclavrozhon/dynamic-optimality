import MultiSplay.JoinPriority
import MultiSplay.InterfaceCommonJoin
import Splay.Lazy.Dynamic

/-!
# A common join retaining the actual rich lazy histories

The output stores both old block lists in order and appends precisely the two
new root intervals. Its interface projection is the constructed strict join
trace. Existing interval minima and pass counters are retained literally.
-/

namespace MultiSplay.RichJoin

open Splay.Tree (BST)
open Splay.Rank (Snapshot External)
open Splay.Lazy (State Block HeapView Element Side)
open Splay.Lazy.Canonical
open JoinIntervals (leftEmbedding rightEmbedding)

variable {l r : Nat}

def rootBlock {n : Nat} (pivot child : Element n) (side : Side) : Block n :=
  ⟨pivot, pivot, side, 0, .growing, [child], 0⟩

noncomputable def state (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (a : State l) (b : State r) : State (0 + l + 1 + r) where
  view := canonicalHeapView (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)
  blocks := a.blocks.map (BlockEmbedding.block (leftEmbedding l r)) ++
    b.blocks.map (BlockEmbedding.block (rightEmbedding l r)) ++
    [rootBlock (JoinRanks.pivot l r) (leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl)) .left,
     rootBlock (JoinRanks.pivot l r) (rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr)) .right]
  value := (InterfaceCommonJoin.final a.toInterface b.toInterface
    (canonicalRoot (Snapshot.ofTree left).withTruePriority sl) (canonicalRoot (Snapshot.ofTree right).withTruePriority sr)).value

theorem toInterface (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (a : State l) (b : State r) :
    (state left right sl sr a b).toInterface = InterfaceCommonJoin.final a.toInterface b.toInterface
      (canonicalRoot (Snapshot.ofTree left).withTruePriority sl) (canonicalRoot (Snapshot.ofTree right).withTruePriority sr) := by
  apply congrArg₂ Splay.Interface.State.mk
  · simp [State.toInterface, state, InterfaceCommonJoin.final, InterfaceForest.priorityJoin, InterfaceForest.setValue, InterfaceForest.join_blocks,
      InterfaceCommonJoin.initial, InterfaceSum.state, List.map_append, List.map_map, Function.comp_def,
      rootBlock, Block.toInterface, BlockEmbedding.block, InterfaceEmbedding.block, InterfaceForest.rootBlock, List.append_assoc]
  · rfl

theorem allElements (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (a : State l) (b : State r) :
    (state left right sl sr a b).allElements =
      a.allElements.map (leftEmbedding l r) ++ b.allElements.map (rightEmbedding l r) ++
      [leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl),
       rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr)] := by
  simp [state, State.allElements, List.flatMap_append, List.flatMap_map, List.map_flatMap,
    BlockEmbedding.block, rootBlock, List.append_assoc]

theorem assigned_permutation (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (a : State l) (b : State r) :
    (state left right sl sr a b).allElements.Perm (JoinIntervals.assigned left right sl sr a.allElements b.allElements) := by
  rw [allElements, (JoinPriority.structure_eq (Snapshot.ofTree left) sl).1,
    (JoinPriority.structure_eq (Snapshot.ofTree right) sr).1]
  simpa only [JoinIntervals.assigned, List.append_assoc] using
    (List.perm_append_comm :
      ((a.allElements.map (leftEmbedding l r) ++ b.allElements.map (rightEmbedding l r)) ++
        [leftEmbedding l r (canonicalRoot (Snapshot.ofTree left) sl), rightEmbedding l r (canonicalRoot (Snapshot.ofTree right) sr)]).Perm
      ([leftEmbedding l r (canonicalRoot (Snapshot.ofTree left) sl), rightEmbedding l r (canonicalRoot (Snapshot.ofTree right) sr)] ++
        (a.allElements.map (leftEmbedding l r) ++ b.allElements.map (rightEmbedding l r))))

theorem attached_assignment (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (a : State l) (b : State r) (owner : Element (0 + l + 1 + r)) (side : Side) :
    (state left right sl sr a b).view.attachedTopDown (state left right sl sr a b).allElements owner side =
      (state left right sl sr a b).view.attachedTopDown
        (JoinIntervals.assigned left right sl sr a.allElements b.allElements) owner side := by
  unfold HeapView.attachedTopDown
  apply List.filter_congr
  intro element _
  simp only [(assigned_permutation left right sl sr a b).mem_iff]

theorem rootBlock_valid {n : Nat} (view : HeapView n) (assigned : List (Element n))
    (pivot child : Element n) (side : Side)
    (parent : view.parent child = some pivot) (childSide : view.side child = side)
    (member : child ∈ assigned) (gap : 0 ≤ view.rawGap child) :
    (rootBlock pivot child side).StructurallyValid view assigned := by
  refine ⟨?_, fun _ => rfl, ?_⟩
  · have inChildren := view.mem_attachedTopDown_iff.mpr ⟨view.mem_topDown_iff.mpr ⟨parent, childSide⟩, member⟩
    obtain ⟨front, back, equation⟩ := List.mem_iff_append.mp inChildren
    exact ⟨front, back, by simpa [rootBlock] using equation⟩
  · simp only [rootBlock, Block.GapValid, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨trivial, fun element same => same.symm ▸ gap⟩

theorem interface_trace {params : Splay.Interface.Parameters}
    (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r) (a : State l) (b : State r)
    (aRep : a.Represents params (Snapshot.ofTree left).withTruePriority sl)
    (bRep : b.Represents params (Snapshot.ofTree right).withTruePriority sr)
    (growingLimit : 2 ≤ params.growingLimit) (valueCap : 3 ≤ params.valueBound) :
    Splay.Interface.Trace params (InterfaceCommonJoin.initial a.toInterface b.toInterface)
      (InterfaceCommonJoin.operations a.toInterface b.toInterface
        (canonicalRoot (Snapshot.ofTree left).withTruePriority sl) (canonicalRoot (Snapshot.ofTree right).withTruePriority sr))
      (state left right sl sr a b).toInterface := by
  rw [toInterface]
  apply InterfaceCommonJoin.trace _ _ _ _ aRep.valid.1 bRep.valid.1
  · simpa only [State.toInterface_allElements, aRep.view_eq, canonicalHeapView] using aRep.stable.root_not_mem
  · simpa only [State.toInterface_allElements, bRep.view_eq, canonicalHeapView] using bRep.stable.root_not_mem
  · simpa only [State.toInterface, aRep.view_eq, canonicalHeapView] using aRep.valuesRealizeGaps.1
  · simpa only [State.toInterface, bRep.view_eq, canonicalHeapView] using bRep.valuesRealizeGaps.1
  · exact growingLimit
  · exact valueCap

theorem valid {params : Splay.Interface.Parameters}
    (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r) (a : State l) (b : State r)
    (aRep : a.Represents params (Snapshot.ofTree left).withTruePriority sl)
    (bRep : b.Represents params (Snapshot.ofTree right).withTruePriority sr)
    (growingLimit : 2 ≤ params.growingLimit) (valueCap : 3 ≤ params.valueBound) :
    (state left right sl sr a b).Valid params := by
  have aRoot : canonicalRoot (Snapshot.ofTree left).withTruePriority sl ∉ a.allElements := by
    simpa only [aRep.view_eq, canonicalHeapView] using aRep.stable.root_not_mem
  have bRoot : canonicalRoot (Snapshot.ofTree right).withTruePriority sr ∉ b.allElements := by
    simpa only [bRep.view_eq, canonicalHeapView] using bRep.stable.root_not_mem
  refine ⟨InterfaceForest.trace_final_valid (interface_trace left right sl sr a b aRep bRep growingLimit valueCap), ?_⟩
  intro block member
  change block ∈ _ ++ _ ++ _ at member
  rcases List.mem_append.mp member with old | fresh
  · rcases List.mem_append.mp old with oldLeft | oldRight
    · obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp oldLeft
      have oldValid := aRep.valid.2 original originalMem
      rw [aRep.view_eq] at oldValid
      have retained := JoinPriority.left_structurallyValid left right sl sr a.allElements b.allElements aRoot bRoot original oldValid
      refine ⟨?_, retained.2⟩
      rw [attached_assignment]
      exact retained.1
    · obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp oldRight
      have oldValid := bRep.valid.2 original originalMem
      rw [bRep.view_eq] at oldValid
      have retained := JoinPriority.right_structurallyValid left right sl sr a.allElements b.allElements aRoot bRoot original oldValid
      refine ⟨?_, retained.2⟩
      rw [attached_assignment]
      exact retained.1
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    have doubled := JoinPriority.structure_eq (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree sl sr)
    rcases fresh with rfl | rfl
    · apply rootBlock_valid
      · change canonicalParent _ _ _ = _
        rw [doubled.2.1, (JoinPriority.structure_eq (Snapshot.ofTree left) sl).1]
        exact JoinHeap.left_root_parent left right sl sr
      · change canonicalSide _ _ _ = _
        rw [doubled.2.2, (JoinPriority.structure_eq (Snapshot.ofTree left) sl).1]
        exact JoinIntervals.left_root_side left right sl sr
      · rw [allElements]
        simp
      · have gap := JoinPriority.left_root_rawGap left right sl sr
        change 0 ≤ (canonicalHeapView _ _).rawGap _
        rw [gap]
        decide
    · apply rootBlock_valid
      · change canonicalParent _ _ _ = _
        rw [doubled.2.1, (JoinPriority.structure_eq (Snapshot.ofTree right) sr).1]
        exact JoinHeap.right_root_parent left right sl sr
      · change canonicalSide _ _ _ = _
        rw [doubled.2.2, (JoinPriority.structure_eq (Snapshot.ofTree right) sr).1]
        exact JoinIntervals.right_root_side left right sl sr
      · rw [allElements]
        simp
      · have gap := JoinPriority.right_root_rawGap left right sl sr
        change 0 ≤ (canonicalHeapView _ _).rawGap _
        rw [gap]
        decide

theorem root_eq (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (a : State l) (b : State r) : (state left right sl sr a b).view.root = JoinRanks.pivot l r := by
  change canonicalRoot _ _ = _
  rw [(JoinPriority.structure_eq (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree sl sr)).1]
  exact JoinIntervals.root_eq left right sl sr

theorem complete {params : Splay.Interface.Parameters}
    (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r) (a : State l) (b : State r)
    (aRep : a.Represents params (Snapshot.ofTree left).withTruePriority sl)
    (bRep : b.Represents params (Snapshot.ofTree right).withTruePriority sr) :
    (state left right sl sr a b).Complete := by
  have leftMem : ∀ element : Element l, leftEmbedding l r element ∈ (state left right sl sr a b).allElements := by
    intro element
    rw [allElements]
    by_cases isRoot : element = canonicalRoot (Snapshot.ofTree left).withTruePriority sl
    · simp [isRoot]
    · have notRoot : element ≠ a.view.root := by simpa only [aRep.view_eq, canonicalHeapView] using isRoot
      have member : element ∈ a.allElements := (aRep.complete element).mpr
        (fun parentNone => notRoot (a.view.parent_eq_none element parentNone))
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨element, member, rfl⟩))
  have rightMem : ∀ element : Element r, rightEmbedding l r element ∈ (state left right sl sr a b).allElements := by
    intro element
    rw [allElements]
    by_cases isRoot : element = canonicalRoot (Snapshot.ofTree right).withTruePriority sr
    · simp [isRoot]
    · have notRoot : element ≠ b.view.root := by simpa only [bRep.view_eq, canonicalHeapView] using isRoot
      have member : element ∈ b.allElements := (bRep.complete element).mpr
        (fun parentNone => notRoot (b.view.parent_eq_none element parentNone))
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨element, member, rfl⟩))
  have pivotFree : JoinRanks.pivot l r ∉ (state left right sl sr a b).allElements := by
    rw [allElements]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map]
    rintro ((⟨x, _, same⟩ | ⟨x, _, same⟩) | (same | same))
    · exact JoinIntervals.left_ne_pivot l r x same
    · exact JoinIntervals.right_ne_pivot l r x same
    · exact JoinIntervals.left_ne_pivot l r _ same.symm
    · exact JoinIntervals.right_ne_pivot l r _ same.symm
  intro element
  constructor
  · intro member parentNone
    have isRoot := (state left right sl sr a b).view.parent_eq_none element parentNone
    rw [root_eq] at isRoot
    exact pivotFree (isRoot ▸ member)
  · intro nonroot
    rcases JoinIntervals.cases_element l r element with ⟨x, rfl⟩ | rfl | ⟨x, rfl⟩
    · exact leftMem x
    · exact False.elim (nonroot (by rw [← root_eq left right sl sr a b]; exact (state left right sl sr a b).view.root_parent))
    · exact rightMem x

theorem valuesRealizeGaps {params : Splay.Interface.Parameters}
    (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r) (a : State l) (b : State r)
    (aRep : a.Represents params (Snapshot.ofTree left).withTruePriority sl)
    (bRep : b.Represents params (Snapshot.ofTree right).withTruePriority sr) :
    (state left right sl sr a b).ValuesRealizeGaps := by
  constructor
  · rw [root_eq]
    change (InterfaceCommonJoin.final _ _ _ _).value _ = 1
    rw [InterfaceCommonJoin.final, InterfaceForest.priorityJoin_other_value]
    · exact InterfaceSum.value_outside _ _ _ _ _
        (by rintro ⟨x, same⟩; exact JoinIntervals.left_ne_pivot l r x same)
        (by rintro ⟨x, same⟩; exact JoinIntervals.right_ne_pivot l r x same)
    · exact (JoinIntervals.left_ne_pivot _ _ _).symm
    · exact (JoinIntervals.right_ne_pivot _ _ _).symm
  · intro block member element elementMem
    change block ∈ _ ++ _ ++ _ at member
    rcases List.mem_append.mp member with old | fresh
    · rcases List.mem_append.mp old with oldLeft | oldRight
      · obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp oldLeft
        obtain ⟨oldElement, oldMem, rfl⟩ := List.mem_map.mp elementMem
        have oldValid := aRep.valid.2 original originalMem
        rw [aRep.view_eq] at oldValid
        have notRoot := BlockEmbedding.member_ne_root _ original a.allElements oldValid oldMem
        change oldElement ≠ canonicalRoot (Snapshot.ofTree left).withTruePriority sl at notRoot
        have oldValue := aRep.valuesRealizeGaps.2 original originalMem oldElement oldMem
        rw [aRep.view_eq] at oldValue
        change (InterfaceCommonJoin.final _ _ _ _).value _ =
          Splay.Analysis.transientContractedGap ((canonicalHeapView _ _).rawGap _) original.intervalGap
        rw [InterfaceCommonJoin.old_left_value _ _ _ _ _ notRoot]
        rw [JoinPriority.left_rawGap left right sl sr notRoot]
        exact oldValue
      · obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp oldRight
        obtain ⟨oldElement, oldMem, rfl⟩ := List.mem_map.mp elementMem
        have oldValid := bRep.valid.2 original originalMem
        rw [bRep.view_eq] at oldValid
        have notRoot := BlockEmbedding.member_ne_root _ original b.allElements oldValid oldMem
        change oldElement ≠ canonicalRoot (Snapshot.ofTree right).withTruePriority sr at notRoot
        have oldValue := bRep.valuesRealizeGaps.2 original originalMem oldElement oldMem
        rw [bRep.view_eq] at oldValue
        change (InterfaceCommonJoin.final _ _ _ _).value _ =
          Splay.Analysis.transientContractedGap ((canonicalHeapView _ _).rawGap _) original.intervalGap
        rw [InterfaceCommonJoin.old_right_value _ _ _ _ _ notRoot]
        rw [JoinPriority.right_rawGap left right sl sr notRoot]
        exact oldValue
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl
      · simp only [rootBlock, List.mem_cons, List.not_mem_nil, or_false] at elementMem
        subst element
        change (InterfaceCommonJoin.final _ _ _ _).value _ =
          Splay.Analysis.transientContractedGap ((canonicalHeapView _ _).rawGap _) 0
        rw [InterfaceCommonJoin.final, InterfaceForest.priorityJoin_left_value _ _ _ _ (JoinIntervals.disjoint _ _ _ _).symm,
          JoinPriority.left_root_rawGap, JoinPriority.root_contracted]
      · simp only [rootBlock, List.mem_cons, List.not_mem_nil, or_false] at elementMem
        subst element
        change (InterfaceCommonJoin.final _ _ _ _).value _ =
          Splay.Analysis.transientContractedGap ((canonicalHeapView _ _).rawGap _) 0
        rw [InterfaceCommonJoin.final, InterfaceForest.priorityJoin_right_value,
          JoinPriority.right_root_rawGap, JoinPriority.root_contracted]

end MultiSplay.RichJoin
