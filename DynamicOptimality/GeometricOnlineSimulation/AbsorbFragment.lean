import DynamicOptimality.GeometricOnlineSimulation.Linearize
import DynamicOptimality.GeometricOnlineSimulation.AbsorbSpine

/-!
# Inserting an expanded perfect-block fragment at a deque end

The fragment's marked skeleton is first turned into a spine, preserving
every untouched perfect block. Its separators are then absorbed into the
existing deque. The cost depends only on newly exposed separators.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR ChaCha.MTR.Pointer SearchRotation DynamicOptimality.SingleFinger
open DynamicOptimality.MultiFinger.TendonDeque (trailing)

theorem to_right_spine (marked : MarkedTree Nat) :
    ∃ count ≤ 6 * marked.skeleton.size,
      Rotations marked.erase
        (Spine.rightSpine (Chain.ofMarked marked).first (Chain.ofMarked marked).cells) count := by
  let chain := Chain.ofMarked marked
  let target := markRight (.hole chain.first) chain.cells
  have holes : marked.holes = target.holes := by
    simpa only [target, markRight_holes, MarkedTree.holes, List.singleton_append] using
      (Chain.holes_ofMarked marked).symm
  have keys : marked.skeleton.inorder = target.skeleton.inorder := by
    simpa only [target, markRight_keys, MarkedTree.skeleton, Tree.inorder, List.nil_append] using
      (Chain.keys_ofMarked marked).symm
  obtain ⟨count, bound, run⟩ := marked_rotations marked target holes keys
  exact ⟨count, bound, by simpa only [target, markRight_erase, MarkedTree.erase] using run⟩

theorem to_left_spine (marked : MarkedTree Nat) :
    ∃ count ≤ 6 * marked.skeleton.size,
      Rotations marked.erase
        (Spine.leftSpine (Chain.ofMarked marked).first (Chain.ofMarked marked).cells) count := by
  let chain := Chain.ofMarked marked
  let target := markLeft (.hole chain.first) chain.cells
  have holes : marked.holes = target.holes := by
    simpa only [target, markLeft_holes, MarkedTree.holes, List.singleton_append] using
      (Chain.holes_ofMarked marked).symm
  have keys : marked.skeleton.inorder = target.skeleton.inorder := by
    simpa only [target, markLeft_keys, MarkedTree.skeleton, Tree.inorder, List.nil_append] using
      (Chain.keys_ofMarked marked).symm
  obtain ⟨count, bound, run⟩ := marked_rotations marked target holes keys
  exact ⟨count, bound, by simpa only [target, markLeft_erase, MarkedTree.erase] using run⟩

theorem Chain.length_ofMarked (marked : MarkedTree Nat) :
    (ofMarked marked).cells.length = marked.skeleton.size := by
  have keys := congrArg List.length (keys_ofMarked marked)
  simpa only [List.length_map, Tree.length_inorder] using keys

namespace OpenDeque

theorem Right.absorb_fragment (outer : Right Nat) (fragment : Fragment Nat) :
    let chain := Chain.ofMarked fragment.marked
    ∃ count,
      Rotations (outer.fill fragment.marked.erase).tree
        ((outer.absorb chain.first chain.cells).fill (trailing chain.first chain.cells)).tree count ∧
      count + (outer.absorb chain.first chain.cells).potential ≤
        outer.potential + 11 * fragment.marked.skeleton.size := by
  let chain := Chain.ofMarked fragment.marked
  obtain ⟨turn, turnBound, turnRun⟩ := to_right_spine fragment.marked
  obtain ⟨absorb, absorbCount, absorbRun, absorbBound⟩ := outer.absorb_rotations chain.first chain.cells
  have lifted : Rotations (outer.fill fragment.marked.erase).tree
      (outer.fill (Spine.rightSpine chain.first chain.cells)).tree turn := by
    simpa only [Right.fill_tree] using outer.port.lift turnRun
  refine ⟨turn + absorb, lifted.append absorbRun, ?_⟩
  change turn + absorb + (outer.absorb chain.first chain.cells).potential ≤
    outer.potential + 11 * fragment.marked.skeleton.size
  have length : chain.cells.length = fragment.marked.skeleton.size := Chain.length_ofMarked _
  rw [length] at absorbBound
  omega

theorem Left.absorb_fragment (outer : Left Nat) (fragment : Fragment Nat) :
    let chain := Chain.ofMarked fragment.marked
    ∃ count,
      Rotations (outer.fill fragment.marked.erase).tree
        ((outer.absorb chain.cells).fill chain.first).tree count ∧
      count + (outer.absorb chain.cells).potential ≤
        outer.potential + 11 * fragment.marked.skeleton.size := by
  let chain := Chain.ofMarked fragment.marked
  obtain ⟨turn, turnBound, turnRun⟩ := to_left_spine fragment.marked
  obtain ⟨absorb, absorbCount, absorbRun, absorbBound⟩ := outer.absorb_rotations chain.first chain.cells
  have lifted : Rotations (outer.fill fragment.marked.erase).tree
      (outer.fill (Spine.leftSpine chain.first chain.cells)).tree turn := by
    simpa only [Left.fill_tree] using outer.port.lift turnRun
  refine ⟨turn + absorb, lifted.append absorbRun, ?_⟩
  change turn + absorb + (outer.absorb chain.cells).potential ≤
    outer.potential + 11 * fragment.marked.skeleton.size
  have length : chain.cells.length = fragment.marked.skeleton.size := Chain.length_ofMarked _
  rw [length] at absorbBound
  omega

end OpenDeque

end DynamicOptimality.GeometricOnlineSimulation
